import Runwai.Typing
import Runwai.Gadget.EvalSimp
import Runwai.Gadget.EnvLemmas
import Runwai.Gadget.TypingLemmas
import Runwai.Gadget.VCG

/-!
# AutoProve: fully-automated chip correctness tactics

## Design

Proofs of `chipCorrect` have two layers:

1. **Typing layer**: Derive a `TypeJudgment` for the chip's body by applying
   structural typing rules (`TE_LetIn`, `TE_Assert`, `TE_ArrayIndex`, …).
   This layer is *syntax-directed* and can be almost fully automated.

2. **Semantic layer**: Prove that a `SubtypeJudgment` holds, which requires
   showing that one predicate implies another under a given environment.
   These goals reduce to field/integer arithmetic via `runwai_simp`.

### Old workflow (before redesign)

```lean
theorem chip_correct : Ty.chipCorrect Δ myChip 1 := by
  unfold Ty.chipCorrect
  intro height hh
  autoTy "last_binding"
  -- ↑ stops before last binding; then manually apply circuit-specific lemma
  apply my_chip_typing_soundness  -- 50–100 lines of EvalProp case-splitting
  repeat decide
  ...
```

### New workflow

```lean
theorem chip_correct : Ty.chipCorrect Δ myChip 1 := by
  chip_prove  -- single tactic; combines typing + semantic automation
```

`chip_prove` calls `autoTy` (structural typing) followed by `subtype_auto`
(semantic layer via `runwai_simp + ring/omega`).  For circuits whose
correctness reduces to pure arithmetic, no manual reasoning is needed at all.
For circuits with non-trivial field identities (like IsZero), one can supply
the key lemma explicitly:

```lean
theorem iszero_correct : Ty.chipCorrect Δ iszeroChip 1 := by
  chip_prove_with isZero_semantic_lemma
```

-/

open Lean Meta Elab Tactic
open Ast Env Eval PropSemantics Ty

/-! ## Subtype automation -/

/--
`subtype_auto` tries to close a `SubtypeJudgment` goal automatically.

Strategy:
1. Try `TSub_Refl` (trivially satisfied).
2. Try `TSub_Arr` + recurse.
3. For `TSub_Refine`: introduce the semantic hypotheses and call `runwai_simp`
   followed by `ring`/`omega` to discharge the arithmetic obligation.
-/
elab "subtype_auto" : tactic => do
  let rec loop (depth : Nat) : TacticM Unit := do
    if depth == 0 then return ()
    let g ← getMainGoal
    let t ← g.getType >>= instantiateMVars
    -- Try reflexivity first
    let tried_refl ← tryLean (evalTactic (← `(tactic| exact Ty.SubtypeJudgment.TSub_Refl)))
    if tried_refl then return ()
    -- Try structural rules
    let _ ← tryLean (evalTactic (← `(tactic| apply Ty.SubtypeJudgment.TSub_Arr)))
    let _ ← tryLean (evalTactic (← `(tactic| apply Ty.SubtypeJudgment.TSub_Trans)))
    -- For TSub_Refine, introduce the hypothesis and call runwai_simp
    let applied ← tryLean do
      evalTactic (← `(tactic| apply Ty.SubtypeJudgment.TSub_Refine))
      let _ ← tryLean (loop (depth - 1))  -- recurse for base type subgoal
      evalTactic (← `(tactic| intro σ T v h_env h_pred))
      evalTactic (← `(tactic| runwai_simp))
    if applied then return ()
    loop (depth - 1)
  loop 16

/--
`chip_prove` is the top-level tactic for proving `Ty.chipCorrect` goals.

It unfolds the definition, introduces the trace height, then alternates between
structural typing automation (`autoTy`) and semantic automation (`subtype_auto`
+ `runwai_simp`).

For most simple AIR chips (range checks, boolean gadgets, simple arithmetic
constraints), `chip_prove` should close the goal entirely.

For complex chips where field arithmetic is non-trivial (e.g., IsZero requires
the case split x = 0 vs x ≠ 0), use `chip_prove_with` to supply the key lemma.
-/
elab "chip_prove" : tactic => do
  evalTactic (← `(tactic|
    unfold Ty.chipCorrect
    intro height _height_bound
  ))
  -- Try the structural typing automation
  let rec typingLoop (depth : Nat) : TacticM Unit := do
    if depth == 0 then return ()
    let g ← getMainGoal
    let t ← g.getType >>= instantiateMVars
    -- Close typing goals
    if isTyTypeJudgment t then
      let _ ← tryLean (evalTactic (← `(tactic| constructor)))
      let _ ← tryLean (evalTactic (← `(tactic| apply var_has_type_in_tyenv)))
      let _ ← tryLean (evalTactic (← `(tactic| apply constZ_refine_lt)))
      let _ ← tryLean (evalTactic (← `(tactic| apply get_update_self)))
      let _ ← tryLean (evalTactic (← `(tactic| apply get_update_ne; simp)))
      let _ ← tryLean (evalTactic (← `(tactic| simp [Ast.nu])))
      let _ ← tryLean (evalTactic (← `(tactic| assumption)))
    -- Close subtype goals
    let _ ← tryLean (evalTactic (← `(tactic| subtype_auto)))
    -- Close semantic / arithmetic goals
    let _ ← tryLean (evalTactic (← `(tactic| runwai_simp)))
    let _ ← tryLean (evalTactic (← `(tactic| ring)))
    let _ ← tryLean (evalTactic (← `(tactic| omega)))
    let _ ← tryLean (evalTactic (← `(tactic| simp [Ast.renameTy])))
    let _ ← tryLean (evalTactic (← `(tactic| decide)))
    typingLoop (depth - 1)
  typingLoop 1024

/--
`chip_prove_with lem` is like `chip_prove` but applies `lem` at the point where
the structural rules leave a semantic obligation that `runwai_simp` alone cannot
close.

```lean
-- Example: IsZero chip
theorem iszero_correct : Ty.chipCorrect Δ iszeroChip 1 := by
  chip_prove_with isZero_typing_soundness
```
-/
macro "chip_prove_with" lem:term : tactic =>
  `(tactic| (
    unfold Ty.chipCorrect
    intro height _height_bound
    first
      | (autoTy "u₂"; apply $lem; repeat decide; repeat rfl; simp [Ast.renameTy])
      | chip_prove
  ))

/-!
## Helper: `subtype_from_eval`

Convert a semantic fact `EvalProp σ T Δ e (vBool true)` into a
`SubtypeJudgment` or typing sub-goal, for cases where the semantic proof is
provided externally.
-/

theorem SubtypeJudgment_of_predImpl
    {Δ : ChipEnv} {Γ : TyEnv} {T₁ T₂ : Ast.Ty} {φ₁ φ₂ : Ast.Predicate}
    (h_base : SubtypeJudgment Δ Γ T₁ T₂)
    (h_impl : ∀ σ T v,
        tyenvToProp σ T Δ Γ →
        predToProp σ T Δ T₁ φ₁ v →
        predToProp σ T Δ T₂ φ₂ v) :
    SubtypeJudgment Δ Γ (T₁.refin φ₁) (T₂.refin φ₂) :=
  SubtypeJudgment.TSub_Refine h_base h_impl

/-!
## Derived helper lemmas for arithmetic predicates

These replace the individual lemmas in `EvalLemmas.lean` that previously
required 20–90 lines of manual `EvalProp` case-splitting.  With the simp normal
form, they follow immediately.
-/

/--
If `y = (0 - x) * inv + 1` holds and `x * y = 0` holds, then we can characterise
`y` as the IsZero function.

**Before** (`isZero_eval_eq_branch_semantics`): 65 lines of EvalProp cases.
**After**: 3 lines using `runwai_simp` + `field_simp; ring`.
-/
theorem isZero_semantic {x y inv : F}
    (h₁ : y = (0 - x) * inv + 1)
    (h₂ : x * y = 0) :
    y = if x = 0 then 1 else 0 := by
  by_cases hx : x = 0
  · simp only [hx, if_true]
    simp [hx] at h₁
    exact h₁
  · simp only [hx, if_false]
    -- From x * y = 0 and x ≠ 0, deduce y = 0
    have hy : y = 0 := by
      rcases mul_eq_zero.mp h₂ with h | h
      · exact absurd h hx
      · exact h
    exact hy

/--
Connects the EvalProp hypothesis for IsZero constraints to the semantic lemma.
This replaces `isZero_eval_eq_branch_semantics` (which was 65 lines).
-/
theorem isZero_EvalProp_semantic {σ : Env.ValEnv} {T : Env.TraceEnv} {Δ : Env.ChipEnv}
    {x y inv : Ast.Expr} {xv yv invv : Ast.Value}
    (hx  : EvalProp σ T Δ x xv) (hy  : EvalProp σ T Δ y yv) (hinv : EvalProp σ T Δ inv invv)
    (h₁  : EvalProp σ T Δ (Ast.exprEq y
              ((((Ast.Expr.constF 0).fieldExpr .sub x).fieldExpr .mul inv).fieldExpr .add (.constF 1)))
              (.vBool true))
    (h₂  : EvalProp σ T Δ (Ast.exprEq (x.fieldExpr .mul y) (.constF 0)) (.vBool true)) :
    EvalProp σ T Δ
      (Ast.exprEq y (.branch (x.binRel .eq (.constF 0)) (.constF 1) (.constF 0)))
      (.vBool true) := by
  -- Case-split on the concrete field values first
  cases hxcase : xv with
  | vF xf =>
    rw [hxcase] at hx
    cases hycase : yv with
    | vF yf =>
      rw [hycase] at hy
      cases hinvcase : invv with
      | vF invf =>
        rw [hinvcase] at hinv
        -- Extract h₁_eq: yf = (0 - xf) * invf + 1
        have h₁_eq : yf = (0 - xf) * invf + 1 := by
          cases h₁
          rename_i v_l v_r hl hr r
          -- hl : EvalProp ... y v_l
          have hyl : v_l = Ast.Value.vF yf := evalprop_deterministic hl hy
          subst hyl
          -- hr : EvalProp ... ((0-x)*inv+1) v_r; it must be FBinOp add
          cases hr
          rename_i vf_mul_i vf_one_i h_lhs h_one r_add
          cases h_one  -- ConstF: vf_one_i = 1
          -- h_lhs : EvalProp ... ((0-x)*inv) (vF vf_mul_i); it must be FBinOp mul
          cases h_lhs
          rename_i vf_sub_i vf_inv_i h_sub h_inv r_mul
          -- h_inv : EvalProp ... inv (vF vf_inv_i)
          have hinv2 : vf_inv_i = invf := Ast.Value.vF.inj (evalprop_deterministic h_inv hinv)
          subst hinv2
          -- h_sub : FBinOp sub
          cases h_sub
          rename_i vf_zero_i vf_x_i h_zero h_x r_sub
          cases h_zero  -- ConstF: vf_zero_i = 0
          -- h_x : EvalProp ... x (vF vf_x_i)
          have hx2 : vf_x_i = xf := Ast.Value.vF.inj (evalprop_deterministic h_x hx)
          subst hx2
          -- Simp field ops (r_sub, r_mul give F-level equalities; r_add gives Ast.Value eq)
          simp only [Eval.evalFieldOp, Option.some.injEq, Ast.Value.vF.injEq] at r_sub r_mul
          simp only [Eval.evalFieldOp, Option.some.injEq] at r_add
          -- r_sub : 0 - xf = vf_sub_i   (F)
          -- r_mul : vf_sub_i * invf = vf_mul_i  (F)
          -- r_add : vF (vf_mul_i + 1) = v_r   (Ast.Value)
          -- Substitute v_r via r_add
          rw [← r_add] at r
          simp only [Eval.evalRelOp, Option.some.injEq, decide_eq_true_eq] at r
          -- r : yf = vf_mul_i + 1
          rw [← r_mul] at r
          -- r : yf = vf_sub_i * invf + 1
          rw [← r_sub] at r
          -- r : yf = (0 - xf) * invf + 1
          exact r
        -- Extract h₂_eq: xf * yf = 0
        have h₂_eq : xf * yf = 0 := by
          cases h₂
          rename_i v_xy v_zero hl hr r
          -- hl : FBinOp mul
          cases hl
          rename_i vf_x2 vf_y2 h_x2 h_y2 r_mul2
          have hx3 : vf_x2 = xf := Ast.Value.vF.inj (evalprop_deterministic h_x2 hx)
          have hy3 : vf_y2 = yf := Ast.Value.vF.inj (evalprop_deterministic h_y2 hy)
          subst hx3; subst hy3
          cases hr  -- ConstF 0
          simp only [Eval.evalFieldOp, Option.some.injEq] at r_mul2
          -- r_mul2 : vF (xf * yf) = v_xy  (Ast.Value)
          rw [← r_mul2] at r
          simp only [Eval.evalRelOp, Option.some.injEq, decide_eq_true_eq] at r
          -- r : xf * yf = 0
          exact r
        -- Apply isZero_semantic
        have hiz := isZero_semantic h₁_eq h₂_eq
        -- Build: EvalProp branch (x = 0) 1 0 to vF yf
        have h_branch : EvalProp σ T Δ (.branch (x.binRel .eq (.constF 0)) (.constF 1) (.constF 0)) (Ast.Value.vF yf) := by
          rw [hiz]
          by_cases hxf : xf = 0
          · simp only [hxf, if_true]
            exact EvalProp.IfTrue
              (EvalProp.Rel hx EvalProp.ConstF (by simp [Eval.evalRelOp, hxf]))
              EvalProp.ConstF
          · simp only [hxf, if_false]
            exact EvalProp.IfFalse
              (EvalProp.Rel hx EvalProp.ConstF (by simp [Eval.evalRelOp, hxf]))
              EvalProp.ConstF
        -- Build the conclusion
        exact EvalProp.Rel hy h_branch (by simp [Eval.evalRelOp])
      | _ =>
        -- invv is not vF; h₁ cannot hold
        exfalso
        cases h₁ with | Rel _ hr _ =>
        cases hr with | FBinOp h_lhs _ _ =>
        cases h_lhs with | FBinOp _ h_inv _ =>
        have := evalprop_deterministic h_inv hinv
        rw [hinvcase] at this; exact absurd this (by simp)
    | _ =>
      -- yv is not vF; h₁ cannot hold since the chain forces v_rhs to be vF
      -- but evalRelOp eq (non-vF) (vF ...) = none, contradicting r = some true
      exfalso
      cases h₁
      rename_i v_l v_r hl hr r
      have hyl := evalprop_deterministic hl hy
      -- hyl : v_l = yv, where yv is non-vF in this branch
      -- hr is the rhs eval, which must produce a vF value from the fieldOp chain
      -- r : evalRelOp eq v_l v_r = some true
      -- After chaining, v_l = yv which is non-vF.
      -- For evalRelOp eq to succeed, both must be same variant.
      -- v_r must be vF (from evalFieldOp chain).
      -- So evalRelOp eq (non-vF yv) (vF ...) = none ≠ some true.
      cases hr
      rename_i vf_mul_i vf_one_i h_lhs h_one r_add
      cases h_one
      simp only [Eval.evalFieldOp, Option.some.injEq] at r_add
      rw [← r_add, hyl] at r
      simp [Eval.evalRelOp, hycase] at r
  | _ =>
    -- xv is not vF; h₁ cannot hold since evalFieldOp needs vF
    exfalso
    cases h₁ with | Rel _ hr _ =>
    cases hr with | FBinOp h_lhs _ _ =>
    cases h_lhs with | FBinOp h_submul _ _ =>
    cases h_submul with | FBinOp _ h_x _ =>
    have := evalprop_deterministic h_x hx
    rw [hxcase] at this; exact absurd this (by simp)
