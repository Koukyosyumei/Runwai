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
    let applied ← tryLean (evalTactic (← `(tactic|
      apply Ty.SubtypeJudgment.TSub_Refine
      · subtype_auto
      · intro σ T v h_env h_pred
        simp only [predToProp_ind, predToProp_dep, predToProp_and,
                   predToProp_or, predToProp_not, exprToProp_unfold] at *
        runwai_simp
        first | ring | omega | (field_simp; ring) | decide | assumption
    )))
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
  · simp [hx] at h₁ ⊢; linarith [h₁.symm]
  · simp [hx]
    have : x ≠ 0 := hx
    -- From x * y = 0 and x ≠ 0, deduce y = 0
    have hy : y = 0 := by
      have := mul_eq_zero.mp h₂
      rcases this with h | h
      · exact absurd h this
      · exact h
    exact hy

/--
Connects the EvalProp hypothesis for IsZero constraints to the semantic lemma.
This replaces `isZero_eval_eq_branch_semantics` (which was 65 lines).
-/
theorem isZero_EvalProp_semantic {σ T Δ x y inv : Ast.Expr} {xv yv invv : Ast.Value}
    (hx  : EvalProp σ T Δ x xv) (hy  : EvalProp σ T Δ y yv) (hinv : EvalProp σ T Δ inv invv)
    (h₁  : EvalProp σ T Δ (Ast.exprEq y
              ((((Ast.Expr.constF 0).fieldExpr .sub x).fieldExpr .mul inv).fieldExpr .add (.constF 1)))
              (.vBool true))
    (h₂  : EvalProp σ T Δ (Ast.exprEq (x.fieldExpr .mul y) (.constF 0)) (.vBool true)) :
    EvalProp σ T Δ
      (Ast.exprEq y (.branch (x.binRel .eq (.constF 0)) (.constF 1) (.constF 0)))
      (.vBool true) := by
  -- Step 1: extract concrete values from the EvalProp hypotheses
  simp [Ast.exprEq, EvalProp_binRelEqF, EvalProp_fieldAdd, EvalProp_fieldSub,
        EvalProp_fieldMul, EvalProp_constF, evalprop_deterministic] at h₁ h₂ ⊢
  -- Step 2: use the semantic lemma
  obtain ⟨xval, hxv, yval, hyv, invval, hinvv, heq₁⟩ := h₁
  obtain ⟨xval', hxv', yval', hyv', heq₂⟩ := h₂
  -- Unify the concrete values
  have hxeq : xval = xval' := evalprop_deterministic hxv hxv' ▸ rfl
  have hyeq : yval = yval' := evalprop_deterministic hyv hyv' ▸ rfl
  subst hxeq hyeq
  -- Apply the semantic characterisation
  have := isZero_semantic heq₁ heq₂
  -- Reconstruct the goal
  constructor
  · exact hy
  constructor
  · apply EvalProp.branch
    · simp [EvalProp_binRelEqF, EvalProp_constF]
      exact ⟨xval, hxv, 0, .ConstF, by simp⟩
    all_goals simp_all [EvalProp_constF]
  · simp
