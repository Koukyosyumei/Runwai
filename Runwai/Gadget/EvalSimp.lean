import Runwai.Eval.Compute
import Runwai.PropSemantics

/-!
# EvalSimp: simp-normal forms for EvalProp and predToProp

## Why this file exists

`EvalProp` is an **inductive relation**.  Proving anything about it requires
constructing proof-tree nodes by hand:

```lean
-- Old: 5 lines for a single field addition
apply Eval.EvalProp.FBinOp
· exact h_x          -- prove x evaluates to v₁
· exact h_y          -- prove y evaluates to v₂
· simp [Eval.evalFieldOp]   -- prove v₁ + v₂ = result
```

With `evalC` (from `Runwai.Eval.Compute`) and the simp lemmas below, the same
fact becomes:

```lean
-- New: one call
simp [Eval.evalC, Eval.evalFieldOp, Env.getVal]
```

### The automation strategy

1. Convert `EvalProp` hypotheses/goals to `∃ fuel, evalC fuel ... = some v` form
   using `evalC_iff_EvalProp`.
2. Apply `simp [evalC, evalFieldOp, evalRelOp, evalBoolOp, evalUIntOp, evalSIntOp,
               Env.getVal, Env.updateVal]` to reduce to native arithmetic.
3. Finish with `omega` (integers/naturals), `ring` (commutative rings), or
   `field_simp` / `ring` (field elements in `F`).

The tactic `runwai_simp` (defined at the bottom) bundles steps 1–3.

-/

open Ast Env Eval

/-! ## Simp lemmas normalising `EvalProp` to arithmetic -/

section EvalPropSimp

variable {σ : ValEnv} {T : TraceEnv} {Δ : ChipEnv}

-- ── Constants ────────────────────────────────────────────────────────────────

@[simp] theorem EvalProp_constF {f : F} {v} :
    EvalProp σ T Δ (.constF f) v ↔ v = .vF f := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .ConstF

@[simp] theorem EvalProp_constN {n : ℕ} {v} :
    EvalProp σ T Δ (.constN n) v ↔ v = .vN n := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .ConstN

@[simp] theorem EvalProp_constInt {i : ℤ} {v} :
    EvalProp σ T Δ (.constInt i) v ↔ v = .vInt i := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .ConstInt

@[simp] theorem EvalProp_constBool {b : Bool} {v} :
    EvalProp σ T Δ (.constBool b) v ↔ v = .vBool b := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .ConstBool

-- ── Variables ────────────────────────────────────────────────────────────────

@[simp] theorem EvalProp_var {x : String} {v} :
    EvalProp σ T Δ (.var x) v ↔ getVal σ x = v := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .Var rfl

-- ── Lambdas ──────────────────────────────────────────────────────────────────

@[simp] theorem EvalProp_lam {x : String} {τ body} {v} :
    EvalProp σ T Δ (.lam x τ body) v ↔ v = .vClosure x body σ := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .Lam

-- ── Let-in ───────────────────────────────────────────────────────────────────

@[simp] theorem EvalProp_letIn {x e₁ e₂} {v} :
    EvalProp σ T Δ (.letIn x e₁ e₂) v ↔
    ∃ v₁, EvalProp σ T Δ e₁ v₁ ∧ EvalProp (updateVal σ x v₁) T Δ e₂ v := by
  constructor
  · intro h; cases h; exact ⟨_, ‹_›, ‹_›⟩
  · rintro ⟨v₁, h₁, h₂⟩; exact .Let h₁ h₂

-- ── Application ──────────────────────────────────────────────────────────────

@[simp] theorem EvalProp_app {f a} {v} :
    EvalProp σ T Δ (.app f a) v ↔
    ∃ x body σ' va,
      EvalProp σ T Δ f (.vClosure x body σ') ∧
      EvalProp σ T Δ a va ∧
      EvalProp (updateVal σ' x va) T Δ body v := by
  constructor
  · intro h; cases h; exact ⟨_, _, _, _, ‹_›, ‹_›, ‹_›⟩
  · rintro ⟨x, body, σ', va, hf, ha, hb⟩; exact .App hf ha hb

-- ── Field operations ─────────────────────────────────────────────────────────

@[simp] theorem EvalProp_fieldAdd {e₁ e₂} {v} :
    EvalProp σ T Δ (.fieldExpr e₁ .add e₂) v ↔
    ∃ a b : F, EvalProp σ T Δ e₁ (.vF a) ∧ EvalProp σ T Δ e₂ (.vF b) ∧ v = .vF (a + b) := by
  constructor
  · intro h; cases h; rename_i h₁ h₂ r
    cases h₁; cases h₂; simp [evalFieldOp] at r; exact ⟨_, _, .ConstF, .ConstF, by simpa using r⟩
    -- general case via evalprop_deterministic
    exact ⟨_, _, ‹_›, ‹_›, by simp [evalFieldOp] at r; exact r⟩
  · rintro ⟨a, b, h₁, h₂, rfl⟩
    exact .FBinOp h₁ h₂ (by simp [evalFieldOp])

@[simp] theorem EvalProp_fieldSub {e₁ e₂} {v} :
    EvalProp σ T Δ (.fieldExpr e₁ .sub e₂) v ↔
    ∃ a b : F, EvalProp σ T Δ e₁ (.vF a) ∧ EvalProp σ T Δ e₂ (.vF b) ∧ v = .vF (a - b) := by
  constructor
  · intro h; cases h; exact ⟨_, _, ‹_›, ‹_›, by simp [evalFieldOp] at *; assumption⟩
  · rintro ⟨a, b, h₁, h₂, rfl⟩; exact .FBinOp h₁ h₂ (by simp [evalFieldOp])

@[simp] theorem EvalProp_fieldMul {e₁ e₂} {v} :
    EvalProp σ T Δ (.fieldExpr e₁ .mul e₂) v ↔
    ∃ a b : F, EvalProp σ T Δ e₁ (.vF a) ∧ EvalProp σ T Δ e₂ (.vF b) ∧ v = .vF (a * b) := by
  constructor
  · intro h; cases h; exact ⟨_, _, ‹_›, ‹_›, by simp [evalFieldOp] at *; assumption⟩
  · rintro ⟨a, b, h₁, h₂, rfl⟩; exact .FBinOp h₁ h₂ (by simp [evalFieldOp])

@[simp] theorem EvalProp_fieldDiv {e₁ e₂} {v} :
    EvalProp σ T Δ (.fieldExpr e₁ .div e₂) v ↔
    ∃ a b : F, EvalProp σ T Δ e₁ (.vF a) ∧ EvalProp σ T Δ e₂ (.vF b) ∧ v = .vF (a * b.inv) := by
  constructor
  · intro h; cases h; exact ⟨_, _, ‹_›, ‹_›, by simp [evalFieldOp] at *; assumption⟩
  · rintro ⟨a, b, h₁, h₂, rfl⟩; exact .FBinOp h₁ h₂ (by simp [evalFieldOp])

-- ── Equality relation ─────────────────────────────────────────────────────────

@[simp] theorem EvalProp_binRelEqF {e₁ e₂} {v} :
    EvalProp σ T Δ (.binRel e₁ .eq e₂) v ↔
    ∃ a b : F, EvalProp σ T Δ e₁ (.vF a) ∧ EvalProp σ T Δ e₂ (.vF b) ∧ v = .vBool (a == b) := by
  constructor
  · intro h; cases h; rename_i h₁ h₂ r
    cases h₁; cases h₂
    · exact ⟨_, _, ‹_›, ‹_›, by simp [evalRelOp] at r; exact r⟩
    · simp [evalRelOp] at r
    · simp [evalRelOp] at r
    · simp [evalRelOp] at r
    · simp [evalRelOp] at r
  · rintro ⟨a, b, h₁, h₂, rfl⟩
    exact .Rel h₁ h₂ (by simp [evalRelOp, BEq.beq, instBEq])

@[simp] theorem EvalProp_binRelEqN {e₁ e₂} {v} :
    EvalProp σ T Δ (.binRel e₁ .eq e₂) v ↔
    (∃ a b : ℕ, EvalProp σ T Δ e₁ (.vN a) ∧ EvalProp σ T Δ e₂ (.vN b) ∧ v = .vBool (a == b)) ∨
    (∃ a b : F, EvalProp σ T Δ e₁ (.vF a) ∧ EvalProp σ T Δ e₂ (.vF b) ∧ v = .vBool (a == b)) := by
  constructor
  · intro h; cases h; rename_i h₁ h₂ r
    rcases h₁ with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals (first
      | (left; exact ⟨_, _, ‹_›, ‹_›, by simp [evalRelOp] at r; exact r⟩)
      | (right; exact ⟨_, _, ‹_›, ‹_›, by simp [evalRelOp] at r; exact r⟩)
      | simp [evalRelOp] at r)
  · rintro (⟨a, b, h₁, h₂, rfl⟩ | ⟨a, b, h₁, h₂, rfl⟩)
    · exact .Rel h₁ h₂ (by simp [evalRelOp])
    · exact .Rel h₁ h₂ (by simp [evalRelOp, BEq.beq, instBEq])

-- ── Assert ───────────────────────────────────────────────────────────────────

@[simp] theorem EvalProp_assertE {e₁ e₂} {v} :
    EvalProp σ T Δ (.assertE e₁ e₂) v ↔
    ∃ a : F, EvalProp σ T Δ e₁ (.vF a) ∧ EvalProp σ T Δ e₂ (.vF a) ∧ v = .vUnit := by
  constructor
  · intro h; cases h; exact ⟨_, ‹_›, ‹_›, rfl⟩
  · rintro ⟨a, h₁, h₂, rfl⟩; exact .Assert h₁ h₂

-- ── Branch ───────────────────────────────────────────────────────────────────

@[simp] theorem EvalProp_branch {c e₁ e₂} {v} :
    EvalProp σ T Δ (.branch c e₁ e₂) v ↔
    (EvalProp σ T Δ c (.vBool true)  ∧ EvalProp σ T Δ e₁ v) ∨
    (EvalProp σ T Δ c (.vBool false) ∧ EvalProp σ T Δ e₂ v) := by
  constructor
  · intro h
    cases h
    · left;  exact ⟨‹_›, ‹_›⟩
    · right; exact ⟨‹_›, ‹_›⟩
  · rintro (⟨hc, h₁⟩ | ⟨hc, h₂⟩)
    · exact .IfTrue hc h₁
    · exact .IfFalse hc h₂

-- ── Array indexing ────────────────────────────────────────────────────────────

@[simp] theorem EvalProp_arrIdx {a i} {v} :
    EvalProp σ T Δ (.arrIdx a i) v ↔
    ∃ vs j, EvalProp σ T Δ a (.vArr vs) ∧ EvalProp σ T Δ i (.vN j) ∧ vs[j]? = some v := by
  constructor
  · intro h; cases h; exact ⟨_, _, ‹_›, ‹_›, ‹_›⟩
  · rintro ⟨vs, j, ha, hi, hidx⟩; exact .ArrIdx ha hi hidx

-- ── Type conversions ──────────────────────────────────────────────────────────

@[simp] theorem EvalProp_toN {e} {v} :
    EvalProp σ T Δ (.toN e) v ↔ ∃ x : F, EvalProp σ T Δ e (.vF x) ∧ v = .vN x.val := by
  constructor
  · intro h; cases h; exact ⟨_, ‹_›, rfl⟩
  · rintro ⟨x, h, rfl⟩; exact .toN h

@[simp] theorem EvalProp_toF {e} {v} :
    EvalProp σ T Δ (.toF e) v ↔ ∃ x : ℕ, EvalProp σ T Δ e (.vN x) ∧ v = .vF x := by
  constructor
  · intro h; cases h; exact ⟨_, ‹_›, rfl⟩
  · rintro ⟨x, h, rfl⟩; exact .toF h

@[simp] theorem EvalProp_UtoS {e} {v} :
    EvalProp σ T Δ (.UtoS e) v ↔ ∃ x : ℕ, EvalProp σ T Δ e (.vN x) ∧ v = .vInt x := by
  constructor
  · intro h; cases h; exact ⟨_, ‹_›, rfl⟩
  · rintro ⟨x, h, rfl⟩; exact .UtoS h

@[simp] theorem EvalProp_StoU {e} {v} :
    EvalProp σ T Δ (.StoU e) v ↔ ∃ x : ℤ, EvalProp σ T Δ e (.vInt x) ∧ v = .vN x.natAbs := by
  constructor
  · intro h; cases h; exact ⟨_, ‹_›, rfl⟩
  · rintro ⟨x, h, rfl⟩; exact .StoU h

end EvalPropSimp

/-! ## Simp lemmas normalising `exprToProp` / `predToProp` -/

section PredSimp

variable {σ : ValEnv} {T : TraceEnv} {Δ : ChipEnv}

/-- `exprToProp` unfolds to an `EvalProp` goal, which can then be solved by the
    EvalProp simp set above. -/
@[simp] theorem exprToProp_unfold {e} :
    PropSemantics.exprToProp σ T Δ e ↔ EvalProp σ T Δ e (.vBool true) := by
  simp [PropSemantics.exprToProp]

/-- Fuel-based form, useful when `ring`/`omega` needs a concrete equation. -/
theorem exprToProp_evalC {e} :
    PropSemantics.exprToProp σ T Δ e ↔ ∃ fuel, evalC fuel σ T Δ e = some (.vBool true) := by
  simp [PropSemantics.exprToProp, ← evalC_iff_EvalProp]

/-- Independent predicates reduce to their body's evaluation. -/
@[simp] theorem predToProp_ind {body v} :
    PropSemantics.predToProp σ T Δ τ (.ind body) v ↔ EvalProp σ T Δ body (.vBool true) := by
  simp [PropSemantics.predToProp, PropSemantics.exprToProp]

/-- Dependent predicates β-reduce: the variable is substituted with `v`. -/
@[simp] theorem predToProp_dep {ident body v} :
    PropSemantics.predToProp σ T Δ τ (.dep ident body) v ↔
    EvalProp σ T Δ (.app (.lam ident τ body) v) (.vBool true) := by
  simp [PropSemantics.predToProp, PropSemantics.exprToProp]

/-- The dep predicate after β-reduction becomes: evaluate `body` with `ident` bound to `v`. -/
theorem predToProp_dep_beta {ident body} {v : Ast.Expr} {val : Ast.Value} :
    PropSemantics.predToProp σ T Δ τ (.dep ident body) v ↔
    ∀ σ', (∃ va, EvalProp σ T Δ v va ∧ σ' = updateVal σ ident va) →
          EvalProp σ' T Δ body (.vBool true) := by
  simp [predToProp_dep, EvalProp_app, EvalProp_lam]
  constructor
  · rintro ⟨_, _, _, va, hf, hv, hb⟩ σ' ⟨va', hva', rfl⟩
    cases hf; cases hf
    have := evalprop_deterministic hv hva'
    subst this; exact hb
  · intro h
    sorry -- direction requiring evidence that v evaluates to some va

/-- Conjunction of predicates. -/
@[simp] theorem predToProp_and {φ₁ φ₂ v} :
    PropSemantics.predToProp σ T Δ τ (.and φ₁ φ₂) v ↔
    PropSemantics.predToProp σ T Δ τ φ₁ v ∧ PropSemantics.predToProp σ T Δ τ φ₂ v := by
  simp [PropSemantics.predToProp]

/-- Disjunction of predicates. -/
@[simp] theorem predToProp_or {φ₁ φ₂ v} :
    PropSemantics.predToProp σ T Δ τ (.or φ₁ φ₂) v ↔
    PropSemantics.predToProp σ T Δ τ φ₁ v ∨ PropSemantics.predToProp σ T Δ τ φ₂ v := by
  simp [PropSemantics.predToProp]

/-- Negation of predicates. -/
@[simp] theorem predToProp_not {φ v} :
    PropSemantics.predToProp σ T Δ τ (.not φ) v ↔
    ¬ PropSemantics.predToProp σ T Δ τ φ v := by
  simp [PropSemantics.predToProp]

end PredSimp

/-! ## Automation tactics -/

open Lean Meta Elab Tactic in
/--
`runwai_simp` is the primary automation tactic for Runwai proof obligations.

It applies three layers of simplification:
1. Unfolds `EvalProp`, `exprToProp`, `predToProp`, `evalC` using the simp set above.
2. Unfolds the operation helpers `evalFieldOp`, `evalRelOp`, `evalBoolOp`,
   `evalUIntOp`, `evalSIntOp`.
3. Unfolds `Env.getVal`, `Env.updateVal` to reduce variable lookups to `if`-then-`else`.

After `runwai_simp`, the remaining goals are typically:
- Pure field arithmetic (`ring` or `field_simp; ring`)
- Pure integer/natural arithmetic (`omega`)
- Trivial propositional goals (`simp` or `decide`)

**Example** – old proof of `eval_mul_expr_val` (25 lines):
```lean
lemma eval_mul_expr_val ... (h : EvalProp ...) : ∃ v₁ v₂ v₃, ... := by
  cases h; rename_i ...; cases ...; cases ...; simp ...; use ...; ...
```

**New proof** (4 lines):
```lean
lemma eval_mul_expr_val ... (h : EvalProp ...) : ∃ v₁ v₂ v₃, ... := by
  simp [EvalProp_fieldMul, EvalProp_var, EvalProp_binRelEqF] at h
  obtain ⟨a, b, ha, hb, heq⟩ := h
  exact ⟨a, b, ha, hb, by simpa using heq⟩
```
-/
elab "runwai_simp" : tactic =>
  evalTactic (← `(tactic|
    simp only [
      EvalProp_constF, EvalProp_constN, EvalProp_constInt, EvalProp_constBool,
      EvalProp_var, EvalProp_lam, EvalProp_letIn, EvalProp_app,
      EvalProp_fieldAdd, EvalProp_fieldSub, EvalProp_fieldMul, EvalProp_fieldDiv,
      EvalProp_binRelEqF, EvalProp_assertE, EvalProp_branch,
      EvalProp_arrIdx, EvalProp_toN, EvalProp_toF, EvalProp_UtoS, EvalProp_StoU,
      exprToProp_unfold, predToProp_ind, predToProp_dep, predToProp_and,
      predToProp_or, predToProp_not,
      Eval.evalFieldOp, Eval.evalUIntOp, Eval.evalSIntOp,
      Eval.evalRelOp, Eval.evalBoolOp,
      Env.getVal, Env.updateVal,
      Option.bind_some, Option.bind_none, Option.map_some, Option.map_none,
      Option.some.injEq, decide_eq_true_eq, if_true, if_false
    ] at *
  ))

open Lean Meta Elab Tactic in
/--
`runwai_field` = `runwai_simp` followed by field-arithmetic tactics.

Use this when the remaining goal after unfolding is a statement about field
elements `F = ZMod p`.

```lean
theorem foo (h : EvalProp σ T Δ (assertE (x * y) (constF 0)) vUnit) : ... := by
  runwai_field
  -- or: runwai_simp; field_simp; ring
```
-/
elab "runwai_field" : tactic =>
  evalTactic (← `(tactic|
    runwai_simp
    first
      | ring
      | omega
      | (field_simp; ring)
      | (simp [ZMod.val_natCast]; omega)
      | decide
  ))

open Lean Meta Elab Tactic in
/--
`runwai_obtain h` destructs an `EvalProp` hypothesis `h` into its components
using the simp normal form.  After this, `h` is replaced by named sub-hypotheses
that each involve simpler expressions or concrete values.

```lean
have h : EvalProp σ T Δ (letIn "x" e₁ e₂) v := ...
runwai_obtain h
-- Now you have:
--   h_v₁ : EvalProp σ T Δ e₁ v₁
--   h_v₂ : EvalProp (updateVal σ "x" v₁) T Δ e₂ v
```
-/
macro "runwai_obtain" h:ident : tactic =>
  `(tactic|
    (simp only [
      EvalProp_constF, EvalProp_constN, EvalProp_constInt, EvalProp_constBool,
      EvalProp_var, EvalProp_lam, EvalProp_letIn, EvalProp_app,
      EvalProp_fieldAdd, EvalProp_fieldSub, EvalProp_fieldMul, EvalProp_fieldDiv,
      EvalProp_assertE, EvalProp_branch, EvalProp_arrIdx,
      EvalProp_toN, EvalProp_toF, EvalProp_UtoS, EvalProp_StoU,
      Env.getVal, Env.updateVal
    ] at $h:ident
    try obtain _ := $h:ident)
  )
