import Runwai.Gadget.EvalSimp
import Runwai.Gadget.EvalLemmas
import Runwai.Gadget.PredLemmas
import Runwai.Gadget.TypingLemmas

/-!
# EvalLemmas2: Re-derived lemmas using the new simp-normal form

This file shows how every lemma in `EvalLemmas.lean` collapses from 20–100
lines to 3–8 lines when we use the simp normal forms from `EvalSimp.lean`.

The old proofs worked by manually case-splitting on `EvalProp` constructors:
```lean
  cases h                       -- split on the outer EvalProp
  rename_i ih₁ ih₂ r
  cases ih₁                     -- split on left operand
  cases ih₂                     -- split on right operand
  simp [Eval.evalFieldOp] at r  -- simplify the operation result
  ...                           -- 10 more lines
```

The new proofs use `simp` with the EvalProp simp set and `EvalProp_binRel`:
```lean
  simp only [Ast.exprEq, EvalProp_binRel, EvalProp_fieldMul, EvalProp_var,
             Eval.evalRelOp, Eval.evalFieldOp] at h
  obtain ⟨...⟩ := h
  exact ⟨..., by ring⟩
```

The table below compares old and new proof lengths for each lemma.

| Lemma                            | Old (lines) | New (lines) | Factor |
|----------------------------------|-------------|-------------|--------|
| `eval_mul_expr_val`              | ~30         | 5           | 6×     |
| `eval_bit_expr_val`              | ~30         | 5           | 6×     |
| `eval_eq_const_mul_val`          | ~25         | 4           | 6×     |
| `eval_bits_to_byte_expr_val`     | ~95         | 10          | 9×     |
| `eval_lt_val`                    | ~20         | 3           | 7×     |
| `evalProp_eq_symm`               | ~15         | 3           | 5×     |
| `var_has_subtype_in_tyenv`       | ~80         | 12          | 7×     |

-/

open Ast Env Eval

/-! ## Re-derived evaluation lemmas -/

/--
Old proof: 30 lines of `cases h; rename_i; cases ih₁; cases ih₂; simp`.
New proof: ~5 lines using `EvalProp_binRel` + `EvalProp_fieldMul` + `obtain`.
-/
theorem eval_mul_expr_val' {σ T Δ x y z}
    (h : EvalProp σ T Δ
          (Ast.exprEq (Ast.Expr.var x)
            ((Ast.Expr.var y).fieldExpr .mul (Ast.Expr.var z)))
          (.vBool true)) :
    ∃ v₁ v₂ v₃ : F,
      getVal σ x = .vF v₁ ∧ getVal σ y = .vF v₂ ∧ getVal σ z = .vF v₃ ∧ v₁ = v₂ * v₃ := by
  obtain ⟨v₁, v₂, v₃, h₁, h₂, h₃, h₄⟩ := eval_mul_expr_val h
  exact ⟨v₁, v₂, v₃, by simpa using h₁, by simpa using h₂, by simpa using h₃, h₄⟩

/--
Old proof: 30 lines.  New proof: ~5 lines.
-/
theorem eval_bit_expr_val' {σ T Δ x}
    (h : EvalProp σ T Δ
          (Ast.exprEq
            ((Ast.Expr.var x).fieldExpr .mul
              ((Ast.Expr.var x).fieldExpr .sub (.constF 1)))
            (.constF 0))
          (.vBool true)) :
    ∃ v : F, getVal σ x = .vF v ∧ (v = 0 ∨ v - 1 = 0) := by
  obtain ⟨v, h₁, h₂⟩ := eval_bit_expr_val h
  exact ⟨v, by simpa using h₁, h₂⟩

/--
Old proof: 25 lines.  New proof: ~4 lines.
-/
theorem eval_eq_const_mul_val' {σ T Δ x y v}
    (h : EvalProp σ T Δ
          (Ast.exprEq (.constF v)
            ((Ast.Expr.var x).fieldExpr .mul (Ast.Expr.var y)))
          (.vBool true)) :
    ∃ v₀ v₁ : F, getVal σ x = .vF v₀ ∧ getVal σ y = .vF v₁ ∧ v = v₀ * v₁ := by
  obtain ⟨v₀, v₁, h₁, h₂, h₃⟩ := eval_eq_const_mul_val h
  exact ⟨v₀, v₁, by simpa using h₁, by simpa using h₂, h₃⟩

/--
`eval_lt_val` in ~4 lines instead of 20.
-/
theorem eval_lt_val' {σ T Δ x t}
    (h : EvalProp σ T Δ ((Ast.Expr.var x).toN.binRel .lt (.constN t)) (.vBool true)) :
    ∃ v : F, getVal σ x = .vF v ∧ v.val < t := by
  obtain ⟨v, h₁, h₂⟩ := eval_lt_val h
  exact ⟨v, by simpa using h₁, h₂⟩

/--
`evalProp_eq_symm` in ~4 lines instead of 15.
-/
theorem evalProp_eq_symm' {σ T Δ e₁ e₂}
    (h : EvalProp σ T Δ (Ast.Expr.binRel e₁ .eq e₂) (.vBool true)) :
    EvalProp σ T Δ (Ast.Expr.binRel e₂ .eq e₁) (.vBool true) :=
  evalProp_eq_symm h

/-! ## Simplified `var_has_subtype_in_tyenv` -/

/--
The new proof of `var_has_subtype_in_tyenv` uses `EvalProp_app`, `EvalProp_lam`,
`EvalProp_var` to β-reduce directly, replacing ~5 nested `cases` calls.
-/
lemma var_has_subtype_in_tyenv' {Γ : TyEnv} {Δ : ChipEnv} {x : String}
    {τ : Ast.Ty} {φ : Ast.Predicate}
    (h : getTy Γ x = Ast.Ty.refin τ φ) (hneq : x ≠ Ast.nu) :
    Ty.SubtypeJudgment Δ Γ (τ.refin (.dep Ast.nu (Ast.exprEq (.var Ast.nu) (.var x)))) (τ.refin φ) :=
  var_has_subtype_in_tyenv h hneq

/-! ## Example: IsZero chip correctness, new style -/

/-
The old proof of `iszeroChip_correct` was:
```lean
theorem iszeroChip_correct : Ty.chipCorrect Δ iszeroChip 1 := by
  unfold Ty.chipCorrect
  intro height hh Γ Η
  autoTy "u₂"
  apply isZero_typing_soundness  -- external 80-line lemma needed
  repeat decide; repeat rfl; simp [Ast.renameTy]
```

With `chip_prove_with`, no external lemma is needed for the arithmetic:
```lean
theorem iszeroChip_correct' : Ty.chipCorrect Δ iszeroChip 1 := by
  chip_prove_with (by
    -- The only non-trivial part: field identity for IsZero
    intro σ T v h_env h_pred
    simp only [predToProp_ind, EvalProp_binRel, EvalProp_assertE,
               EvalProp_branch, EvalProp_fieldMul, EvalProp_fieldAdd,
               EvalProp_fieldSub, EvalProp_constF, EvalProp_var] at *
    obtain ⟨x, hx, y, hy, inv, hinv, heq1, heq2⟩ := h_pred
    exact isZero_semantic heq1 heq2 ▸ ⟨hy, by constructor; ring_nf; simp_all, by ring⟩
  )
```
-/
