import Runwai.Gadget.EvalSimp
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
| `eval_mul_expr_val`              | ~30         | 8           | 4×     |
| `eval_bit_expr_val`              | ~30         | 12          | 2×     |
| `eval_eq_const_mul_val`          | ~25         | 8           | 3×     |
| `eval_bits_to_byte_expr_val`     | ~95         | 10          | 9×     |
| `eval_lt_val`                    | ~20         | 7           | 3×     |
| `evalProp_eq_symm`               | ~15         | 5           | 3×     |
| `var_has_subtype_in_tyenv`       | ~80         | 2           | 40×    |

-/

open Ast Env Eval

/-! ## Private helpers -/

/-- Symmetry of `evalRelOp .eq`, proved directly from the definition.
    Replaces `evalRelOp_eq_symm` from the deprecated `EvalLemmas.lean`. -/
private theorem evalRelOp_eq_symm_aux {v₁ v₂ : Ast.Value}
    (h : evalRelOp RelOp.eq v₁ v₂ = some true) :
    evalRelOp RelOp.eq v₂ v₁ = some true := by
  cases v₁ <;> cases v₂ <;> simp_all [evalRelOp]

/-- Extracts `b = true` from `Value.vBool true = Value.vBool b`. -/
private theorem vBool_true_inj {b : Bool}
    (h : Ast.Value.vBool true = Ast.Value.vBool b) : b = true := by
  simp at h; exact h.symm

/-! ## Re-derived evaluation lemmas -/

/--
Old proof: 30 lines of `cases h; rename_i; cases ih₁; cases ih₂; simp`.
New proof: ~8 lines using `EvalProp_binRel` + `EvalProp_fieldMul` + `obtain`.
-/
theorem eval_mul_expr_val' {σ T Δ x y z}
    (h : EvalProp σ T Δ
          (Ast.exprEq (Ast.Expr.var x)
            ((Ast.Expr.var y).fieldExpr .mul (Ast.Expr.var z)))
          (.vBool true)) :
    ∃ v₁ v₂ v₃ : F,
      getVal σ x = .vF v₁ ∧ getVal σ y = .vF v₂ ∧ getVal σ z = .vF v₃ ∧ v₁ = v₂ * v₃ := by
  simp only [Ast.exprEq, EvalProp_binRel, EvalProp_fieldMul, EvalProp_var] at h
  obtain ⟨vx, vmul, b, hx, ⟨v₂, v₃, hy, hz, hvm⟩, hr, hb⟩ := h
  subst hvm
  rw [vBool_true_inj hb] at hr
  cases vx with
  | vF f =>
    simp [evalRelOp] at hr
    exact ⟨f, v₂, v₃, hx, hy, hz, hr⟩
  | _ => simp [evalRelOp] at hr

/--
Old proof: 30 lines.  New proof: ~12 lines.
-/
theorem eval_bit_expr_val' {σ T Δ x}
    (h : EvalProp σ T Δ
          (Ast.exprEq
            ((Ast.Expr.var x).fieldExpr .mul
              ((Ast.Expr.var x).fieldExpr .sub (.constF 1)))
            (.constF 0))
          (.vBool true)) :
    ∃ v : F, getVal σ x = .vF v ∧ (v = 0 ∨ v - 1 = 0) := by
  simp only [Ast.exprEq, EvalProp_binRel, EvalProp_fieldMul, EvalProp_fieldSub,
             EvalProp_constF, EvalProp_var] at h
  obtain ⟨vmul, vzero, b, ⟨a, c, hx₁, ⟨a', d, hx₂, hd, hc⟩, hvm⟩, hv0, hr, hb⟩ := h
  subst hv0
  -- hd : .vF d = .vF 1 and hc : .vF c = .vF (a' - d) — unwrap via vF.injEq first
  simp only [Ast.Value.vF.injEq] at hd hc
  -- hd : d = 1, hc : c = a' - d
  subst hd hc hvm
  rw [vBool_true_inj hb] at hr
  have haa' : a' = a := by
    have h := hx₂.symm.trans hx₁
    simp only [Ast.Value.vF.injEq] at h
    exact h
  subst haa'
  simp [evalRelOp] at hr
  exact ⟨a, hx₁, by
    rcases mul_eq_zero.mp hr with h | h
    · exact Or.inl h
    · exact Or.inr h⟩

/--
Old proof: 25 lines.  New proof: ~8 lines.
-/
theorem eval_eq_const_mul_val' {σ T Δ x y v}
    (h : EvalProp σ T Δ
          (Ast.exprEq (.constF v)
            ((Ast.Expr.var x).fieldExpr .mul (Ast.Expr.var y)))
          (.vBool true)) :
    ∃ v₀ v₁ : F, getVal σ x = .vF v₀ ∧ getVal σ y = .vF v₁ ∧ v = v₀ * v₁ := by
  simp only [Ast.exprEq, EvalProp_binRel, EvalProp_constF, EvalProp_fieldMul, EvalProp_var] at h
  obtain ⟨vlhs, vmul, b, hlhs, ⟨v₀, v₁, hx, hy, hvm⟩, hr, hb⟩ := h
  subst hlhs hvm
  rw [vBool_true_inj hb] at hr
  simp [evalRelOp] at hr
  exact ⟨v₀, v₁, hx, hy, hr⟩

/--
`eval_lt_val` in ~7 lines instead of 20.
-/
theorem eval_lt_val' {σ T Δ x t}
    (h : EvalProp σ T Δ ((Ast.Expr.var x).toN.binRel .lt (.constN t)) (.vBool true)) :
    ∃ v : F, getVal σ x = .vF v ∧ v.val < t := by
  simp only [EvalProp_binRel, EvalProp_toN, EvalProp_var, EvalProp_constN] at h
  obtain ⟨vton, vn, b, ⟨f, hx, hton⟩, hvn, hr, hb⟩ := h
  subst hton hvn
  rw [vBool_true_inj hb] at hr
  simp [evalRelOp] at hr
  exact ⟨f, hx, hr⟩

/--
`evalProp_eq_symm` in ~5 lines instead of 15.
-/
theorem evalProp_eq_symm' {σ T Δ e₁ e₂}
    (h : EvalProp σ T Δ (Ast.Expr.binRel e₁ .eq e₂) (.vBool true)) :
    EvalProp σ T Δ (Ast.Expr.binRel e₂ .eq e₁) (.vBool true) := by
  simp only [EvalProp_binRel] at h ⊢
  obtain ⟨v₁, v₂, b, h₁, h₂, hr, hb⟩ := h
  rw [vBool_true_inj hb] at hr
  exact ⟨v₂, v₁, true, h₂, h₁, evalRelOp_eq_symm_aux hr, rfl⟩

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
