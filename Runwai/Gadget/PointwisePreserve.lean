import Runwai.Typing
import Runwai.Gadget.Utils
import Runwai.Gadget.EnvLemmas
import Runwai.Gadget.EvalLemmas

open Ast

/--
If two environments `Γ₁` and `Γ₂` are pointwise equal (i.e., any lookup yields the same
result in both), then updating both with the same binding `(x, τ)` preserves this
pointwise equality.
-/
lemma update_preserve_pointwise
  (Γ₁ Γ₂ : Env.TyEnv) (x : String) (τ : Ast.Ty)
  (h : ∀ y, Env.lookupTy Γ₁ y = Env.lookupTy Γ₂ y) :
  ∀ y, Env.lookupTy (Env.updateTy Γ₁ x τ) y = Env.lookupTy (Env.updateTy Γ₂ x τ) y := by
  intro y
  by_cases hy : y = x
  · subst hy
    simp [lookup_update_self]
  · simp [lookup_update_ne _ _ _ _ hy, h y]

/-- Pointwise equality of type environments is a symmetric relation. -/
lemma lookupTy_pointwise_symm (Γ₁ Γ₂: Env.TyEnv)
  (h₁: ∀ x, Env.lookupTy Γ₁ x = Env.lookupTy Γ₂ x):
  ∀ x, Env.lookupTy Γ₂ x = Env.lookupTy Γ₁ x := by {
    intro x
    have h₂ := h₁ x
    exact Eq.symm h₂
  }

/--
If the property `varToProp` holds for a variable `ident` under a type environment `Γ₁`, it will
also hold under a different environment `Γ₂`, provided that `Γ₁` and `Γ₂` are pointwise equal.
-/
theorem varToProp_pointwise_preserve (σ: Env.ValEnv) (T: Env.TraceEnv) (Δ: Env.ChipEnv) (Γ₁ Γ₂: Env.TyEnv) (ident: String)
  (h₁: ∀ x, Env.lookupTy Γ₁ x = Env.lookupTy Γ₂ x) (h₂: PropSemantics.varToProp σ T Δ Γ₁ ident):
  PropSemantics.varToProp σ T Δ Γ₂ ident := by {
    simp [PropSemantics.varToProp] at h₂ ⊢
    have h₁' := h₁ ident
    rw[← h₁']
    exact h₂
  }

/--
If the property `tyenvToProp` holds for an entire type environment `Γ₁` that is pointwise equal to `Γ₂`, it will also hold
for `Γ₂`.
-/
theorem tyenvToProp_pointwise_preserve (σ: Env.ValEnv) (T: Env.TraceEnv) (Δ: Env.ChipEnv) (Γ₁ Γ₂: Env.TyEnv)
  (h₁: ∀ x, Env.lookupTy Γ₁ x = Env.lookupTy Γ₂ x) (h₂: PropSemantics.tyenvToProp σ T Δ Γ₁):
  PropSemantics.tyenvToProp σ T Δ Γ₂ := by {
    unfold PropSemantics.tyenvToProp at h₂ ⊢
    intro x τ h₃
    have h₄ := h₁ x
    rw[← h₄] at h₃
    have h₅ := h₂ x τ h₃
    exact varToProp_pointwise_preserve σ T Δ Γ₁ Γ₂ x h₁ h₅
  }

/--
A subtyping judgment `τ₁ <: τ₂` that is valid in a type environment `Γ₁` remains valid if `Γ₁`
is replaced by any other environment `Γ₂` that is pointwise equal to it.
-/
theorem subtyping_pointwise_preserve (Δ: Env.ChipEnv) (Γ₁: Env.TyEnv) (τ₁ τ₂: Ast.Ty)
  (h₂: Ty.SubtypeJudgment Δ Γ₁ τ₁ τ₂) :
  ∀ Γ₂: Env.TyEnv, (∀ x, Env.lookupTy Γ₁ x = Env.lookupTy Γ₂ x) →
    Ty.SubtypeJudgment Δ Γ₂ τ₁ τ₂ := by {
      induction h₂ with
      | TSub_Refl => intros; constructor
      | TSub_Trans h₁ h₂ ih₁ ih₂ => {
        intro Γ₂ h
        apply Ty.SubtypeJudgment.TSub_Trans
        apply ih₁; exact h
        apply ih₂; exact h
      }
      | TSub_Refine h₁ ih₁ ih₂ => {
        intro Γ₂ h
        apply Ty.SubtypeJudgment.TSub_Refine
        apply ih₂; exact h
        intro σ T e h₂
        apply ih₁
        exact tyenvToProp_pointwise_preserve σ T Δ Γ₂ Γ₁ (lookupTy_pointwise_symm Γ₁ Γ₂ h) h₂
      }
      | TSub_Fun h₁ h₂ ih₁ ih₂ => {
        intro Γ₂ h
        apply Ty.SubtypeJudgment.TSub_Fun
        rename_i x y z τx τy τs τr
        apply ih₁; exact h
        apply ih₂; exact h
      }
      | TSub_Arr h₁ ih => {
        intro Γ₂ h
        apply Ty.SubtypeJudgment.TSub_Arr; apply ih; assumption
      }
    }

/--
A typing judgment `e : τ` that is valid in a type environment `Γ₁` remains valid if `Γ₁` is
replaced by any other environment `Γ₂` that is pointwise equal to it.
-/
theorem typing_pointwise_preserve (Δ: Env.ChipEnv) (Η: Env.UsedNames) (Γ₁: Env.TyEnv) (e: Ast.Expr) (τ: Ast.Ty)
  (h₂: @Ty.TypeJudgment Δ Γ₁ Η e τ) :
  ∀ Γ₂: Env.TyEnv, (∀ x, Env.lookupTy Γ₁ x = Env.lookupTy Γ₂ x) →
        @Ty.TypeJudgment Δ Γ₂ Η e τ := by {
    induction h₂ with
    | TE_Var ha => intro Γ₂ h; apply Ty.TypeJudgment.TE_Var; rwa [← h]
    | TE_VarEnv h₁ => intro Γ₂ h; apply Ty.TypeJudgment.TE_VarEnv; rwa [← h]
    | TE_VarFunc _ =>
      rename_i Γ' x₁ x₂ τ₁ τ₂ h
      intro Γ₂ h'
      apply Ty.TypeJudgment.TE_VarFunc
      have h₃ := h' x₁
      rw[← h₃]
      exact h
    | TE_ArrayIndex _ h₂ h₃ a_ih => {
      intro Γ₂ h
      rename_i i φ h₁
      apply Ty.TypeJudgment.TE_ArrayIndex
      apply h₃
      exact h
      apply a_ih
      exact h
    }
    | TE_Branch _ _ _ ih₀ ih₁ ih₂ => intro Γ₂ h; apply Ty.TypeJudgment.TE_Branch (ih₀ Γ₂ h) (ih₁ Γ₂ h) (ih₂ Γ₂ h)
    | TE_ConstF => intros; constructor
    | TE_ConstZ => intros; constructor
    | TE_ConstBool => intros; constructor
    | TE_Assert _ _ ih₁ ih₂ => intro Γ₂ h; apply Ty.TypeJudgment.TE_Assert (ih₁ Γ₂ h) (ih₂ Γ₂ h)
    | TE_BinOpField _ _ ih₁ ih₂ => intro Γ₂ h; apply Ty.TypeJudgment.TE_BinOpField (ih₁ Γ₂ h) (ih₂ Γ₂ h)
    | TE_BinOpInteger _ _ ih₁ ih₂ => intro Γ₂ h; apply Ty.TypeJudgment.TE_BinOpInteger (ih₁ Γ₂ h) (ih₂ Γ₂ h)
    | TE_BinOpRel _ _ ih₁ ih₂ => intro Γ₂ h; apply Ty.TypeJudgment.TE_BinOpRel (ih₁ Γ₂ h) (ih₂ Γ₂ h)
    | TE_Abs ih₀ _ ih₂ =>
      intro Γ₂ h
      apply Ty.TypeJudgment.TE_Abs
      · rwa [← update_preserve_pointwise _ _ _ _ h]
      · apply ih₂; exact update_preserve_pointwise _ _ _ _ h
    | TE_App h₁ h₂ h₃ ih₁ ih₂ =>
      intro Γ₂ h
      apply Ty.TypeJudgment.TE_App
      apply ih₁
      exact h
      apply ih₂
      exact h
      exact h₃
    | TE_SUB h₀ h₁ ih =>
      intro Γ₂ h
      apply Ty.TypeJudgment.TE_SUB
      · apply ih; assumption
      . exact subtyping_pointwise_preserve Δ _ _ _ h₁ Γ₂ h
    | TE_LetIn h₁ h₂ ih₁ ih₂ =>
      rename_i Γ' Η' x₁ e₁ e₂ τ₁ τ₂ h'
      intro Γ₂ h
      apply Ty.TypeJudgment.TE_LetIn
      have hu := @update_preserve_pointwise Γ' Γ₂ x₁ τ₁ h
      have h' := hu x₁
      rw[h₁] at h'
      rw[← h']
      apply ih₂
      exact h
      apply h'
      have hu := @update_preserve_pointwise Γ' Γ₂ x₁ τ₁ h
      exact hu
    | TE_LookUp h₁ h₂ => {
      rename_i Γ' Η' vname cname args c φ φ' τ' h₅ h₆ h₇ h₈
      intro Γ₂ h₉
      apply Ty.TypeJudgment.TE_LookUp
      exact h₁
      exact h₂
      rfl
      apply h₈
      rw[h₆]
      have hu := @update_preserve_pointwise Γ' Γ₂ vname (Ty.unit.refin (Ty.lookup_pred args c φ Η')) h₉
      exact hu
    }
  }
