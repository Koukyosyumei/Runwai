import Runwai.Typing
import Runwai.Gadget.Utils

open Ast

lemma lookup_ext (Γ :Env.TyEnv) (x y : String) (τ : Ty)
  (h: (Env.lookupTy Γ x).isSome = true):
  (Env.lookupTy (Env.updateTy Γ y τ) x).isSome = true := by
  simp [Env.lookupTy, Env.updateTy]
  cases dec: (decide (y = x)) with
  | true => simp [dec]
  | false => simp [dec]; exact h

lemma lookup_update_ne
  (Γ : Env.TyEnv) (x y : String) (τ : Ast.Ty) (hxy : y ≠ x) :
  Env.lookupTy (Env.updateTy Γ x τ) y = Env.lookupTy Γ y := by
  unfold Env.updateTy
  unfold Env.lookupTy
  cases dec : (decide (x = y)) with
  | true => simp_all
  | false => simp [dec]

lemma lookup_update_ne_of_lookup
  (Γ : Env.TyEnv) (x y : String) (τ₁ τ₂ : Ast.Ty) (hxy : y ≠ x) (hy: Env.lookupTy Γ y = τ₂):
  Env.lookupTy (Env.updateTy Γ x τ₁) y = τ₂ := by
  unfold Env.updateTy
  unfold Env.lookupTy at ⊢ hy
  cases dec : (decide (x = y)) with
  | true => simp_all
  | false => simp_all

lemma lookup_update_self
  (Γ : Env.TyEnv) (x : String) (τ : Ast.Ty) :
  Env.lookupTy (Env.updateTy Γ x τ) x = τ := by
  unfold Env.updateTy Env.lookupTy
  simp_all

lemma update_preserve_pointwise
  (Γ₁ Γ₂ : Env.TyEnv) (x : String) (τ : Ast.Ty)
  (h : ∀ y, Env.lookupTy Γ₁ y = Env.lookupTy Γ₂ y) :
  ∀ y, Env.lookupTy (Env.updateTy Γ₁ x τ) y = Env.lookupTy (Env.updateTy Γ₂ x τ) y := by
  intro y
  by_cases hy : y = x
  · subst hy
    simp [lookup_update_self]
  · simp [lookup_update_ne _ _ _ _ hy, h y]

theorem eq_none_of_isSome_eq_false {α : Type _}
    {o : Option α} (h : o.isSome = false) : o = none := by
  cases o <;> simp_all

lemma lookup_empty_none (x: String):
  Env.lookupTy [] x = none := by {
    unfold Env.lookupTy
    simp
  }

theorem lookup_mem_of_eq {Γ: Env.TyEnv} {x: String} {τ: Ast.Ty}:
  Env.lookupTy Γ x = τ → (x, τ) ∈ Γ := by {
    unfold Env.lookupTy
    cases b: List.find? (fun x_1 ↦ decide (x_1.1 = x)) Γ with
    | none => simp_all
    | some val => {
      have b' : (List.find? (fun x_1 ↦ decide (x_1.1 = x)) Γ).isSome = true := by simp_all
      have b'' := List.get_find?_mem b'
      have b''' := List.find?_eq_some_iff_append.mp b
      simp_all
      have b'''' : val.1 = x := by simp_all
      cases val with
      | mk v₁ v₂ =>{
        have h₁: v₁ = x := by simp_all
        intro h₂
        have h₃: v₂ = τ := by simp_all
        rw[h₁] at b''
        rw[h₃] at b''
        exact b''
      }
    }
  }

theorem lookup_mem_impl_some {Γ: Env.TyEnv} {x: String} {τ: Ast.Ty} (hmem: (x, τ) ∈ Γ):
  (Env.lookupTy Γ x).isSome  := by {
    unfold Env.lookupTy
    cases b: List.find? (fun x_1 ↦ decide (x_1.1 = x)) Γ with
    | none => {
      simp at b
      have b' := b x τ hmem
      simp at b'
    }
    | some val => simp
  }

lemma lookupTy_pointwise_symm (Γ₁ Γ₂: Env.TyEnv)
  (h₁: ∀ x, Env.lookupTy Γ₁ x = Env.lookupTy Γ₂ x):
  ∀ x, Env.lookupTy Γ₂ x = Env.lookupTy Γ₁ x := by {
    intro x
    have h₂ := h₁ x
    exact Eq.symm h₂
  }

lemma mem_update_preserve (Γ: Env.TyEnv) (x x': String) (τ τ': Ty) (h: (x, τ) ∈ Γ):
  (x, τ) ∈ (Env.updateTy Γ x' τ') := by
  unfold Env.updateTy
  by_cases hx : (Γ.find? (fun p => p.1 = x')).isSome
  · simp_all
  · simp [h]
