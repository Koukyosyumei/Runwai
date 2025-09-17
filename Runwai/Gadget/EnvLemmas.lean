import Runwai.Typing
import Runwai.Gadget.Utils

open Ast

/--
If a variable `x` exists in a type environment `Γ`, it will also exist in an environment
formed by updating `Γ` with another binding `(y, τ)`. This holds regardless of whether `x` and
`y` are the same.
-/
lemma lookup_ext (Γ :Env.TyEnv) (x y : String) (τ : Ty)
  (h: (Env.lookupTy Γ x).isSome = true):
  (Env.lookupTy (Env.updateTy Γ y τ) x).isSome = true := by
  simp [Env.lookupTy, Env.updateTy]
  cases dec: (decide (y = x)) with
  | true => simp [dec]
  | false => simp [dec]; exact h

/--
Looking up a variable `y` in an environment updated with a *different* variable `x` is
equivalent to looking up `y` in the original environment. The update at `x` has no effect
on the lookup of `y`.
-/
lemma lookup_update_ne
  (Γ : Env.TyEnv) (x y : String) (τ : Ast.Ty) (hxy : y ≠ x) :
  Env.lookupTy (Env.updateTy Γ x τ) y = Env.lookupTy Γ y := by
  unfold Env.updateTy
  unfold Env.lookupTy
  cases dec : (decide (x = y)) with
  | true => simp_all
  | false => simp [dec]

lemma lookup_val_update_ne
  (σ : Env.ValEnv) (x y : String) (v : Ast.Value) (hxy : y ≠ x) :
  Env.lookupVal (Env.updateVal σ x v) y = Env.lookupVal σ y := by
  simp [Env.updateVal, Env.lookupVal]
  cases dec : (decide (x = y)) with
  | true => simp_all
  | false => simp [dec]

/--
A more specific version of `lookup_update_ne`. If looking up `y` in `Γ` yields `τ₂`,
then looking up `y` in an environment updated at a different variable `x` will still yield `τ₂`.
-/
lemma lookup_update_ne_of_lookup
  (Γ : Env.TyEnv) (x y : String) (τ₁ τ₂ : Ast.Ty) (hxy : y ≠ x) (hy: Env.lookupTy Γ y = τ₂):
  Env.lookupTy (Env.updateTy Γ x τ₁) y = τ₂ := by
  unfold Env.updateTy
  unfold Env.lookupTy at ⊢ hy
  cases dec : (decide (x = y)) with
  | true => simp_all
  | false => simp_all

/--
Looking up a variable `x` in an environment that has just been updated with a binding
for `x` will return the new type `τ`. This is the "read-your-write" property for the
type environment.
-/
lemma lookup_update_self
  (Γ : Env.TyEnv) (x : String) (τ : Ast.Ty) :
  Env.lookupTy (Env.updateTy Γ x τ) x = τ := by
  unfold Env.updateTy Env.lookupTy
  simp_all

/-- A helper theorem for `Option`: if an option's `isSome` property is false, the option
must be `none`. -/
theorem eq_none_of_isSome_eq_false {α : Type _}
    {o : Option α} (h : o.isSome = false) : o = none := by
  cases o <;> simp_all

/-- Looking up any variable `x` in an empty type environment results in `none`. -/
lemma lookup_empty_none (x: String):
  Env.lookupTy [] x = none := by {
    unfold Env.lookupTy
    simp
  }

/--
If looking up a variable `x` in environment `Γ` returns a specific type `τ`, then the
pair `(x, τ)` must be a member of the list representing `Γ`. This connects the lookup
operation to list membership.
-/
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

/--
If a binding `(x, τ)` is a member of the environment `Γ`, then looking up `x` in `Γ`
will not result in `none`. It will return `some` value.
-/
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

/--
If a binding `(x, τ)` is a member of an environment `Γ`, it remains a member after
the environment is updated with another binding `(x', τ')`.
-/
lemma mem_update_preserve (Γ: Env.TyEnv) (x x': String) (τ τ': Ty) (h: (x, τ) ∈ Γ):
  (x, τ) ∈ (Env.updateTy Γ x' τ') := by
  unfold Env.updateTy
  by_cases hx : (Γ.find? (fun p => p.1 = x')).isSome
  · simp_all
  · simp [h]
