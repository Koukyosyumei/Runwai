import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.List.Basic

theorem length_eq_zero {α : Type} {xs : List α} :
  xs.length = 0 → xs = [] := by
  cases xs <;> simp

lemma ne_imp_exists_diff {α: Type} {xs ys : List α}
    (hlen : xs.length = ys.length) (hne : xs ≠ ys) :
    ∃ i, ∃ (h : i < xs.length),
      xs.get ⟨i, h⟩ ≠ ys.get ⟨i, by rwa [←hlen]⟩ := by
  contrapose! hne
  apply List.ext_get hlen
  intro i hx hy
  specialize hne i hx
  simpa [←hlen] using hne

lemma zip_get_ne {α β: Type} {es : List α} {xs xs' : List β} {i : Nat}
    (h_len₁ : xs.length = es.length)
    (h_len₂ : xs.length = xs'.length)
    (h_i_xs : i < xs.length)
    (h : xs.get ⟨i, h_i_xs⟩ ≠ xs'.get ⟨i, by rwa [← h_len₂]⟩) :
    (es.zip xs).get ⟨i, by
      rw [List.length_zip, h_len₁]
      simp_all
      rw[h_len₂] at h_i_xs
      rw[h_len₁] at h_i_xs
      exact h_i_xs⟩ ≠
    (es.zip xs').get ⟨i, by
      rw [List.length_zip, ← h_len₁]
      simp_all
      rw[h_len₂] at h_i_xs
      rw[h_len₁] at h_i_xs
      exact h_i_xs⟩ := by
  intro eq
  apply h
  have := congrArg Prod.snd eq
  simpa using this

theorem ne_symm' {α} {a b : α} (h : a ≠ b) : b ≠ a :=
by
  simpa [eq_comm] using h
