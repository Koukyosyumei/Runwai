import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.List.Basic

import Runwai.Typing

open Ast

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

theorem evalprop_deterministic
  {σ : Env.ValEnv} {Δ : Env.CircuitEnv} {e : Expr} :
  ∀ {v₁ v₂}, Eval.EvalProp σ Δ e v₁ → Eval.EvalProp σ Δ e v₂ → v₁ = v₂ := by
  intro v₁ v₂ h₁ h₂
  induction h₁ generalizing v₂ with
  | ConstF => cases h₂; rfl
  | ConstZ => cases h₂; rfl
  | ConstBool => cases h₂; rfl
  | ConstArr h_length h_forall in_det =>
    rename_i es xs
    cases h₂
    case ConstArr xs' h_length' h_forall' =>
    have hlen : xs.length = xs'.length := by
      rw [← h_length, h_length']
    by_contra hneq
    have hneq' : ¬ xs = xs' := by simp_all
    have ⟨i, hi_lt, hi_ne⟩ := ne_imp_exists_diff hlen hneq'
    have hes_ne := zip_get_ne (Eq.symm h_length) hlen hi_lt hi_ne
    have h_len₁ : i < (es.zip xs).length := by
      rw [List.length_zip, h_length]
      simp_all
      rw[hlen] at hi_lt
      exact hi_lt
    have h_len₂ : i < (es.zip xs').length := by
      rw [List.length_zip, h_length, hlen]
      simp_all
    set exs_lhs := (es.zip xs).get ⟨i, h_len₁⟩ with lhs_eq
    set exs_rhs := (es.zip xs').get ⟨i, h_len₂⟩ with rhs_eq
    have h_in: exs_lhs ∈ es.zip xs := by apply List.get_mem
    have h_in': exs_rhs ∈ es.zip xs' := by apply List.get_mem
    have h₁ := h_forall exs_lhs h_in
    have h₂ := h_forall' exs_rhs h_in'
    have h₃ : exs_lhs.1 = exs_rhs.1 := by simp_all
    rw[← h₃] at h₂
    have h₄ := in_det exs_lhs h_in h₂
    simp_all
  | Var lookup_eq =>
    cases h₂
    case Var lookup_eq' =>
      rw[lookup_eq] at  lookup_eq'
      exact lookup_eq'
  | Lam =>
    cases h₂
    case Lam => rfl
  | Let ih₁ ih₂ ih₁_ih ih₂_ih =>
    cases h₂
    case Let ih₁' ih₂' =>
    rename_i σ' Δ' x' e₁' e_2' v₁' v₂' v₃
    have hv₁ := ih₁_ih ih₁'
    rw[← hv₁] at ih₂'
    exact ih₂_ih ih₂'
  | App ih_f ih_a ih_b ih_f_ih ih_a_ih ih_b_ih => {
    cases h₂
    case App ih_f' ih_a' ih_b' =>
    have hf_eq := ih_f_ih ih_f'
    have ha_eq := ih_a_ih ih_a'
    simp_all
    exact ih_b_ih ih_b'
  }
  | FBinOp ih₁ ih₂ r ih₁_ih ih₂_ih => {
    cases h₂
    case FBinOp i₁' i₂' ih₁' ih₂' ih₃' =>
    have h₁_eq := ih₁_ih ih₁'
    have h₂_eq := ih₂_ih ih₂'
    simp_all
  }
  | BoolOp ih₁ ih₂ bv ih₁_ih ih₂_ih => {
    cases h₂
    case BoolOp b₁' b₂' b₃' ih₁' ih₂' ih₃' =>
    have h₁_eq := ih₁_ih ih₁'
    have h₂_eq := ih₂_ih ih₃'
    simp_all
  }
  | Rel ih₁ ih₂ bv ih₁_ih ih₂_ih => {
    cases h₂
    case Rel b₁' b₂' b₃' ih₁' ih₂' ih₃' =>
    have h₁_eq := ih₁_ih ih₁'
    have h₂_eq := ih₂_ih ih₃'
    simp_all
  }
  | IfTrue ihc ih₁ ihc_ih ih₁_ih => {
    cases h₂
    case IfTrue ih₁' ih₂' =>
      have h₁_eq := ih₁_ih ih₂'
      exact h₁_eq
    case IfFalse ih₁' ih₂' =>
      have h₁_eq := ihc_ih ih₁'
      simp_all
  }
  | IfFalse ihc ih₁ ihc_ih ih₁_ih => {
    cases h₂
    case IfFalse ih₁' ih₂' =>
      have h₁_eq := ih₁_ih ih₂'
      exact h₁_eq
    case IfTrue ih₁' ih₂' =>
      have h₁_eq := ihc_ih ih₁'
      simp_all
  }
  | Assert ih₁ ih₂ ok ih₁_ih ih₂_ih => {
    cases h₂
    case Assert v₁' v₂' b he ih₁' ih₂' =>
      have h₁_eq := ih₁_ih ih₁'
      have h₂_eq := ih₂_ih ih₂'
      simp_all
  }
  | ArrIdx iha ihi idx iha_ih ihi_ih => {
    cases h₂
    case ArrIdx vs' j' iha' ihi' idx' =>
      have ha := iha_ih iha'
      have hi := ihi_ih ihi'
      simp_all
  }

theorem ne_symm' {α} {a b : α} (h : a ≠ b) : b ≠ a :=
by
  simpa [eq_comm] using h

theorem swap_preserve (Γ: Env.TyEnv) (x₁ x₂: String) (τ₁ τ₂: Ast.Ty) (hne: x₁ ≠ x₂):
  ∀ x, Env.lookupTy (Env.updateTy (Env.updateTy Γ x₁ τ₁) x₂ τ₂) x = Env.lookupTy (Env.updateTy (Env.updateTy Γ x₂ τ₂) x₁ τ₁) x := by
  unfold Env.updateTy
  by_cases h₁ : (Γ.find? (fun x => x.1 = x₁)).isSome
  · by_cases h₂ : (Γ.find? (fun x => x.1 = x₂)).isSome
    · simp [h₁, h₂]
    · simp [h₁, h₂]
  · by_cases h₂ : (Γ.find? (fun x => x.1 = x₂)).isSome
    · simp [h₁, h₂]
    · simp [h₁, h₂]
      intro x
      have hne' : x₂ ≠ x₁ := ne_symm' hne
      simp_all
      by_cases b₃: x = x₁
      . unfold Env.lookupTy
        simp_all
      . by_cases b₄: x = x₂
        . unfold Env.lookupTy
          simp_all
        . unfold Env.lookupTy
          have hΓ : (List.find? (fun x_1 => decide (x_1.1 = x)) [(x₁, τ₁), (x₂, τ₂)]) = none := by
            have b₃' := ne_symm' b₃
            have b₄' := ne_symm' b₄
            simp_all
          have hΓ' : (List.find? (fun x_1 => decide (x_1.1 = x)) [(x₂, τ₂), (x₁, τ₁)]) = none := by
            have b₃' := ne_symm' b₃
            have b₄' := ne_symm' b₄
            simp_all
          simp [hΓ, hΓ']

lemma lookup_update_other
  (Γ : Env.TyEnv) (x y : String) (τ : Ast.Ty) (hxy : y ≠ x) :
  Env.lookupTy (Env.updateTy Γ x τ) y = Env.lookupTy Γ y := by
  unfold Env.updateTy
  by_cases hx : (Γ.find? (fun (p, _) => p = x)).isSome
  · simp [hx, Env.lookupTy]
  · simp [hx, Env.lookupTy]
    simp_all
    have h₁ : (if x = y then some (y, τ) else none) = none := by {
      simp_all
      exact ne_symm' hxy
    }
    rw[h₁]
    simp_all

lemma lookup_update_self
  (Γ : Env.TyEnv) (x : String) (τ : Ast.Ty) :
  Env.lookupTy (Env.updateTy Γ x τ) x =
    match Env.lookupTy Γ x with
    | some t => some t
    | none   => some τ := by
  unfold Env.updateTy
  by_cases hx : (Γ.find? (fun (p, _) => p = x)).isSome
  · unfold Env.lookupTy
    rw[hx]
    simp_all
    cases hx': List.find? (fun x_1 ↦ decide (x_1.1 = x)) Γ with
    | none => {
      simp_all
      obtain ⟨τ'⟩ := hx
      rename_i h'
      have hy := hx' x τ'
      simp at hy
      contradiction
    }
    | some val => {
      simp_all
    }
  · simp_all
    simp [Env.lookupTy]
    cases hx': List.find? (fun x_1 ↦ decide (x_1.1 = x)) Γ with
    | none => {
      simp_all
    }
    | some val => {
      simp_all
    }

lemma update_preserve_pointwise
  (Γ₁ Γ₂ : Env.TyEnv) (x : String) (τ : Ast.Ty)
  (h : ∀ y, Env.lookupTy Γ₁ y = Env.lookupTy Γ₂ y) :
  ∀ y, Env.lookupTy (Env.updateTy Γ₁ x τ) y = Env.lookupTy (Env.updateTy Γ₂ x τ) y := by
  intro y
  by_cases hy : y = x
  · subst hy
    simp [lookup_update_self, h]
  · simp [lookup_update_other _ _ _ _ hy, h y]

theorem eq_none_of_isSome_eq_false {α : Type _}
    {o : Option α} (h : o.isSome = false) : o = none := by
  cases o <;> simp_all

lemma lookup_update_self_none (Γ: Env.TyEnv) (x: String) (τ: Ast.Ty) (h: Env.lookupTy Γ x = none):
  Env.lookupTy (Env.updateTy Γ x τ) x = τ:= by {
    unfold Env.lookupTy at h ⊢
    unfold Env.updateTy
    simp_all
    cases b: List.find? (fun x_1 ↦ decide (x_1.1 = x)) Γ with
    | none => {
      simp
      rw[b]
      simp_all
    }
    | some val => {
      simp_all
    }
  }

lemma lookup_update_ne (Γ: Env.TyEnv) (x y: String) (τ: Ast.Ty) (h: x ≠ y):
  Env.lookupTy (Env.updateTy Γ x τ) y = Env.lookupTy Γ y := by
  unfold Env.lookupTy Env.updateTy
  simp
  by_cases hx : (List.find? (fun p => decide (p.1 = x)) Γ).isSome
  · simp [hx]
  · simp [hx]
    have h': (if x = y then some (x, τ) else none) = none := by simp_all
    rw[h']
    simp

lemma lookup_update_ne_none (Γ: Env.TyEnv) (x y: String) (hne: x ≠ y) (h: Env.lookupTy Γ y = none) (τ: Ast.Ty):
  Env.lookupTy (Env.updateTy Γ x τ) y = none := by {
    unfold Env.lookupTy at h ⊢
    unfold Env.updateTy
    simp_all
    cases b: List.find? (fun x_1 ↦ decide (x_1.1 = x)) Γ with
    | none => simp_all
    | some val => simp_all
  }

lemma lookup_empty_none (x: String):
  Env.lookupTy [] x = none := by {
    unfold Env.lookupTy
    simp
  }

lemma lookup_update_other_preserve (Γ: Env.TyEnv) (x y: String) (τ₁ τ₂: Ast.Ty) (h: Env.lookupTy Γ x = τ₁):
  Env.lookupTy (Env.updateTy Γ y τ₂) x = τ₁ := by {
    unfold Env.lookupTy at h ⊢
    unfold Env.updateTy
    simp_all
    cases b: List.find? (fun x_1 ↦ decide (x_1.1 = x)) Γ with
    | none => simp_all
    | some val => {
      cases b': List.find? (fun x_1 ↦ decide (x_1.1 = y)) Γ with
      | none => {
        simp_all
      }
      | some val => {
        simp_all
      }
    }
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

theorem varToProp_pointwise_preserve (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ₁ Γ₂: Env.TyEnv) (ident: String)
  (h₁: ∀ x, Env.lookupTy Γ₁ x = Env.lookupTy Γ₂ x) (h₂: PropSemantics.varToProp σ Δ Γ₁ ident):
  PropSemantics.varToProp σ Δ Γ₂ ident := by {
    unfold PropSemantics.varToProp at h₂ ⊢
    have h₁' := h₁ ident
    rw[← h₁']
    exact h₂
  }

theorem tyenvToProp_pointwise_preserve (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ₁ Γ₂: Env.TyEnv)
  (h₁: ∀ x, Env.lookupTy Γ₁ x = Env.lookupTy Γ₂ x) (h₂: PropSemantics.tyenvToProp σ Δ Γ₁):
  PropSemantics.tyenvToProp σ Δ Γ₂ := by {
    unfold PropSemantics.tyenvToProp at h₂ ⊢
    intro x τ h₃
    have h₄ := h₁ x
    rw[← h₄] at h₃
    have h₅ := h₂ x τ h₃
    exact varToProp_pointwise_preserve σ Δ Γ₁ Γ₂ x h₁ h₅
  }

theorem subtyping_pointwise_preserve (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ₁: Env.TyEnv) (τ₁ τ₂: Ast.Ty)
  (h₂: Ty.SubtypeJudgment σ Δ Γ₁ τ₁ τ₂) :
  ∀ Γ₂: Env.TyEnv, (∀ x, Env.lookupTy Γ₁ x = Env.lookupTy Γ₂ x) →
    Ty.SubtypeJudgment σ Δ Γ₂ τ₁ τ₂ := by {
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
        intro v h'₁ h'₂
        apply ih₁
        rename_i σ' Δ' Γ' τ₁' τ₂' φ₁' φ₂'
        exact tyenvToProp_pointwise_preserve σ' Δ' Γ₂ Γ' (lookupTy_pointwise_symm Γ' Γ₂ h) h'₁
        exact h'₂
      }
      | TSub_Fun h₁ h₂ ih₁ ih₂ => {
        intro Γ₂ h
        apply Ty.SubtypeJudgment.TSub_Fun
        apply ih₁; exact h
        apply ih₂; exact h
      }
      | TSub_Arr h₁ ih => {
        intro Γ₂ h
        apply Ty.SubtypeJudgment.TSub_Arr; apply ih; assumption
      }
    }

theorem typing_pointwise_preserve (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ₁: Env.TyEnv) (e: Ast.Expr) (τ: Ast.Ty)
  (h₂: @Ty.TypeJudgment σ Δ Γ₁ e τ) :
  ∀ Γ₂: Env.TyEnv, (∀ x, Env.lookupTy Γ₁ x = Env.lookupTy Γ₂ x) →
        @Ty.TypeJudgment σ Δ Γ₂ e τ := by {
    induction h₂ with
    | TE_Var _ ha => intro Γ₂ h; apply Ty.TypeJudgment.TE_Var; rwa [← h]
    | TE_VarEnv _ h₁ => intro Γ₂ h; apply Ty.TypeJudgment.TE_VarEnv; rwa [← h]
    | TE_VarFunc _ =>
      rename_i Γ' x₁ x₂ τ₁ τ₂ h
      intro Γ₂ h'
      apply Ty.TypeJudgment.TE_VarFunc
      have h₃ := h' x₁
      rw[← h₃]
      exact h
    | TE_ArrayIndex _ h₂ h₃ a_ih => intro Γ₂ h; apply Ty.TypeJudgment.TE_ArrayIndex (a_ih Γ₂ h) h₂ h₃
    | TE_Branch _ _ ih₁ ih₂ => intro Γ₂ h; apply Ty.TypeJudgment.TE_Branch (ih₁ Γ₂ h) (ih₂ Γ₂ h)
    | TE_ConstF => intros; constructor
    | TE_ConstZ => intros; constructor
    | TE_Assert _ _ ih₁ ih₂ => intro Γ₂ h; apply Ty.TypeJudgment.TE_Assert (ih₁ Γ₂ h) (ih₂ Γ₂ h)
    | TE_BinOpField _ _ ih₁ ih₂ => intro Γ₂ h; apply Ty.TypeJudgment.TE_BinOpField (ih₁ Γ₂ h) (ih₂ Γ₂ h)
    | TE_Abs ih₀ _ ih₂ =>
      intro Γ₂ h
      apply Ty.TypeJudgment.TE_Abs
      · rwa [← update_preserve_pointwise _ _ _ _ h]
      · apply ih₂; exact update_preserve_pointwise _ _ _ _ h
    | TE_App _ h₂ _ ih₁ ih₂ =>
      intro Γ₂ h
      apply Ty.TypeJudgment.TE_App (ih₁ Γ₂ h) h₂ (ih₂ Γ₂ h)
    | TE_SUB h₀ _ ih =>
      intro Γ₂ h
      apply Ty.TypeJudgment.TE_SUB
      · exact subtyping_pointwise_preserve σ Δ _ _ _ h₀ Γ₂ h
      · apply ih; assumption
    | TE_LetIn h₁ h₂ ih₁ ih₂ =>
      rename_i Γ' x₁ e₁ e₂ τ₁ τ₂ h'
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
  }

lemma mem_update_preserve (Γ: Env.TyEnv) (x x': String) (τ τ': Ty) (h: (x, τ) ∈ Γ):
  (x, τ) ∈ (Env.updateTy Γ x' τ') := by
  unfold Env.updateTy
  by_cases hx : (Γ.find? (fun p => p.1 = x')).isSome
  · simp_all
  · simp [hx, h]

theorem tyenvToProp_update_subset (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv) (x: String) (τ: Ty)
  (h: PropSemantics.tyenvToProp σ Δ (Env.updateTy Γ x τ)):
  PropSemantics.tyenvToProp σ Δ Γ:= by {
    unfold PropSemantics.tyenvToProp at h ⊢
    by_contra hn
    simp at hn
    obtain ⟨x', hn₁, hn₂⟩ := hn
    obtain ⟨τ', hn₃⟩ := hn₁
    have hn₄ := lookup_update_other_preserve Γ x' x τ' τ hn₃
    have h₂ := h x' τ' hn₄
    unfold PropSemantics.varToProp at hn₂ h₂
    cases ov: Env.lookupTy Γ x' with
    | none => {
      unfold Env.lookupTy at ov
      cases b: List.find? (fun x ↦ decide (x.1 = x')) Γ with
      | none => {
        simp_all
      }
      | some val => {
        rw[b] at ov
        cases val with
        | mk fst snd => {
          simp at ov
        }
      }
    }
    | some τ₁ => {
      have h₄ := lookup_update_other_preserve Γ x' x τ₁ τ ov
      rw[ov] at hn₂
      rw[h₄] at h₂
      simp_all
    }
}

theorem subtype_update_preserve
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv) (τ₁ τ₂ τ₃: Ty) (x: String)
  (h: Ty.SubtypeJudgment σ Δ Γ τ₁ τ₂):
  Ty.SubtypeJudgment σ Δ (Env.updateTy Γ x τ₃) τ₁ τ₂ := by {
    induction h generalizing τ₃ with
    | TSub_Refl => constructor
    | TSub_Trans _ _ ih₁ ih₂ => apply Ty.SubtypeJudgment.TSub_Trans; apply ih₁; apply ih₂
    | TSub_Refine _ ih₁ ih₂ =>
      apply Ty.SubtypeJudgment.TSub_Refine (ih₂ τ₃)
      intro v hv₁ hv₂
      apply ih₁; apply tyenvToProp_update_subset; exact hv₁; exact hv₂
    | TSub_Fun _ _ ih₁ ih₂ => apply Ty.SubtypeJudgment.TSub_Fun; apply ih₁; apply ih₂
    | TSub_Arr _ ih => apply Ty.SubtypeJudgment.TSub_Arr; apply ih
  }

lemma isZero_eval_eq_branch_semantics {x y inv: Expr} {σ: Env.ValEnv} {Δ: Env.CircuitEnv}
  (h₁ : Eval.EvalProp σ Δ (exprEq y ((((Expr.constF 0).fieldExpr FieldOp.sub x).fieldExpr FieldOp.mul inv).fieldExpr
                  FieldOp.add (Expr.constF 1))) (Value.vBool true))
  (h₂ : Eval.EvalProp σ Δ (exprEq (x.fieldExpr FieldOp.mul y) (Expr.constF 0)) (Value.vBool true))
  (hx : Eval.EvalProp σ Δ x xv) (hy : Eval.EvalProp σ Δ y yv) (hinv : Eval.EvalProp σ Δ inv invv) :
  Eval.EvalProp σ Δ (exprEq y (.branch (x.binRel RelOp.eq (Expr.constF 0)) (Expr.constF 1) (Expr.constF 0))) (Value.vBool true) := by {
  cases h₁; cases h₂; rename_i v₁ v₂ ih₁ ih₂ r v₃ v₄ ih₃ ih₄ ih₅
  cases ih₂; cases ih₃; cases ih₄; rename_i v₅ v₆ ih₂ ih₃ ih₄ i₃ i₄ ih₆ ih₇ ih₈
  cases ih₂; cases ih₃; rename_i i₅ i₆ ih₂ ih₃ ih₉
  cases ih₂; rename_i i₁ i₂ ih₂ ihh₁ ihh₂
  cases ih₂
  have he₁ := evalprop_deterministic hy ih₁
  have he₂ := evalprop_deterministic hx ih₆
  have he₃ := evalprop_deterministic hinv ih₃
  have he₄ := evalprop_deterministic hy ih₇
  cases ih₈; simp at ih₅; cases ih₉; simp at ih₄; cases ihh₂; simp at ih₄
  set x_val := i₃; set y_val := i₄; set inv_val := i₆
  have he₅ := evalprop_deterministic ih₆ ihh₁
  simp at r
  rw[he₄] at he₁; rw[← ih₄, ← he₁] at r
  simp_all
  rw[← he₅] at ih₅ r
  unfold exprEq; apply Eval.EvalProp.Rel; exact ih₁
  have h₃: x_val = 0 → Eval.EvalProp σ Δ ((x.binRel RelOp.eq (Expr.constF 0)).branch (Expr.constF 1) (Expr.constF 0)) (Value.vF 1) := by {
    intro h
    apply Eval.EvalProp.IfTrue; apply Eval.EvalProp.Rel; exact ihh₁
    apply Eval.EvalProp.ConstF; unfold Eval.evalRelOp
    simp_all; apply Eval.EvalProp.ConstF
  }
  have h₄: x_val ≠ 0 → Eval.EvalProp σ Δ ((x.binRel RelOp.eq (Expr.constF 0)).branch (Expr.constF 1) (Expr.constF 0)) (Value.vF 0) := by {
    intro h
    apply Eval.EvalProp.IfFalse; apply Eval.EvalProp.Rel; exact ihh₁
    apply Eval.EvalProp.ConstF; unfold Eval.evalRelOp
    simp_all; apply Eval.EvalProp.ConstF
  }
  have h₅: Eval.EvalProp σ Δ ((x.binRel RelOp.eq (Expr.constF 0)).branch (Expr.constF 1) (Expr.constF 0)) (if x_val = 0 then (Value.vF 1) else (Value.vF 0)) := by {
    by_cases h : x_val = 0
    . simp_all
    . simp_all
  }
  exact h₅
  by_cases hz: x_val = 0
  . simp_all; rw[← he₅] at ih₄; rw [zero_mul, neg_zero, zero_add] at ih₄; rw[← ih₄]; simp
  . simp_all; rw[← ih₄]; simp
}

lemma isZero_typing_soundness (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv) (φ₁ φ₂ φ₃: Ast.Predicate)
  (x y inv u₁ u₂: String)
  (htx: Env.lookupTy Γ x = (Ty.refin Ast.Ty.field φ₁))
  (hty: Env.lookupTy Γ y = (Ty.refin Ast.Ty.field φ₂))
  (htinv: @Ty.TypeJudgment σ Δ Γ (.var inv) (Ty.refin Ast.Ty.field φ₃))
  (hne₃: ¬ u₁ = u₂)
  (hhf₁: Env.lookupTy Γ u₁ = none)
  (hhf₂: Env.lookupTy Γ u₂ = none):
  @Ty.TypeJudgment σ Δ Γ
    (Ast.Expr.letIn u₁ (.assertE (.var y) (.fieldExpr (.fieldExpr (.fieldExpr (.constF 0) .sub (.var x)) .mul (.var inv)) (.add) (.constF 1)))
      (Ast.Expr.letIn u₂ (.assertE (.fieldExpr (.var x) .mul (.var y)) (.constF 0)) (.var u₂)))
    (Ty.refin Ast.Ty.unit (Ast.Predicate.const (exprEq (.var y) (.branch (.binRel (.var x) (.eq) (.constF 0)) (.constF 1) (.constF 0))))) := by {
    apply Ty.TypeJudgment.TE_LetIn; apply lookup_update_self_none; exact hhf₁
    apply Ty.TypeJudgment.TE_Assert; apply Ty.TypeJudgment.TE_VarEnv; exact hty
    repeat apply Ty.TypeJudgment.TE_BinOpField
    apply Ty.TypeJudgment.TE_ConstF; apply Ty.TypeJudgment.TE_VarEnv; exact htx; exact htinv
    apply Ty.TypeJudgment.TE_ConstF; apply Ty.TypeJudgment.TE_LetIn; apply lookup_update_self_none
    rw[← hhf₂]
    apply lookup_update_ne; exact hne₃
    apply Ty.TypeJudgment.TE_Assert; apply Ty.TypeJudgment.TE_BinOpField; apply Ty.TypeJudgment.TE_VarEnv
    apply lookup_update_other_preserve; exact htx
    apply Ty.TypeJudgment.TE_VarEnv
    apply lookup_update_other_preserve
    . exact hty
    apply Ty.TypeJudgment.TE_ConstF
    have h_sub : @Ty.SubtypeJudgment σ Δ (Env.updateTy
      (Env.updateTy Γ u₁
        (Ty.unit.refin
          (Predicate.const
            (exprEq (Expr.var y)
              ((((Expr.constF 0).fieldExpr FieldOp.sub (.var x)).fieldExpr FieldOp.mul (Expr.var inv)).fieldExpr FieldOp.add
                (Expr.constF 1))))))
      u₂ (Ty.unit.refin (Predicate.const (exprEq ((Expr.var x).fieldExpr FieldOp.mul (Expr.var y)) (Expr.constF 0)))))
      (Ty.unit.refin (Predicate.const (exprEq ((Expr.var x).fieldExpr FieldOp.mul (Expr.var y)) (Expr.constF 0))))
      (Ty.unit.refin
        (Predicate.const (exprEq (Expr.var y) (((Expr.var x).binRel RelOp.eq (Expr.constF 0)).branch (Expr.constF 1) (Expr.constF 0))))) := by {
        apply Ty.SubtypeJudgment.TSub_Refine
        apply Ty.SubtypeJudgment.TSub_Refl
        unfold PropSemantics.tyenvToProp PropSemantics.predToProp PropSemantics.exprToProp PropSemantics.varToProp
        simp
        intro v h₁ h₂
        set φ₁ := (Predicate.const
          (exprEq (Expr.var y)
            ((((Expr.constF 0).fieldExpr FieldOp.sub (Expr.var x)).fieldExpr FieldOp.mul (Expr.var inv)).fieldExpr FieldOp.add
              (Expr.constF 1))))
        set φ₂ := (Predicate.const (exprEq ((Expr.var x).fieldExpr FieldOp.mul (Expr.var y)) (Expr.constF 0)))
        have h₃ := h₁ u₁ (Ty.unit.refin φ₁)
        have h₄: Env.lookupTy (Env.updateTy (Env.updateTy Γ u₁ (Ty.unit.refin φ₁)) u₂ (Ty.unit.refin φ₂)) u₁ = (Ty.unit.refin φ₁) := by {
          apply lookup_update_other_preserve
          apply lookup_update_self_none
          exact hhf₁
        }
        have h₅ := lookup_mem_of_eq h₄
        rw[h₄] at h₃
        simp at h₃
        unfold PropSemantics.predToProp PropSemantics.exprToProp φ₁ at h₃
        simp at h₃
        apply isZero_eval_eq_branch_semantics h₃ h₂
        repeat apply Eval.EvalProp.Var; rfl
      }
    apply Ty.TypeJudgment.TE_SUB h_sub
    apply Ty.TypeJudgment.TE_VarEnv
    apply lookup_update_self_none
    apply lookup_update_ne_none
    exact hne₃
    exact hhf₂
}
