import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.List.Basic

import Runwai.Typing

open Ast

theorem evalprop_var_deterministic
  {σ : Env.ValEnv} {Δ : Env.CircuitEnv} {x : String} :
  ∀ {v₁ v₂}, Eval.EvalProp σ Δ (Expr.var x) v₁ → Eval.EvalProp σ Δ (Expr.var x) v₂ → v₁ = v₂ := by {
    intro v₁ v₂ h₁ h₂
    cases h₁
    cases h₂
    simp_all
  }

theorem length_eq_zero {α : Type} {xs : List α} :
  xs.length = 0 → xs = [] := by
  cases xs with
  | nil =>
    intro _; rfl
  | cons x xs' =>
    intro h
    simp at h

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
  | ConstF =>
    cases h₂
    case ConstF => rfl
  | ConstZ =>
    cases h₂
    case ConstZ => rfl
  | ConstBool =>
    cases h₂
    case ConstBool => rfl
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

theorem ty_preserve (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ₁: Env.TyEnv) (e: Ast.Expr) (τ: Ast.Ty)
  (h₂: @Ty.TypeJudgment σ Δ Γ₁ e τ) :
  ∀ Γ₂: Env.TyEnv, (∀ x, Env.lookupTy Γ₁ x = Env.lookupTy Γ₂ x) →
        @Ty.TypeJudgment σ Δ Γ₂ e τ := by {
    induction h₂ with
    | TE_Var φ ha => {
      rename_i Γ' x' τ'
      intro Γ₂ h
      apply Ty.TypeJudgment.TE_Var
      have h₁' := h x'
      rw[← h₁']
      exact ha
    }
    | TE_VarEnv φ _ => {
      rename_i Γ' x τ h₁
      intro Γ₂ h₂
      apply Ty.TypeJudgment.TE_VarEnv
      have h₃ := h₂ x
      rw[← h₃]
      exact h₁
    }
    | TE_VarFunc _ => {
      rename_i Γ' x₁ x₂ τ₁ τ₂ h
      intro Γ₂ h'
      apply Ty.TypeJudgment.TE_VarFunc
      have h₃ := h' x₁
      rw[← h₃]
      exact h
    }
    | TE_ArrayIndex h₁ h₂ h₃ a_ih => {
      rename_i e₁ e₂ τ' idx n φ h₅
      intro Γ₂ h₄
      apply Ty.TypeJudgment.TE_ArrayIndex
      apply a_ih
      exact h₄
      exact h₂
      exact h₃
    }
    | TE_Branch h₁ h₂ ih₁ ih₂ => {
      sorry
    }
    | TE_ConstF => {
      sorry
    }
    | TE_ConstZ => {
      sorry
    }
    | TE_Assert h₁ h₂ ih₁ ih₂ => {
      sorry
    }
    | TE_BinOpField h₁ h₂ ih₁ ih₂ => {
      sorry
    }
    | TE_Abs ih₀ ih₁ ih₂ => {
      rename_i Γ' x₁' τ₁' τ₂' e'
      intro Γ₂ h
      apply Ty.TypeJudgment.TE_Abs
      have hu := @update_preserve_pointwise Γ' Γ₂ x₁' τ₁' h
      have h' := hu x₁'
      rw[← h']
      exact ih₀
      apply ih₂
      have hu := @update_preserve_pointwise Γ' Γ₂ x₁' τ₁' h
      exact hu
    }
    | TE_App h₁ h₂ h₃ ih₁ ih₂ => {
      rename_i e₁ e₂ x τ₁ τ₂ v₁ h₅
      intro Γ₂ h
      apply Ty.TypeJudgment.TE_App
      apply ih₁
      exact h
      exact h₂
      apply ih₂
      exact h
    }
    | TE_SUB h₀ ht ih => {
      rename_i Γ' e₁ τ₁ τ₂
      intro Γ₂ h
      apply Ty.TypeJudgment.TE_SUB
      sorry
      apply ih
      exact h
    }
    | TE_LetIn h₁ h₂ ih₁ ih₂ => {
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
  }

theorem ty_swap_preserve (Γ: Env.TyEnv) (x₁ x₂: String) (τ₁ τ₂: Ast.Ty) (hne: x₁ ≠ x₂)
  (h: @Ty.TypeJudgment σ Δ (Env.updateTy (Env.updateTy Γ x₁ τ₁) x₂ τ₂) e τ₁):
  @Ty.TypeJudgment σ Δ (Env.updateTy (Env.updateTy Γ x₂ τ₂) x₁ τ₁) e τ₁ := by {
    sorry
  }

theorem type_update_preserve
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv) (e: Expr) (τ₁ τ₂: Ty) (x: String)
  (h₁: @Ty.TypeJudgment σ Δ Γ e τ₁):
  @Ty.TypeJudgment σ Δ (Env.updateTy Γ x τ₂) e τ₁ := by {
    induction h₁ generalizing τ₂ with
    | TE_Var φ _ => {
      apply Ty.TypeJudgment.TE_Var
      sorry
      sorry
    }
    | TE_VarEnv φ _ => {
      apply Ty.TypeJudgment.TE_VarEnv
      sorry
    }
    | TE_VarFunc _ => {
      apply Ty.TypeJudgment.TE_VarFunc
      sorry
    }
    | TE_ArrayIndex hi₁ hi₂ hi₃ hi₄ => {
      apply Ty.TypeJudgment.TE_ArrayIndex
      apply hi₄ τ₂
      exact hi₂
      exact hi₃
    }
    | TE_Branch hi₁ hi₂ hi₃ hi₄ => {
      apply Ty.TypeJudgment.TE_Branch
      exact hi₃ τ₂
      exact hi₄ τ₂
    }
    | TE_ConstF => {
      apply Ty.TypeJudgment.TE_ConstF
    }
    | TE_ConstZ => {
      apply Ty.TypeJudgment.TE_ConstZ
    }
    | TE_Assert ih₁ ih₂ ih₃ ih₄ => {
      apply Ty.TypeJudgment.TE_Assert
      apply ih₃ τ₂
      apply ih₄ τ₂
    }
    | TE_BinOpField ih₁ ih₂ ih₄ ih₅ => {
      apply Ty.TypeJudgment.TE_BinOpField
      apply ih₄ τ₂
      apply ih₅ τ₂
    }
    | TE_Abs ih₁ ih₂ => {
      rename_i Γ' x' τ₁' τ₂' e' h
      apply Ty.TypeJudgment.TE_Abs
      by_cases b: x = x'
      . simp_all
        intro a b h₂
        sorry
      . sorry
      sorry
      --unfold Env.updateTy at h ⊢
      --simp_all
    }
    | TE_App ih₁ ih₂ ih₃ ih₄ ih₅ => {
      apply Ty.TypeJudgment.TE_App
      apply ih₄ τ₂
      exact ih₂
      apply ih₅
    }
    | TE_SUB h₀ ht ih₁ => {
      apply Ty.TypeJudgment.TE_SUB
      sorry
      apply ih₁
    }
    | TE_LetIn h₁ h₂ ih₁ ih₂ => {
      apply Ty.TypeJudgment.TE_LetIn
      sorry
      sorry
      sorry
      sorry
    }
  }

lemma isZero_eval_eq_branch_semantics {x y inv: Expr} {σ: Env.ValEnv} {Δ: Env.CircuitEnv}
  (h₁: Eval.EvalProp σ Δ (exprEq y ((((Expr.constF 0).fieldExpr FieldOp.sub x).fieldExpr FieldOp.mul inv).fieldExpr
                  FieldOp.add (Expr.constF 1))) (Value.vBool true))
  (h₂: Eval.EvalProp σ Δ (exprEq (x.fieldExpr FieldOp.mul y) (Expr.constF 0)) (Value.vBool true)) :
  Eval.EvalProp σ Δ (exprEq y (.branch (x.binRel RelOp.eq (Expr.constF 0)) (Expr.constF 1) (Expr.constF 0))) (Value.vBool true) := by {
    cases h₁ with
    | Rel ih₁ ih₂ r₁ => {
      rename_i v₁ v₂
      cases ih₂ with
      | FBinOp ih₃ ih₄ r₂ => {
        rename_i i₁ i₂
        cases ih₃ with
        | FBinOp ih₅ ih₆ r₃ => {
          rename_i i₃ i₄
          cases ih₅ with
          | FBinOp ih₇ ih₈ r₄ => {
            rename_i i₅ i₆
            cases h₂ with
            | Rel ih₉ ih₁₀ r₅ => {
              rename_i i₇ i₈
              cases ih₄
              cases ih₇
              cases ih₁₀
              cases ih₉ with
              | FBinOp ih₁₁ ih₁₂ r₆ => {
                rename_i i₉ i₁₀
                unfold Eval.evalFieldOp at r₂ r₃ r₄ r₆
                simp_all
                cases v₁ with
                | vF xv₁ => {
                  cases v₂ with
                  | vF xv₂ => {
                    cases i₇ with
                    | vF xv₃ => {
                      simp at r₁ r₅
                      simp_all
                      have h₁ := evalprop_deterministic ih₈ ih₁₁
                      have h₂ := evalprop_deterministic ih₁ ih₁₂
                      simp_all
                      set inv_val := i₄
                      set x_val := i₉
                      set y_val := i₁₀
                      rw[← r₄] at r₃
                      rw[← r₃] at r₂
                      unfold exprEq
                      apply Eval.EvalProp.Rel
                      exact ih₁₂
                      have h₃: x_val = 0 → Eval.EvalProp σ Δ ((x.binRel RelOp.eq (Expr.constF 0)).branch (Expr.constF 1) (Expr.constF 0)) (Value.vF 1) := by {
                        intro h
                        apply Eval.EvalProp.IfTrue
                        apply Eval.EvalProp.Rel
                        exact ih₁₁
                        apply Eval.EvalProp.ConstF
                        unfold Eval.evalRelOp
                        simp_all
                        apply Eval.EvalProp.ConstF
                      }
                      have h₄: x_val ≠ 0 → Eval.EvalProp σ Δ ((x.binRel RelOp.eq (Expr.constF 0)).branch (Expr.constF 1) (Expr.constF 0)) (Value.vF 0) := by {
                        intro h
                        apply Eval.EvalProp.IfFalse
                        apply Eval.EvalProp.Rel
                        exact ih₁₁
                        apply Eval.EvalProp.ConstF
                        unfold Eval.evalRelOp
                        simp_all
                        apply Eval.EvalProp.ConstF
                      }
                      have h₅: Eval.EvalProp σ Δ ((x.binRel RelOp.eq (Expr.constF 0)).branch (Expr.constF 1) (Expr.constF 0)) (if x_val = 0 then (Value.vF 1) else (Value.vF 0)) := by {
                        by_cases hz : x_val = 0
                        . simp_all
                        . simp_all
                      }
                      exact h₅
                      by_cases hz: x_val = 0
                      . simp_all
                        rw[← r₃] at r₄
                        rw[← r₄] at r₂
                        rw [neg_zero, zero_mul, zero_add] at r₂
                        rw[r₂]
                      . simp_all
                    }
                    | _ => simp_all
                  }
                  | _ => simp_all
                }
                | vZ => {
                  cases v₂ with
                  | _ => simp_all
                }
                | _ => simp_all
              }
            }
          }
        }
      }
    }
  }

theorem eq_none_of_isSome_eq_false {α : Type _}
    {o : Option α} (h : o.isSome = false) : o = none := by
  cases o <;> simp_all

lemma nonupdate (Γ: Env.TyEnv) (x: String) (τ: Ast.Ty) (h: Env.lookupTy Γ x = none):
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

lemma dif_lookup (Γ: Env.TyEnv) (x y: String) (τ: Ast.Ty) (h: x ≠ y):
  Env.lookupTy (Env.updateTy Γ x τ) y = Env.lookupTy Γ y := by
  unfold Env.lookupTy Env.updateTy
  simp
  by_cases hx : (List.find? (fun p => decide (p.1 = x)) Γ).isSome
  · simp [hx]
  · -- case: x not in Γ
    simp [hx]
    have h': (if x = y then some (x, τ) else none) = none := by simp_all
    rw[h']
    simp

lemma isZero_typing_soundness (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv) (φ₁ φ₂ φ₃: Ast.Predicate)
  (x y inv : Expr)
  (u₁ u₂: String)
  (htx: @Ty.TypeJudgment σ Δ Γ x (Ty.refin Ast.Ty.field φ₁))
  (hty: @Ty.TypeJudgment σ Δ Γ y (Ty.refin Ast.Ty.field φ₂))
  (htinv: @Ty.TypeJudgment σ Δ Γ inv (Ty.refin Ast.Ty.field φ₃))
  (hne₁: (Expr.var u₁) ≠ x)
  (hne₂: (Expr.var u₁) ≠ y)
  (hne₃: ¬ u₁ = u₂)
  (hhf₁: Env.lookupTy Γ u₁ = none)
  (hhf₂: Env.lookupTy Γ u₂ = none)
  (hf₁: ¬ (Γ.find? (·.1 = u₁)).isSome)
  (hf₂: ¬ (Γ.find? (·.1 = u₂)).isSome):
  @Ty.TypeJudgment σ Δ Γ
    (Ast.Expr.letIn u₁ (.assertE y (.fieldExpr (.fieldExpr (.fieldExpr (.constF 0) .sub x) .mul inv) (.add) (.constF 1)))
      (Ast.Expr.letIn u₂ (.assertE (.fieldExpr x .mul y) (.constF 0)) (.var u₂)))
    (Ty.refin Ast.Ty.unit (Ast.Predicate.const (exprEq y (.branch (.binRel x (.eq) (.constF 0)) (.constF 1) (.constF 0))))) := by {
    apply Ty.TypeJudgment.TE_LetIn
    apply nonupdate
    exact hhf₁
    apply Ty.TypeJudgment.TE_Assert
    exact hty
    apply Ty.TypeJudgment.TE_BinOpField
    apply Ty.TypeJudgment.TE_BinOpField
    apply Ty.TypeJudgment.TE_BinOpField
    apply Ty.TypeJudgment.TE_ConstF
    exact htx
    exact htinv
    apply Ty.TypeJudgment.TE_ConstF
    apply Ty.TypeJudgment.TE_LetIn
    apply nonupdate
    rw[← hhf₂]
    apply dif_lookup
    exact hne₃
    apply Ty.TypeJudgment.TE_Assert
    apply Ty.TypeJudgment.TE_BinOpField
    apply type_update_preserve
    . exact htx
    apply type_update_preserve
    . exact hty
    apply Ty.TypeJudgment.TE_ConstF
    have h_sub : @Ty.SubtypeJudgment σ Δ (Env.updateTy
      (Env.updateTy Γ u₁
        (Ty.unit.refin
          (Predicate.const
            (exprEq y
              ((((Expr.constF 0).fieldExpr FieldOp.sub x).fieldExpr FieldOp.mul inv).fieldExpr FieldOp.add
                (Expr.constF 1))))))
      u₂ (Ty.unit.refin (Predicate.const (exprEq (x.fieldExpr FieldOp.mul y) (Expr.constF 0)))))
      (Ty.unit.refin (Predicate.const (exprEq (x.fieldExpr FieldOp.mul y) (Expr.constF 0))))
      (Ty.unit.refin
        (Predicate.const (exprEq y ((x.binRel RelOp.eq (Expr.constF 0)).branch (Expr.constF 1) (Expr.constF 0))))) := by {
        apply Ty.SubtypeJudgment.TSub_Refine
        apply Ty.SubtypeJudgment.TSub_Refl
        unfold PropSemantics.tyenvToProp
        unfold PropSemantics.predToProp
        unfold PropSemantics.exprToProp
        unfold PropSemantics.varToProp
        simp
        unfold Env.lookupTy
        unfold Env.updateTy
        simp
        intro v h₁ h₂
        have h₃ := h₁ u₁ (Ty.unit.refin
              (Predicate.const
                (exprEq y
                  ((((Expr.constF 0).fieldExpr FieldOp.sub x).fieldExpr FieldOp.mul inv).fieldExpr FieldOp.add
                    (Expr.constF 1)))))
        have h₄ : ¬ u₂ = u₁ := by exact ne_symm' hne₃
        --simp
        have hf₃: (Γ.find? (·.1 = u₁)) = none := eq_none_of_isSome_eq_false (by simp [hf₁])
        rw [hf₃] at h₃
        simp_all
        unfold PropSemantics.predToProp at h₃
        unfold PropSemantics.exprToProp at h₃
        apply isZero_eval_eq_branch_semantics h₃ h₂
      }
    apply Ty.TypeJudgment.TE_SUB
    exact h_sub
    apply Ty.TypeJudgment.TE_VarEnv
    unfold Env.updateTy Env.lookupTy
    simp_all
    have hf₅: (List.find? (fun x ↦ decide (x.1 = u₂)) Γ) = none := by sorry
    rw[hf₅]
    simp_all
}
