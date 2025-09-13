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

theorem evalRelOp_eq_symm {v₁ v₂: Ast.Value} (h: Eval.evalRelOp Ast.RelOp.eq v₁ v₂ = some true):
  Eval.evalRelOp Ast.RelOp.eq v₂ v₁ = some true := by {
    unfold Eval.evalRelOp at h ⊢
    simp at h ⊢
    cases v₁
    cases v₂
    repeat simp_all
    cases v₂
    repeat simp_all
    cases v₂
    repeat simp_all
  }

theorem evalProp_eq_symm
  {σ: Env.ValEnv} {Δ: Env.ChipEnv} {e₁ e₂: Expr} (h: Eval.EvalProp σ Δ (Ast.Expr.binRel e₁ Ast.RelOp.eq e₂) (Ast.Value.vBool true)):
  Eval.EvalProp σ Δ (Ast.Expr.binRel e₂ Ast.RelOp.eq e₁) (Ast.Value.vBool true) := by {
    cases h
    rename_i v₁ v₂ h₁ h₂ h₃
    apply evalRelOp_eq_symm at h₃
    apply Eval.EvalProp.Rel
    exact h₂
    exact h₁
    exact h₃
  }

theorem evalprop_deterministic
  {σ : Env.ValEnv} {Δ : Env.ChipEnv} {e : Expr} :
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
  | ZBinOp ih₁ ih₂ r ih₁_ih ih₂_ih => {
    cases h₂
    case ZBinOp i₁' i₂' ih₁' ih₂' ih₃' =>
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
  | LookUp => {
    cases h₂
    rename_i ih₁ ih₂
    apply ih₁ ih₂
  }
  | toZ => {
    cases h₂
    rename_i v₁ ih₀ ih₁ fv₂ ih₃
    have h := ih₁ ih₃
    have h' : v₁ = fv₂ := by simp_all
    simp_all
  }

theorem evalProp_eq_trans
  {σ: Env.ValEnv} {Δ: Env.ChipEnv} {e₁ e₂ e₃: Expr}
  (h₁: Eval.EvalProp σ Δ (Ast.Expr.binRel e₁ Ast.RelOp.eq e₂) (Ast.Value.vBool true))
  (h₂: Eval.EvalProp σ Δ (Ast.Expr.binRel e₁ Ast.RelOp.eq e₃) (Ast.Value.vBool true)):
  Eval.EvalProp σ Δ (Ast.Expr.binRel e₂ Ast.RelOp.eq e₃) (Ast.Value.vBool true) := by {
    cases h₁
    cases h₂
    rename_i v₁ v₂ ih₁ ih₂ ih₃ v₃ v₄ ih₄ ih₅ ih₆
    have h := evalprop_deterministic ih₁ ih₄
    rw[← h] at ih₆
    unfold Eval.evalRelOp at ih₃ ih₆
    cases v₁ with
    | vF => {
      cases v₂ with
      | vF => {
        simp at ih₆
        cases v₄ with
        | vF => {
          simp at ih₃ ih₆
          apply Eval.EvalProp.Rel
          exact ih₂
          exact ih₅
          unfold Eval.evalRelOp
          simp
          rw[← ih₃, ← ih₆]
        }
        | _ => simp at ih₆
      }
      | _ => simp at ih₃
    }
    | vZ => {
      cases v₂ with
      | vZ => {
        simp at ih₆
        cases v₄ with
        | vZ => {
          simp at ih₃ ih₆
          apply Eval.EvalProp.Rel
          exact ih₂
          exact ih₅
          unfold Eval.evalRelOp
          simp
          rw[← ih₃, ← ih₆]
        }
        | _ => simp at ih₆
      }
      | _ => simp at ih₃
    }
    | vBool => {
      cases v₂ with
      | vBool => {
        simp at ih₆
        cases v₄ with
        | vBool => {
          simp at ih₃ ih₆
          apply Eval.EvalProp.Rel
          exact ih₂
          exact ih₅
          unfold Eval.evalRelOp
          simp
          rw[← ih₃, ← ih₆]
        }
        | _ => simp at ih₆
      }
      | _ => simp at ih₃
    }
    | _ => simp_all
  }

theorem ne_symm' {α} {a b : α} (h : a ≠ b) : b ≠ a :=
by
  simpa [eq_comm] using h

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

theorem varToProp_pointwise_preserve (σ: Env.ValEnv) (Δ: Env.ChipEnv) (Γ₁ Γ₂: Env.TyEnv) (ident: String)
  (h₁: ∀ x, Env.lookupTy Γ₁ x = Env.lookupTy Γ₂ x) (h₂: PropSemantics.varToProp σ Δ Γ₁ ident):
  PropSemantics.varToProp σ Δ Γ₂ ident := by {
    unfold PropSemantics.varToProp at h₂ ⊢
    have h₁' := h₁ ident
    rw[← h₁']
    exact h₂
  }

theorem tyenvToProp_pointwise_preserve (σ: Env.ValEnv) (Δ: Env.ChipEnv) (Γ₁ Γ₂: Env.TyEnv)
  (h₁: ∀ x, Env.lookupTy Γ₁ x = Env.lookupTy Γ₂ x) (h₂: PropSemantics.tyenvToProp σ Δ Γ₁):
  PropSemantics.tyenvToProp σ Δ Γ₂ := by {
    unfold PropSemantics.tyenvToProp at h₂ ⊢
    intro x τ h₃
    have h₄ := h₁ x
    rw[← h₄] at h₃
    have h₅ := h₂ x τ h₃
    exact varToProp_pointwise_preserve σ Δ Γ₁ Γ₂ x h₁ h₅
  }

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
        intro σ e h₂
        apply ih₁
        exact tyenvToProp_pointwise_preserve σ Δ Γ₂ Γ₁ (lookupTy_pointwise_symm Γ₁ Γ₂ h) h₂
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
    | TE_App h₂ _ ih₁ ih₂ =>
      intro Γ₂ h
      apply Ty.TypeJudgment.TE_App
      apply ih₁
      exact h
      apply ih₂
      exact h
       --(ih₁ Γ₂ h) h₂ (ih₂ Γ₂ h)
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

lemma mem_update_preserve (Γ: Env.TyEnv) (x x': String) (τ τ': Ty) (h: (x, τ) ∈ Γ):
  (x, τ) ∈ (Env.updateTy Γ x' τ') := by
  unfold Env.updateTy
  by_cases hx : (Γ.find? (fun p => p.1 = x')).isSome
  · simp_all
  · simp [h]

lemma isZero_eval_eq_branch_semantics {x y inv: Expr} {σ: Env.ValEnv} {Δ: Env.ChipEnv}
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

lemma isZero_typing_soundness (Δ: Env.ChipEnv) (Η: Env.UsedNames) (Γ: Env.TyEnv) (φ₁ φ₂ φ₃: Ast.Predicate)
  (x y inv u₁ u₂: String)
  (htx: Env.lookupTy Γ x = (Ty.refin Ast.Ty.field φ₁))
  (hty: Env.lookupTy Γ y = (Ty.refin Ast.Ty.field φ₂))
  (htinv: @Ty.TypeJudgment Δ Γ Η (.var inv) (Ty.refin Ast.Ty.field φ₃))
  (hne₁: ¬ x = u₁)
  (hne₂: ¬ y = u₁)
  (hne₃: ¬ u₁ = u₂):
  @Ty.TypeJudgment Δ Γ Η
    (Ast.Expr.letIn u₁ (.assertE (.var y) (.fieldExpr (.fieldExpr (.fieldExpr (.constF 0) .sub (.var x)) .mul (.var inv)) (.add) (.constF 1)))
      (Ast.Expr.letIn u₂ (.assertE (.fieldExpr (.var x) .mul (.var y)) (.constF 0)) (.var u₂)))
    (Ty.refin Ast.Ty.unit (Ast.Predicate.ind (exprEq (.var y) (.branch (.binRel (.var x) (.eq) (.constF 0)) (.constF 1) (.constF 0))))) := by {
    apply Ty.TypeJudgment.TE_LetIn; apply lookup_update_self;
    apply Ty.TypeJudgment.TE_Assert; apply Ty.TypeJudgment.TE_VarEnv; exact hty
    repeat apply Ty.TypeJudgment.TE_BinOpField
    apply Ty.TypeJudgment.TE_ConstF; apply Ty.TypeJudgment.TE_VarEnv; exact htx; exact htinv
    apply Ty.TypeJudgment.TE_ConstF; apply Ty.TypeJudgment.TE_LetIn; apply lookup_update_self
    apply Ty.TypeJudgment.TE_Assert; apply Ty.TypeJudgment.TE_BinOpField; apply Ty.TypeJudgment.TE_VarEnv
    rw[← htx]; apply lookup_update_ne; exact hne₁
    apply Ty.TypeJudgment.TE_VarEnv
    rw[← hty]; apply lookup_update_ne; exact hne₂
    apply Ty.TypeJudgment.TE_ConstF
    have h_sub : @Ty.SubtypeJudgment Δ (Env.updateTy
      (Env.updateTy Γ u₁
        (Ty.unit.refin
          (Ast.Predicate.ind
            (exprEq (Expr.var y)
              ((((Expr.constF 0).fieldExpr FieldOp.sub (.var x)).fieldExpr FieldOp.mul (Expr.var inv)).fieldExpr FieldOp.add
                (Expr.constF 1))))))
      u₂ (Ty.unit.refin (Ast.Predicate.ind (exprEq ((Expr.var x).fieldExpr FieldOp.mul (Expr.var y)) (Expr.constF 0)))))
      (Ty.unit.refin (Ast.Predicate.ind (exprEq ((Expr.var x).fieldExpr FieldOp.mul (Expr.var y)) (Expr.constF 0))))
      (Ty.unit.refin
        (Ast.Predicate.ind (exprEq (Expr.var y) (((Expr.var x).binRel RelOp.eq (Expr.constF 0)).branch (Expr.constF 1) (Expr.constF 0))))) := by {
        apply Ty.SubtypeJudgment.TSub_Refine
        apply Ty.SubtypeJudgment.TSub_Refl
        unfold PropSemantics.tyenvToProp PropSemantics.predToProp PropSemantics.exprToProp PropSemantics.varToProp
        intro σ e h₂
        set φ₁ := (Ast.Predicate.ind
          (exprEq (Expr.var y)
            ((((Expr.constF 0).fieldExpr FieldOp.sub (Expr.var x)).fieldExpr FieldOp.mul (Expr.var inv)).fieldExpr FieldOp.add
              (Expr.constF 1))))
        set φ₂ := (Ast.Predicate.ind (exprEq ((Expr.var x).fieldExpr FieldOp.mul (Expr.var y)) (Expr.constF 0)))
        have h₃ := h₂ u₁ (Ty.unit.refin φ₁)
        have h₄: Env.lookupTy (Env.updateTy (Env.updateTy Γ u₁ (Ty.unit.refin φ₁)) u₂ (Ty.unit.refin φ₂)) u₁ = (Ty.unit.refin φ₁) := by {
          apply lookup_update_ne_of_lookup
          exact hne₃
          apply lookup_update_self
        }
        have h₅ := h₃ h₄
        rw[h₄] at h₅
        simp at h₅
        unfold PropSemantics.predToProp PropSemantics.exprToProp at h₅
        intro h₁
        apply isZero_eval_eq_branch_semantics h₅ h₁
        repeat apply Eval.EvalProp.Var; rfl
      }
    apply Ty.TypeJudgment.TE_SUB
    apply Ty.TypeJudgment.TE_VarEnv
    apply lookup_update_self
    exact h_sub
}

abbrev bit_value_type (ident: String): Ast.Ty := (Ast.Ty.unit.refin
                                                  (Ast.Predicate.ind
                                                    (Ast.exprEq
                                                      ((Ast.Expr.var ident).fieldExpr Ast.FieldOp.mul
                                                        ((Ast.Expr.var ident).fieldExpr
                                                          Ast.FieldOp.sub (Ast.Expr.constF 1)))
                                                      (Ast.Expr.constF 0))))

abbrev bits_to_byte_expr (i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇: String) : Ast.Expr :=
                                      ((((((((Ast.Expr.var i₀).fieldExpr Ast.FieldOp.add
                                                                ((Ast.Expr.var i₁).fieldExpr
                                                                  Ast.FieldOp.mul (Ast.Expr.constF 2))).fieldExpr
                                                            Ast.FieldOp.add
                                                            ((Ast.Expr.var i₂).fieldExpr
                                                              Ast.FieldOp.mul (Ast.Expr.constF 4))).fieldExpr
                                                        Ast.FieldOp.add
                                                        ((Ast.Expr.var i₃).fieldExpr
                                                          Ast.FieldOp.mul (Ast.Expr.constF 8))).fieldExpr
                                                    Ast.FieldOp.add
                                                    ((Ast.Expr.var i₄).fieldExpr Ast.FieldOp.mul
                                                      (Ast.Expr.constF 16))).fieldExpr
                                                Ast.FieldOp.add
                                                ((Ast.Expr.var i₅).fieldExpr Ast.FieldOp.mul
                                                  (Ast.Expr.constF 32))).fieldExpr
                                            Ast.FieldOp.add
                                            ((Ast.Expr.var i₆).fieldExpr Ast.FieldOp.mul
                                              (Ast.Expr.constF 64))).fieldExpr
                                        Ast.FieldOp.add
                                        ((Ast.Expr.var i₇).fieldExpr Ast.FieldOp.mul
                                          (Ast.Expr.constF 128)))
abbrev eq_mul_refinement (i₁ i₂ i₃: String): Ast.Ty := Ast.Ty.unit.refin
                        (Ast.Predicate.ind
                          (Ast.exprEq (Ast.Expr.var i₁)
                            ((Ast.Expr.var i₂).fieldExpr Ast.FieldOp.mul
                              (Ast.Expr.var i₃))))

lemma bit_value_0_or_1 {x: F} (h: x * (x - 1) = 0): x = 0 ∨ x = 1 := by {
  simp_all
  rcases h with h_case | h_case
  {
    left
    exact h_case
  }
  {
    right
    apply sub_eq_iff_eq_add.mp h_case
  }
}

lemma bit_value_mul_zero {x: F} (h: x = 0 ∨ x - 1 = 0): x * (x - 1) = 0 := by {
  simp_all
  /-
  rcases h with h_case | h_case
  {
    left
    exact h_case
  }
  {
    right
    simp_all
  }
  -/
}


lemma bit_val_to_nat {x: F} (h: x = 0 ∨ x = 1) : x.val = 0 ∨ x.val = 1 := by {
  rcases h with h_case | h_case
  {
    left
    simp
    exact h_case
  }
  {
    right
    rw[h_case]
    rfl
  }
}

lemma bit_le_one {x: ℕ} (h: x = 0 ∨ x = 1): x ≤ 1 := by {
  cases h
  {
    rename_i h
    rw[h]
    simp
  }
  {
    rename_i h
    rw[h]
  }
}

lemma binary_mul_binary_nat {x y z: ℕ} (h₁: x = 0 ∨ x = 1) (h₂: y = 0 ∨ y = 1) (h₃: z = x * y): z = 0 ∨ z = 1 := by {
  cases h₁
  cases h₂
  simp_all
  simp_all
  simp_all
}

lemma binary_mul_binary_F {x y z: F} (h₁: x = 0 ∨ x = 1) (h₂: y = 0 ∨ y = 1) (h₃: z = x * y): z = 0 ∨ z = 1 := by {
  cases h₁
  cases h₂
  simp_all
  simp_all
  simp_all
}

lemma word_range_val_bound
  {value_0 value_1 value_2 value_3 most_sig_byte_decomp_0
   most_sig_byte_decomp_1 most_sig_byte_decomp_2 most_sig_byte_decomp_3
   most_sig_byte_decomp_4 most_sig_byte_decomp_5 most_sig_byte_decomp_6 most_sig_byte_decomp_7
   and_most_sig_byte_decomp_0_to_2 and_most_sig_byte_decomp_0_to_3 and_most_sig_byte_decomp_0_to_4
   and_most_sig_byte_decomp_0_to_5 and_most_sig_byte_decomp_0_to_6 and_most_sig_byte_decomp_0_to_7: F}
  (h₀: most_sig_byte_decomp_0 * (most_sig_byte_decomp_0 - 1) = 0)
  (h₁: most_sig_byte_decomp_1 * (most_sig_byte_decomp_1 - 1) = 0)
  (h₂: most_sig_byte_decomp_2 * (most_sig_byte_decomp_2 - 1) = 0)
  (h₃: most_sig_byte_decomp_3 * (most_sig_byte_decomp_3 - 1) = 0)
  (h₄: most_sig_byte_decomp_4 * (most_sig_byte_decomp_4 - 1) = 0)
  (h₅: most_sig_byte_decomp_5 * (most_sig_byte_decomp_5 - 1) = 0)
  (h₆: most_sig_byte_decomp_6 * (most_sig_byte_decomp_6 - 1) = 0)
  (h₇: most_sig_byte_decomp_7 * (most_sig_byte_decomp_7 - 1) = 0)
  (h₉: most_sig_byte_decomp_0 + most_sig_byte_decomp_1 * 2 + most_sig_byte_decomp_2 * 4 + most_sig_byte_decomp_3 * 8 + most_sig_byte_decomp_4 * 16 + most_sig_byte_decomp_5 * 32 + most_sig_byte_decomp_6 * 64 + most_sig_byte_decomp_7 * 128 = value_3)
  (h₁₀: most_sig_byte_decomp_7 = 0)
  (h₁₁: and_most_sig_byte_decomp_0_to_2 = most_sig_byte_decomp_0 * most_sig_byte_decomp_1)
  (h₁₂: and_most_sig_byte_decomp_0_to_3 = and_most_sig_byte_decomp_0_to_2 * most_sig_byte_decomp_2)
  (h₁₃: and_most_sig_byte_decomp_0_to_4 = and_most_sig_byte_decomp_0_to_3 * most_sig_byte_decomp_3)
  (h₁₄: and_most_sig_byte_decomp_0_to_5 = and_most_sig_byte_decomp_0_to_4 * most_sig_byte_decomp_4)
  (h₁₅: and_most_sig_byte_decomp_0_to_6 = and_most_sig_byte_decomp_0_to_5 * most_sig_byte_decomp_5)
  (h₁₆: and_most_sig_byte_decomp_0_to_7 = and_most_sig_byte_decomp_0_to_6 * most_sig_byte_decomp_6)
  (h₁₇: and_most_sig_byte_decomp_0_to_7 * value_0 = 0)
  (h₁₈: and_most_sig_byte_decomp_0_to_7 * value_1 = 0)
  (h₁₉: and_most_sig_byte_decomp_0_to_7 * value_2 = 0)
  (h₂₀: value_0.val < 256)
  (h₂₁: value_1.val < 256)
  (h₂₂: value_2.val < 256)
  (h₂₃: value_3.val < 256)
  : value_0.val + value_1.val * 256 + value_2.val * (256 ^ 2) + value_3.val * (256 ^ 3) < 2130706433 := by {
  -- 1) each decomposed bit is 0 or 1
  have b0 : most_sig_byte_decomp_0 = 0 ∨ most_sig_byte_decomp_0 = 1 := bit_value_0_or_1 h₀
  have b1 : most_sig_byte_decomp_1 = 0 ∨ most_sig_byte_decomp_1 = 1 := bit_value_0_or_1 h₁
  have b2 : most_sig_byte_decomp_2 = 0 ∨ most_sig_byte_decomp_2 = 1 := bit_value_0_or_1 h₂
  have b3 : most_sig_byte_decomp_3 = 0 ∨ most_sig_byte_decomp_3 = 1 := bit_value_0_or_1 h₃
  have b4 : most_sig_byte_decomp_4 = 0 ∨ most_sig_byte_decomp_4 = 1 := bit_value_0_or_1 h₄
  have b5 : most_sig_byte_decomp_5 = 0 ∨ most_sig_byte_decomp_5 = 1 := bit_value_0_or_1 h₅
  have b6 : most_sig_byte_decomp_6 = 0 ∨ most_sig_byte_decomp_6 = 1 := bit_value_0_or_1 h₆
  have b7 : most_sig_byte_decomp_7 = 0 ∨ most_sig_byte_decomp_7 = 1 := bit_value_0_or_1 h₇
  -- 2) because bit7 = 0, value_3 ≤ 127
  have v3_le_127 : value_3.val ≤ 127 := by
    { -- value_3 = sum_{i=0..7} bit_i * 2^i and bit7 = 0 so upper bound is when bits0..6 = 1
      rw [← h₉, h₁₀]
      have : most_sig_byte_decomp_0.val + most_sig_byte_decomp_1.val * 2 + most_sig_byte_decomp_2.val * 4 + most_sig_byte_decomp_3.val * 8 +
            most_sig_byte_decomp_4.val * 16 + most_sig_byte_decomp_5.val * 32 + most_sig_byte_decomp_6.val * 64 ≤ 1 + 2 + 4 + 8 + 16 + 32 + 64 := by
      { have b0' : most_sig_byte_decomp_0.val ≤ 1 := bit_le_one (bit_val_to_nat b0)
        have b1' : most_sig_byte_decomp_1.val ≤ 1 := bit_le_one (bit_val_to_nat b1)
        have b2' : most_sig_byte_decomp_2.val ≤ 1 := bit_le_one (bit_val_to_nat b2)
        have b3' : most_sig_byte_decomp_3.val ≤ 1 := bit_le_one (bit_val_to_nat b3)
        have b4' : most_sig_byte_decomp_4.val ≤ 1 := bit_le_one (bit_val_to_nat b4)
        have b5' : most_sig_byte_decomp_5.val ≤ 1 := bit_le_one (bit_val_to_nat b5)
        have b6' : most_sig_byte_decomp_6.val ≤ 1 := bit_le_one (bit_val_to_nat b6)
        gcongr
        simp
        exact b1'
        simp
        exact b2'
        simp
        exact b3'
        simp
        exact b4'
        simp
        exact b5'
        simp
        exact b6'
      }
      simp at this ⊢
      simp [ZMod.val_add, ZMod.val_mul]
      rw [Nat.mod_eq_of_lt]
      exact this
      apply Nat.lt_trans
      exact Nat.lt_succ_of_le this
      unfold p
      simp
    }
  have c0 := binary_mul_binary_F b0 b1 h₁₁
  have c1 := binary_mul_binary_F c0 b2 h₁₂
  have c2 := binary_mul_binary_F c1 b3 h₁₃
  have c3 := binary_mul_binary_F c2 b4 h₁₄
  have c4 := binary_mul_binary_F c3 b5 h₁₅
  have c5 := bit_val_to_nat (binary_mul_binary_F c4 b6 h₁₆)
  cases c5
  {
    rename_i h
    have : value_3.val < 127 := by {
      by_contra hcontra
      have h_eq : ZMod.val value_3 = 127 := by
        apply le_antisymm v3_le_127
        exact Nat.le_of_not_lt hcontra
      have decomp :
          most_sig_byte_decomp_0 = 1 ∧
          most_sig_byte_decomp_1 = 1 ∧
          most_sig_byte_decomp_2 = 1 ∧
          most_sig_byte_decomp_3 = 1 ∧
          most_sig_byte_decomp_4 = 1 ∧
          most_sig_byte_decomp_5 = 1 ∧
          most_sig_byte_decomp_6 = 1 := by {
          rw[h₁₀] at h₉
          rcases b0 with (rfl | rfl) <;>
          rcases b1 with (rfl | rfl) <;>
          rcases b2 with (rfl | rfl) <;>
          rcases b3 with (rfl | rfl) <;>
          rcases b4 with (rfl | rfl) <;>
          rcases b5 with (rfl | rfl) <;>
          rcases b6 with (rfl | rfl)
          all_goals
            simp at h₉
            rw[← h₉] at h_eq
            try contradiction
          simp
        }
      rcases decomp with ⟨d0, d1, d2, d3, d4, d5, d6⟩
      simp_all
    }
    calc
      value_0.val + value_1.val * 256 + value_2.val * 256^2 + value_3.val * 256^3
          ≤ 255 + 255*256 + 255*256^2 + 126*256^3 := by
            apply Nat.add_le_add
            apply Nat.add_le_add
            apply Nat.add_le_add
            · exact Nat.lt_succ_iff.mp h₂₀
            · rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (Nat.lt_succ_iff.mp h₂₁)
            · rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (Nat.lt_succ_iff.mp h₂₂)
            · {
              have h_le : value_3.val ≤ 126 := Nat.lt_succ_iff.mp this
              rw [Nat.mul_comm]
              exact Nat.mul_le_mul_left _ h_le
            }
      _ = 2130706431 := by simp
      _ < 2130706433 := by simp
  }
  {
    rename_i h
    have : and_most_sig_byte_decomp_0_to_7 = 1 := by {
      rw[← ZMod.val_one'] at h
      apply ZMod.val_injective
      exact h
    }
    rw[this] at h₁₇ h₁₈ h₁₉
    simp at h₁₇ h₁₈ h₁₉
    rw[h₁₇, h₁₈, h₁₉]
    simp
    rw [Nat.mul_comm]
    calc
      16777216 * value_3.val ≤ 16777216 * 127 := Nat.mul_le_mul_left 16777216 v3_le_127
      _ < 127 * 16777216 + 1 := by norm_num
  }
}

lemma eval_eq_then_lt {σ Δ e₁ e₂ e₃}
  (h₁: Eval.EvalProp σ Δ (Ast.exprEq e₁ e₂) (Ast.Value.vBool true))
  (h₂: Eval.EvalProp σ Δ (Ast.Expr.binRel (Ast.Expr.toZ e₂) Ast.RelOp.lt e₃) (Ast.Value.vBool true))
  : Eval.EvalProp σ Δ (Ast.Expr.binRel (Ast.Expr.toZ e₁) Ast.RelOp.lt e₃) (Ast.Value.vBool true) := by {
    cases h₂
    rename_i ih₁ ih₂ r
    cases ih₁
    rename_i h
    cases h₁
    rename_i ih₁ ih₂ r
    have hv := evalprop_deterministic h ih₂
    rename_i ev₃ hev₃ v₂ hlt ev₁ ev₂
    unfold Eval.evalRelOp at hlt
    simp at hlt
    cases ev₃ with
    | vZ v₃ => {
      simp at hlt
      rw[← hv] at r
      unfold Eval.evalRelOp at r
      simp at r
      cases ev₁ with
      | vF v₁ => {
        simp at r
        apply Eval.EvalProp.Rel
        apply Eval.EvalProp.toZ
        exact ih₁
        exact hev₃
        unfold Eval.evalRelOp
        simp
        rw[r]
        exact hlt
      }
      | _ => simp at r
    }
    | _ => simp at hlt
  }

lemma eval_mul_expr_val {σ x y z Δ} (h: Eval.EvalProp σ Δ
  (Ast.exprEq (Ast.Expr.var x)
    ((Ast.Expr.var y).fieldExpr Ast.FieldOp.mul (Ast.Expr.var z)))
  (Ast.Value.vBool true)) :
  ∃ v₁ v₂ v₃: F, Env.lookupVal σ x = some (Ast.Value.vF v₁) ∧
                 Env.lookupVal σ y = some (Ast.Value.vF v₂) ∧
                 Env.lookupVal σ z = some (Ast.Value.vF v₃) ∧
                 (v₁ = v₂ * v₃) := by {
    cases h
    rename_i v₁ v₂ ih₁ ih₂ r₂
    cases ih₁
    cases ih₂
    rename_i v₃ v₄ ih₁ ih₂ r₂'
    cases ih₁
    cases ih₂
    cases r₂'
    simp at r₂
    cases v₁ with
    | vF vf₁ => {
      simp at r₂
      use vf₁
      use v₃
      use v₄
      apply And.intro
      simp_all
      apply And.intro
      simp_all
      apply And.intro
      simp_all
      exact r₂
    }
    | _ => simp at r₂
                 }

lemma eval_bit_expr_val {σ Δ x} (h: Eval.EvalProp σ Δ
  (Ast.exprEq
    ((Ast.Expr.var x).fieldExpr Ast.FieldOp.mul
      ((Ast.Expr.var x).fieldExpr Ast.FieldOp.sub (Ast.Expr.constF 1)))
    (Ast.Expr.constF 0))
  (Ast.Value.vBool true)) : ∃ v: F, Env.lookupVal σ x = some (Ast.Value.vF v) ∧ (v = 0 ∨ v - 1 = 0) := by {
    cases h
    rename_i ih₁ ih₂ r₁;
    cases ih₁;
    rename_i ih₃ ih₄ r₂;
    cases ih₂;
    cases ih₃;
    cases ih₄;
    rename_i ih₁ ih₂ r₂;
    cases ih₁;
    cases ih₂;
    cases r₂;
    simp at r₂;
    unfold Eval.evalRelOp at r₁;
    simp at r₁;
    rw [← r₂] at r₁;
    simp at r₁;
    rename_i v₁ vf₁ h₁ vf₂ h₂
    use vf₁
    have h_eq : vf₁ = vf₂ := by {
      rw[h₂] at h₁
      simp_all
    }
    rw [← h_eq] at r₁
    apply And.intro
    simp_all
    exact r₁
  }

lemma eval_eq_const_mul_val {σ Δ x y v} (h: Eval.EvalProp σ Δ
  (Ast.exprEq (Ast.Expr.constF v)
    ((Ast.Expr.var x).fieldExpr Ast.FieldOp.mul (Ast.Expr.var y)))
  (Ast.Value.vBool true)):
  ∃ v₀ v₁: F,
  Env.lookupVal σ x = some (Ast.Value.vF v₀) ∧ Env.lookupVal σ y = some (Ast.Value.vF v₁) ∧
  v = v₀ * v₁ := by {
    cases h
    rename_i v₈ u₈ ih₁ ih₂ r₈
    cases ih₁
    cases ih₂
    rename_i v₈' u₈' ih₁ ih₂ r₈'
    cases ih₁
    cases ih₂
    unfold Eval.evalFieldOp at r₈'
    simp at r₈'
    unfold Eval.evalRelOp at r₈
    cases u₈ <;> simp at r₈
    use v₈'
    use u₈'
    simp_all
  }

lemma eval_bits_to_byte_expr_val {σ Δ x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈} (h: Eval.EvalProp σ Δ
  (Ast.exprEq
    (bits_to_byte_expr x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇)
    (Ast.Expr.var x₈))
  (Ast.Value.vBool true)) : ∃ v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈: F,
    Env.lookupVal σ x₀ = some (Ast.Value.vF v₀) ∧ Env.lookupVal σ x₁ = some (Ast.Value.vF v₁) ∧
    Env.lookupVal σ x₂ = some (Ast.Value.vF v₂) ∧ Env.lookupVal σ x₃ = some (Ast.Value.vF v₃) ∧
    Env.lookupVal σ x₄ = some (Ast.Value.vF v₄) ∧ Env.lookupVal σ x₅ = some (Ast.Value.vF v₅) ∧
    Env.lookupVal σ x₆ = some (Ast.Value.vF v₆) ∧ Env.lookupVal σ x₇ = some (Ast.Value.vF v₇) ∧
    Env.lookupVal σ x₈ = some (Ast.Value.vF v₈) ∧
    v₀ + v₁ * 2 + v₂ * 4 + v₃ * 8 + v₄ * 16 + v₅ * 32 + v₆ * 64 + v₇ * 128 = v₈ := by {
    cases h
    rename_i ih₁ ih₂ r₁
    cases ih₁
    rename_i ih₃ ih₄ r₂
    cases ih₂
    cases ih₃
    rename_i ih₇ ih₈ r₄
    cases ih₄
    rename_i ih₉ ih₁₀ r₅
    cases ih₇
    rename_i ih₁₃ ih₁₄ r₇
    cases ih₈
    rename_i ih₁₅ ih₁₆ r₈
    cases ih₉
    cases ih₁₀
    cases ih₁₃
    rename_i ih₁₇ ih₁₈ r₉
    cases ih₁₄
    rename_i ih₁₉ ih₂₀ r₁₀
    cases ih₁₅
    cases ih₁₆
    cases ih₁₇
    rename_i ih₂₁ ih₂₂ r₁₁
    cases ih₁₈
    rename_i ih₂₂ ih₂₃ r₁₂
    cases ih₁₉
    cases ih₂₀
    cases ih₂₁
    rename_i ih₂₄ ih₂₅ r₁₃
    cases ih₂₂
    cases ih₂₃
    cases ih₂₄
    rename_i ih₂₅ ih₂₆ r₁₄
    cases ih₂₅
    cases ih₂₆
    rename_i ih₂₇ ih₂₈ r₁₅
    cases ih₂₇
    cases ih₂₈
    cases ih₂₂
    rename_i ih₂₉ ih₃₀ r₁₆
    cases ih₂₉
    cases ih₃₀
    cases ih₂₅
    rename_i ih₃₁ ih₃₂ r₁₇
    cases ih₃₁
    cases ih₃₂
    unfold Eval.evalFieldOp at r₂ r₄ r₅ r₇ r₈ r₉ r₁₀ r₁₁ r₁₂ r₁₃ r₁₄ r₁₅
    simp at r₂ r₄ r₅ r₇ r₈ r₉ r₁₀ r₁₁ r₁₂ r₁₃ r₁₄ r₁₅ r₁₆ r₁₇
    rw[← r₁₅] at r₁₄
    rw[← r₁₄] at r₁₃
    rw[← r₁₃] at r₁₁
    rw[← r₁₂] at r₉
    rw[← r₁₁] at r₉
    rw[← r₁₀] at r₇
    rw[← r₉] at r₇
    rw[← r₈] at r₄
    rw[← r₇] at r₄
    rw[← r₁₆] at r₄
    rw[← r₅] at r₂
    rw[← r₄] at r₂
    rw[← r₁₇] at r₂
    rename_i e₀ v₀ fff₀ fff₁ v₂ ff₀ ff₁ ff₂ ff₃ ff₄ ff₅ h₀ f₀ f₁ f₂ h₁ f₃ f₄ f₅ h₂ f₆ f₇ h₃ f₈ f₉ h₄ f₁₀ h₅ f₁₁ h₆ f₁₂ h₇
    unfold Eval.evalRelOp at r₁
    rw[← r₂] at r₁
    cases v₀ <;> simp at r₁;
    rename_i v₉
    use f₈
    use f₁₀
    use f₁₂
    use f₁₁
    use f₅
    use f₂
    use ff₅
    use ff₂
    use v₉
    simp_all
  }

lemma tyenv_to_eval_expr {σ Δ Γ x e} (h₁: PropSemantics.tyenvToProp σ Δ Γ) (h₂: Env.lookupTy Γ x = some (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind e))):
  (Eval.EvalProp σ Δ e (Ast.Value.vBool true)) := by {
    unfold PropSemantics.tyenvToProp PropSemantics.varToProp PropSemantics.predToProp at h₁
    have h₁' := h₁ x (Ast.Ty.unit.refin (Ast.Predicate.ind e)) h₂
    rw[h₂] at h₁'
    simp at h₁'
    unfold PropSemantics.exprToProp at h₁'
    exact h₁'
  }

lemma tyenv_and_to_eval_exprs {σ Δ Γ x e₁ e₂} (h₁: PropSemantics.tyenvToProp σ Δ Γ) (h₂: Env.lookupTy Γ x = some (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.and (Ast.Predicate.ind e₁) (Ast.Predicate.ind e₂)))):
  (Eval.EvalProp σ Δ e₁ (Ast.Value.vBool true)) ∧ (Eval.EvalProp σ Δ e₂ (Ast.Value.vBool true)) := by {
    unfold PropSemantics.tyenvToProp PropSemantics.varToProp PropSemantics.predToProp at h₁
    have h₁' := h₁ x (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.and (Ast.Predicate.ind e₁) (Ast.Predicate.ind e₂))) h₂
    rw[h₂] at h₁'
    simp at h₁'
    unfold PropSemantics.predToProp PropSemantics.exprToProp at h₁'
    exact h₁'
  }

lemma eval_lt_val {σ Δ x t} (h: Eval.EvalProp σ Δ ((Ast.Expr.var x).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ t)) (Ast.Value.vBool true)):
  ∃ v : F, Env.lookupVal σ x = some (Ast.Value.vF v) ∧ v.val < t := by {
    cases h
    rename_i ih₀ ih₁ r₁
    cases ih₀
    rename_i ih₀
    cases ih₀
    cases ih₁
    unfold Eval.evalRelOp at r₁
    simp at r₁
    rename_i v h
    use v
    simp_all
  }

lemma constZ_refine_lt {Δ Γ Η x y} {h: x < y} :
  @Ty.TypeJudgment Δ Γ Η (Ast.Expr.constZ x) (Ast.Ty.int.refin (Ast.Predicate.dep "v" ((Ast.Expr.var "v").binRel Ast.RelOp.lt (Ast.Expr.constZ y)))) := by {
  apply Ty.TypeJudgment.TE_SUB
  apply Ty.TypeJudgment.TE_ConstZ
  apply Ty.SubtypeJudgment.TSub_Refine
  apply Ty.SubtypeJudgment.TSub_Refl
  intro σ v h₁ h₂
  unfold PropSemantics.predToProp PropSemantics.exprToProp at h₂ ⊢
  cases h₂
  rename_i va ih₁ ih₂ ih₃
  cases ih₁
  cases ih₃
  rename_i v₁ v₂ ih₁ ih₃ r
  cases ih₃
  unfold Eval.evalRelOp at r
  cases v₁ <;> simp at r
  rw[r] at ih₁
  apply Eval.EvalProp.App
  apply Eval.EvalProp.Lam
  exact ih₂
  apply Eval.EvalProp.Rel
  exact ih₁
  apply Eval.EvalProp.ConstZ
  unfold Eval.evalRelOp
  simp
  exact h
}
