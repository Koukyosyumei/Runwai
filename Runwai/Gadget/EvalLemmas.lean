import Runwai.Typing
import Runwai.Gadget.Abbrev
import Runwai.Gadget.Utils

open Ast

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
