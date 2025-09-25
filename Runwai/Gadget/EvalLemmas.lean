import Runwai.Typing
import Runwai.Gadget.Abbrev
import Runwai.Gadget.Utils

open Ast

/--
The equality operator `Ast.RelOp.eq` is symmetric. If evaluating `v₁ = v₂`
yields `true`, then evaluating `v₂ = v₁` will also yield `true`.
-/
theorem evalRelOp_eq_symm {v₁ v₂: Ast.Value} (h: Eval.evalRelOp Ast.RelOp.eq v₁ v₂ = some true):
  Eval.evalRelOp Ast.RelOp.eq v₂ v₁ = some true := by {
    simp [Eval.evalRelOp] at h ⊢
    cases v₁
    cases v₂
    repeat simp_all
    cases v₂
    repeat simp_all
    cases v₂
    repeat simp_all
  }

/--
The symmetry of equality to the expression evaluation level. If the expression `e₁ = e₂`
evaluates to `true`, then the expression `e₂ = e₁` also evaluates to `true`. This relies on the
symmetry of the underlying `evalRelOp` function.
-/
theorem evalProp_eq_symm
  {σ: Env.ValEnv} {T: Env.TraceEnv} {Δ: Env.ChipEnv} {e₁ e₂: Expr} (h: Eval.EvalProp σ T Δ (Ast.Expr.binRel e₁ Ast.RelOp.eq e₂) (Ast.Value.vBool true)):
  Eval.EvalProp σ T Δ (Ast.Expr.binRel e₂ Ast.RelOp.eq e₁) (Ast.Value.vBool true) := by {
    cases h
    rename_i v₁ v₂ h₁ h₂ h₃
    apply evalRelOp_eq_symm at h₃
    apply Eval.EvalProp.Rel
    exact h₂
    exact h₁
    exact h₃
  }

/--
The `Eval.EvalProp` relation is deterministic. For any given expression `e`,
if it can be evaluated to a value `v₁` and also to a value `v₂`, then
`v₁` and `v₂` must be identical. This ensures that expression evaluation is a function.
-/
theorem evalprop_deterministic
  {σ : Env.ValEnv} {T: Env.TraceEnv} {Δ : Env.ChipEnv} {e : Expr} :
  ∀ {v₁ v₂}, Eval.EvalProp σ T Δ e v₁ → Eval.EvalProp σ T Δ e v₂ → v₁ = v₂ := by
  intro v₁ v₂ h₁ h₂
  induction h₁ generalizing v₂ with
  | ConstF => cases h₂; rfl
  | ConstN => cases h₂; rfl
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
  | Assert ih₁ ih₂ ih₁_ih ih₂_ih => {
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
    rename_i h_body h_chip h_trace h_callee_validity i vs h_bound h_args_len h_evals
             h_asserts h_body_ih h_callee_validity_ih h_evals_ih h_asserts_ih c' row'
             i' vs' h_bound' h_trace' h_callee_validity' h_chip' h_args_len' h_eval'
             h_asserts' h_body'
    apply h_body_ih h_body'
  }
  | Len => {
    cases h₂
    rename_i h h_ih vs h'
    have h := h_ih h'
    simp at h ⊢
    rw[h]
  }
  | toN => {
    cases h₂
    rename_i v₁ ih₀ ih₁ fv₂ ih₃
    have h := ih₁ ih₃
    have h' : v₁ = fv₂ := by simp_all
    simp_all
  }
  | toF => {
    cases h₂
    rename_i v₁ ih₀ ih₁ fv₂ ih₃
    have h := ih₁ ih₃
    have h' : v₁ = fv₂ := by simp_all
    simp_all
  }

/--
The transitivity of equality at the expression level. If `e₁ = e₂` evaluates to true
and `e₁ = e₃` evaluates to true, then `e₂ = e₃` must also evaluate to true. This relies on
the deterministic nature of the evaluator.
-/
theorem evalProp_eq_trans
  {σ: Env.ValEnv} {T: Env.TraceEnv} {Δ: Env.ChipEnv} {e₁ e₂ e₃: Expr}
  (h₁: Eval.EvalProp σ T Δ (Ast.Expr.binRel e₁ Ast.RelOp.eq e₂) (Ast.Value.vBool true))
  (h₂: Eval.EvalProp σ T Δ (Ast.Expr.binRel e₁ Ast.RelOp.eq e₃) (Ast.Value.vBool true)):
  Eval.EvalProp σ T Δ (Ast.Expr.binRel e₂ Ast.RelOp.eq e₃) (Ast.Value.vBool true) := by {
    cases h₁
    cases h₂
    rename_i v₁ v₂ ih₁ ih₂ ih₃ v₃ v₄ ih₄ ih₅ ih₆
    have h := evalprop_deterministic ih₁ ih₄
    rw[← h] at ih₆
    simp [Eval.evalRelOp] at ih₃ ih₆
    cases v₁ with
    | vF => {
      cases v₂ with
      | vF => {
        cases v₄ with
        | vF => {
          simp at ih₃ ih₆
          apply Eval.EvalProp.Rel
          exact ih₂
          exact ih₅
          simp [Eval.evalRelOp]
          rw[← ih₃, ← ih₆]
        }
        | _ => simp at ih₆
      }
      | _ => simp at ih₃
    }
    | vN => {
      cases v₂ with
      | vN => {
        cases v₄ with
        | vN => {
          simp at ih₃ ih₆
          apply Eval.EvalProp.Rel
          exact ih₂
          exact ih₅
          simp [Eval.evalRelOp]
          rw[← ih₃, ← ih₆]
        }
        | _ => simp at ih₆
      }
      | _ => simp at ih₃
    }
    | vBool => {
      cases v₂ with
      | vBool => {
        cases v₄ with
        | vBool => {
          simp at ih₃ ih₆
          apply Eval.EvalProp.Rel
          exact ih₂
          exact ih₅
          simp [Eval.evalRelOp]
          rw[← ih₃, ← ih₆]
        }
        | _ => simp at ih₆
      }
      | _ => simp at ih₃
    }
    | _ => simp_all
  }

/--
If `e₁` is proven to be equal to `e₂`, and a less-than relation involving `e₂` holds (i.e., `toN e₂ < e₃`),
then the same relation must also hold for `e₁` (i.e., `toN e₁ < e₃`).
-/
lemma eval_eq_then_lt {σ T Δ e₁ e₂ e₃}
  (h₁: Eval.EvalProp σ T Δ (Ast.exprEq e₁ e₂) (Ast.Value.vBool true))
  (h₂: Eval.EvalProp σ T Δ (Ast.Expr.binRel (Ast.Expr.toN e₂) Ast.RelOp.lt e₃) (Ast.Value.vBool true))
  : Eval.EvalProp σ T Δ (Ast.Expr.binRel (Ast.Expr.toN e₁) Ast.RelOp.lt e₃) (Ast.Value.vBool true) := by {
    cases h₂
    rename_i ih₁ ih₂ r
    cases ih₁
    rename_i h
    cases h₁
    rename_i ih₁ ih₂ r
    have hv := evalprop_deterministic h ih₂
    rename_i ev₃ hev₃ v₂ hlt ev₁ ev₂
    simp [Eval.evalRelOp] at hlt
    cases ev₃ with
    | vN v₃ => {
      simp at hlt
      rw[← hv] at r
      simp [Eval.evalRelOp] at r
      cases ev₁ with
      | vF v₁ => {
        simp at r
        apply Eval.EvalProp.Rel
        apply Eval.EvalProp.toN
        exact ih₁
        exact hev₃
        simp [Eval.evalRelOp]
        rw[r]
        exact hlt
      }
      | _ => simp at r
    }
    | _ => simp at hlt
  }

/--
Connection from the successful evaluation of a symbolic multiplication
expression `x = y * z` to the concrete values in the environment. It proves that if this
expression holds, then `x`, `y`, and `z` must be bound to field values `v₁`, `v₂`, `v₃`
in the environment `σ` such that `v₁ = v₂ * v₃`.
-/
lemma eval_mul_expr_val {σ T x y z Δ} (h: Eval.EvalProp σ T Δ
  (Ast.exprEq (Ast.Expr.var x)
    ((Ast.Expr.var y).fieldExpr Ast.FieldOp.mul (Ast.Expr.var z)))
  (Ast.Value.vBool true)) :
  ∃ v₁ v₂ v₃: F, Env.getVal σ x = some (Ast.Value.vF v₁) ∧
                 Env.getVal σ y = some (Ast.Value.vF v₂) ∧
                 Env.getVal σ z = some (Ast.Value.vF v₃) ∧
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

/--
If the expression `x * (x - 1) = 0` evaluates to true, it proves that the variable `x` must
be bound to a field value `v` in the environment `σ` that represents a bit (i.e., `v` is either 0 or 1).
-/
lemma eval_bit_expr_val {σ T Δ x} (h: Eval.EvalProp σ T Δ
  (Ast.exprEq
    ((Ast.Expr.var x).fieldExpr Ast.FieldOp.mul
      ((Ast.Expr.var x).fieldExpr Ast.FieldOp.sub (Ast.Expr.constF 1)))
    (Ast.Expr.constF 0))
  (Ast.Value.vBool true)) : ∃ v: F, Env.getVal σ x = some (Ast.Value.vF v) ∧ (v = 0 ∨ v - 1 = 0) := by {
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
    simp [Eval.evalRelOp] at r₁;
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

/--
If `constF v = x * y` evaluates to true, this proves that `x` and `y` must be bound to
field values `v₀` and `v₁` in the environment `σ` such that their product equals the constant `v`.
-/
lemma eval_eq_const_mul_val {σ T Δ x y v} (h: Eval.EvalProp σ T Δ
  (Ast.exprEq (Ast.Expr.constF v)
    ((Ast.Expr.var x).fieldExpr Ast.FieldOp.mul (Ast.Expr.var y)))
  (Ast.Value.vBool true)):
  ∃ v₀ v₁: F,
  Env.getVal σ x = some (Ast.Value.vF v₀) ∧ Env.getVal σ y = some (Ast.Value.vF v₁) ∧
  v = v₀ * v₁ := by {
    cases h
    rename_i v₈ u₈ ih₁ ih₂ r₈
    cases ih₁
    cases ih₂
    rename_i v₈' u₈' ih₁ ih₂ r₈'
    cases ih₁
    cases ih₂
    simp [Eval.evalFieldOp] at r₈'
    simp [Eval.evalRelOp] at r₈
    cases u₈ <;> simp at r₈
    use v₈'
    use u₈'
    simp_all
  }

lemma eval_bits_to_byte_expr_val {σ T Δ x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈} (h: Eval.EvalProp σ T Δ
  (Ast.exprEq
    (bits_to_byte_expr x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇)
    (Ast.Expr.var x₈))
  (Ast.Value.vBool true)) : ∃ v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈: F,
    Env.getVal σ x₀ = some (Ast.Value.vF v₀) ∧ Env.getVal σ x₁ = some (Ast.Value.vF v₁) ∧
    Env.getVal σ x₂ = some (Ast.Value.vF v₂) ∧ Env.getVal σ x₃ = some (Ast.Value.vF v₃) ∧
    Env.getVal σ x₄ = some (Ast.Value.vF v₄) ∧ Env.getVal σ x₅ = some (Ast.Value.vF v₅) ∧
    Env.getVal σ x₆ = some (Ast.Value.vF v₆) ∧ Env.getVal σ x₇ = some (Ast.Value.vF v₇) ∧
    Env.getVal σ x₈ = some (Ast.Value.vF v₈) ∧
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
    simp [Eval.evalFieldOp] at r₂ r₄ r₅ r₇ r₈ r₉ r₁₀ r₁₁ r₁₂ r₁₃ r₁₄ r₁₅ r₁₆ r₁₇
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
    simp [Eval.evalRelOp] at r₁
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

/--
If the expression `toN x < constN t` evaluates to true, it proves that the variable `x` is bound
to a field value `v` in the environment `σ`, and that the numeric representation of `v` is less
than the constant `t`.
-/
lemma eval_lt_val {σ T Δ x t} (h: Eval.EvalProp σ T Δ ((Ast.Expr.var x).toN.binRel Ast.RelOp.lt (Ast.Expr.constN t)) (Ast.Value.vBool true)):
  ∃ v : F, Env.getVal σ x = some (Ast.Value.vF v) ∧ v.val < t := by {
    cases h
    rename_i ih₀ ih₁ r₁
    cases ih₀
    rename_i ih₀
    cases ih₀
    cases ih₁
    simp [Eval.evalRelOp] at r₁
    rename_i v h
    use v
    simp_all
  }

lemma eval_lt_lam_val {σ T Δ x t}
  (h: Eval.EvalProp σ T Δ
  ((Expr.lam Ast.nu Ty.field ((Expr.var Ast.nu).toN.binRel RelOp.lt (Expr.constN t))).app (Expr.var x))
  (Value.vBool true)):
  ∃ v : F, Env.getVal σ x = some (Ast.Value.vF v) ∧ v.val < t := by {
    cases h
    rename_i ih₀ ih₁ r₁
    cases ih₀
    cases ih₁
    rename_i r₂
    rw[← r₂] at r₁
    cases r₁
    rename_i ih₀ ih₁ r₁
    cases ih₀
    rename_i ih₂
    cases ih₁
    cases ih₂
    rename_i r₃
    simp [Eval.evalRelOp] at r₁
    rename_i v
    use v
    apply And.intro
    unfold Env.getVal Env.updateVal at r₃
    simp at r₃
    simp [Env.getVal]
    exact r₃
    exact r₁
  }

/-
Eval.EvalProp σ T Δ (Ast.exprEq (Ast.Expr.var "i") (Ast.Expr.constN k)) (Ast.Value.vBool true)
-/
lemma eval_var_eq_int (h: Eval.EvalProp σ T Δ (Ast.exprEq (Ast.Expr.var x) (Ast.Expr.constN k)) (Ast.Value.vBool true)):
  Env.getVal σ x = (Ast.Value.vN k) := by {
      cases h
      rename_i ih₁ ih₂ r
      cases ih₂
      cases ih₁
      rename_i v' i_is_k
      cases v' with
      | vN i_val => {
        simp[Eval.evalRelOp] at r
        rw[r] at i_is_k
        exact i_is_k
      }
      | _ => {
        simp at r
      }
  }

/-
Eval.EvalProp σ T Δ
  ((Ast.Expr.lam Ast.nu Ast.Ty.uint (Ast.exprEq (Ast.Expr.var Ast.nu) (Ast.Expr.constN height))).app (Ast.Expr.var "n"))
  (Ast.Value.vBool true)
-/
lemma eval_app_lam_eq_int (h: Eval.EvalProp σ T Δ
  ((Ast.Expr.lam x Ast.Ty.uint (Ast.exprEq (Ast.Expr.var x) (Ast.Expr.constN v))).app (Ast.Expr.var y))
  (Ast.Value.vBool true)):
  Env.getVal σ y = (Ast.Value.vN v) := by {
    cases h
    rename_i ih_f ih_a ih_b
    cases ih_f
    cases ih_a
    rename_i va' a
    cases ih_b
    rename_i ih₁ ih₂ r
    cases ih₂
    cases ih₁
    rename_i v₁' a
    unfold Env.getVal Env.updateVal at a
    simp at a
    cases v₁' with
    | vN x => {
      simp[Eval.evalRelOp] at r
      rw[r] at a
      rename_i n_is_height
      rw[a] at n_is_height
      exact n_is_height
    }
    |_ => {
      simp at r
    }
  }

lemma eval_height_check (h: Eval.EvalProp σ T Δ
  ((Ast.Expr.lam Ast.nu
        ((((Ast.Ty.field.refin (Ast.Predicate.ind (Ast.Expr.constBool true))).arr 1).refin
              (Ast.Predicate.ind (Ast.Expr.constBool true))).arr
          height)
        (Ast.exprEq (Ast.Expr.var Ast.nu).len (Ast.Expr.constN height))).app
    (Ast.Expr.var trace))
  (Ast.Value.vBool true)):
  ∃ trace_array: List Ast.Value, Env.getVal σ trace = some (Ast.Value.vArr trace_array) ∧
  trace_array.length = height := by {
  cases h
  rename_i ihf iha ihb
  cases ihf
  cases iha
  cases ihb
  rename_i ih₁ ih₂ trace_arr_length
  cases ih₂
  cases ih₁
  rename_i h
  cases h
  rename_i a
  unfold Env.getVal Env.updateVal at a
  simp at a
  rename_i h_trace trace_arr
  rw[a] at h_trace
  simp[Eval.evalRelOp] at trace_arr_length
  use trace_arr
  apply And.intro
  simp
  exact h_trace
  simp_all
}
