import Runwai.Typing
import Runwai.Gadget.Utils
import Runwai.Gadget.EnvLemmas

open Ast

/--
If a variable `x` is typed with a refinement `{_ : unit | e}` in a semantically valid
environment, this lemma provides a proof that the expression `e` will evaluate to `true`.
-/
lemma tyenv_to_eval_expr {σ T Δ Γ x τ e} (h₁: PropSemantics.tyenvToProp σ T Δ Γ) (h₂: Env.lookupTy Γ x = some (Ast.Ty.refin τ (Ast.Predicate.ind e))):
  (Eval.EvalProp σ T Δ e (Ast.Value.vBool true)) := by {
    unfold PropSemantics.tyenvToProp at h₁
    simp [PropSemantics.varToProp] at h₁
    have h₁' := h₁ x (Ast.Ty.refin τ (Ast.Predicate.ind e)) h₂
    rw[h₂] at h₁'
    simp at h₁'
    exact h₁'
  }

--  | Ast.Predicate.dep ident body => fun v => exprToProp σ Δ (Ast.Expr.app (Ast.Expr.lam ident τ body) v)
lemma tyenv_dep_to_eval_expr {σ T Δ Γ x τ body} (h₁: PropSemantics.tyenvToProp σ T Δ Γ) (h₂: Env.lookupTy Γ x = some (Ast.Ty.refin τ (Ast.Predicate.dep v body))):
  (Eval.EvalProp σ T Δ (Ast.Expr.app (Ast.Expr.lam v τ body) (Ast.Expr.var x)) (Ast.Value.vBool true)) := by {
    unfold PropSemantics.tyenvToProp at h₁
    simp [PropSemantics.varToProp] at h₁
    have h₁' := h₁ x (Ast.Ty.refin τ (Ast.Predicate.dep v body)) h₂
    rw[h₂] at h₁'
    simp at h₁'
    exact h₁'
  }

/--
Deconstructs a **conjunctive type guarantee** into individual runtime proofs.

If a variable's type guarantees that `e₁ ∧ e₂` holds, this lemma allows us to derive
separate evaluation proofs for both `e₁` and `e₂`.
-/
lemma tyenv_and_to_eval_exprs {σ T Δ Γ x e₁ e₂} (h₁: PropSemantics.tyenvToProp σ T Δ Γ) (h₂: Env.lookupTy Γ x = some (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.and (Ast.Predicate.ind e₁) (Ast.Predicate.ind e₂)))):
  (Eval.EvalProp σ T Δ e₁ (Ast.Value.vBool true)) ∧ (Eval.EvalProp σ T Δ e₂ (Ast.Value.vBool true)) := by {
    unfold PropSemantics.tyenvToProp at h₁
    simp [PropSemantics.varToProp] at h₁
    have h₁' := h₁ x (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.and (Ast.Predicate.ind e₁) (Ast.Predicate.ind e₂))) h₂
    rw[h₂] at h₁'
    simp at h₁'
    exact h₁'
  }

lemma tyenvToProp_implies_varToProp
  (σ : Env.ValEnv) (T: Env.TraceEnv) (Δ : Env.ChipEnv) (Γ : Env.TyEnv)
  (x : String) (τ : Ast.Ty) (φ : Ast.Predicate)
  (hΓx : Env.lookupTy Γ x = Ast.Ty.refin τ φ)
  (hmt : PropSemantics.tyenvToProp σ T Δ Γ) :
  PropSemantics.varToProp σ T Δ Γ x := by
  dsimp [PropSemantics.tyenvToProp] at hmt
  apply hmt
  exact hΓx

lemma constZ_refine_lt {Δ Γ Η x y} {h: x < y} :
  @Ty.TypeJudgment Δ Γ Η (Ast.Expr.constZ x) (Ast.Ty.int.refin (Ast.Predicate.dep Ast.mu ((Ast.Expr.var Ast.mu).binRel Ast.RelOp.lt (Ast.Expr.constZ y)))) := by {
  apply Ty.TypeJudgment.TE_SUB
  apply Ty.TypeJudgment.TE_ConstZ
  apply Ty.SubtypeJudgment.TSub_Refine
  apply Ty.SubtypeJudgment.TSub_Refl
  intro σ T v h₁ h₂
  simp [PropSemantics.predToProp] at h₂ ⊢
  cases h₂
  rename_i va ih₁ ih₂ ih₃
  cases ih₁
  cases ih₃
  rename_i v₁ v₂ ih₁ ih₃ r
  cases ih₃
  simp [Eval.evalRelOp] at r
  cases v₁ <;> simp at r
  rw[r] at ih₁
  apply Eval.EvalProp.App
  apply Eval.EvalProp.Lam
  exact ih₂
  apply Eval.EvalProp.Rel
  exact ih₁
  apply Eval.EvalProp.ConstZ
  simp [Eval.evalRelOp]
  exact h
}

lemma varZ_refine_lt {Δ Γ Η x v₁ v₂} {h₀: Env.lookupTy Γ x = (Ast.Ty.refin Ast.Ty.int (Ast.Predicate.dep Ast.mu (Ast.exprEq (Ast.Expr.var Ast.mu) (Ast.Expr.constZ v₁))))} {h₁: v₁ < v₂} :
  @Ty.TypeJudgment Δ Γ Η (Ast.Expr.var x) (Ast.Ty.int.refin (Ast.Predicate.dep Ast.mu ((Ast.Expr.var Ast.mu).binRel Ast.RelOp.lt (Ast.Expr.constZ v₂)))) := by {
  apply Ty.TypeJudgment.TE_SUB
  apply Ty.TypeJudgment.TE_VarEnv
  exact h₀
  apply Ty.SubtypeJudgment.TSub_Refine
  apply Ty.SubtypeJudgment.TSub_Refl
  intro σ T v h₃ h₄
  unfold PropSemantics.tyenvToProp at h₃
  have h₅ := h₃ x ((Ty.int.refin (Predicate.dep mu (exprEq (Expr.var mu) (Expr.constZ v₁))))) h₀
  simp [PropSemantics.predToProp] at h₄ ⊢
  simp [PropSemantics.varToProp] at h₅
  rw[h₀] at h₅
  simp at h₅
  cases h₄
  rename_i ih_f ih_a ih_b
  cases ih_f
  cases ih_b
  rename_i ih₁ ih₂ r
  cases ih₁
  rename_i a
  unfold Env.lookupVal Env.updateVal at a
  simp at a
  rw[← a] at r
  cases ih₂
  simp [Eval.evalRelOp] at r
  rename_i va₁ va₂
  cases va₁ with
  | vZ x => {
    simp at r
    apply Eval.EvalProp.App
    apply Eval.EvalProp.Lam
    exact ih_a
    apply Eval.EvalProp.Rel
    apply Eval.EvalProp.Var
    unfold Env.lookupVal Env.updateVal
    simp
    rfl
    apply Eval.EvalProp.ConstZ
    rw[r]
    simp [Eval.evalRelOp]
    exact h₁
  }
  | _ => {
    simp at r
  }
}

lemma varZ_refine_int_diff_lt {Γ Η} (n x: String)
  (h₀: Env.lookupTy Γ n = (Ast.Ty.refin Ast.Ty.int
      (Ast.Predicate.dep mu (Ast.exprEq (Ast.Expr.var mu) (Ast.Expr.constZ height)))))
  (h₁: Env.lookupTy Γ x = (Ast.Ty.unit.refin
      (Ast.Predicate.ind
        ((Ast.Expr.var i).binRel Ast.RelOp.lt
          ((Ast.Expr.var n).integerExpr Ast.IntegerOp.sub (Ast.Expr.constZ d))))))
  (h₂: Env.lookupTy Γ i = (Ast.Ty.int.refin φ))
  (h₃: i ≠ mu):
  @Ty.TypeJudgment Δ Γ Η ((Ast.Expr.var i).integerExpr Ast.IntegerOp.add (Ast.Expr.constZ d))
    (Ast.Ty.int.refin (Ast.Predicate.dep mu ((Ast.Expr.var mu).binRel Ast.RelOp.lt (Ast.Expr.constZ height)))) := by {
    apply Ty.TypeJudgment.TE_SUB
    apply Ty.TypeJudgment.TE_BinOpInteger
    apply Ty.TypeJudgment.TE_VarEnv
    exact h₂
    apply Ty.TypeJudgment.TE_ConstZ
    apply Ty.SubtypeJudgment.TSub_Refine
    apply Ty.SubtypeJudgment.TSub_Refl
    intro σ T v ha hb
    unfold PropSemantics.tyenvToProp at ha
    have h₀' := ha n (Ty.int.refin (Predicate.dep mu (exprEq (Expr.var mu) (Expr.constZ height)))) h₀
    have h₁' := ha x (Ty.unit.refin
      (Predicate.ind ((Expr.var i).binRel RelOp.lt ((Expr.var n).integerExpr IntegerOp.sub (Expr.constZ d))))) h₁
    simp at h₀' h₁'
    rw[h₀] at h₀'
    simp at h₀'
    rw[h₁] at h₁'
    simp at h₁'
    cases h₀'
    rename_i ihf iha idx
    cases ihf
    cases iha
    cases idx
    rename_i ih₁ ih₂ r
    cases ih₂
    cases ih₁
    rename_i a
    unfold Env.lookupVal Env.updateVal at a
    simp at a
    cases h₁'
    rename_i ih₁ ih₂ r
    cases ih₁
    cases ih₂
    rename_i ih₁ ih₂ r
    cases ih₂
    cases ih₁
    simp at r
    rename_i hn' _ r' i_val _ r hi n_val hn
    rw[hn] at hn'
    rw[← hn'] at a
    rw[← a] at r'
    simp at r'
    rename_i r''
    rw[← r] at r''
    simp at hb
    cases hb
    rename_i ihf iha ihb
    cases ihf
    cases ihb
    rename_i ih₁ ih₂ r
    cases ih₁
    rename_i a
    unfold Env.lookupVal Env.updateVal at a
    simp at a
    cases ih₂
    rename_i ih₁ ih₂ r
    cases ih₁
    cases ih₂
    simp at r
    cases i_val with
    | vZ i_val' => {
      simp at r''
      simp[PropSemantics.predToProp]
      apply Eval.EvalProp.App
      apply Eval.EvalProp.Lam
      exact iha
      apply Eval.EvalProp.Rel
      apply Eval.EvalProp.Var
      unfold Env.lookupVal Env.updateVal
      simp
      rfl
      apply Eval.EvalProp.ConstZ
      rename_i ih₂ _ u₁ _ ih₁ _ _
      rw[← r] at ih₁
      cases u₁ with
      | vZ uv₁ => {
        simp at ih₁
        rw[a]
        rw[ih₁]
        rename_i a'
        rename_i va' v2₂' i'
        have : Env.lookupVal (Env.updateVal σ mu va') i = Env.lookupVal σ i := by {
          apply lookup_val_update_ne
          exact h₃
        }
        rw[this] at a'
        rw[hi] at a'
        rw[r'] at r''
        simp at a'
        rw[a'] at r''
        simp [Eval.evalRelOp]
        omega
      }
      | _ => {
        simp at ih₁
      }
    }
    | _ => {
      simp at r''
    }
  }
