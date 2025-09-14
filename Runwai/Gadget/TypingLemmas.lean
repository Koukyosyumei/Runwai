import Runwai.Typing
import Runwai.Gadget.Utils

open Ast

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
