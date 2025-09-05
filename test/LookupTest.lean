import Runwai.Ast
import Runwai.Env
import Runwai.Eval
import Runwai.Gadget
import Runwai.Typing
--import Runwai.PP

@[simp]
def assertCircuit : Ast.Circuit := {
  name    := "assert",
  ident_t := "trace",
  ident_i := "i",
  width   := 2,
  goal    := Ast.Ty.refin Ast.Ty.unit
    (Ast.Predicate.ind
      (Ast.Expr.binRel (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 1))
                       Ast.RelOp.eq (Ast.Expr.constF 2))),
  body    := (Ast.Expr.letIn "u" (Ast.Expr.assertE
              (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 1))
              (Ast.Expr.constF 2))
            (Ast.Expr.var "u"))
}

@[simp]
def lookupCircuit : Ast.Circuit := {
  name    := "lookup",
  ident_t := "trace",
  ident_i := "i",
  width   := 2,
  goal    := Ast.Ty.refin Ast.Ty.unit
              (Ast.Predicate.ind (Ast.Expr.binRel
                (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 0))
                  Ast.RelOp.eq
                (Ast.Expr.constF 2))),
  body    := Ast.Expr.letIn "u" (Ast.Expr.lookup "assert"
                [((Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 0)),
                  (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 1)))])
                (Ast.Expr.var "u")
}

def σ : Env.ValEnv := []
def Δ : Env.CircuitEnv := [("assert", assertCircuit), ("lookup", lookupCircuit)]

theorem lookupCircuit_correct : Ty.circuitCorrect Δ lookupCircuit 1 := by
  unfold Ty.circuitCorrect lookupCircuit
  intro x i hs hi hrow ht
  let envs := Ty.makeEnvs assertCircuit (Ast.Value.vArr x) (Ast.Value.vZ i) x.length
  let σ := envs.1
  let Γ := envs.2
  simp_all
  intro h
  apply Ty.TypeJudgment.TE_LetIn; rfl
  apply Ty.TypeJudgment.TE_LookUp; repeat rfl
  let τ' := (Ast.Ty.unit.refin
      (Ty.lookup_pred
        [(((Ast.Expr.var "trace").arrIdx (Ast.Expr.var "i")).arrIdx (Ast.Expr.constZ 0),
            ((Ast.Expr.var "trace").arrIdx (Ast.Expr.var "i")).arrIdx (Ast.Expr.constZ 1))]
        (Env.lookupCircuit Δ "assert")
        (Ast.Predicate.ind
          ((((Ast.Expr.var "trace").arrIdx (Ast.Expr.var "i")).arrIdx (Ast.Expr.constZ 1)).binRel Ast.RelOp.eq
            (Ast.Expr.constF 2)))
        ["trace", "i"]))
  let Γ' := (Env.updateTy
    (Env.updateTy
      (Env.updateTy [] "trace"
        (((((Ast.Ty.field.refin (Ast.Predicate.ind (Ast.Expr.constBool true))).arr 2).refin
                  (Ast.Predicate.ind (Ast.Expr.constBool true))).arr
              ↑x.length).refin
          (Ast.Predicate.ind (Ast.Expr.constBool true))))
      "i"
      (Ast.Ty.int.refin (Ast.Predicate.dep "v" ((Ast.Expr.var "v").binRel Ast.RelOp.lt (Ast.Expr.constZ x.length)))))
    "u" τ')
  have hs : Ty.SubtypeJudgment σ Δ Γ' τ'
         (Ast.Ty.unit.refin
    (Ast.Predicate.ind
      ((((Ast.Expr.var "trace").arrIdx (Ast.Expr.var "i")).arrIdx (Ast.Expr.constZ 0)).binRel Ast.RelOp.eq
        (Ast.Expr.constF 2)))) := by {
      apply Ty.SubtypeJudgment.TSub_Refine
      apply Ty.SubtypeJudgment.TSub_Refl
      intro v h₁ h₂
      unfold PropSemantics.tyenvToProp at h₁
      have h₃ := h₁ "u"
      unfold Γ' Env.lookupTy Env.updateTy PropSemantics.varToProp Env.lookupTy τ' at h₃
      simp at h₃
      unfold Ty.lookup_pred at h₃
      have hat : (Env.lookupCircuit Δ "assert").ident_t = "trace" := by {
        unfold Env.lookupCircuit Δ; simp }
      have hai : (Env.lookupCircuit Δ "assert").ident_i = "i" := by {
        unfold Env.lookupCircuit Δ; simp }
      rw[hat, hai] at h₃
      unfold Env.freshName at h₃
      simp at h₃
      repeat unfold Ast.renameVarinPred at h₃
      repeat unfold Ast.renameVar at h₃; simp at h₃
      unfold PropSemantics.predToProp at h₃
      obtain ⟨h₄,h₅⟩ := h₃
      unfold PropSemantics.predToProp PropSemantics.exprToProp at h₄ h₅ ⊢
      apply evalProp_eq_symm at h₅
      apply evalProp_eq_trans h₅ h₄
        }
  apply Ty.TypeJudgment.TE_SUB hs
  unfold Γ'
  apply Ty.TypeJudgment.TE_VarEnv
  unfold Env.lookupTy Env.updateTy
  simp
  rfl
