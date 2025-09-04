import Runwai.Ast
import Runwai.Env
import Runwai.Eval
import Runwai.Gadget
import Runwai.Typing
import Runwai.PP

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
    (Ast.Predicate.ind
      (Ast.Expr.binRel (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 0))
                       Ast.RelOp.eq (Ast.Expr.constF 2))),
  body    := (Ast.Expr.lookup "assert" [((Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 0)), (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 1)))])
}

def σ : Env.ValEnv := []
def Δ : Env.CircuitEnv := [("assert", assertCircuit), ("lookup", lookupCircuit)]

theorem lookupCircuit_correct : Ty.circuitCorrect Δ lookupCircuit 1 := by
  unfold Ty.circuitCorrect
  intro x i height hs hi ht hσ
  let envs := Ty.makeEnvs assertCircuit (Ast.Value.vArr x) (Ast.Value.vZ i) height
  let σ := envs.1
  let Γ := envs.2
  unfold lookupCircuit
  simp_all
  apply Ty.TypeJudgment.TE_SUB
  apply Ty.SubtypeJudgment.TSub_Refine
  apply Ty.SubtypeJudgment.TSub_Refl
  intro v
  intro h₁
  intro h₂
  unfold PropSemantics.predToProp
  unfold PropSemantics.exprToProp
  apply Eval.EvalProp.Rel
  apply Eval.EvalProp.ArrIdx
  apply Eval.EvalProp.ArrIdx
  apply Eval.EvalProp.Var
  unfold Env.lookupVal
  unfold Env.updateVal
  simp
  rfl
  apply Eval.EvalProp.Var
  unfold Env.lookupVal
  unfold Env.updateVal
  simp
  rfl
  unfold PropSemantics.tyenvToProp at h₁
  u

  apply Ty.TypeJudgment.TE_LookUp
  rfl
  rfl
  have h₁: Ast.renameVarinPred
        (Ast.Predicate.ind
          ((((Ast.Expr.var "trace").arrIdx (Ast.Expr.var "i")).arrIdx (Ast.Expr.constZ 1)).binRel Ast.RelOp.eq
            (Ast.Expr.constF 2)))
        (Env.lookupCircuit Δ "assert").ident_t (Env.freshName ["trace", "i"] (Env.lookupCircuit Δ "assert").ident_t) = (Ast.Predicate.ind
          ((((Ast.Expr.var "trace'").arrIdx (Ast.Expr.var "i")).arrIdx (Ast.Expr.constZ 1)).binRel Ast.RelOp.eq
            (Ast.Expr.constF 2))) := by {
                unfold Ast.renameVarinPred
                simp
                unfold Ast.renameVar
                unfold Env.freshName
                simp
                unfold Ast.renameVar
                simp
                unfold Ast.renameVar
                simp
                unfold Ast.renameVar
                simp
                unfold Env.lookupCircuit
                unfold Δ
                simp
            }
  rw[h₁]
  have le : List.foldl (fun acc y ↦ acc.and (Ast.Predicate.ind (Ast.exprEq y.1 y.2)))
    (Ast.renameVarinPred
      (Ast.renameVarinPred
        (Ast.Predicate.ind
          ((((Ast.Expr.var "trace").arrIdx (Ast.Expr.var "i")).arrIdx (Ast.Expr.constZ 1)).binRel Ast.RelOp.eq
            (Ast.Expr.constF 2)))
        (Env.lookupCircuit Δ "assert").ident_t (Env.freshName ["trace", "i"] (Env.lookupCircuit Δ "assert").ident_t))
      (Env.lookupCircuit Δ "assert").ident_i (Env.freshName ["trace", "i"] (Env.lookupCircuit Δ "assert").ident_i))
    [(((Ast.Expr.var "trace").arrIdx (Ast.Expr.var "i")).arrIdx (Ast.Expr.constZ 0),
        ((Ast.Expr.var "trace").arrIdx (Ast.Expr.var "i")).arrIdx (Ast.Expr.constZ 1))]
    = (Ast.Predicate.ind
        ((((Ast.Expr.var "trace'").arrIdx (Ast.Expr.var "i'")).arrIdx (Ast.Expr.constZ 1)).binRel Ast.RelOp.eq
          (Ast.Expr.constF 2))) := by {
            unfold Ast.renameVarinPred
            unfold Ast.renameVarinPred
            unfold Ast.renameVar
            unfold Ast.renameVar

          }
  unfold Ast.renameVarinPred at le
  unfold List.foldl at le

  unfold Ast.renameVar at le
  simp
  intro h₁
  intro h₂
  simp

  apply Ty.TypeJudgment.TE_SUB
  apply Ty.SubtypeJudgment.TSub_Refine
  apply Ty.SubtypeJudgment.TSub_Refl
  intro v
  intro h₁
  intro h₂
  unfold PropSemantics.predToProp at h₂

  unfold PropSemantics.predToProp
  unfold PropSemantics.exprToProp
  apply Eval.EvalProp.Rel
  apply Eval.EvalProp.ArrIdx
  apply Eval.EvalProp.ArrIdx
  apply Eval.EvalProp.Var
  unfold Env.lookupVal
  unfold Env.updateVal
  simp
  rfl
  apply Eval.EvalProp.Var
  unfold Env.lookupVal
  unfold Env.updateVal
  simp
  rfl
  sorry
  apply Eval.EvalProp.ConstZ
  sorry
  sorry
  apply Eval.EvalProp.ConstF
  sorry
  sorry
  sorry
  sorry
