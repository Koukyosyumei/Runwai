import Runwai.Typing

@[simp]
def assertCircuit : Ast.Circuit := {
  name   := "assert",
  inputs := ("trace", Ast.Ty.refin (Ast.Ty.arr (Ast.Ty.refin (Ast.Ty.arr (Ast.Ty.refin Ast.Ty.field (Ast.Predicate.const (Ast.Expr.constBool true))) 2) (Ast.Predicate.const (Ast.Expr.constBool True))) 2) (Ast.Predicate.const (Ast.Expr.constBool true))),
  output := ("u", Ast.Ty.refin (Ast.Ty.unit)
                      (Ast.Predicate.const (Ast.Expr.binRel
                        (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.constF 1)) (Ast.Expr.constF 0))
                        Ast.RelOp.eq
                        (Ast.Expr.constF 2)))),
  body   := (Ast.Expr.letIn "u" (Ast.Expr.assertE
              (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.constF 1)) (Ast.Expr.constF 0))
              (Ast.Expr.constF 2))
            (Ast.Expr.var "u"))
}

def Δ : Env.CircuitEnv := [("assert", assertCircuit)]

theorem assertCircuit_correct : (Ty.circuitCorrect Δ assertCircuit) := by
  unfold Ty.circuitCorrect
  unfold assertCircuit
  simp_all
  intro x hs hi hσ
  set envs := Ty.makeEnvs assertCircuit x
  set σ := envs.1
  set Γ := envs.2
  apply Ty.TypeJudgment.TE_LetIn
  apply Ty.TypeJudgment.TE_Assert
  apply Ty.TypeJudgment.TE_ArrayIndex
  apply Ty.TypeJudgment.TE_ArrayIndex
  apply Ty.TypeJudgment.TE_Var
  unfold Ty.makeEnvs
  unfold Env.updateTy
  unfold Env.lookupTy
  simp_all
  constructor
  . constructor
    . constructor
      . constructor
        . rfl
        . rfl
      . rfl
    . rfl
  . rfl
  apply Eval.EvalProp.ConstF
  simp_all
  apply Eval.EvalProp.ConstF
  simp_all
  apply Ty.TypeJudgment.TE_ConstF
  apply Ty.TypeJudgment.TE_VarEnv
  unfold Env.updateTy
  unfold Env.lookupTy
  simp_all
  unfold Ast.exprEq
  rfl
