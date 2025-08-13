import Runwai.Typing

@[simp]
def assertCircuit : Ast.Circuit := {
  name   := "assert",
  width  := 2,
  goal   := Ast.Expr.binRel (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.constF 1)) (Ast.Expr.constF 0))
              Ast.RelOp.eq (Ast.Expr.constF 2),
  body   := (Ast.Expr.letIn "u" (Ast.Expr.assertE
              (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.constF 1)) (Ast.Expr.constF 0))
              (Ast.Expr.constF 2))
            (Ast.Expr.var "u"))
}

def Δ : Env.CircuitEnv := [("assert", assertCircuit)]

theorem assertCircuit_correct : (Ty.circuitCorrect Δ assertCircuit 1) := by
  unfold Ty.circuitCorrect
  unfold assertCircuit
  simp_all
  intro x i height hs hi hσ
  set envs := Ty.makeEnvs assertCircuit x i height
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
