import Runwai.Ast
import Runwai.Env
import Runwai.Eval
import Runwai.Gadget
import Runwai.Typing

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
      (Ast.Expr.binRel (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace'") (Ast.Expr.var "i")) (Ast.Expr.constZ 1))
                       Ast.RelOp.eq (Ast.Expr.constF 2))),
  body    := (Ast.Expr.lookup "assert" [((Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 0)), (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 1)))])
}

def σ : Env.ValEnv := []
def Δ : Env.CircuitEnv := [("assert", assertCircuit), ("lookup", lookupCircuit)]

theorem lookupCircuit_correct : Ty.circuitCorrect Δ lookupCircuit 1 := by
  unfold Ty.circuitCorrect
  intro x i height hs hi ht hσ
  let envs := Ty.makeEnvs assertCircuit x (Ast.Value.vZ i) height
  let σ := envs.1
  let Γ := envs.2
  unfold lookupCircuit
  simp_all
  apply Ty.TypeJudgment.TE_LookUp
  rfl
  rfl
  unfold Env.lookupCircuit
  unfold Env.freshName
  unfold Δ
  simp_all
  unfold Ast.renameVarinPred
  simp_all
  repeat unfold Ast.renameVar; simp
