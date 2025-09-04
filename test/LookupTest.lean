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
    (Ast.Predicate.and
      (Ast.Predicate.ind (Ast.Expr.binRel (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace'") (Ast.Expr.var "i'")) (Ast.Expr.constZ 1))
                       Ast.RelOp.eq (Ast.Expr.constF 2)))
      (Ast.Predicate.ind (Ast.exprEq (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 0))
                                     (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 1))))),
  body    := (Ast.Expr.lookup "assert" [((Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 0)), (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 1)))])
}

def σ : Env.ValEnv := []
def Δ : Env.CircuitEnv := [("assert", assertCircuit), ("lookup", lookupCircuit)]

theorem lookupCircuit_correct : Ty.circuitCorrect Δ lookupCircuit 1 := by
  unfold Ty.circuitCorrect
  intro x i hs hi hrow ht
  let envs := Ty.makeEnvs assertCircuit (Ast.Value.vArr x) (Ast.Value.vZ i) x.length
  let σ := envs.1
  let Γ := envs.2
  unfold lookupCircuit
  simp_all
  intro h
  apply Ty.TypeJudgment.TE_LookUp
  rfl
  rfl
  repeat unfold Ast.renameVarinPred; simp
  repeat unfold Env.freshName Ast.renameVar Env.lookupCircuit Δ; simp
  repeat unfold Ast.renameVar; simp
