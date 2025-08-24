import Runwai.Typing
import Runwai.Gadget
--import Runwai.PP

@[simp]
def assertCircuit : Ast.Circuit := {
  name   := "assert",
  width  := 2,
  goal   := Ast.Ty.refin Ast.Ty.unit
    (Ast.Predicate.lam "v"
      (Ast.Expr.binRel (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 1))
                       Ast.RelOp.eq (Ast.Expr.constF 2))),
  body   := (Ast.Expr.letIn "u" (Ast.Expr.assertE
              (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 1))
              (Ast.Expr.constF 2))
            (Ast.Expr.var "u"))
}

/-
@[simp]
def iszeroCircuit : Ast.Circuit := {
  name   := "iszero",
  width  := 3,
  goal   := (Ast.exprEq (.var "y") (.branch (.binRel (.var "x") (.eq) (.constF 0)) (.constF 1) (.constF 0)))
  body   := (Ast.Expr.letIn "x" (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 0))
              (Ast.Expr.letIn "y" (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 1))
                (Ast.Expr.letIn "inv" (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 2))
                  (Ast.Expr.letIn "u₁" (.assertE (.var "y") (.fieldExpr (.fieldExpr (.fieldExpr (.constF 0) .sub (.var "x")) .mul (.var "inv")) (.add) (.constF 1)))
                    (Ast.Expr.letIn "u₂" (.assertE (.fieldExpr (.var "x") .mul (.var "y")) (.constF 0)) (.var "u₂")))
                )
              )
            )
}
-/

def Δ : Env.CircuitEnv := [("assert", assertCircuit)]

theorem assertCircuit_correct : Ty.circuitCorrect Δ assertCircuit 1 := by
  unfold Ty.circuitCorrect
  intro x i height hs hi ht hσ
  let envs := Ty.makeEnvs assertCircuit x (Ast.Value.vZ i) height
  let σ := envs.1
  let Γ := envs.2
  apply Ty.TypeJudgment.TE_LetIn
  · apply lookup_update_self
  · apply Ty.TypeJudgment.TE_Assert
    · apply Ty.TypeJudgment.TE_ArrayIndex; apply Ty.TypeJudgment.TE_ArrayIndex; apply Ty.TypeJudgment.TE_Var
      apply lookup_update_ne
      simp
      apply Eval.EvalProp.Var; exact rfl
      simp
      exact hi
      apply Eval.EvalProp.ConstZ
      simp
    . apply Ty.TypeJudgment.TE_ConstF
  . constructor;
    apply lookup_update_self

syntax "auto_judgment" : tactic
macro_rules
| `(tactic| auto_judgment) => `(tactic|
    {
      repeat constructor
      simp_all
      constructor;
      simp_all
    }
  )

syntax "lookup_recent_update" : tactic
macro_rules
| `(tactic| lookup_recent_update) => `(tactic|
    {
      apply lookup_update_self_none; apply lookup_update_ne
      simp
    }
  )


/-
theorem iszeroCircuit_correct : Ty.circuitCorrect Δ iszeroCircuit 1 := by
  unfold Ty.circuitCorrect
  intro x i height hs hi ht hσ
  let envs := Ty.makeEnvs iszeroCircuit x (Ast.Value.vZ i) height
  let σ := envs.1
  let Γ := envs.2
  --unfold iszeroCircuit
  apply Ty.TypeJudgment.TE_LetIn
  · lookup_recent_update
  · auto_judgment
  . apply Ty.TypeJudgment.TE_LetIn
    . lookup_recent_update
    · auto_judgment
    . apply Ty.TypeJudgment.TE_LetIn
      . lookup_recent_update
      · auto_judgment
      . apply isZero_typing_soundness
        repeat apply lookup_update_ne; simp
        apply Ty.TypeJudgment.TE_VarEnv
        lookup_recent_update; simp;
        repeat apply lookup_update_ne; simp

theorem iszeroCircuit_correct_long : Ty.circuitCorrect Δ iszeroCircuit 1 := by
  unfold Ty.circuitCorrect
  intro x i height hs hi ht hσ
  let envs := Ty.makeEnvs iszeroCircuit x (Ast.Value.vZ i) height
  let σ := envs.1
  let Γ := envs.2
  unfold iszeroCircuit; simp
  apply Ty.TypeJudgment.TE_LetIn
  · apply lookup_update_self_none; apply lookup_update_ne
    simp
  · apply Ty.TypeJudgment.TE_ArrayIndex
    apply Ty.TypeJudgment.TE_ArrayIndex
    apply Ty.TypeJudgment.TE_Var
    apply lookup_update_ne
    simp
    apply Eval.EvalProp.Var
    unfold Env.lookupVal
    unfold Env.updateVal
    simp
    rfl
    simp
    exact hi
    apply Eval.EvalProp.ConstZ
    simp
  . apply Ty.TypeJudgment.TE_LetIn
    . apply lookup_update_self_none; apply lookup_update_ne
      simp
    · apply Ty.TypeJudgment.TE_ArrayIndex
      apply Ty.TypeJudgment.TE_ArrayIndex
      apply Ty.TypeJudgment.TE_Var
      apply lookup_update_ne
      simp
      apply Eval.EvalProp.Var
      unfold Env.lookupVal
      unfold Env.updateVal
      simp
      rfl
      simp
      exact hi
      apply Eval.EvalProp.ConstZ
      simp
    . apply Ty.TypeJudgment.TE_LetIn
      . apply lookup_update_self_none; apply lookup_update_ne
        simp
      · apply Ty.TypeJudgment.TE_ArrayIndex
        apply Ty.TypeJudgment.TE_ArrayIndex
        apply Ty.TypeJudgment.TE_Var
        apply lookup_update_ne
        simp
        apply Eval.EvalProp.Var
        unfold Env.lookupVal
        unfold Env.updateVal
        simp
        rfl
        simp
        exact hi
        apply Eval.EvalProp.ConstZ
        simp
      . apply isZero_typing_soundness
        apply lookup_update_ne; simp
        apply lookup_update_ne; simp
        apply Ty.TypeJudgment.TE_VarEnv
        apply lookup_update_self_none
        apply lookup_update_ne; simp; simp; apply lookup_update_ne
        simp; apply lookup_update_ne; simp
-/
