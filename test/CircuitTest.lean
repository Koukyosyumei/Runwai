import Runwai.Typing
import Runwai.Gadget
import Runwai.PP
import Runwai.Tactic

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
def iszeroCircuit : Ast.Circuit := {
  name    := "iszero",
  ident_t := "trace",
  ident_i := "i",
  width   := 3,
  goal    := Ast.Ty.refin Ast.Ty.unit
    (Ast.Predicate.ind
      (Ast.exprEq (.var "y") (.branch (.binRel (.var "x") (.eq) (.constF 0)) (.constF 1) (.constF 0))))
  body    := (Ast.Expr.letIn "x" (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 0))
              (Ast.Expr.letIn "y" (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 1))
                (Ast.Expr.letIn "inv" (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 2))
                  (Ast.Expr.letIn "u₁" (.assertE (.var "y") (.fieldExpr (.fieldExpr (.fieldExpr (.constF 0) .sub (.var "x")) .mul (.var "inv")) (.add) (.constF 1)))
                    (Ast.Expr.letIn "u₂" (.assertE (.fieldExpr (.var "x") .mul (.var "y")) (.constF 0)) (.var "u₂")))
                )
              )
            )
}

@[simp]
def wordRangeCheckerCircuit : Ast.Circuit := {
  name := "word_range_checker",
  ident_t := "trace",
  ident_i := "i",
  width := 18,
  goal := Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind
    (.binRel (.integerExpr (.integerExpr (.integerExpr (.toZ (.var "value_0")) .add ((.integerExpr (.toZ (.var "value_1")) .mul (.constZ 256)))) .add ((.integerExpr (.toZ (.var "value_2")) .mul (.constZ (256^2))))) .add (.integerExpr (.toZ (.var "value_3")) .mul (.constZ (256^3))))
      .lt (.constZ 2130706433)))
  body := (.letIn "value_0" (Ast.trace_i_j "trace" "i" 0)
          (.letIn "value_1" (Ast.trace_i_j "trace" "i" 1)
          (.letIn "value_2" (Ast.trace_i_j "trace" "i" 2)
          (.letIn "value_3" (Ast.trace_i_j "trace" "i" 3)
          (.letIn "most_sig_byte_decomp_0" (Ast.trace_i_j "trace" "i" 4)
          (.letIn "most_sig_byte_decomp_1" (Ast.trace_i_j "trace" "i" 5)
          (.letIn "most_sig_byte_decomp_2" (Ast.trace_i_j "trace" "i" 6)
          (.letIn "most_sig_byte_decomp_3" (Ast.trace_i_j "trace" "i" 7)
          (.letIn "most_sig_byte_decomp_4" (Ast.trace_i_j "trace" "i" 8)
          (.letIn "most_sig_byte_decomp_5" (Ast.trace_i_j "trace" "i" 9)
          (.letIn "most_sig_byte_decomp_6" (Ast.trace_i_j "trace" "i" 10)
          (.letIn "most_sig_byte_decomp_7" (Ast.trace_i_j "trace" "i" 11)
          (.letIn "and_most_sig_byte_decomp_0_to_2" (Ast.trace_i_j "trace" "i" 12)
          (.letIn "and_most_sig_byte_decomp_0_to_3" (Ast.trace_i_j "trace" "i" 13)
          (.letIn "and_most_sig_byte_decomp_0_to_4" (Ast.trace_i_j "trace" "i" 14)
          (.letIn "and_most_sig_byte_decomp_0_to_5" (Ast.trace_i_j "trace" "i" 15)
          (.letIn "and_most_sig_byte_decomp_0_to_6" (Ast.trace_i_j "trace" "i" 16)
          (.letIn "and_most_sig_byte_decomp_0_to_7" (Ast.trace_i_j "trace" "i" 17)
          (.letIn "u₁"
            (.assertE (.fieldExpr
                        (.fieldExpr
                          (.fieldExpr
                            (.fieldExpr
                              (.fieldExpr
                                (.fieldExpr
                                  (.fieldExpr
                                    (.var "most_sig_byte_decomp_0")
                                    .add
                                    (.fieldExpr (.var "most_sig_byte_decomp_1") .mul (.constF 2)))
                                  .add
                                  (.fieldExpr
                                    (.var "most_sig_byte_decomp_2") .mul (.constF 4)))
                                    .add
                                    (.fieldExpr (.var "most_sig_byte_decomp_3") .mul (.constF 8))
                                )
                              .add
                              (.fieldExpr (.var "most_sig_byte_decomp_4") .mul (.constF 16))
                            )
                            .add
                            (.fieldExpr (.var "most_sig_byte_decomp_5") .mul (.constF 32))
                          )
                          .add
                          (.fieldExpr (.var "most_sig_byte_decomp_6") .mul (.constF 64))
                        )
                        .add
                        (.fieldExpr (.var "most_sig_byte_decomp_7") .mul (.constF 128))
                      )
              (.var "value_3")
            )
            (.letIn "u₂" (.assertE (.var "most_sig_byte_decomp_7") (.constF 0))
            (.letIn "u₃" (.assertE (.var "and_most_sig_byte_decomp_0_to_2") (.fieldExpr (.var "most_sig_byte_decomp_0") .mul (.var "most_sig_byte_decomp_1")))
            (.letIn "u₄" (.assertE (.var "and_most_sig_byte_decomp_0_to_3") (.fieldExpr (.var "and_most_sig_byte_decomp_0_to_2") .mul (.var "most_sig_byte_decomp_2")))
            (.letIn "u₅" (.assertE (.var "and_most_sig_byte_decomp_0_to_4") (.fieldExpr (.var "and_most_sig_byte_decomp_0_to_3") .mul (.var "most_sig_byte_decomp_3")))
            (.letIn "u₆" (.assertE (.var "and_most_sig_byte_decomp_0_to_5") (.fieldExpr (.var "and_most_sig_byte_decomp_0_to_4") .mul (.var "most_sig_byte_decomp_4")))
            (.letIn "u₇" (.assertE (.var "and_most_sig_byte_decomp_0_to_6") (.fieldExpr (.var "and_most_sig_byte_decomp_0_to_5") .mul (.var "most_sig_byte_decomp_5")))
            (.letIn "u₈" (.assertE (.var "and_most_sig_byte_decomp_0_to_7") (.fieldExpr (.var "and_most_sig_byte_decomp_0_to_6") .mul (.var "most_sig_byte_decomp_6")))
            (.letIn "u₉" (.assertE (.var "and_most_sig_byte_decomp_0_to_7") (.fieldExpr (.fieldExpr (.var "value_0") .add (.var "value_1")) .add (.var "value_2")))
              (.var "u₉"))))))))))))))))))))))))))))
}

def Δ : Env.CircuitEnv := [("assert", assertCircuit)]

theorem assertCircuit_correct : Ty.circuitCorrect Δ assertCircuit 1 := by
  unfold Ty.circuitCorrect
  intro x i hs hi hrow ht hσ
  let envs := Ty.makeEnvs assertCircuit (Ast.Value.vArr x) (Ast.Value.vZ i) x.length
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

theorem iszeroCircuit_correct : Ty.circuitCorrect Δ iszeroCircuit 1 := by
  unfold Ty.circuitCorrect
  intro x i height hs hi hrow ht
  let envs := Ty.makeEnvs iszeroCircuit (Ast.Value.vArr x) (Ast.Value.vZ i) x.length
  let σ := envs.1
  let Γ := envs.2
  repeat
    apply Ty.TypeJudgment.TE_LetIn;
    · apply lookup_update_self;
    · auto_judgment;
  apply isZero_typing_soundness
  repeat apply lookup_update_ne; simp
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_self;
  repeat decide

theorem iszeroCircuit_correct_long : Ty.circuitCorrect Δ iszeroCircuit 1 := by
  unfold Ty.circuitCorrect
  intro x i height hs hi hrow ht
  let envs := Ty.makeEnvs iszeroCircuit (Ast.Value.vArr x) (Ast.Value.vZ i) x.length
  let σ := envs.1
  let Γ := envs.2
  unfold iszeroCircuit; simp
  apply Ty.TypeJudgment.TE_LetIn
  · apply lookup_update_self
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
    exact hs
    apply Eval.EvalProp.ConstZ
    simp
  . apply Ty.TypeJudgment.TE_LetIn
    . apply lookup_update_self
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
      exact hs
      apply Eval.EvalProp.ConstZ
      simp
    . apply Ty.TypeJudgment.TE_LetIn
      . apply lookup_update_self
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
        exact hs
        apply Eval.EvalProp.ConstZ
        simp
      . apply isZero_typing_soundness
        apply lookup_update_ne; simp
        apply lookup_update_ne; simp
        apply Ty.TypeJudgment.TE_VarEnv
        apply lookup_update_self
        decide
        decide
        decide
