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
  goal    := Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind (Ast.exprEq (Ast.trace_i_j "trace" "i" 1) (Ast.Expr.constF 2))),
  body    := (Ast.Expr.letIn "u" (Ast.Expr.assertE (Ast.trace_i_j "trace" "i" 1) (Ast.Expr.constF 2)) (Ast.Expr.var "u"))
}

@[simp]
def assertCircuit_2 : Ast.Circuit := {
  name    := "assert_2",
  ident_t := "trace",
  ident_i := "i",
  width   := 3,
  goal    := Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind (Ast.exprEq (Ast.trace_i_j "trace" "i" 2) (Ast.Expr.constF 3))),
  body    := (Ast.Expr.letIn "u" (Ast.Expr.assertE (Ast.trace_i_j "trace" "i" 2) (Ast.Expr.constF 3)) (Ast.Expr.var "u"))
}

@[simp]
def lookupCircuit : Ast.Circuit := {
  name    := "lookup",
  ident_t := "trace",
  ident_i := "i",
  width   := 2,
  goal    := Ast.Ty.refin Ast.Ty.unit
              (Ast.Predicate.ind (Ast.exprEq (Ast.trace_i_j "trace" "i" 0) (Ast.Expr.constF 2))),
  body    := Ast.Expr.lookup "u" "assert" [((Ast.trace_i_j "trace" "i" 0), (Ast.trace_i_j "trace" "i" 1))] (Ast.Expr.var "u")
}

@[simp]
def lookupCircuit_2 : Ast.Circuit := {
  name    := "lookup_2",
  ident_t := "trace",
  ident_i := "i",
  width   := 2,
  goal    := Ast.Ty.refin Ast.Ty.unit
              (Ast.Predicate.ind (Ast.exprEq (Ast.trace_i_j "trace" "i" 1) (Ast.Expr.constF 3))),
  body    := Ast.Expr.lookup "u₁" "assert" [((Ast.trace_i_j "trace" "i" 0), (Ast.trace_i_j "trace" "i" 1))]
              (Ast.Expr.lookup "u₂" "assert_2" [((Ast.trace_i_j "trace" "i" 1), (Ast.trace_i_j "trace" "i" 2))] (Ast.Expr.var "u₂"))
}

def σ : Env.ValEnv := []
def Δ : Env.CircuitEnv := [("assert", assertCircuit), ("assert_2", assertCircuit_2), ("lookup", lookupCircuit)]

theorem lookupCircuit_correct : Ty.circuitCorrect Δ lookupCircuit 1 := by
  unfold Ty.circuitCorrect lookupCircuit
  intro x i hs hi hrow ht
  let envs := Ty.makeEnvs assertCircuit (Ast.Value.vArr x) (Ast.Value.vZ i) x.length
  let σ := envs.1
  let Γ := envs.2
  simp_all
  intro h
  apply Ty.TypeJudgment.TE_LookUp; repeat rfl
  let τ' := (Ast.Ty.unit.refin
      (Ty.lookup_pred
        [(Ast.trace_i_j "trace" "i" 0, Ast.trace_i_j "trace" "i" 1)]
        (Env.lookupCircuit Δ "assert")
        (Ast.Predicate.ind (Ast.exprEq (Ast.trace_i_j "trace" "i" 1) (Ast.Expr.constF 2)))
        ["i", "trace"]))
  let Γ' := (Env.updateTy
    (Env.updateTy
      (Env.updateTy [] "trace"
        (((((Ast.Ty.field.refin Ast.constTruePred).arr 2).refin Ast.constTruePred).arr ↑x.length).refin Ast.constTruePred))
      "i"
      (Ast.Ty.int.refin (Ast.Predicate.dep "v" ((Ast.Expr.var "v").binRel Ast.RelOp.lt (Ast.Expr.constZ x.length)))))
    "u" τ')
  have hs : Ty.SubtypeJudgment σ Δ Γ' τ'
         (Ast.Ty.unit.refin (Ast.Predicate.ind (Ast.exprEq (Ast.trace_i_j "trace" "i" 0) (Ast.Expr.constF 2)))) := by {
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

theorem lookupCircuit_correct_2 : Ty.circuitCorrect Δ lookupCircuit_2 1 := by
  unfold Ty.circuitCorrect lookupCircuit_2
  intro x i hs hi hrow ht
  let envs := Ty.makeEnvs assertCircuit (Ast.Value.vArr x) (Ast.Value.vZ i) x.length
  let σ := envs.1
  let Γ := envs.2
  simp_all
  intro h
  apply Ty.TypeJudgment.TE_LookUp; repeat rfl
  apply Ty.TypeJudgment.TE_LookUp; repeat rfl
  have ht : (Ty.update_UsedNames (Env.lookupCircuit Δ "assert") ["i", "trace"]) = ["i'", "trace'", "i", "trace"] := by {
    unfold Ty.update_UsedNames Env.lookupCircuit Δ Env.freshName; simp
  }
  let τ' := (Ast.Ty.unit.refin
      (Ty.lookup_pred
        [(Ast.trace_i_j "trace" "i" 1, Ast.trace_i_j "trace" "i" 2)]
        (Env.lookupCircuit Δ "assert_2")
        (Ast.Predicate.ind (Ast.exprEq (Ast.trace_i_j "trace" "i" 2) (Ast.Expr.constF 3)))
        ["i'", "trace'", "i", "trace"]))
  let Γ' := (Env.updateTy
    (Env.updateTy
      (Env.updateTy
        (Env.updateTy []
        "trace"
          (((((Ast.Ty.field.refin Ast.constTruePred).arr 2).refin Ast.constTruePred).arr ↑x.length).refin Ast.constTruePred))
        "i"
          (Ast.Ty.int.refin (Ast.Predicate.dep "v" ((Ast.Expr.var "v").binRel Ast.RelOp.lt (Ast.Expr.constZ x.length)))))
        "u₁"
          (Ast.Ty.unit.refin
            (Ty.lookup_pred [(Ast.trace_i_j "trace" "i" 0, Ast.trace_i_j "trace" "i" 1)] (Env.lookupCircuit Δ "assert")
              (Ast.Predicate.ind (Ast.exprEq (Ast.trace_i_j "trace" "i" 1) (Ast.Expr.constF 2))) ["i", "trace"])))
        "u₂" τ')
  have hs : Ty.SubtypeJudgment σ Δ Γ' τ'
         (Ast.Ty.unit.refin (Ast.Predicate.ind (Ast.exprEq (Ast.trace_i_j "trace" "i" 1) (Ast.Expr.constF 3)))) := by {
      apply Ty.SubtypeJudgment.TSub_Refine
      apply Ty.SubtypeJudgment.TSub_Refl
      intro v h₁ h₂
      unfold PropSemantics.tyenvToProp at h₁
      have h₃ := h₁ "u₂"
      unfold Γ' Env.lookupTy Env.updateTy PropSemantics.varToProp Env.lookupTy τ' Ty.lookup_pred at h₃
      have hat : (Env.lookupCircuit Δ "assert_2").ident_t = "trace" := by {unfold Env.lookupCircuit Δ; simp }
      have hai : (Env.lookupCircuit Δ "assert_2").ident_i = "i" := by {unfold Env.lookupCircuit Δ; simp }
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
  rw[ht]
  apply Ty.TypeJudgment.TE_SUB hs
  unfold Γ'
  apply Ty.TypeJudgment.TE_VarEnv
  unfold Env.lookupTy Env.updateTy
  simp
  rfl
