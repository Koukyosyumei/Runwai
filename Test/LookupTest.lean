import Runwai.Ast
import Runwai.Env
import Runwai.Eval
import Runwai.Gadget
import Runwai.Typing
--import Runwai.PP

@[simp]
def assertCircuit : Ast.Chip := {
  name    := "assert",
  ident_t := "trace",
  ident_i := "i",
  width   := 2,
  goal    := Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind (Ast.exprEq (Ast.trace_i_j "trace" "i" 1) (Ast.Expr.constF 2))),
  body    := (Ast.Expr.letIn "u" (Ast.Expr.assertE (Ast.trace_i_j "trace" "i" 1) (Ast.Expr.constF 2)) (Ast.Expr.var "u"))
}

@[simp]
def assertCircuit_2 : Ast.Chip := {
  name    := "assert_2",
  ident_t := "trace",
  ident_i := "i",
  width   := 3,
  goal    := Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind (Ast.exprEq (Ast.trace_i_j "trace" "i" 2) (Ast.Expr.constF 3))),
  body    := (Ast.Expr.letIn "u" (Ast.Expr.assertE (Ast.trace_i_j "trace" "i" 2) (Ast.Expr.constF 3)) (Ast.Expr.var "u"))
}

@[simp]
def getChip : Ast.Chip := {
  name    := "lookup",
  ident_t := "trace",
  ident_i := "i",
  width   := 2,
  goal    := Ast.Ty.refin Ast.Ty.unit
              (Ast.Predicate.ind (Ast.exprEq (Ast.trace_i_j "trace" "i" 0) (Ast.Expr.constF 2))),
  body    := Ast.Expr.lookup "u" "assert" [((Ast.trace_i_j "trace" "i" 0), (Ast.trace_i_j "trace" "i" 1))] (Ast.Expr.var "u")
}

@[simp]
def lookupChip_2 : Ast.Chip := {
  name    := "lookup_2",
  ident_t := "trace",
  ident_i := "i",
  width   := 2,
  goal    := Ast.Ty.refin Ast.Ty.unit
              (Ast.Predicate.ind (Ast.exprEq (Ast.trace_i_j "trace" "i" 1) (Ast.Expr.constF 3))),
  body    := Ast.Expr.lookup "u₁" "assert" [((Ast.trace_i_j "trace" "i" 0), (Ast.trace_i_j "trace" "i" 1))]
              (Ast.Expr.lookup "u₂" "assert_2" [((Ast.trace_i_j "trace" "i" 1), (Ast.trace_i_j "trace" "i" 2))] (Ast.Expr.var "u₂"))
}

def Δ' : Env.ChipEnv := [("assert", assertCircuit), ("assert_2", assertCircuit_2), ("lookup", getChip)]

theorem lookupChip_correct : Ty.chipCorrect Δ' getChip 1 := by
  unfold Ty.chipCorrect getChip
  intro i hi Γ Η
  apply Ty.TypeJudgment.TE_LookUp; repeat rfl
  apply Ty.TypeJudgment.TE_SUB
  apply Ty.TypeJudgment.TE_VarEnv
  unfold Env.getTy Env.updateTy
  simp
  apply And.intro
  rfl
  rfl
  apply Ty.SubtypeJudgment.TSub_Refine
  apply Ty.SubtypeJudgment.TSub_Refl
  intro σ T v h₁ h₂
  unfold PropSemantics.tyenvToProp at h₁
  have h₃ := h₁ "u"
  unfold Env.getTy Env.updateTy PropSemantics.varToProp Env.getTy at h₃
  simp at h₃
  unfold Ty.lookup_pred at h₃
  have hat : (Env.getChip Δ' "assert").ident_t = "trace" := by {
    unfold Env.getChip Δ'; simp }
  have hai : (Env.getChip Δ' "assert").ident_i = "i" := by {
    unfold Env.getChip Δ'; simp }
  rw[hat, hai] at h₃
  unfold Env.freshName at h₃
  simp at h₃
  simp [Ast.renameVarinPred, Ast.renameVar] at h₃
  obtain ⟨h₄,h₅⟩ := h₃
  simp [PropSemantics.exprToProp] at h₄ h₅ ⊢
  apply evalProp_eq_symm at h₅
  apply evalProp_eq_trans h₅ h₄

theorem lookupChip_correct_2 : Ty.chipCorrect Δ' lookupChip_2 1 := by
  unfold Ty.chipCorrect lookupChip_2
  intro i hi Γ Η
  apply Ty.TypeJudgment.TE_LookUp; repeat rfl
  apply Ty.TypeJudgment.TE_LookUp; repeat rfl
  have ht : (Ty.update_UsedNames (Env.getChip Δ' "assert") ["i", "trace"]) = ["i'", "trace'", "i", "trace"] := by {
    unfold Ty.update_UsedNames Env.getChip Δ' Env.freshName; simp
  }
  let τ' := (Ast.Ty.unit.refin
      (Ty.lookup_pred
        [(Ast.trace_i_j "trace" "i" 1, Ast.trace_i_j "trace" "i" 2)]
        (Env.getChip Δ' "assert_2")
        (Ast.Predicate.ind (Ast.exprEq (Ast.trace_i_j "trace" "i" 2) (Ast.Expr.constF 3)))
        ["i'", "trace'", "i", "trace"]))
  rw[ht]
  apply Ty.TypeJudgment.TE_SUB
  apply Ty.TypeJudgment.TE_VarEnv
  unfold Env.getTy Env.updateTy
  simp
  apply And.intro
  rfl
  rfl
  apply Ty.SubtypeJudgment.TSub_Refine
  apply Ty.SubtypeJudgment.TSub_Refl
  intro σ T v h₁ h₂
  unfold PropSemantics.tyenvToProp at h₁
  have h₃ := h₁ "u₂"
  unfold Env.getTy Env.updateTy PropSemantics.varToProp Env.getTy Ty.lookup_pred at h₃
  have hat : (Env.getChip Δ' "assert_2").ident_t = "trace" := by {unfold Env.getChip Δ'; simp }
  have hai : (Env.getChip Δ' "assert_2").ident_i = "i" := by {unfold Env.getChip Δ'; simp }
  rw[hat, hai] at h₃
  unfold Env.freshName at h₃
  simp at h₃
  simp [Ast.renameVarinPred, Ast.renameVar] at h₃
  obtain ⟨h₄,h₅⟩ := h₃
  apply evalProp_eq_symm at h₅
  apply evalProp_eq_trans h₅ h₄
