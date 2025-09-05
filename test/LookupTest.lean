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
  unfold Ty.circuitCorrect
  intro x i hs hi hrow ht
  let envs := Ty.makeEnvs assertCircuit (Ast.Value.vArr x) (Ast.Value.vZ i) x.length
  let σ := envs.1
  let Γ := envs.2
  unfold lookupCircuit
  simp_all
  intro h
  apply Ty.TypeJudgment.TE_LetIn
  unfold Env.lookupTy Env.updateTy
  simp
  apply Ty.TypeJudgment.TE_LookUp
  rfl
  rfl
  rfl
  let Γ' := (Env.updateTy
    (Env.updateTy
      (Env.updateTy [] "trace"
        (((((Ast.Ty.field.refin (Ast.Predicate.ind (Ast.Expr.constBool true))).arr 2).refin
                  (Ast.Predicate.ind (Ast.Expr.constBool true))).arr
              ↑x.length).refin
          (Ast.Predicate.ind (Ast.Expr.constBool true))))
      "i"
      (Ast.Ty.int.refin (Ast.Predicate.dep "v" ((Ast.Expr.var "v").binRel Ast.RelOp.lt (Ast.Expr.constZ x.length)))))
    "u"
    (Ast.Ty.unit.refin
      (List.foldl
        (fun acc y ↦
          acc.and
            (Ast.Predicate.ind
              (Ast.exprEq y.1
                (Ast.renameVar
                  (Ast.renameVar y.2 (Env.lookupCircuit Δ "assert").ident_t
                    (Env.freshName ["trace", "i"] (Env.lookupCircuit Δ "assert").ident_t) 1000)
                  (Env.lookupCircuit Δ "assert").ident_i
                  (Env.freshName ["trace", "i"] (Env.lookupCircuit Δ "assert").ident_i) 1000))))
        (Ast.renameVarinPred
          (Ast.renameVarinPred
            (Ast.Predicate.ind
              ((((Ast.Expr.var "trace").arrIdx (Ast.Expr.var "i")).arrIdx (Ast.Expr.constZ 1)).binRel Ast.RelOp.eq
                (Ast.Expr.constF 2)))
            (Env.lookupCircuit Δ "assert").ident_t
            (Env.freshName ["trace", "i"] (Env.lookupCircuit Δ "assert").ident_t))
          (Env.lookupCircuit Δ "assert").ident_i (Env.freshName ["trace", "i"] (Env.lookupCircuit Δ "assert").ident_i))
        [(((Ast.Expr.var "trace").arrIdx (Ast.Expr.var "i")).arrIdx (Ast.Expr.constZ 0),
            ((Ast.Expr.var "trace").arrIdx (Ast.Expr.var "i")).arrIdx (Ast.Expr.constZ 1))])))
  have hs : Ty.SubtypeJudgment σ Δ Γ' (Ast.Ty.unit.refin
    (List.foldl
      (fun acc y ↦
        acc.and
          (Ast.Predicate.ind
            (Ast.exprEq y.1
              (Ast.renameVar
                (Ast.renameVar y.2 (Env.lookupCircuit Δ "assert").ident_t
                  (Env.freshName ["trace", "i"] (Env.lookupCircuit Δ "assert").ident_t) 1000)
                (Env.lookupCircuit Δ "assert").ident_i
                (Env.freshName ["trace", "i"] (Env.lookupCircuit Δ "assert").ident_i) 1000))))
      (Ast.renameVarinPred
        (Ast.renameVarinPred
          (Ast.Predicate.ind
            ((((Ast.Expr.var "trace").arrIdx (Ast.Expr.var "i")).arrIdx (Ast.Expr.constZ 1)).binRel Ast.RelOp.eq
              (Ast.Expr.constF 2)))
          (Env.lookupCircuit Δ "assert").ident_t (Env.freshName ["trace", "i"] (Env.lookupCircuit Δ "assert").ident_t))
        (Env.lookupCircuit Δ "assert").ident_i (Env.freshName ["trace", "i"] (Env.lookupCircuit Δ "assert").ident_i))
      [(((Ast.Expr.var "trace").arrIdx (Ast.Expr.var "i")).arrIdx (Ast.Expr.constZ 0),
          ((Ast.Expr.var "trace").arrIdx (Ast.Expr.var "i")).arrIdx (Ast.Expr.constZ 1))]))
         (Ast.Ty.unit.refin
    (Ast.Predicate.ind
      ((((Ast.Expr.var "trace").arrIdx (Ast.Expr.var "i")).arrIdx (Ast.Expr.constZ 0)).binRel Ast.RelOp.eq
        (Ast.Expr.constF 2)))) := by {
      apply Ty.SubtypeJudgment.TSub_Refine
      apply Ty.SubtypeJudgment.TSub_Refl
      intro v
      intro h₁
      intro h₂
      unfold PropSemantics.tyenvToProp at h₁
      have h₃ := h₁ "u"
      unfold Γ' at h₃
      unfold Env.lookupTy Env.updateTy at h₃
      simp at h₃
      unfold PropSemantics.varToProp at h₃
      unfold Env.lookupTy at h₃
      simp at h₃
      unfold Env.lookupCircuit Δ Env.freshName at h₃
      simp at h₃
      unfold Ast.renameVarinPred at h₃
      unfold Ast.renameVarinPred at h₃
      unfold Ast.renameVar at h₃
      simp at h₃
      unfold Ast.renameVar at h₃
      simp at h₃
      unfold Ast.renameVar at h₃
      simp at h₃
      unfold Ast.renameVar at h₃
      simp at h₃
      unfold Ast.renameVar at h₃
      simp at h₃
      unfold PropSemantics.predToProp at h₃
      obtain ⟨h₄,h₅⟩ := h₃
      unfold PropSemantics.predToProp at h₄ h₅
      unfold PropSemantics.exprToProp at h₄ h₅
      unfold Δ
      unfold assertCircuit
      unfold lookupCircuit
      unfold PropSemantics.predToProp
      unfold PropSemantics.exprToProp
      apply evalProp_eq_symm at h₅
      apply evalProp_eq_trans h₅ h₄
        }
  apply Ty.TypeJudgment.TE_SUB hs
  unfold Γ'
  apply Ty.TypeJudgment.TE_VarEnv
  unfold Env.lookupTy Env.updateTy
  simp
