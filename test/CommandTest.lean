import Runwai.Typing
import Runwai.Gadget
import Runwai.Command
import Runwai.Tactic

#runwai_register chip Assert1(trace, i, 2) -> {Unit| trace [i][1] == Fp 2} {let u = assert_eq(trace [i][1], Fp 2) in u}
#runwai_check Assert1

#runwai_register chip IsZero(trace, i, 3) -> {Unit| y == if x == Fp 0 then {Fp 1} else {Fp 0}} {
  let x = trace [i][0] in
    let y = trace [i][1] in
      let inv = trace [i][2] in
        let u₁ = assert_eq(y, ((Fp 0 - x) * inv) + Fp 1) in
          let u₂ = assert_eq(x*y, Fp 0) in u₂
}

#runwai_register chip Lookup(trace, i, 2) -> {Unit| trace [i][0] == Fp 2} {
  let u = #Assert1(trace [i][0] : trace [i][1]) in u
}

#runwai_prove Assert1 := by {
  rename_i Δ h_delta x i hs hi ht hty hσ σ Γ
  apply Ty.TypeJudgment.TE_LetIn
  · apply lookup_update_self
  · apply Ty.TypeJudgment.TE_Assert
    · auto_judgment
    . apply Ty.TypeJudgment.TE_ConstF
  . constructor;
    apply lookup_update_self
}

#runwai_prove IsZero := by {
  repeat
    apply Ty.TypeJudgment.TE_LetIn;
    · apply lookup_update_self;
    · auto_judgment;
  apply isZero_typing_soundness
  repeat apply lookup_update_ne; simp
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_self;
  repeat decide
}

#runwai_prove Lookup := by {
  rename_i Δ h_delta trace i hs hi ht he hty hσ σ Γ
  apply Ty.TypeJudgment.TE_LookUp; repeat rfl
  set τ' := (Ast.Ty.unit.refin
      (Ty.lookup_pred
        [(Ast.trace_i_j "trace" "i" 0, Ast.trace_i_j "trace" "i" 1)]
        (Env.lookupChip Δ "Assert1")
        (Ast.Predicate.ind (Ast.exprEq (Ast.trace_i_j "trace" "i" 1) (Ast.Expr.constF 2)))
        ["i", "trace"])) with hτ'
  set Γ' := (Env.updateTy
    (Env.updateTy
      (Env.updateTy [] "trace"
        (((((Ast.Ty.field.refin Ast.constTruePred).arr 2).refin Ast.constTruePred).arr trace.length).refin Ast.constTruePred))
      "i"
      (Ast.Ty.int.refin (Ast.Predicate.dep "v" ((Ast.Expr.var "v").binRel Ast.RelOp.lt (Ast.Expr.constZ trace.length)))))
    "u" τ') with hΓ'
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
      have hat : (Env.lookupChip Δ "Assert1").ident_t = "trace" := by {
        rw[h_delta]
        unfold Env.lookupChip; simp }
      have hai : (Env.lookupChip Δ "Assert1").ident_i = "i" := by {
        rw[h_delta]
        unfold Env.lookupChip; simp }
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
  rw[← h_delta]
  rw[← hτ']
  rw[← hΓ']
  simp
  apply Ty.TypeJudgment.TE_SUB
  exact hs
  apply Ty.TypeJudgment.TE_VarEnv
  unfold Env.lookupTy Γ' Env.updateTy
  simp
  rw[hτ']
}
