import Runwai.Typing
import Runwai.Gadget
import Runwai.Command

#runwai_register circuit Assert1(2) -> {Unit| trace [i][1] == Fp 2} {let u = assert trace [i][1] = Fp 2 in u}
#runwai_check Assert1

#runwai_prove Assert1 := by {
  rename_i Δ h_delta x i height hs hi ht hty hσ σ Γ
  apply Ty.TypeJudgment.TE_LetIn
  · apply lookup_update_self
  · apply Ty.TypeJudgment.TE_Assert
    · apply Ty.TypeJudgment.TE_ArrayIndex; apply Ty.TypeJudgment.TE_ArrayIndex; apply Ty.TypeJudgment.TE_Var
      apply lookup_update_ne_of_lookup
      simp
      apply lookup_update_self
      apply Eval.EvalProp.Var; exact rfl
      simp
      exact hi
      apply Eval.EvalProp.ConstZ
      simp
    . apply Ty.TypeJudgment.TE_ConstF
  . constructor;
    apply lookup_update_self
}
