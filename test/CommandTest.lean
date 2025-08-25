import Runwai.Typing
import Runwai.Gadget
import Runwai.Command
import Runwai.Tactic

#runwai_register circuit Assert1(2) -> {Unit| trace [i][1] == Fp 2} {let u = assert_eq(trace [i][1], Fp 2) in u}
#runwai_check Assert1

#runwai_register circuit IsZero(3) -> {Unit| y == if x == Fp 0 then {Fp 1} else {Fp 0}} {
  let x = trace [i][0] in
    let y = trace [i][1] in
      let inv = trace [i][2] in
        let u₁ = assert_eq(y, ((Fp 0 - x) * inv) + Fp 1) in
          let u₂ = assert_eq(x*y, Fp 0) in u₂
}

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
