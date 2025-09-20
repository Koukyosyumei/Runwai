import Runwai.Typing
import Runwai.Gadget
--import Runwai.PP
import Runwai.Tactic

import Lean.Parser.Tactic

open Lean Elab Tactic


@[simp]
def assertChip : Ast.Chip := {
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
def iszeroChip : Ast.Chip := {
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
def iszeroChip2: Ast.Chip := {
  name    := "iszero2",
  ident_t := "trace",
  ident_i := "i",
  width   := 3,
  goal    := Ast.Ty.refin Ast.Ty.unit
    (Ast.Predicate.ind
      (Ast.exprEq (.var "β") (.branch (.binRel (.var "α") (.eq) (.constF 0)) (.constF 1) (.constF 0))))
  body    := (Ast.Expr.letIn "α" (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 0))
              (Ast.Expr.letIn "β" (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 1))
                (Ast.Expr.letIn "γ" (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 2))
                  (Ast.Expr.letIn "u₁" (.app (.app (.app iszero_func (.var "α")) (.var "β")) (.var "γ"))
                     (.var "u₁"))
                )
              )
            )
}

@[simp]
def u8chip : Ast.Chip := {
  name := "u8",
  ident_t := "trace",
  ident_i := "i"
  width := 1,
  goal := Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind (Ast.Expr.binRel (Ast.Expr.toZ (Ast.trace_i_j "trace" "i" 0)) Ast.RelOp.lt (Ast.Expr.constZ 256))),
  body := Ast.Expr.assertE (Ast.Expr.constF 0) (Ast.Expr.constF 0)
}

@[simp]
def clkChip : Ast.Chip := {
  name := "clk",
  ident_t := "trace",
  ident_i := "i",
  width := 1,
  goal := Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind (Ast.Expr.branch (.binRel (.var "i") Ast.RelOp.lt (.var "n")) (Ast.exprEq (Ast.trace_i_j "trace" "i" 0) (.toF (.var "i"))) (Ast.Expr.constBool true)))
  body := (.letIn "u₀" (.branch (Ast.exprEq (.var "i") (.constZ 0))
                          (.assertE (Ast.trace_i_j "trace" "i" 0) (.constF 0))
                          (.assertE (.constF 1) (.constF 1)))
          (.letIn "u₁" (.branch (.binRel (.var "i") Ast.RelOp.lt (.integerExpr (.var "n") Ast.IntegerOp.sub (.constZ 1)))
                          (.assertE (Ast.trace_ip1_j "trace" "i" 0) (.fieldExpr (Ast.trace_i_j "trace" "i" 0) .add (.constF 1)))
                          (.assertE (.constF 1) (.constF 1)))
           (.var "u₁")))
}

abbrev trace_ci_cj (ident_t: String) (i j: ℕ) := ((Ast.Expr.var ident_t).arrIdx (Ast.Expr.constZ i)).arrIdx (Ast.Expr.constZ j)
abbrev trace_cip1_cj (ident_t: String) (i j: ℕ) := ((Ast.Expr.var ident_t).arrIdx (Ast.Expr.integerExpr (Ast.Expr.constZ i) Ast.IntegerOp.add (Ast.Expr.constZ 1))).arrIdx (Ast.Expr.constZ j)

@[simp]
def koalabearWordRangeCheckerChip : Ast.Chip := {
  name := "koalabear_word_range_checker",
  ident_t := "trace",
  ident_i := "i",
  width := 18,
  goal := Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind
    (.binRel (.integerExpr (.integerExpr (.integerExpr (.toZ (.var "alpha_0")) .add ((.integerExpr (.toZ (.var "alpha_1")) .mul (.constZ 256)))) .add ((.integerExpr (.toZ (.var "alpha_2")) .mul (.constZ (256^2))))) .add (.integerExpr (.toZ (.var "alpha_3")) .mul (.constZ (256^3))))
      .lt (.constZ 2130706433)))
  body := (.letIn "alpha_0" (Ast.trace_i_j "trace" "i" 0)
          (.letIn "alpha_1" (Ast.trace_i_j "trace" "i" 1)
          (.letIn "alpha_2" (Ast.trace_i_j "trace" "i" 2)
          (.letIn "alpha_3" (Ast.trace_i_j "trace" "i" 3)
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
          (.lookup "l₀" "u8" [(.var "alpha_0", (Ast.trace_i_j "trace" "i" 0))]
          (.lookup "l₁" "u8" [(.var "alpha_1", (Ast.trace_i_j "trace" "i" 0))]
          (.lookup "l₂" "u8" [(.var "alpha_2", (Ast.trace_i_j "trace" "i" 0))]
          (.lookup "l₃" "u8" [(.var "alpha_3", (Ast.trace_i_j "trace" "i" 0))]
          (.letIn "u₁"
            (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app
              koalabear_word_range_checker_func
                (.var "alpha_0")) (.var "alpha_1")) (.var "alpha_2")) (.var "alpha_3"))
                (.var "most_sig_byte_decomp_0")) (.var "most_sig_byte_decomp_1"))
                (.var "most_sig_byte_decomp_2")) (.var "most_sig_byte_decomp_3"))
                (.var "most_sig_byte_decomp_4")) (.var "most_sig_byte_decomp_5"))
                (.var "most_sig_byte_decomp_6")) (.var "most_sig_byte_decomp_7"))
                (.var "and_most_sig_byte_decomp_0_to_2")) (.var "and_most_sig_byte_decomp_0_to_3"))
                (.var "and_most_sig_byte_decomp_0_to_4")) (.var "and_most_sig_byte_decomp_0_to_5"))
                (.var "and_most_sig_byte_decomp_0_to_6")) (.var "and_most_sig_byte_decomp_0_to_7"))
            (.var "u₁"))))))))))))))))))))))))
}

def Δ : Env.ChipEnv := [("assert", assertChip), ("u8", u8chip)]

theorem assertChip_correct : Ty.chipCorrect Δ assertChip 1 := by
  unfold Ty.chipCorrect
  intro height hh Γ Η
  apply Ty.TypeJudgment.TE_LetIn
  · apply lookup_update_self
  · apply Ty.TypeJudgment.TE_Assert
    · apply Ty.TypeJudgment.TE_ArrayIndex
      apply Ty.TypeJudgment.TE_ArrayIndex
      apply Ty.TypeJudgment.TE_Var
      apply lookup_update_ne
      simp
      apply Ty.TypeJudgment.TE_VarEnv
      apply lookup_update_ne
      simp
      apply constZ_refine_lt
      simp
    . apply Ty.TypeJudgment.TE_ConstF
  . constructor;
    apply lookup_update_self

theorem iszeroChip_correct : Ty.chipCorrect Δ iszeroChip 1 := by
  unfold Ty.chipCorrect
  intro height hh Γ Η
  auto_trace_index
  apply isZero_typing_soundness
  repeat apply lookup_update_ne; simp
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_self;
  repeat decide

lemma eval_var_toF_eq_const_toF {σ T k i v}
    (h_lookup : Env.lookupVal σ i = (.vZ k)) :
    Eval.EvalProp σ T Δ ((Ast.Expr.var i).toF) v ↔
    Eval.EvalProp σ T Δ ((Ast.Expr.constZ k).toF) v := by {
    constructor
    {
      intro h
      cases h
      rename_i h
      cases h
      rename_i a
      rw[h_lookup] at a
      simp at a
      rw[← a]
      apply Eval.EvalProp.toF
      apply Eval.EvalProp.ConstZ
    }
    {
      intro h
      cases h
      rename_i h
      cases h
      apply Eval.EvalProp.toF
      apply Eval.EvalProp.Var
      exact h_lookup
    }
}

lemma eval_trace_i_j_eq_trace_ci_c {σ T k i trace j v}
    (h_lookup : Env.lookupVal σ i = .vZ k) :
    Eval.EvalProp σ T Δ (Ast.trace_i_j trace i j) v ↔
    Eval.EvalProp σ T Δ (trace_ci_cj trace k j) v := by {
    constructor
    {
      intro h
      cases h
      rename_i iha ihi idx
      cases ihi
      cases iha
      rename_i iha ihi idx
      cases ihi
      rename_i a
      rw[h_lookup] at a
      simp at a
      apply Eval.EvalProp.ArrIdx
      apply Eval.EvalProp.ArrIdx
      exact iha
      apply Eval.EvalProp.ConstZ
      rw[← a] at idx
      exact idx
      apply Eval.EvalProp.ConstZ
      rename_i idx' vs j
      exact idx'
    }
    {
      intro h
      cases h
      rename_i iha ihi idx
      cases ihi
      cases iha
      rename_i iha ihi idx
      cases ihi
      apply Eval.EvalProp.ArrIdx
      apply Eval.EvalProp.ArrIdx
      exact iha
      apply Eval.EvalProp.Var
      exact h_lookup
      exact idx
      apply Eval.EvalProp.ConstZ
      rename_i idx' vs'
      exact idx'
    }
}

lemma eval_exprEq_trace_eq (h_lookup : Env.lookupVal σ i = .vZ k) :
  Eval.EvalProp σ T Δ (Ast.exprEq (Ast.trace_i_j tr i j) (Ast.Expr.var i).toF) (Ast.Value.vBool true) ↔
  Eval.EvalProp σ T Δ (Ast.exprEq (trace_ci_cj tr k j) (.constF k)) (Ast.Value.vBool true) := by {
    constructor
    {
      intro h
      cases h
      rename_i ih₁ ih₂ r
      have ih₁' := (eval_trace_i_j_eq_trace_ci_c h_lookup).mp ih₁
      have ih₂' := (eval_var_toF_eq_const_toF h_lookup).mp ih₂
      apply Eval.EvalProp.Rel
      exact ih₁'
      apply Eval.EvalProp.ConstF
      cases ih₂
      rename_i h
      cases h
      rename_i a
      rw[h_lookup] at a
      simp at a
      rw[← a] at r
      exact r
    }
    {
      intro h
      cases h
      rename_i ih₁ ih₂ r
      cases ih₁
      cases ih₂
      rename_i iha ihi idx
      cases ihi
      cases iha
      rename_i iha ihi idx
      cases ihi
      rename_i v₁' idx' vs vs'
      simp [Eval.evalRelOp] at r
      cases v₁' with
      | vF => {
        simp at r
        rename_i x
        apply Eval.EvalProp.Rel
        apply Eval.EvalProp.ArrIdx
        apply Eval.EvalProp.ArrIdx
        exact iha
        apply Eval.EvalProp.Var
        exact h_lookup
        exact idx
        apply Eval.EvalProp.ConstZ
        exact vs
        apply Eval.EvalProp.toF
        apply Eval.EvalProp.Var
        exact h_lookup
        rw[r]
        simp [Eval.evalRelOp]
      }
      | _ => {
        simp at r
      }
    }
  }

lemma clp_base (hΓ: Γ = Ty.makeEnvs clkChip height) (hΓ': Γ' =
  Env.updateTy
    (Env.updateTy Γ "u₀"
      (Ast.Ty.unit.refin
        (((Ast.Predicate.ind (Ast.exprEq (Ast.Expr.var "i") (Ast.Expr.constZ 0))).and
              (Ast.Predicate.ind (Ast.exprEq (Ast.trace_i_j "trace" "i" 0) (Ast.Expr.constF 0)))).or
          ((Ast.Predicate.ind (Ast.exprEq (Ast.Expr.var "i") (Ast.Expr.constZ 0))).not.and
            (Ast.Predicate.ind (Ast.exprEq (Ast.Expr.constF 1) (Ast.Expr.constF 1)))))))
    "u₁"
    (Ast.Ty.unit.refin
      (((Ast.Predicate.ind
                ((Ast.Expr.var "i").binRel Ast.RelOp.lt
                  ((Ast.Expr.var "n").integerExpr Ast.IntegerOp.sub (Ast.Expr.constZ 1)))).and
            (Ast.Predicate.ind
              (Ast.exprEq (Ast.trace_ip1_j "trace" "i" 0)
                ((Ast.trace_i_j "trace" "i" 0).fieldExpr Ast.FieldOp.add (Ast.Expr.constF 1))))).or
        ((Ast.Predicate.ind
                ((Ast.Expr.var "i").binRel Ast.RelOp.lt
                  ((Ast.Expr.var "n").integerExpr Ast.IntegerOp.sub (Ast.Expr.constZ 1)))).not.and
          (Ast.Predicate.ind (Ast.exprEq (Ast.Expr.constF 1) (Ast.Expr.constF 1))))))) :
  @Ty.TypeJudgment Δ (Env.updateTy Γ' "u₄" (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind (Ast.exprEq (.var "i") (.constZ 0))))) Η (Ast.Expr.var "u₁")
              (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind (Ast.exprEq (Ast.trace_i_j "trace" "i" 0) (.toF (.var "i"))))) := by {
    apply Ty.TypeJudgment.TE_SUB
    apply Ty.TypeJudgment.TE_VarEnv
    rw [hΓ']
    apply lookup_update_ne
    simp
    apply Ty.SubtypeJudgment.TSub_Refine
    apply Ty.SubtypeJudgment.TSub_Refl
    intro σ T v h₁ h₂
    unfold PropSemantics.tyenvToProp at h₁
    rw [hΓ', hΓ] at h₁
    have hu₀ := h₁ "u₀" (Ast.Ty.unit.refin
              (((Ast.Predicate.ind (Ast.exprEq (Ast.Expr.var "i") (Ast.Expr.constZ 0))).and
                    (Ast.Predicate.ind (Ast.exprEq (Ast.trace_i_j "trace" "i" 0) (Ast.Expr.constF 0)))).or
                ((Ast.Predicate.ind (Ast.exprEq (Ast.Expr.var "i") (Ast.Expr.constZ 0))).not.and
                  (Ast.Predicate.ind (Ast.exprEq (Ast.Expr.constF 1) (Ast.Expr.constF 1))))))
    have hu₄ := h₁ "u₄" (Ast.Ty.unit.refin (Ast.Predicate.ind (Ast.exprEq (Ast.Expr.var "i") (Ast.Expr.constZ 0))))
    simp [Env.lookupTy, Env.updateTy] at hu₀ hu₄
    cases hu₀ with
    | inl h => {
      obtain ⟨h₁, h₂⟩ := h
      cases h₁
      rename_i ih₁ ih₂ r
      cases ih₂
      cases ih₁
      rename_i v₁ a
      cases v₁ with
      | vZ x => {
        simp at r
        cases h₂
        rename_i ih₁ ih₂ r'
        cases ih₂
        rename_i v₁'
        cases v₁' with
        | vF x => {
          simp at r'
          rw[r'] at ih₁
          rw[r] at a
          simp [PropSemantics.predToProp]
          apply Eval.EvalProp.Rel
          exact ih₁
          apply Eval.EvalProp.toF
          apply Eval.EvalProp.Var
          exact a
          simp [Eval.evalRelOp]
        }
        | _ => {
          simp at r'
        }
      }
      | _ => {
        simp at r
      }
    }
    | inr h => {
      obtain ⟨h₁, h₂⟩ := h
      contradiction
    }
              }

theorem clpChip_correct : Ty.chipCorrect Δ clkChip 2 := by {
  unfold Ty.chipCorrect
  intro height hh Γ Η
  apply Ty.TypeJudgment.TE_LetIn
  apply lookup_update_self
  apply Ty.TypeJudgment.TE_Branch
  apply Ty.TypeJudgment.TE_BinOpRel
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_ne
  simp
  apply Ty.TypeJudgment.TE_ConstZ
  apply Ty.TypeJudgment.TE_Assert
  apply Ty.TypeJudgment.TE_ArrayIndex
  apply Ty.TypeJudgment.TE_ArrayIndex
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_ne
  simp
  simp[Η, Env.freshName]
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_ne
  simp
  simp[Η, Env.freshName]
  apply constZ_refine_lt
  simp
  apply Ty.TypeJudgment.TE_ConstF
  apply Ty.TypeJudgment.TE_Assert
  apply Ty.TypeJudgment.TE_ConstF
  apply Ty.TypeJudgment.TE_ConstF

  apply Ty.TypeJudgment.TE_LetIn
  apply lookup_update_self
  apply Ty.TypeJudgment.TE_Branch
  apply Ty.TypeJudgment.TE_BinOpRel
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_ne
  simp
  apply Ty.TypeJudgment.TE_BinOpInteger
  apply Ty.TypeJudgment.TE_Var
  apply lookup_update_ne
  simp
  apply Ty.TypeJudgment.TE_ConstZ
  apply Ty.TypeJudgment.TE_Assert
  apply Ty.TypeJudgment.TE_ArrayIndex
  apply Ty.TypeJudgment.TE_ArrayIndex
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_ne
  simp
  simp[Η, Env.freshName]
  sorry
  apply constZ_refine_lt
  simp
  apply Ty.TypeJudgment.TE_BinOpField
  apply Ty.TypeJudgment.TE_ArrayIndex
  apply Ty.TypeJudgment.TE_ArrayIndex
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_ne
  simp[Η, Env.freshName]
  sorry
  apply constZ_refine_lt
  simp
  apply Ty.TypeJudgment.TE_ConstF
  apply Ty.TypeJudgment.TE_Assert
  apply Ty.TypeJudgment.TE_ConstF
  apply Ty.TypeJudgment.TE_ConstF
  set Γ' := (Env.updateTy
    (Env.updateTy Γ "u₀"
      (Ast.Ty.unit.refin
        (((Ast.Predicate.ind (Ast.exprEq (Ast.Expr.var "i") (Ast.Expr.constZ 0))).and
              (Ast.Predicate.ind (Ast.exprEq (Ast.trace_i_j "trace" "i" 0) (Ast.Expr.constF 0)))).or
          ((Ast.Predicate.ind (Ast.exprEq (Ast.Expr.var "i") (Ast.Expr.constZ 0))).not.and
            (Ast.Predicate.ind (Ast.exprEq (Ast.Expr.constF 1) (Ast.Expr.constF 1)))))))
    "u₁"
    (Ast.Ty.unit.refin
      (((Ast.Predicate.ind
                ((Ast.Expr.var "i").binRel Ast.RelOp.lt
                  ((Ast.Expr.var "n").integerExpr Ast.IntegerOp.sub (Ast.Expr.constZ 1)))).and
            (Ast.Predicate.ind
              (Ast.exprEq (Ast.trace_ip1_j "trace" "i" 0)
                ((Ast.trace_i_j "trace" "i" 0).fieldExpr Ast.FieldOp.add (Ast.Expr.constF 1))))).or
        ((Ast.Predicate.ind
                ((Ast.Expr.var "i").binRel Ast.RelOp.lt
                  ((Ast.Expr.var "n").integerExpr Ast.IntegerOp.sub (Ast.Expr.constZ 1)))).not.and
          (Ast.Predicate.ind (Ast.exprEq (Ast.Expr.constF 1) (Ast.Expr.constF 1))))))) with hΓ'
  have ih0 : @Ty.TypeJudgment Δ (Env.updateTy Γ' "u₄" (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind (Ast.exprEq (.var "i") (.constZ 0))))) Η (Ast.Expr.var "u₁")
              (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind (Ast.exprEq (Ast.trace_i_j "trace" "i" 0) (.toF (.var "i"))))) := by {
    apply clp_base
    rfl
    exact hΓ'
  }
  have ih1 : ∀ k: ℕ,
            @Ty.TypeJudgment Δ (Env.updateTy Γ' "u₄" (Ast.Ty.refin Ast.Ty.unit
                (Ast.Predicate.and (Ast.Predicate.ind (Ast.exprEq (.var "i") (.constZ k)))
                                   (Ast.Predicate.ind (Ast.exprEq (Ast.trace_i_j "trace" "i" 0) (.toF (.constZ k))))))) Η (Ast.Expr.var "u₁")
              (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind (Ast.renameVar (Ast.Expr.branch (.binRel (.var "i") Ast.RelOp.lt (.var "n")) (Ast.exprEq (Ast.trace_i_j "trace" "i" 0) (.toF (.var "i"))) (Ast.Expr.constBool true)) "i" (Ast.Expr.constZ (k + 1)) 1000))):= by {
    intro k
    apply Ty.TypeJudgment.TE_SUB
    apply Ty.TypeJudgment.TE_VarEnv
    apply lookup_update_ne
    simp
    apply Ty.SubtypeJudgment.TSub_Refine
    apply Ty.SubtypeJudgment.TSub_Refl
    intro σ T v h₁ h₂
    unfold PropSemantics.tyenvToProp at h₁
    simp[Ast.renameVar]
    have hu₀ := h₁ "n" (Ast.Ty.refin Ast.Ty.int (Ast.Predicate.dep Ast.mu (Ast.exprEq (Ast.Expr.var Ast.mu) (Ast.Expr.constZ height))))
    have hu₁ := h₁ "i" (Ast.Ty.refin Ast.Ty.int
      (Ast.Predicate.dep Ast.mu (Ast.Expr.binRel (Ast.Expr.var Ast.mu) Ast.RelOp.lt (Ast.Expr.constZ height))))
    have hu₄ := h₁ "u₄" (Ast.Ty.unit.refin
            ((Ast.Predicate.ind (Ast.exprEq (Ast.Expr.var "i") (Ast.Expr.constZ k))).and
              (Ast.Predicate.ind (Ast.exprEq (Ast.trace_i_j "trace" "i" 0) (Ast.Expr.constZ k).toF))))
    have hu₅ := h₁ "trace" (.refin (.arr (.refin (.arr (.refin .field
      (Ast.Predicate.ind (Ast.Expr.constBool true))) 1) (Ast.Predicate.ind (Ast.Expr.constBool true))) height) (Ast.Predicate.dep Ast.mu (Ast.exprEq (Ast.Expr.len (.var Ast.mu)) (.constZ height))))
    simp [Env.lookupTy, Env.updateTy, Γ', Γ, Ty.makeEnvs] at hu₀ hu₁ hu₄ hu₅
    cases hu₅
    rename_i ihf iha ihb
    cases ihf
    cases iha
    cases ihb
    rename_i ih₁ ih₂ trace_arr_length
    cases ih₂
    cases ih₁
    rename_i h
    cases h
    rename_i a
    unfold Env.lookupVal Env.updateVal at a
    simp at a
    rename_i h_trace trace_arr
    rw[a] at h_trace
    simp[Eval.evalRelOp] at trace_arr_length

    obtain ⟨h₁', h₂'⟩ := hu₄
    cases h₂'
    rename_i ih₁ ih₂ trace_i_0_val_k
    cases ih₂
    rename_i h
    cases h
    rename_i v'
    cases v' with
    | vF trace_i_0_val => {
      simp[Eval.evalRelOp] at trace_i_0_val_k
      cases h₁'
      rename_i ih₁ ih₂ r
      cases ih₂
      cases ih₁
      rename_i v' i_is_k
      cases v' with
      | vZ i_val => {
        simp[Eval.evalRelOp] at r
        rw[r] at i_is_k
        cases hu₀
        rename_i ih_f ih_a ih_b
        cases ih_f
        cases ih_a
        rename_i va' a
        cases ih_b
        rename_i ih₁ ih₂ r
        cases ih₂
        cases ih₁
        rename_i v₁' a
        unfold Env.lookupVal Env.updateVal at a
        simp at a
        cases v₁' with
        | vZ x => {
          simp[Eval.evalRelOp] at r
          rw[r] at a
          rename_i n_is_height
          rw[a] at n_is_height
          simp [PropSemantics.predToProp] at h₂
          cases h₂ with
          | inl h => {
            obtain ⟨h₁, h₂⟩ := h
            cases h₂
            rename_i trace_ip1_0_eval ih₂' r
            cases ih₂'
            rename_i ih₁' ih₂' r
            have := evalprop_deterministic ih₁ ih₁'
            rw[← this] at r
            cases ih₂'
            simp [Eval.evalFieldOp] at r
            rename_i v₁ v₂ r' i₂
            rw[← r] at r'
            cases h₁
            rename_i ih₁ ih₂ r''
            cases ih₁
            rename_i a
            rw[i_is_k] at a
            rw[← a] at r''
            cases ih₂
            rename_i ih₁ ih₂ r
            cases ih₁
            cases ih₂
            rename_i a
            rw[n_is_height] at a
            rw[← a] at r
            simp[Eval.evalIntegerOp] at r
            rw[← r] at r''
            simp[Eval.evalRelOp] at r''
            have r''' := Nat.lt_sub_iff_add_lt.mp r''
            have hb : Eval.EvalProp σ T Δ ((Ast.Expr.constZ (k + 1)).binRel Ast.RelOp.lt (Ast.Expr.var "n")) (Ast.Value.vBool true) := by {
              apply Eval.EvalProp.Rel
              apply Eval.EvalProp.ConstZ
              apply Eval.EvalProp.Var
              exact n_is_height
              simp [Eval.evalRelOp]
              exact r'''
            }
            apply Eval.EvalProp.IfTrue
            exact hb
            cases v₁ with
            | vF => {
              simp[Eval.evalRelOp] at r'
              rw[r'] at trace_ip1_0_eval
              rw[trace_i_0_val_k] at trace_ip1_0_eval
              cases trace_ip1_0_eval
              rename_i iha ihi idx_kp1
              cases ihi
              cases iha
              rename_i iha ihi idx_0
              cases ihi
              rename_i ih₁ ih₂ r
              cases ih₂
              cases ih₁
              rename_i a
              rw[i_is_k] at a
              rw[← a] at r
              simp [Eval.evalIntegerOp] at r
              rw[← r] at idx_0
              cases iha
              rename_i a
              rw[h_trace] at a
              simp at a
              rw[← a] at idx_0
              apply Eval.EvalProp.Rel
              apply Eval.EvalProp.ArrIdx
              apply Eval.EvalProp.ArrIdx
              apply Eval.EvalProp.Var
              exact h_trace
              apply Eval.EvalProp.ConstZ
              exact idx_0
              apply Eval.EvalProp.ConstZ
              exact idx_kp1
              apply Eval.EvalProp.toF
              apply Eval.EvalProp.ConstZ
              simp[Eval.evalRelOp]
            }
            | _ => {
              simp[Eval.evalRelOp] at r'
            }
          }
          | inr h => {
              have hk : k ≥ height - 1 := by {
                by_contra
                rename_i hx
                simp at hx
                obtain ⟨h₁, _⟩ := h
                have : Eval.EvalProp σ T Δ ((Ast.Expr.var "i").binRel Ast.RelOp.lt ((Ast.Expr.var "n").integerExpr Ast.IntegerOp.sub (Ast.Expr.constZ 1))) (Ast.Value.vBool true) := by {
                  apply Eval.EvalProp.Rel
                  apply Eval.EvalProp.Var
                  exact i_is_k
                  apply Eval.EvalProp.ZBinOp
                  apply Eval.EvalProp.Var
                  exact n_is_height
                  apply Eval.EvalProp.ConstZ
                  simp[Eval.evalIntegerOp]
                  rfl
                  simp[Eval.evalRelOp]
                  apply Nat.lt_sub_iff_add_lt.mpr
                  exact hx
                }
                contradiction
              }
              have : Eval.EvalProp σ T Δ ((Ast.Expr.constZ (k + 1)).binRel Ast.RelOp.lt (Ast.Expr.var "n")) (Ast.Value.vBool false) := by {
                apply Eval.EvalProp.Rel
                apply Eval.EvalProp.ConstZ
                apply Eval.EvalProp.Var
                exact n_is_height
                simp [Eval.evalRelOp]
                omega
              }
              apply Eval.EvalProp.IfFalse
              exact this
              apply Eval.EvalProp.ConstBool
          }
        }
        | _ => {
          simp[Eval.evalRelOp] at r
        }
      }
      | _ => simp[Eval.evalRelOp] at r
    }
    | _ => simp[Eval.evalRelOp] at trace_i_0_val_k
  }
  sorry
}

theorem iszeroChip2_correct : Ty.chipCorrect Δ iszeroChip2 1 := by
  unfold Ty.chipCorrect
  intro i hi Γ Η
  auto_trace_index
  apply Ty.TypeJudgment.TE_LetIn
  rfl
  apply Ty.TypeJudgment.TE_App
  apply Ty.TypeJudgment.TE_App
  apply Ty.TypeJudgment.TE_App
  apply iszero_func_typing_soundness
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_ne_of_lookup
  simp
  apply lookup_update_ne_of_lookup
  simp
  apply lookup_update_self
  rfl
  simp [Ast.renameTy, Ast.renameVarinPred, Ast.renameVar]
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_ne_of_lookup
  simp
  apply lookup_update_self
  rfl
  simp [Ast.renameTy, Ast.renameVarinPred, Ast.renameVar]
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_self
  rfl
  simp [Ast.renameTy, Ast.renameVarinPred, Ast.renameVar]
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_self

lemma eval_var_lt_of_update
  (h₀: Eval.EvalProp σ T Δ v va)
  (h₁: Eval.EvalProp σ T Δ (v.toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ t)) (Ast.Value.vBool true)):
  Eval.EvalProp (Env.updateVal σ x va) T Δ ((Ast.Expr.var x).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ t))
  (Ast.Value.vBool true) := by {
    cases h₁
    rename_i ih₁ ih₂ r
    cases ih₁
    rename_i h
    cases va with
    | vF x => {
      have := evalprop_deterministic h h₀
      simp at this
      rw[this] at r
      cases ih₂
      apply Eval.EvalProp.Rel
      apply Eval.EvalProp.toZ
      apply Eval.EvalProp.Var
      simp [Env.lookupVal, Env.updateVal]
      rfl
      apply Eval.EvalProp.ConstZ
      exact r
    }
    | _ => {
      have := evalprop_deterministic h h₀
      simp at this
    }
  }

lemma u8_lookup_refines_lt256 (x u: String)
  (h₀: Env.lookupTy Γ x = Ast.Ty.refin Ast.Ty.field φ)
  (h₁: Env.lookupTy Γ u = some ((Ast.Ty.unit.refin
          (Ty.lookup_pred [(Ast.Expr.var x, Ast.trace_i_j "trace" "i" 0)] (Env.lookupChip Δ "u8")
            (Ast.Predicate.ind ((Ast.trace_i_j "trace" "i" 0).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))
            Η))))
  (h₂: (Env.freshName Η (Env.lookupChip Δ "u8").ident_i) = new_ident_i)
  (h₃: (Env.freshName Η (Env.lookupChip Δ "u8").ident_t) = new_ident_t)
  (h₄: new_ident_t ≠ "i")
  (h₅: x ≠ Ast.mu):
  @Ty.TypeJudgment Δ Γ Η (Ast.Expr.var x)
    (Ast.Ty.refin Ast.Ty.field (Ast.Predicate.dep Ast.mu ((Ast.Expr.var Ast.mu).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))) := by {
    apply Ty.TypeJudgment.TE_SUB
    apply Ty.TypeJudgment.TE_Var
    exact h₀
    apply Ty.SubtypeJudgment.TSub_Refine
    apply Ty.SubtypeJudgment.TSub_Refl
    intro σ T v hty hp

    unfold Ty.lookup_pred at h₁
    have hu8_i : (Env.lookupChip Δ "u8").ident_i = "i" := by {
      unfold Env.lookupChip Δ
      simp
    }
    have hu8_t : (Env.lookupChip Δ "u8").ident_t = "trace" := by {
      unfold Env.lookupChip Δ
      simp
    }
    rw[h₂, h₃, hu8_i, hu8_t] at h₁
    simp [Ast.renameVarinPred, Ast.renameVar] at h₁
    rw [if_neg h₄] at h₁
    have he := tyenv_and_to_eval_exprs hty h₁
    obtain ⟨he₁,he₂⟩ := he
    have he₃ := eval_eq_then_lt he₂ he₁

    simp [PropSemantics.predToProp] at hp
    cases hp
    rename_i va ih_f ih_a ih_b

    have heq : Eval.EvalProp σ T Δ (Ast.exprEq v (Ast.Expr.var x)) (Ast.Value.vBool true) := by {
      cases ih_f
      cases ih_b
      rename_i ih₁ ih₂ r
      cases ih₁
      rename_i ih₁
      simp [Env.lookupVal, Env.updateVal] at ih₁
      rw[← ih₁] at r
      cases ih₂
      rename_i ih₂
      have : Env.lookupVal (Env.updateVal σ Ast.mu va) x = Env.lookupVal σ x := by {
        apply lookup_val_update_ne
        exact h₅
      }
      rw[this] at ih₂
      rw[← ih₂] at r
      apply Eval.EvalProp.Rel
      exact ih_a
      apply Eval.EvalProp.Var
      exact ih₂
      rw[← ih₂]
      exact r
    }
    have he₄ := eval_eq_then_lt heq he₃
    simp [PropSemantics.predToProp]
    apply Eval.EvalProp.App
    apply Eval.EvalProp.Lam
    exact ih_a
    apply eval_var_lt_of_update
    exact ih_a
    exact he₄
    }

lemma u8_freshName_ne_i : Env.freshName
    (Ty.update_UsedNames (Env.lookupChip Δ "u8")
      (Ty.update_UsedNames (Env.lookupChip Δ "u8")
        (Ty.update_UsedNames (Env.lookupChip Δ "u8")
          (Ty.update_UsedNames (Env.lookupChip Δ "u8") ["i", "trace"]))))
    (Env.lookupChip Δ "u8").ident_t ≠
  "i" := by {
    unfold Ty.update_UsedNames Env.lookupChip Δ
    simp [Env.freshName]
  }

theorem koalabearWordRangeCheckerChip_correct : Ty.chipCorrect Δ koalabearWordRangeCheckerChip 1 := by
  unfold Ty.chipCorrect
  intro height hh Γ Η
  auto_trace_index
  repeat
    apply Ty.TypeJudgment.TE_LookUp
    rfl; rfl; rfl
  apply Ty.TypeJudgment.TE_LetIn
  apply lookup_update_self
  repeat apply Ty.TypeJudgment.TE_App
  apply koalabear_word_range_checker_func_typing_soundness
  apply u8_lookup_refines_lt256 "alpha_0" "l₀"
  apply lookup_update_ne
  simp
  apply lookup_update_ne
  simp
  repeat rfl
  exact u8_freshName_ne_i
  decide
  rfl
  simp [Ast.renameTy, Ast.renameVarinPred, Ast.renameVar]
  apply u8_lookup_refines_lt256 "alpha_1" "l₁"
  apply lookup_update_ne
  simp
  apply lookup_update_ne
  simp
  repeat rfl
  exact u8_freshName_ne_i
  decide
  rfl
  simp [Ast.renameTy, Ast.renameVarinPred, Ast.renameVar]
  have hmu₀ : (Ast.mu ≠ "value_0") := by decide
  rw[if_neg hmu₀]
  rw[if_neg hmu₀]
  simp [Ast.renameVarinPred, Ast.renameVar]
  apply u8_lookup_refines_lt256 "alpha_2" "l₂"
  apply lookup_update_ne
  simp
  apply lookup_update_ne
  simp
  repeat rfl
  exact u8_freshName_ne_i
  decide
  rfl
  simp [Ast.renameTy, Ast.renameVarinPred, Ast.renameVar]
  have hmu₀ : (Ast.mu ≠ "value_0") := by decide
  rw[if_neg hmu₀]
  rw[if_neg hmu₀]
  simp [Ast.renameVarinPred, Ast.renameVar]
  have hmu₁ : (Ast.mu ≠ "value_1") := by decide
  rw[if_neg hmu₁]
  rw[if_neg hmu₁]
  simp [Ast.renameVarinPred, Ast.renameVar]
  have hmu₂ : (Ast.mu ≠ "value_2") := by decide
  rw[if_neg hmu₂]
  rw[if_neg hmu₂]
  apply u8_lookup_refines_lt256 "alpha_3" "l₃"
  apply lookup_update_ne
  simp
  apply lookup_update_self
  repeat rfl
  exact u8_freshName_ne_i
  decide
  rfl
  simp [Ast.renameTy, Ast.renameVarinPred, Ast.renameVar]
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_ne
  simp
  rfl
  apply Ty.TypeJudgment.TE_VarEnv
  simp [Ast.renameVarinPred, Ast.renameVar]
  apply lookup_update_ne
  simp
  simp [Ast.renameTy, Ast.renameVarinPred, Ast.renameVar]
  apply And.intro
  rfl
  apply And.intro
  repeat rfl
  repeat
    apply Ty.TypeJudgment.TE_VarEnv
    apply lookup_update_ne
    simp
    simp [Ast.renameTy, Ast.renameVarinPred, Ast.renameVar]
    apply And.intro
    rfl
    apply And.intro
    rfl
    rfl
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_ne
  simp
  simp [Ast.renameTy, Ast.renameVarinPred, Ast.renameVar]
  rfl
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_self
