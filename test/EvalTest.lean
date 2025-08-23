import Mathlib.Tactic.NormNum.Core

import Runwai.Ast
import Runwai.Env
import Runwai.Eval

-- --------------------------------------------------
-- evalRelOp tests
-- --------------------------------------------------
example : Eval.evalRelOp Ast.RelOp.eq (Ast.Value.vF 2) (Ast.Value.vF 2) = some true := rfl
example : Eval.evalRelOp Ast.RelOp.lt (Ast.Value.vF 2) (Ast.Value.vF 5) = some true := rfl
example : Eval.evalRelOp Ast.RelOp.le (Ast.Value.vF 5) (Ast.Value.vF 5) = some true := rfl
example : Eval.evalRelOp Ast.RelOp.lt (Ast.Value.vBool true) (Ast.Value.vBool false) = none := rfl

def σ₀ : Env.ValEnv := []
def Δ₀ : Env.CircuitEnv := []

-- --------------------------------------------------
-- eval on basic constants & var/let
-- --------------------------------------------------
example: Eval.EvalProp σ₀ Δ₀ (.constF 42) (.vF 42) := Eval.EvalProp.ConstF
example: Eval.EvalProp σ₀ Δ₀ (.constBool false) (.vBool false) := Eval.EvalProp.ConstBool
example: Eval.EvalProp σ₀ Δ₀ (.arr [.constF 42, .constF 43]) (.vArr [.vF 42, .vF 43]) := by
  apply Eval.EvalProp.ConstArr
  rfl
  intro xe hx
  cases hx with
| head =>
  simp
  apply Eval.EvalProp.ConstF
| tail xe h₂ =>
  cases h₂ with
  | head h₃ =>
    simp
    apply Eval.EvalProp.ConstF
  | tail h₄ =>
    contradiction

def σ₁ := Env.updateVal σ₀ "y" (Ast.Value.vF 99)
example: Eval.EvalProp σ₁ Δ₀ (.var "y") (.vF 99) := by
  apply Eval.EvalProp.Var
  simp [σ₁, σ₀]
  unfold Env.updateVal Env.lookupVal
  simp_all

example: Eval.EvalProp σ₀ Δ₀
        (.letIn "z" (.constF 7) (.fieldExpr (Ast.Expr.var "z") .mul (.constF 3))) (.vF 21) := by
  apply Eval.EvalProp.Let
  apply Eval.EvalProp.ConstF
  apply Eval.EvalProp.FBinOp
  apply Eval.EvalProp.Var
  unfold Env.updateVal Env.lookupVal
  simp_all
  rfl
  apply Eval.EvalProp.ConstF
  unfold Eval.evalFieldOp
  simp_all
  rfl
