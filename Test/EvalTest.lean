import Mathlib.Tactic.NormNum.Core

import Runwai.Ast
import Runwai.Env
import Runwai.Eval
import Runwai.Gadget

-- --------------------------------------------------
-- evalRelOp tests
-- --------------------------------------------------
example : Eval.evalRelOp Ast.RelOp.eq (Ast.Value.vF 2) (Ast.Value.vF 2) = some true := rfl
--example : Eval.evalRelOp Ast.RelOp.lt (Ast.Value.vF 2) (Ast.Value.vF 5) = some true := rfl
--example : Eval.evalRelOp Ast.RelOp.le (Ast.Value.vF 5) (Ast.Value.vF 5) = some true := rfl
example : Eval.evalRelOp Ast.RelOp.lt (Ast.Value.vBool true) (Ast.Value.vBool false) = none := rfl

-- Signed integer relational tests
example : Eval.evalRelOp Ast.RelOp.eq (Ast.Value.vInt 5) (Ast.Value.vInt 5) = some true := rfl
example : Eval.evalRelOp Ast.RelOp.lt (Ast.Value.vInt (-3)) (Ast.Value.vInt 5) = some true := rfl
example : Eval.evalRelOp Ast.RelOp.le (Ast.Value.vInt 5) (Ast.Value.vInt 5) = some true := rfl

-- --------------------------------------------------
-- evalSIntOp tests
-- --------------------------------------------------
example : Eval.evalSIntOp Ast.IntOp.add (Ast.Value.vInt 3) (Ast.Value.vInt 7) = some (Ast.Value.vInt 10) := rfl
example : Eval.evalSIntOp Ast.IntOp.sub (Ast.Value.vInt 10) (Ast.Value.vInt 3) = some (Ast.Value.vInt 7) := rfl
example : Eval.evalSIntOp Ast.IntOp.mul (Ast.Value.vInt 4) (Ast.Value.vInt 5) = some (Ast.Value.vInt 20) := rfl
example : Eval.evalSIntOp Ast.IntOp.add (Ast.Value.vInt (-5)) (Ast.Value.vInt 3) = some (Ast.Value.vInt (-2)) := rfl

def σ₀ : Env.ValEnv := []
def Δ'₀ : Env.ChipEnv := []
def T₀ : Env.TraceEnv := []

-- --------------------------------------------------
-- eval on basic constants & var/let
-- --------------------------------------------------
example: Eval.EvalProp σ₀ T₀ Δ'₀ (.constF 42) (.vF 42) := Eval.EvalProp.ConstF
example: Eval.EvalProp σ₀ T₀ Δ'₀ (.constBool false) (.vBool false) := Eval.EvalProp.ConstBool
example: Eval.EvalProp σ₀ T₀ Δ'₀ (.constInt 42) (.vInt 42) := Eval.EvalProp.ConstInt
example: Eval.EvalProp σ₀ T₀ Δ'₀ (.constInt (-5)) (.vInt (-5)) := Eval.EvalProp.ConstInt
example: Eval.EvalProp σ₀ T₀ Δ'₀ (.arr [.constF 42, .constF 43]) (.vArr [.vF 42, .vF 43]) := by
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
example: Eval.EvalProp σ₁ T₀ Δ'₀ (.var "y") (.vF 99) := by
  apply Eval.EvalProp.Var
  simp [σ₁, σ₀]
  unfold Env.updateVal Env.getVal
  simp_all

example: Eval.EvalProp σ₀ T₀ Δ'₀
        (.letIn "z" (.constF 7) (.fieldExpr (Ast.Expr.var "z") .mul (.constF 3))) (.vF 21) := by
  apply Eval.EvalProp.Let
  apply Eval.EvalProp.ConstF
  apply Eval.EvalProp.FBinOp
  apply Eval.EvalProp.Var
  unfold Env.updateVal Env.getVal
  simp_all
  rfl
  apply Eval.EvalProp.ConstF
  unfold Eval.evalFieldOp
  simp_all
  rfl

-- Signed integer operation test
example: Eval.EvalProp σ₀ T₀ Δ'₀
        (.sintExpr (.constInt 5) .add (.constInt 3)) (.vInt 8) := by
  apply Eval.EvalProp.SIntBinOp
  apply Eval.EvalProp.ConstInt
  apply Eval.EvalProp.ConstInt
  unfold Eval.evalSIntOp
  simp_all

-- Conversion test: UtoS (Unsigned to Signed)
example: Eval.EvalProp σ₀ T₀ Δ'₀ (.UtoS (.constN 42)) (.vInt 42) := by
  apply Eval.EvalProp.UtoS
  apply Eval.EvalProp.ConstN
