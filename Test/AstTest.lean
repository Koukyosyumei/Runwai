import Mathlib.Tactic.NormNum.Core

import Runwai.Ast

example : (Ast.Value.vF 3) = (Ast.Value.vF 3) := rfl
example : (Ast.Value.vBool true) ≠ (Ast.Value.vBool false) := by simp_all
