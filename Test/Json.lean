import Mathlib.Tactic.NormNum.Core

import Runwai.Ast
import Runwai.Json

example : (Ast.Value.vF 3) = (Ast.Value.vF 3) := rfl
example : (Ast.Value.vBool true) ≠ (Ast.Value.vBool false) := by simp_all

#eval tyToJson (Ast.Ty.refin Ast.Ty.unit
    (Ast.Predicate.ind
      (Ast.Expr.binRel (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constN 1))
                       Ast.RelOp.eq (Ast.Expr.constF 2))))

#eval exprToJson (Ast.Expr.letIn "u" (Ast.Expr.assertE
              (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constN 1))
              (Ast.Expr.constF 2))
            (Ast.Expr.var "u"))

#eval exprToJson (.letIn "u₀" (.branch (Ast.exprEq (.var "i") (.constN 0))
                          (.assertE (Ast.trace_i_j "trace" "i" 0) (.constF 0))
                          (.assertE (.constF 1) (.constF 1)))
          (.letIn "u₁" (.branch (.binRel (.var "i") Ast.RelOp.lt (.uintExpr (.var "@n") Ast.IntOp.sub (.constN 1)))
                          (.assertE (Ast.trace_ip1_j "trace" "i" 0) (.fieldExpr (Ast.trace_i_j "trace" "i" 0) .add (.constF 1)))
                          (.assertE (.constF 1) (.constF 1)))
           (.var "u₁")))
