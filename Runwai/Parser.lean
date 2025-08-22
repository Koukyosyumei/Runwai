import Lean
import Lean.Meta
import Lean.Elab.Command
import Lean.Parser
import Lean.Elab

import Runwai.Ast
import Runwai.Typing
import Runwai.Field
import Runwai.Env
import Runwai.Eval

open Lean Parser
open Lean Meta

---------------------------------------------
--------------- Declare Types ---------------
---------------------------------------------
declare_syntax_cat runwai_ty

-- Basic types
syntax "Field"                                 : runwai_ty
syntax "Bool"                                  : runwai_ty

-- Array types: “[T: n]”
syntax "[" runwai_ty ":" num "]"                         : runwai_ty

-- Refinement types: “{ x : T | φ }”
syntax "{" runwai_ty "|" term "}"      : runwai_ty

-- Function‐type arrow: “(x : T1) → T2”
syntax "(" ident ":" runwai_ty ")" "→" runwai_ty   : runwai_ty

---------------------------------------------------
--------------- Declare Expressions ---------------
---------------------------------------------------
declare_syntax_cat runwai_expr

-- Constants:
syntax num                                       : runwai_expr
syntax "true"                                    : runwai_expr
syntax "false"                                   : runwai_expr

-- Variables (any identifier)
syntax ident                                     : runwai_expr

-- Boolean‐operators: “e₁ ∧ e₂” or “e₁ && e₂”, “e₁ ∨ e₂” or “e₁ || e₂”
syntax runwai_expr "&&" runwai_expr                  : runwai_expr
syntax runwai_expr "||" runwai_expr                  : runwai_expr
syntax runwai_expr "and" runwai_expr                 : runwai_expr  -- alternative keyword
syntax runwai_expr "or"  runwai_expr                 : runwai_expr

-- Integer ops:  “e₁ + e₂”  “e₁ - e₂”  “e₁ * e₂”
syntax runwai_expr "+" runwai_expr                   : runwai_expr
syntax runwai_expr "-" runwai_expr                   : runwai_expr
syntax runwai_expr "*" runwai_expr                   : runwai_expr
syntax runwai_expr "/" runwai_expr                   : runwai_expr

-- Relational:  “e₁ == e₂”  “e₁ < e₂”  “e₁ <= e₂”
syntax runwai_expr "==" runwai_expr                  : runwai_expr
syntax runwai_expr "<"  runwai_expr                  : runwai_expr
syntax runwai_expr "<=" runwai_expr                  : runwai_expr

-- Branch: if c {e₁} else {e₂}
syntax "if" runwai_expr "{" runwai_expr "}" "else" "{" runwai_expr "}" : runwai_expr

-- Assert: “assert e₁ = e₂”
syntax "assert" runwai_expr "=" runwai_expr          : runwai_expr

-- Circuit reference:  “#Name (e₁, e₂, … ,eₙ)”
-- syntax "#" ident "(" sepBy1(runwai_expr, ",") ")"  : runwai_expr

-- Array indexing: “a[e]”
syntax runwai_expr "[" runwai_expr "]"               : runwai_expr

-- Lambda:  “lam x: T => e”
syntax "lam" ident ":" runwai_ty "=>" runwai_expr    : runwai_expr

-- Application (juxtaposition) is “f a” or you can rely on precedence of “runwai_expr runwai_expr” by default.
syntax runwai_expr "(" runwai_expr ")"               : runwai_expr

-- Let‐binding: “let x = e₁ in e₂”
syntax "let" ident "=" runwai_expr "in" runwai_expr  : runwai_expr

---------------------------------------------------
--------------- Declare Param ---------------------
---------------------------------------------------
declare_syntax_cat runwai_param
syntax ident ":" runwai_ty : runwai_param

---------------------------------------------------
--------------- Declare Circuit -------------------
---------------------------------------------------
declare_syntax_cat runwai_circuit

-- circuit A (x1, x2, …, xn) -> T {body}
syntax "circuit" ident "(" sepBy(runwai_param, ",") ")" "->" runwai_ty "{" runwai_expr "}" : runwai_circuit

---------------------------------------------------
--------------- Declare File ----------------------
---------------------------------------------------

declare_syntax_cat runwai_file
syntax (runwai_circuit)+ : runwai_file

namespace Frontend

unsafe def elaborateProp (stx : Syntax) : MetaM Ast.Expr := do
  match stx with
  | `(term| $n:num) => do
      let v := n.getNat
      let v' := (v: F)
      pure (Ast.Expr.constF v')

  -- Boolean literals
  | `(term| True)  => pure (Ast.Expr.constBool True)
  | `(term| False) => pure (Ast.Expr.constBool False)

  -- Boolean variables (identifiers)  — we treat `p` as a Bool var
  | `(term| $x:ident) => pure (Ast.Expr.var x.getId.toString)

  -- ¬ φ
  | `(term| ! $φ:term) => do
      let φ' ← elaborateProp φ
      -- We could encode “¬ φ” as `boolExpr φ Not φ`, but we don’t currently have a `UnaryOp`.
      -- For now, we can say “(φ == false)”
      pure (Ast.Expr.binRel φ' Ast.RelOp.eq (Ast.Expr.constBool False))

  | `(term| $e₁:term + $e₂:term) => do
      let e₁' ← elaborateProp e₁
      let e₂' ← elaborateProp e₂
      pure (Ast.Expr.fieldExpr e₁' Ast.FieldOp.add e₂')

  | `(term| $e₁:term * $e₂:term) => do
      let e₁' ← elaborateProp e₁
      let e₂' ← elaborateProp e₂
      pure (Ast.Expr.fieldExpr e₁' Ast.FieldOp.mul e₂')

  -- φ && ψ  or φ ∧ ψ
  | `(term| $φ:term && $ψ:term) => do
      let φ' ← elaborateProp φ
      let ψ' ← elaborateProp ψ
      pure (Ast.Expr.boolExpr φ' Ast.BooleanOp.and ψ')

  | `(term| $φ:term "and" $ψ:term) => do
      let φ' ← elaborateProp φ
      let ψ' ← elaborateProp ψ
      pure (Ast.Expr.boolExpr φ' Ast.BooleanOp.and ψ')

  -- φ || ψ  or φ ∨ ψ
  | `(term| $φ:term || $ψ:term) => do
      let φ' ← elaborateProp φ
      let ψ' ← elaborateProp ψ
      pure (Ast.Expr.boolExpr φ' Ast.BooleanOp.or ψ')

  | `(term| $φ:term "or" $ψ:term) => do
      let φ' ← elaborateProp φ
      let ψ' ← elaborateProp ψ
      pure (Ast.Expr.boolExpr φ' Ast.BooleanOp.or ψ')

  -- φ == ψ
  | `(term| $φ:term == $ψ:term) => do
      let φ' ← elaborateProp φ
      let ψ' ← elaborateProp ψ
      pure (Ast.Expr.binRel φ' Ast.RelOp.eq ψ')

  -- φ < ψ
  | `(term| $φ:term < $ψ:term) => do
      let φ' ← elaborateProp φ
      let ψ' ← elaborateProp ψ
      pure (Ast.Expr.binRel φ' Ast.RelOp.lt ψ')

  -- φ <= ψ
  | `(term| $φ:term <= $ψ:term) => do
      let φ' ← elaborateProp φ
      let ψ' ← elaborateProp ψ
      pure (Ast.Expr.binRel φ' Ast.RelOp.le ψ')

  | _ => throwError "unsupported proposition syntax: {stx}"

end Frontend
