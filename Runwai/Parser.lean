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
declare_syntax_cat runwai_expr

-- Basic types
syntax "Field"                                 : runwai_ty
syntax "Bool"                                  : runwai_ty
syntax "Unit"                                  : runwai_ty

-- Array types: “[T: n]”
syntax "[" runwai_ty ":" num "]"                         : runwai_ty

-- Refinement types: “{ x : T | φ }”
syntax "{" runwai_ty "|" runwai_expr "}"      : runwai_ty

-- Function‐type arrow: “(x : T1) → T2”
syntax "(" ident ":" runwai_ty ")" "→" runwai_ty   : runwai_ty

---------------------------------------------------
--------------- Declare Expressions ---------------
---------------------------------------------------

-- Constants:
syntax num                                       : runwai_expr
syntax "Fp" num                                   : runwai_expr
syntax "true"                                    : runwai_expr
syntax "false"                                   : runwai_expr

-- Variables (any identifier)
syntax ident                                     : runwai_expr

-- Boolean‐operators: “e₁ ∧ e₂” or “e₁ && e₂”, “e₁ ∨ e₂” or “e₁ || e₂”
syntax runwai_expr "&&" runwai_expr                  : runwai_expr
syntax runwai_expr "||" runwai_expr                  : runwai_expr
syntax runwai_expr "and" runwai_expr                 : runwai_expr  -- alternative keyword
syntax runwai_expr "or"  runwai_expr                 : runwai_expr

-- Arithmetic ops:  “e₁ + e₂”  “e₁ - e₂”  “e₁ * e₂”
syntax runwai_expr "+" runwai_expr                   : runwai_expr
syntax runwai_expr "-" runwai_expr                   : runwai_expr
syntax runwai_expr "*" runwai_expr                   : runwai_expr
syntax runwai_expr "/" runwai_expr                   : runwai_expr

syntax runwai_expr "<+>" runwai_expr                 : runwai_expr
syntax runwai_expr "<->" runwai_expr                 : runwai_expr
syntax runwai_expr "<*>" runwai_expr                 : runwai_expr
syntax runwai_expr "</>" runwai_expr                 : runwai_expr


-- Relational:  “e₁ == e₂”  “e₁ < e₂”  “e₁ <= e₂”
syntax runwai_expr "==" runwai_expr                  : runwai_expr
syntax runwai_expr "<"  runwai_expr                  : runwai_expr
syntax runwai_expr "<=" runwai_expr                  : runwai_expr

-- Branch: if c {e₁} else {e₂}
syntax "if" runwai_expr "then" "{" runwai_expr "}" "else" "{" runwai_expr "}" : runwai_expr

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
-- syntax "circuit" ident "(" sepBy(runwai_param, ",") ")" "->" runwai_ty "{" runwai_expr "}" : runwai_circuit
syntax "circuit" ident "(" num ")" "->" runwai_ty "{" runwai_expr "}" : runwai_circuit

---------------------------------------------------
--------------- Declare File ----------------------
---------------------------------------------------

declare_syntax_cat runwai_file
syntax (runwai_circuit)+ : runwai_file

namespace Frontend

mutual
/-- Given a `Syntax` of category `runwai_ty`, return the corresponding `Ast.Ty`. -/
unsafe def elaborateType (stx : Syntax) : MetaM Ast.Ty := do
  match stx with

  -- Field and Bool
  | `(runwai_ty| Field)      => pure (Ast.Ty.refin Ast.Ty.field (Ast.Predicate.ind (Ast.Expr.constBool True)))
  | `(runwai_ty| Bool)       => pure Ast.Ty.bool
  | `(runwai_ty| Unit)       => pure Ast.Ty.unit

  -- Array type: “[T]”
  | `(runwai_ty| [ $t:runwai_ty : $n:num ]) => do
      let t' ← elaborateType t
      pure (Ast.Ty.arr t' n.getNat)

  -- Refinement: “{ x : T | φ }”
  | `(runwai_ty| { $T:runwai_ty | $φ:runwai_expr } ) => do
      let T' ← match T with
      --| `(runwai_ty| Int) => pure Ast.Ty.int
      | `(runwai_ty| Field) => pure Ast.Ty.field
      | `(runwai_ty| Bool) => pure Ast.Ty.bool
      | `(runwai_ty| Unit) => pure Ast.Ty.unit
      | _ => throwError "unsupported type syntax: {stx}"
      -- We want to turn `φ` (a Lean `term`) into an `Ast.Expr` (of Boolean sort).
      let φ' ← elaborateExpr φ
      pure (Ast.Ty.refin T' (Ast.Predicate.ind φ'))

  -- Function type: “(x : T1) → T2”
  | `(runwai_ty| ( $x:ident : $Tdom:runwai_ty ) → $Tcod:runwai_ty ) => do
      let dom ← elaborateType Tdom
      let cod ← elaborateType Tcod
      pure (Ast.Ty.func x.getId.toString dom cod)

  | _ => throwError "unsupported type syntax: {stx}"

/--
  `elaborateExpr` turns a `Syntax` node of category `runwai_expr` into an `Ast.Expr`.
  We match eagerly on every concrete‐syntax pattern we declared above.
-/
unsafe def elaborateExpr (stx : Syntax) : MetaM Ast.Expr := do
  match stx with
  | `(runwai_expr| $n:num) => do
    let v := n.getNat
    pure (Ast.Expr.constZ v)

  -- Field literal “123”: → `constF 123`
  | `(runwai_expr| Fp $n:num) => do
    let v := n.getNat
    let v' := (v: F)
    pure (Ast.Expr.constF v')

  -- Boolean literals
  | `(runwai_expr| true)  => pure (Ast.Expr.constBool True)
  | `(runwai_expr| false) => pure (Ast.Expr.constBool False)

  -- Variables (ident): “x”, “y”, etc.
  | `(runwai_expr| $x:ident) => pure (Ast.Expr.var x.getId.toString)

  -- if c {e₁} else {e₂}
  | `(runwai_expr| if $c then {$e₁} else {$e₂}) => do
    let c' ← elaborateExpr c
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.branch c' e₁' e₂')

  -- assert e₁ = e₂
  | `(runwai_expr| assert $e₁ = $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.assertE e₁' e₂')

  -- Boolean “e₁ && e₂”
  | `(runwai_expr| $e₁ && $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.boolExpr e₁' Ast.BooleanOp.and e₂')

  | `(runwai_expr| $e₁ and $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.boolExpr e₁' Ast.BooleanOp.and e₂')

  -- Boolean “e₁ || e₂”
  | `(runwai_expr| $e₁ || $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.boolExpr e₁' Ast.BooleanOp.or e₂')

  | `(runwai_expr| $e₁ or $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.boolExpr e₁' Ast.BooleanOp.or e₂')

  -- Field arithmetic: “e₁ + e₂”  “e₁ - e₂”  “e₁ * e₂”
  | `(runwai_expr| $e₁ + $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.fieldExpr e₁' Ast.FieldOp.add e₂')

  | `(runwai_expr| $e₁ - $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.fieldExpr e₁' Ast.FieldOp.sub e₂')

  | `(runwai_expr| $e₁ * $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.fieldExpr e₁' Ast.FieldOp.mul e₂')

  | `(runwai_expr| $e₁ / $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.fieldExpr e₁' Ast.FieldOp.div e₂')

  -- Relational: “e₁ == e₂”, “e₁ < e₂”, “e₁ <= e₂”
  | `(runwai_expr| $e₁ == $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.binRel e₁' Ast.RelOp.eq e₂')

  | `(runwai_expr| $e₁ < $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.binRel e₁' Ast.RelOp.lt e₂')

  | `(runwai_expr| $e₁ <= $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.binRel e₁' Ast.RelOp.le e₂')

    /-
  -- $ts,*
  -- Circuit reference: “#C (e₁, e₂, …, eN)”
  | `(runwai_expr| # $C:ident ($args:runwai_expr,*)) => do
    let name := C.getId.toString
    -- We only support a single‐argument circRef in AST, so if there are multiple args,
    -- you might want to nest them or wrap them in a tuple. For now, assume 1:
    match args.getElems.toList with
    | [a] =>
        let a'  ← elaborateExpr a
        pure (Ast.Expr.circRef name a')
    | _   => throwError "only single‐arg circuit calls supported, got {args.getElems.toList.length}"
    -/

  -- Array indexing: “a[e]”
  | `(runwai_expr| $a [ $i ] ) => do
    let a' ← elaborateExpr a
    let i' ← elaborateExpr i
    pure (Ast.Expr.arrIdx a' i')

  -- Lambda:  “lam x : T => body”
  | `(runwai_expr| lam $x:ident : $T:runwai_ty => $body) => do
    let T'   ← elaborateType T
    let b'   ← elaborateExpr body
    pure (Ast.Expr.lam x.getId.toString T' b')

  -- Application “f (a)”
  | `(runwai_expr| $f ($a)) => do
    let f' ← elaborateExpr f
    let a' ← elaborateExpr a
    pure (Ast.Expr.app f' a')

  -- Let‐binding: “let x = v in body”
  | `(runwai_expr| let $x:ident = $v in $body) => do
    let v' ← elaborateExpr v
    let b' ← elaborateExpr body
    pure (Ast.Expr.letIn x.getId.toString v' b')

  -- Catch‐all
  | _ => throwError "unsupported expression syntax: {stx}"
end

/-- Helper: elaborate a single parameter syntax `(x : T)` into `(String × Ast.Ty)`. -/
unsafe def elaborateParam (stx : Syntax) : MetaM (String × Ast.Ty) := do
  match stx with
  | `(runwai_param| $x:ident : $T:runwai_ty) => do
      let T' ← elaborateType T
      pure (x.getId.toString, T')
  | _ =>
      throwError "unsupported parameter syntax: {stx}, expected `x : T`"

-- circuit A (x1, x2, …, xn) -> T {body}
/-- Given a single `runwai_circuit` syntax, produce an `Ast.Circuit`. -/
unsafe def elaborateCircuit (stx : Syntax) : MetaM Ast.Circuit := do
  match stx with
  | `(runwai_circuit| circuit $name:ident ( $width:num ) -> $goal:runwai_ty { $body:runwai_expr } ) => do
      let nameStr  := name.getId.toString
      let width'   := width.getNat
      let goal'    ← elaborateType goal
      let body'    ← elaborateExpr body
      pure {
        name  := nameStr,
        width := width'
        goal  := goal'
        body  := body'
      }
  | _ => throwError "invalid `circuit …` syntax: {stx}"

/-- A “file” of Loda is one or more `circuit` declarations. -/
unsafe def elabLodaFile (stx : Syntax) : MetaM (Array Ast.Circuit) := do
  match stx with
  | `(runwai_file| $[$cs:runwai_circuit]*) =>
      cs.mapM fun c => elaborateCircuit c
  | _ => throwError "invalid Loda file syntax"

/--
  If you ever want to parse a string in MetaM (outside of the “command” front‐end),
  you can do something like this:
-/
unsafe def parseLodaProgram (content : String) : MetaM (List Ast.Circuit) := do
  let env ← getEnv
  let fname := `anonymous
  match Lean.Parser.runParserCategory env `runwai_file content fname.toString with
  | Except.error err => throwError err
  | Except.ok stx   =>
      let cs ← elabLodaFile stx
      pure cs.toList

end Frontend
