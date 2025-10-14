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
syntax "Field"                                     : runwai_ty
syntax "UInt"                                      : runwai_ty
syntax "SInt"                                      : runwai_ty
syntax "Bool"                                      : runwai_ty
syntax "Unit"                                      : runwai_ty

-- Array types: “[T: n]”
syntax "[" runwai_ty ":" num "]"                   : runwai_ty

-- Refinement types: “{ x : T | φ }”
syntax "{" runwai_ty "|" runwai_expr "}"           : runwai_ty
syntax "{" ident ":" runwai_ty "|" runwai_expr "}" : runwai_ty

-- Function‐type arrow: “(x : T1) → T2”
syntax "(" ident ":" runwai_ty ")" "→" runwai_ty   : runwai_ty

---------------------------------------------------
--------------- Declare Expressions ---------------
---------------------------------------------------

-- Constants:
syntax num                                       : runwai_expr
syntax "Fp" num                                   : runwai_expr
syntax "Sint" num                                 : runwai_expr
syntax "Sint" "-" num                             : runwai_expr
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

syntax runwai_expr "{+}" runwai_expr                 : runwai_expr
syntax runwai_expr "{-}" runwai_expr                 : runwai_expr
syntax runwai_expr "{*}" runwai_expr                 : runwai_expr

-- Relational:  “e₁ == e₂”  “e₁ < e₂”  “e₁ <= e₂”
syntax runwai_expr "==" runwai_expr                  : runwai_expr
syntax runwai_expr "<"  runwai_expr                  : runwai_expr
syntax runwai_expr "<=" runwai_expr                  : runwai_expr

-- Branch: if c {e₁} else {e₂}
syntax "if" runwai_expr "then" "{" runwai_expr "}" "else" "{" runwai_expr "}" : runwai_expr

-- Assert: “assert e₁ = e₂”
syntax "assert_eq" "(" runwai_expr "," runwai_expr ")" : runwai_expr

-- "toN"
syntax "toN" "(" runwai_expr ")"                     : runwai_expr

-- "toF"
syntax "toF" "(" runwai_expr ")"                     : runwai_expr

-- "toSInt"
syntax "toSInt" "(" runwai_expr ")"                  : runwai_expr

-- "toUInt"
syntax "toUInt" "(" runwai_expr ")"                  : runwai_expr

-- Array indexing: “a[e]”
syntax runwai_expr "[" runwai_expr "]"               : runwai_expr

-- Lambda:  “lam x: T => e”
syntax "lam" ident ":" runwai_ty "=>" runwai_expr    : runwai_expr

-- Application (juxtaposition) is “f a” or you can rely on precedence of “runwai_expr runwai_expr” by default.
syntax runwai_expr "(" runwai_expr ")"               : runwai_expr

-- Let‐binding: “let x = e₁ in e₂”
syntax "let" ident "=" runwai_expr "in" runwai_expr  : runwai_expr

syntax pair := runwai_expr ":" runwai_expr

-- Lookup: “let x = #Name (f₁:t₁, f₂:t₂, … ,fₙ:tₙ) in e”
syntax "let" ident "=" "lookup" ident "(" sepBy1(pair, ",") ")" "in" runwai_expr  : runwai_expr

syntax "(" runwai_expr ")" : runwai_expr

---------------------------------------------------
--------------- Declare Param ---------------------
---------------------------------------------------
declare_syntax_cat runwai_param
syntax ident ":" runwai_ty : runwai_param

---------------------------------------------------
--------------- Declare Chip -------------------
---------------------------------------------------
declare_syntax_cat runwai_chip

-- Chip A (trace, i, width) -> T {body}
-- syntax "Chip" ident "(" sepBy(runwai_param, ",") ")" "->" runwai_ty "{" runwai_expr "}" : runwai_chip
syntax "chip" ident "(" ident "," ident "," num ")" "->" runwai_ty "{" runwai_expr "}" : runwai_chip

---------------------------------------------------
--------------- Declare File ----------------------
---------------------------------------------------

declare_syntax_cat runwai_file
syntax (runwai_chip)+ : runwai_file

namespace Frontend

mutual
/-- Given a `Syntax` of category `runwai_ty`, return the corresponding `Ast.Ty`. -/
unsafe def elaborateType (stx : Syntax) : MetaM Ast.Ty := do
  match stx with

  -- Field and Bool
  | `(runwai_ty| Field)      => pure (Ast.Ty.refin Ast.Ty.field (Ast.Predicate.ind (Ast.Expr.constBool True)))
  | `(runwai_ty| UInt)       => pure (Ast.Ty.refin Ast.Ty.uint (Ast.Predicate.ind (Ast.Expr.constBool True)))
  | `(runwai_ty| SInt)       => pure (Ast.Ty.refin Ast.Ty.sint (Ast.Predicate.ind (Ast.Expr.constBool True)))
  | `(runwai_ty| Bool)       => pure (Ast.Ty.refin Ast.Ty.bool (Ast.Predicate.ind (Ast.Expr.constBool True)))
  | `(runwai_ty| Unit)       => pure Ast.Ty.unit

  -- Array type: “[T]”
  | `(runwai_ty| [ $t:runwai_ty : $n:num ]) => do
      let t' ← elaborateType t
      pure (Ast.Ty.arr t' n.getNat)

  -- Refinement: "{ x : T | φ }"
  | `(runwai_ty| { $T:runwai_ty | $φ:runwai_expr } ) => do
      let T' ← match T with
      | `(runwai_ty| Field) => pure Ast.Ty.field
      | `(runwai_ty| UInt) => pure Ast.Ty.uint
      | `(runwai_ty| SInt) => pure Ast.Ty.sint
      | `(runwai_ty| Bool) => pure Ast.Ty.bool
      | `(runwai_ty| Unit) => pure Ast.Ty.unit
      | _ => throwError "unsupported type syntax: {stx}"
      -- We want to turn `φ` (a Lean `term`) into an `Ast.Expr` (of Boolean sort).
      let φ' ← elaborateExpr φ
      pure (Ast.Ty.refin T' (Ast.Predicate.ind φ'))

  | `(runwai_ty| { $x:ident : $T:runwai_ty | $φ:runwai_expr } ) => do
      let T' ← match T with
      | `(runwai_ty| UInt) => pure Ast.Ty.uint
      | `(runwai_ty| SInt) => pure Ast.Ty.sint
      | `(runwai_ty| Field) => pure Ast.Ty.field
      | `(runwai_ty| Bool) => pure Ast.Ty.bool
      | `(runwai_ty| Unit) => pure Ast.Ty.unit
      | _ => throwError "unsupported type syntax: {stx}"
      let φ' ← elaborateExpr φ
      pure (Ast.Ty.refin T' (Ast.Predicate.dep x.getId.toString φ'))

  -- Function type: “(x : T1) → T2”
  | `(runwai_ty| ( $x:ident : $Tdom:runwai_ty ) → $Tcod:runwai_ty ) => do
      let dom ← elaborateType Tdom
      let cod ← elaborateType Tcod
      pure (Ast.Ty.func x.getId.toString dom cod)

  | _ => throwError "unsupported type syntax: {stx}"

unsafe def elaborateExprPair (stx : Syntax) : MetaM (Ast.Expr × Ast.Expr) := do
  match stx with
  | `(pair| $left:runwai_expr : $right:runwai_expr) => do
    let left' ← elaborateExpr left
    let right' ← elaborateExpr right
    pure (left', right')

  | _ => throwError "unsupported expression syntax: {stx}"

/--
  `elaborateExpr` turns a `Syntax` node of category `runwai_expr` into an `Ast.Expr`.
  We match eagerly on every concrete‐syntax pattern we declared above.
-/
unsafe def elaborateExpr (stx : Syntax) : MetaM Ast.Expr := do
  match stx with
  | `(runwai_expr| $n:num) => do
    let v := n.getNat
    pure (Ast.Expr.constN v)

  -- Field literal "123": → `constF 123`
  | `(runwai_expr| Fp $n:num) => do
    let v := n.getNat
    let v' := (v: F)
    pure (Ast.Expr.constF v')

  -- Signed integer literals "Sint 123": → `constInt 123`
  | `(runwai_expr| Sint $n:num) => do
    let v := n.getNat
    let v' := (v: ℤ)
    pure (Ast.Expr.constInt v')

  -- Signed integer literals "Sint - 123": → `constInt -123`
  | `(runwai_expr| Sint - $n:num) => do
    let v := n.getNat
    let v' := -(v: ℤ)
    pure (Ast.Expr.constInt v')

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
  | `(runwai_expr| assert_eq ($e₁, $e₂)) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.assertE e₁' e₂')

  -- Boolean “e₁ && e₂”
  | `(runwai_expr| $e₁ && $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.boolExpr e₁' Ast.BoolOp.and e₂')

  | `(runwai_expr| $e₁ and $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.boolExpr e₁' Ast.BoolOp.and e₂')

  -- Boolean “e₁ || e₂”
  | `(runwai_expr| $e₁ || $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.boolExpr e₁' Ast.BoolOp.or e₂')

  | `(runwai_expr| $e₁ or $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.boolExpr e₁' Ast.BoolOp.or e₂')

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

  -- UInt arithmetic
  | `(runwai_expr| $e₁ <+> $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.uintExpr e₁' Ast.IntOp.add e₂')

  | `(runwai_expr| $e₁ <-> $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.uintExpr e₁' Ast.IntOp.sub e₂')

  | `(runwai_expr| $e₁ <*> $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.uintExpr e₁' Ast.IntOp.mul e₂')

  -- SInt arithmetic
  | `(runwai_expr| $e₁ {+} $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.sintExpr e₁' Ast.IntOp.add e₂')

  | `(runwai_expr| $e₁ {-} $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.sintExpr e₁' Ast.IntOp.sub e₂')

  | `(runwai_expr| $e₁ {*} $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.sintExpr e₁' Ast.IntOp.mul e₂')

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

  -- Conversion
  | `(runwai_expr| toN ($e)) => do
    let e' ← elaborateExpr e
    pure (Ast.Expr.toN e')

  | `(runwai_expr| toF ($e)) => do
    let e' ← elaborateExpr e
    pure (Ast.Expr.toF e')

  | `(runwai_expr| toSInt ($e)) => do
    let e' ← elaborateExpr e
    pure (Ast.Expr.toSInt e')

  | `(runwai_expr| toUInt ($e)) => do
    let e' ← elaborateExpr e
    pure (Ast.Expr.toUInt e')

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

  -- Lookup: “let x = lookup Name (f₁:t₁, f₂:t₂, … ,fₙ:tₙ) in e”
  | `(runwai_expr| let $vname:ident = lookup $cname:ident ($args:pair,*) in $body) => do
    let args' ← args.getElems.toList.mapM elaborateExprPair
    let b' ← elaborateExpr body
    pure (Ast.Expr.lookup vname.getId.toString cname.getId.toString args' b')

  | `(runwai_expr| ($e)) => do
    elaborateExpr e

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

-- Chip A (x1, x2, …, xn) -> T {body}
/-- Given a single `runwai_chip` syntax, produce an `Ast.Chip`. -/
unsafe def elaborateChip (stx : Syntax) : MetaM Ast.Chip := do
  match stx with
  | `(runwai_chip| chip $name:ident ( $ident_t:ident, $ident_i:ident, $width:num ) -> $goal:runwai_ty { $body:runwai_expr } ) => do
      let goal'    ← elaborateType goal
      let body'    ← elaborateExpr body
      pure {
        name    := name.getId.toString,
        ident_t := ident_t.getId.toString
        ident_i := ident_i.getId.toString
        width   := width.getNat
        goal    := goal'
        body    := body'
      }
  | _ => throwError "invalid `Chip …` syntax: {stx}"

/-- A “file” of Loda is one or more `Chip` declarations. -/
unsafe def elabLodaFile (stx : Syntax) : MetaM (Array Ast.Chip) := do
  match stx with
  | `(runwai_file| $[$cs:runwai_chip]*) =>
      cs.mapM fun c => elaborateChip c
  | _ => throwError "invalid Loda file syntax"

/--
  If you ever want to parse a string in MetaM (outside of the “command” front‐end),
  you can do something like this:
-/
unsafe def parseLodaProgram (content : String) : MetaM (List Ast.Chip) := do
  let env ← getEnv
  let fname := `anonymous
  match Lean.Parser.runParserCategory env `runwai_file content fname.toString with
  | Except.error err => throwError err
  | Except.ok stx   =>
      let cs ← elabLodaFile stx
      pure cs.toList

end Frontend
