import Lean
import Runwai.Ast

open Lean PrettyPrinter Delaborator SubExpr


@[app_unexpander Ast.Expr.var]
def unexpVar : Unexpander
  | `($_ $x:str) =>
      let str := x.getString
      let name := mkIdent $ Name.mkSimple str
      `($name)
  | _ => throw ()

@[app_unexpander Ast.Expr.constF]
def unexpConstF : Unexpander
  | `($_ $n) =>
    let f := mkIdent $ Name.mkSimple "F"
    `($f $n)
  | _ => throw ()

@[app_unexpander Ast.Expr.constN]
def unexpConstZ : Unexpander
  | `($_ $n) => `($n)
  | _ => throw ()

@[app_unexpander Ast.Expr.arrIdx]
def unexpArrIdx : Unexpander
  | `($_ $a $i) => `($a[$i])
  | _           => throw ()

@[app_unexpander Ast.Expr.constBool]
def unexpConstBool : Unexpander
  | `($_ $b) => `($b)
  | _ => throw ()

@[app_unexpander Ast.Expr.fieldExpr]
def unexpFieldExpr : Unexpander
  | `($_ $lhs  $op $rhs) =>
    match op.raw with
    | Syntax.ident _ _ id _ =>
        if id == ``Ast.FieldOp.add then
          `($lhs + $rhs)
        else if id == ``Ast.FieldOp.sub then
          `($lhs - $rhs)
        else if id == ``Ast.FieldOp.mul then
          `($lhs * $rhs)
        else if id == ``Ast.FieldOp.div then
          `($lhs / $rhs)
        else
          `($lhs 345+ $rhs)
    | _ => `($lhs 123+ $rhs)
    --`($lhs $op $rhs)
  | _ => throw ()

@[app_unexpander Ast.Expr.boolExpr]
def unexpBoolExpr : Unexpander
  | `($_ $lhs $op $rhs) =>
    match op.raw with
    | Syntax.ident _ _ n _ =>
        if n == ``Ast.BooleanOp.and then `($lhs ∧ $rhs)
        else if n == ``Ast.BooleanOp.or  then `($lhs ∨ $rhs)
        else throw ()
    | _ => throw ()
  | _ => throw ()

@[app_unexpander Ast.Expr.binRel]
def unexpBinRel : Unexpander
  | `($_ $lhs $op $rhs) =>
    match op.raw with
    | Syntax.ident _ _ n _ =>
        if n == ``Ast.RelOp.eq then `($lhs = $rhs)
        else if n == ``Ast.RelOp.lt then `($lhs < $rhs)
        else if n == ``Ast.RelOp.le then `($lhs ≤ $rhs)
        else throw ()
    | _ => throw ()
  | _ => throw ()

@[app_unexpander Ast.Expr.assertE]
def unexpAssert : Unexpander
  | `($_ $lhs $rhs) => `(assert_eq ($lhs, $rhs))
  | _ => throw ()

@[app_unexpander Ast.Expr.branch]
def unexpBranch : Unexpander
  | `($_ $c $t $e) => `(if $c then $t else $e)
  | _ => throw ()

@[app_unexpander Ast.Expr.app]
def unexpApp : Unexpander
  | `($_ $f $a) => `($f $a)
  | _ => throw ()

@[app_unexpander Ast.Expr.letIn]
def unexpLet : Unexpander
  | `($_ $x:str $v $body) =>
      let str := x.getString
      let id := mkIdent $ Name.mkSimple str
      let f₀ := mkIdent $ Name.mkSimple "let"
      let f₁ := mkIdent $ Name.mkSimple "in"
    `($f₀ $id = $v $f₁ $body)
  | _ => throw ()

@[app_unexpander Ast.Predicate.ind]
def unexpPredInd : Unexpander
  | `($_ $e) => `($e)
  | _        => throw ()

@[app_unexpander Ast.Predicate.dep]
def unexpPredDep : Unexpander
  | `($_ $e) => `($e)
  | _        => throw ()

@[app_unexpander Ast.Ty.unknown]
def unexpTyUnknown : Unexpander
  | `($_) =>
    let id := mkIdent (Name.mkSimple "unknown")
    `($id)

@[app_unexpander Ast.Ty.unit]
def unexpTyUnit : Unexpander
  | `($_) =>
    let id := mkIdent (Name.mkSimple "uint")
    `($id)

@[app_unexpander Ast.Ty.field]
def unexpTyField : Unexpander
  | `($_) =>
    let id := mkIdent (Name.mkSimple "F")
    `($id)

@[app_unexpander Ast.Ty.int]
def unexpTyInt : Unexpander
  | `($_) =>
    let id := mkIdent (Name.mkSimple "int")
    `($id)

@[app_unexpander Ast.Ty.bool]
def unexpTyBool : Unexpander
  | `($_) =>
    let id := mkIdent (Name.mkSimple "bool")
    `($id)

/-- [T; n] -/
@[app_unexpander Ast.Ty.arr]
def unexpTyArr : Unexpander
  | `($_ $t $n) =>
    `([$t : $n])
  | _                   => throw ()

@[app_unexpander Ast.Ty.refin]
def unexpTyRefin : Unexpander
  | `($_ $t $p) =>
    let nu := mkIdent (Name.mkSimple "ν")
    match p.raw with
    | Syntax.ident _ _ n _ =>
      if n == `true then `($t)
      else `({$nu :: $t ∣ $p})
    | _ => `({$nu :: $t ∣ $p})
  | _ => throw ()

/-
@[app_unexpander Ast.Expr.binRel]
def unexpBinRel : Unexpander
  | `($_ $lhs $op $rhs) =>
    match op.raw with
    | Syntax.ident _ _ n _ =>
        if n == ``Ast.RelOp.eq then `($lhs = $rhs)
        else if n == ``Ast.RelOp.lt then `($lhs < $rhs)
        else if n == ``Ast.RelOp.le then `($lhs ≤ $rhs)
        else throw ()
    | _ => throw ()
  | _ => throw ()
-/

#check Ast.FieldOp.add
#check Ast.Expr.constF 12
#check Ast.Expr.constN 12
#check Ast.Expr.constBool true
#check Ast.Expr.constBool false
#check Ast.Ty.arr Ast.Ty.field 2
#check Ast.Ty.refin Ast.Ty.field (Ast.Predicate.ind (Ast.Expr.constF 12))
#check Ast.Ty.refin Ast.Ty.field (Ast.Predicate.ind (Ast.Expr.constBool true))
#check Ast.Ty.refin Ast.Ty.field (Ast.Predicate.ind (Ast.Expr.constBool True))
#check Ast.Expr.fieldExpr (Ast.Expr.constF 3) (Ast.FieldOp.add) (Ast.Expr.constF 4)
#check Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.constN 2)
#check Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")
#check Ast.Expr.letIn "u" (Ast.Expr.constF 123) (Ast.Expr.var "u")
