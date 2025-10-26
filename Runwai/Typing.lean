--import Init.Data.List.Basic
--import Init.Data.List.Find
import Mathlib.Data.List.Basic

import Runwai.Ast
import Runwai.Env
import Runwai.Eval
import Runwai.PropSemantics

/-!
  # Subtyping and Typing Judgments for Runwai

  This module defines:
  1. A **subtyping** relation `SubtypeJudgment`
     between (optional) Runwai types under environments.
  2. A **typing** relation `TypeJudgment`
     assigning types to Runwai expressions.
  3. A conversion of a `Chip` into a `Prop`
     expressing its correctness w.r.t. its input/output refinements.
-/

namespace Ty


@[simp]
abbrev branchLabel      : String := "@branch"

@[simp]
abbrev indBaseLabel     : String := "@ind_base"

@[simp]
abbrev indStepPrevLabel : String := "@ind_step_prev"

@[simp]
abbrev indStepEqKLabel  : String := "@ind_step_eq_k"

@[simp]
abbrev heightLabel      : String := "@n"

/--
  Subtyping judgment between two optional types `τ₁ → τ₂`
  under valuation `σ`, Chips `Δ`, type env `Γ`, and fuel.
-/
inductive SubtypeJudgment :
  Env.ChipEnv → Env.TyEnv → Ast.Ty → Ast.Ty → Prop where
  /-- TSUB-REFL: Reflexivity -/
  | TSub_Refl {Δ: Env.ChipEnv} {Γ: Env.TyEnv} {τ : Ast.Ty} :
      SubtypeJudgment Δ Γ τ τ

  /-- TSUB-TRANS: Transitivity -/
  | TSub_Trans {Δ: Env.ChipEnv} {Γ: Env.TyEnv} {τ₁ τ₂ τ₃ : Ast.Ty} :
      SubtypeJudgment Δ Γ τ₁ τ₂ →
      SubtypeJudgment Δ Γ τ₂ τ₃ →
      SubtypeJudgment Δ Γ τ₁ τ₃

  /-- TSUB-REFINE: Refinement subtyping -/
  | TSub_Refine {Δ: Env.ChipEnv} {Γ: Env.TyEnv} {T₁ T₂ : Ast.Ty} {φ₁ φ₂ : Ast.Predicate} :
      SubtypeJudgment Δ Γ T₁ T₂ →
      (∀ σ: Env.ValEnv, ∀ T: Env.TraceEnv, ∀ v: Ast.Expr, PropSemantics.tyenvToProp σ T Δ Γ → (PropSemantics.predToProp σ T Δ T₁ φ₁ v → PropSemantics.predToProp σ T Δ T₂ φ₂ v)) →
      SubtypeJudgment Δ Γ (Ast.Ty.refin T₁ φ₁) (Ast.Ty.refin T₂ φ₂)

  /-- TODO: Convert this rule to a theorem/lemma via other rules-/
  | TSub_RefineInduction {Δ: Env.ChipEnv} {Γ: Env.TyEnv} {T₁ T₂ : Ast.Ty} {φ₁ φ₂ : Ast.Predicate} {b: ℕ} (i: String):
      Env.getTy Γ i = some (Ast.Ty.refin Ast.Ty.uint (Ast.Predicate.dep Ast.nu (Ast.Expr.binRel (Ast.Expr.var Ast.nu) Ast.RelOp.lt (Ast.Expr.constN b)))) →
      SubtypeJudgment Δ Γ T₁ T₂ →
      (∀ σ: Env.ValEnv, ∀ T: Env.TraceEnv, ∀ v: Ast.Expr,
        PropSemantics.tyenvToProp σ T Δ (Env.updateTy Γ indBaseLabel (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind (Ast.exprEq (.var i) (.constN 0))))) →
        PropSemantics.predToProp σ T Δ T₁ φ₁ v →
        PropSemantics.predToProp σ T Δ T₂ (Ast.renameVarinPred φ₂ i (Ast.Expr.constN 0)) v) →
      (∀ k: ℕ, ∀ σ: Env.ValEnv, ∀ T: Env.TraceEnv, ∀ v: Ast.Expr, k < b - 1 →
        PropSemantics.tyenvToProp σ T Δ
        (Env.updateTy (Env.updateTy Γ
          indStepPrevLabel (Ast.Ty.refin Ast.Ty.unit (Ast.renameVarinPred φ₂ i (Ast.Expr.constN k))))
          indStepEqKLabel  (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind (Ast.exprEq (.var i) (.constN k))))) →
        PropSemantics.predToProp σ T Δ T₁ φ₁ v →
        PropSemantics.predToProp σ T Δ T₂ (Ast.renameVarinPred φ₂ i (Ast.Expr.constN (k + 1))) v) →
      SubtypeJudgment Δ Γ (Ast.Ty.refin T₁ φ₁) (Ast.Ty.refin T₂ φ₂)

  /-- TSUB-FUN: Function subtyping -/
  | TSub_Fun {Δ: Env.ChipEnv} {Γ: Env.TyEnv} {x y z: String} {τx τy τr τs : Ast.Ty} :
      SubtypeJudgment Δ Γ τy τx →
      -- Using a fresh variable z to avoid capture
      SubtypeJudgment Δ Γ (Ast.renameTy τr x (Ast.Expr.var z)) (Ast.renameTy τs y (Ast.Expr.var z)) →
      SubtypeJudgment Δ Γ (Ast.Ty.func x τx τr) (Ast.Ty.func y τy τs)

  /-- TSUB-ARR: Array subtyping -/
  | TSub_Arr {Δ: Env.ChipEnv} {Γ: Env.TyEnv} {T₁ T₂ : Ast.Ty} {n: ℕ} :
      SubtypeJudgment Δ Γ T₁ T₂ →
      SubtypeJudgment Δ Γ (Ast.Ty.arr T₁ n) (Ast.Ty.arr T₂ n)

/--
Constructs the predicate required for a `lookup` expression. It combines the chip's goal
predicate `φ` with equality constraints for all provided `args`, ensuring variable names
are fresh to prevent capture.
-/
def lookup_pred (args: List (Ast.Expr × Ast.Expr)) (c: Ast.Chip) (φ: Ast.Predicate) (Η: Env.UsedNames): Ast.Predicate :=
  args.foldl
  (fun acc y => Ast.Predicate.and acc (Ast.Predicate.ind (Ast.exprEq y.fst (Ast.renameVar (Ast.renameVar y.snd c.ident_t (Ast.Expr.var (Env.freshName Η c.ident_t)) 1000) c.ident_i (Ast.Expr.var (Env.freshName Η c.ident_i)) 1000))))
  (Ast.renameVarinPred (Ast.renameVarinPred φ c.ident_t (Ast.Expr.var (Env.freshName Η c.ident_t))) c.ident_i (Ast.Expr.var (Env.freshName Η c.ident_i)))

/--
Updates the set of used names `Η` with the fresh names generated for a chip's trace and
instance identifiers during a `lookup`.
-/
def update_UsedNames (c: Ast.Chip) (Η: Env.UsedNames) : Env.UsedNames :=
  [Env.freshName Η c.ident_i, Env.freshName Η c.ident_t] ++ Η

/--
  Typing judgment `Γ ⊢ e : τ`: expression `e` has type `τ`
  under type environment `Γ`, valuation `σ`, Chips `Δ`, and fuel.
-/
inductive TypeJudgment {Δ: Env.ChipEnv}:
  Env.TyEnv → Env.UsedNames → Ast.Expr → Ast.Ty → Prop where
  -- TE-VAR
  | TE_Var {Γ: Env.TyEnv} {Η: Env.UsedNames} {x : String} {T: Ast.Ty} {φ: Ast.Predicate}:
    Env.getTy Γ x = (Ast.Ty.refin T φ) →
    TypeJudgment Γ Η (Ast.Expr.var x) (Ast.Ty.refin T (Ast.Predicate.dep Ast.nu (Ast.exprEq (Ast.Expr.var Ast.nu) (Ast.Expr.var x))))

  | TE_VarEnv {Γ: Env.TyEnv} {Η: Env.UsedNames} {x : String} {T: Ast.Ty} {φ: Ast.Predicate}:
    Env.getTy Γ x = (Ast.Ty.refin T φ) →
    TypeJudgment Γ Η (Ast.Expr.var x) (Ast.Ty.refin T φ)

  -- TE-VAR-FUNC
  | TE_VarFunc {Γ: Env.TyEnv} {Η: Env.UsedNames} {f x : String} {τ₁ τ₂: Ast.Ty}:
    Env.getTy Γ f = (Ast.Ty.func x τ₁ τ₂) →
    TypeJudgment Γ Η (Ast.Expr.var f) (Ast.Ty.func x τ₁ τ₂)

  -- TE-ARRY-INDEX
  | TE_ArrayIndex {Γ: Env.TyEnv} {Η: Env.UsedNames} {e idx: Ast.Expr} {τ: Ast.Ty} {n: ℕ} {φ: Ast.Predicate}:
    TypeJudgment Γ Η e (Ast.Ty.refin (Ast.Ty.arr τ n) φ) →
    TypeJudgment Γ Η idx (Ast.Ty.refin (Ast.Ty.uint) (Ast.Predicate.dep Ast.nu (Ast.Expr.binRel (Ast.Expr.var Ast.nu) Ast.RelOp.lt (Ast.Expr.constN n)))) →
    TypeJudgment Γ Η (Ast.Expr.arrIdx e idx) τ

  -- TE-BRANCH
  | TE_Branch {Γ: Env.TyEnv} {Η: Env.UsedNames} {c e₁ e₂: Ast.Expr} {τ: Ast.Ty} {φ₀ φ₁ φ₂: Ast.Predicate}:
    TypeJudgment Γ Η c  (Ast.Ty.refin Ast.Ty.bool φ₀) →
    TypeJudgment (Env.updateTy Γ (Env.freshName Η branchLabel) (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind c))) ((Env.freshName Η branchLabel) :: Η) e₁ (Ast.Ty.refin τ φ₁) →
    TypeJudgment (Env.updateTy Γ (Env.freshName Η branchLabel) (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.not (Ast.Predicate.ind c)))) ((Env.freshName Η branchLabel) :: Η) e₂ (Ast.Ty.refin τ φ₂) →
    TypeJudgment Γ Η (Ast.Expr.branch c e₁ e₂)
      (Ast.Ty.refin τ (Ast.Predicate.or
        (Ast.Predicate.and (Ast.Predicate.ind c) φ₁)
        (Ast.Predicate.and (Ast.Predicate.not (Ast.Predicate.ind c)) φ₂)))

  -- TE-CONSTF
  | TE_ConstF {Γ: Env.TyEnv} {Η: Env.UsedNames} {f: F} :
    TypeJudgment Γ Η (Ast.Expr.constF f) (Ast.Ty.refin (Ast.Ty.field) (Ast.Predicate.dep Ast.nu (Ast.exprEq (Ast.Expr.var Ast.nu) (Ast.Expr.constF f))))

  -- TE-CONSTZ
  | TE_ConstN {Γ: Env.TyEnv} {Η: Env.UsedNames} {f: ℕ} :
    TypeJudgment Γ Η (Ast.Expr.constN f) (Ast.Ty.refin (Ast.Ty.uint) (Ast.Predicate.dep Ast.nu (Ast.exprEq (Ast.Expr.var Ast.nu) (Ast.Expr.constN f))))

  -- TE-CONSTINT
  | TE_ConstInt {Γ: Env.TyEnv} {Η: Env.UsedNames} {i: ℤ} :
    TypeJudgment Γ Η (Ast.Expr.constInt i) (Ast.Ty.refin (Ast.Ty.sint) (Ast.Predicate.dep Ast.nu (Ast.exprEq (Ast.Expr.var Ast.nu) (Ast.Expr.constInt i))))

  -- TE-BOOL
  | TE_ConstBool {Γ: Env.TyEnv} {Η: Env.UsedNames} {b: Bool} :
    TypeJudgment Γ Η (Ast.Expr.constBool b) (Ast.Ty.refin (Ast.Ty.bool) (Ast.Predicate.dep Ast.nu (Ast.exprEq (Ast.Expr.var Ast.nu) (Ast.Expr.constBool b))))

  -- TE-ASSERT
  | TE_Assert {Γ: Env.TyEnv} {Η: Env.UsedNames} {e₁ e₂: Ast.Expr} {φ₁ φ₂: Ast.Predicate}:
    TypeJudgment Γ Η e₁ (Ast.Ty.refin (Ast.Ty.field) φ₁) →
    TypeJudgment Γ Η e₂ (Ast.Ty.refin (Ast.Ty.field) φ₂) →
    TypeJudgment Γ Η (Ast.Expr.assertE e₁ e₂) (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind (Ast.exprEq e₁ e₂)))

  -- TE-BINOPFIELD
  | TE_BinOpField {Γ: Env.TyEnv} {Η: Env.UsedNames} {e₁ e₂: Ast.Expr} {φ₁ φ₂: Ast.Predicate} {op: Ast.FieldOp}:
    TypeJudgment Γ Η e₁ (Ast.Ty.refin (Ast.Ty.field) φ₁) →
    TypeJudgment Γ Η e₂ (Ast.Ty.refin (Ast.Ty.field) φ₂) →
  TypeJudgment Γ Η (Ast.Expr.fieldExpr e₁ op e₂) ((Ast.Ty.refin (Ast.Ty.field) (Ast.Predicate.dep Ast.nu (Ast.exprEq (Ast.Expr.var Ast.nu) (Ast.Expr.fieldExpr e₁ op e₂)))))

  -- TE-BINOPINT
  | TE_BinOpUInt {Γ: Env.TyEnv} {Η: Env.UsedNames} {e₁ e₂: Ast.Expr} {φ₁ φ₂: Ast.Predicate} {op: Ast.IntOp}:
    TypeJudgment Γ Η e₁ (Ast.Ty.refin (Ast.Ty.uint) φ₁) →
    TypeJudgment Γ Η e₂ (Ast.Ty.refin (Ast.Ty.uint) φ₂) →
  TypeJudgment Γ Η (Ast.Expr.uintExpr e₁ op e₂) ((Ast.Ty.refin (Ast.Ty.uint) (Ast.Predicate.dep Ast.nu (Ast.exprEq (Ast.Expr.var Ast.nu) (Ast.Expr.uintExpr e₁ op e₂)))))

  -- TE-BINOPSINT
  | TE_BinOpSInt {Γ: Env.TyEnv} {Η: Env.UsedNames} {e₁ e₂: Ast.Expr} {φ₁ φ₂: Ast.Predicate} {op: Ast.IntOp}:
    TypeJudgment Γ Η e₁ (Ast.Ty.refin (Ast.Ty.sint) φ₁) →
    TypeJudgment Γ Η e₂ (Ast.Ty.refin (Ast.Ty.sint) φ₂) →
  TypeJudgment Γ Η (Ast.Expr.sintExpr e₁ op e₂) ((Ast.Ty.refin (Ast.Ty.sint) (Ast.Predicate.dep Ast.nu (Ast.exprEq (Ast.Expr.var Ast.nu) (Ast.Expr.sintExpr e₁ op e₂)))))

  -- TE-BINOPREL
  | TE_BinOpRel {Γ: Env.TyEnv} {Η: Env.UsedNames} {e₁ e₂: Ast.Expr} {τ: Ast.Ty} {φ₁ φ₂: Ast.Predicate} {op: Ast.RelOp}:
    TypeJudgment Γ Η e₁ (Ast.Ty.refin τ φ₁) →
    TypeJudgment Γ Η e₂ (Ast.Ty.refin τ φ₂) →
  TypeJudgment Γ Η (Ast.Expr.binRel e₁ op e₂) ((Ast.Ty.refin (Ast.Ty.bool) (Ast.Predicate.dep Ast.nu (Ast.exprEq (Ast.Expr.var Ast.nu) (Ast.Expr.binRel e₁ op e₂)))))

  -- TE-ABS (function abstraction)
  | TE_Abs {Γ: Env.TyEnv} {Η: Env.UsedNames} {x: String} {τ₁ τ₂: Ast.Ty} {e: Ast.Expr}:
    Env.getTy (Env.updateTy Γ x τ₁) x = τ₁ →
    TypeJudgment (Env.updateTy Γ x τ₁) Η e (τ₂) →
    TypeJudgment Γ Η (Ast.Expr.lam x τ₁ e) ((Ast.Ty.func x τ₁ τ₂))

  -- TE-APP
  | TE_App {Γ: Env.TyEnv} {Η: Env.UsedNames} {x₁ x₂: Ast.Expr} {s: String} {τ₁ τ₂ τ₂': Ast.Ty}
    (h₁: @TypeJudgment Δ Γ Η x₁ (Ast.Ty.func s τ₁ τ₂))
    (h₂: @TypeJudgment Δ Γ Η x₂ τ₁)
    (h₃: τ₂' = (Ast.renameTy τ₂ s x₂)):
    TypeJudgment Γ Η (Ast.Expr.app x₁ x₂) τ₂'

  -- TE_SUB
  | TE_SUB {Γ: Env.TyEnv} {Η: Env.UsedNames} {e: Ast.Expr} {τ₁ τ₂: Ast.Ty}
    (ht : @TypeJudgment Δ Γ Η e τ₁)
    (h₀ : SubtypeJudgment Δ Γ τ₁ τ₂) :
    TypeJudgment Γ Η e τ₂

  -- TE-LETIN
  | TE_LetIn {Γ: Env.TyEnv} {Η: Env.UsedNames} {x : String} {e₁ e₂ : Ast.Expr} {τ₁ τ₂ : Ast.Ty}
    (h₀: Env.getTy (Env.updateTy Γ x τ₁) x = τ₁)
    (h₁: @TypeJudgment Δ Γ Η e₁ τ₁)
    (h₂: @TypeJudgment Δ (Env.updateTy Γ x τ₁) Η e₂ τ₂):
    TypeJudgment Γ Η (Ast.Expr.letIn x e₁ e₂) τ₂

  -- TE-UtoS
  | TE_UtoS {Γ: Env.TyEnv} {Η: Env.UsedNames} {e: Ast.Expr} {φ: Ast.Predicate}:
    TypeJudgment Γ Η e (Ast.Ty.refin (Ast.Ty.uint) φ) →
    TypeJudgment Γ Η (Ast.Expr.UtoS e) (Ast.Ty.refin (Ast.Ty.sint) (Ast.Predicate.dep Ast.nu (Ast.exprEq (Ast.Expr.var Ast.nu) (Ast.Expr.UtoS e))))

  -- TE-StoU
  | TE_StoU {Γ: Env.TyEnv} {Η: Env.UsedNames} {e: Ast.Expr} {φ: Ast.Predicate}:
    TypeJudgment Γ Η e (Ast.Ty.refin (Ast.Ty.sint) φ) →
    TypeJudgment Γ Η (Ast.Expr.StoU e) (Ast.Ty.refin (Ast.Ty.uint) (Ast.Predicate.dep Ast.nu (Ast.exprEq (Ast.Expr.var Ast.nu) (Ast.Expr.StoU e))))

  -- TE-LOOKUP
  | TE_LookUp {Γ: Env.TyEnv} {Η: Env.UsedNames} {vname cname : String} {args: List (Ast.Expr × Ast.Expr)}
              {c: Ast.Chip} {φ φ': Ast.Predicate} {e: Ast.Expr} {τ: Ast.Ty}
    (hc: c = Env.getChip Δ cname)
    (hτ: c.goal = Ast.Ty.refin Ast.Ty.unit φ)
    (hn: φ' = lookup_pred args c φ Η)
    (h₂: @TypeJudgment Δ (Env.updateTy Γ vname (Ast.Ty.refin Ast.Ty.unit φ')) (update_UsedNames c Η) e τ):
    TypeJudgment Γ Η (Ast.Expr.lookup vname cname args e) τ

  /-
  -- TE-INDUCTIVE (TODO: convert this rule to a theorem via TSUB-REFINE)
  | TE_Inductive {Γ: Env.TyEnv} {Η: Env.UsedNames} {φ: Ast.Predicate} {e: Ast.Expr} {τ: Ast.Ty} {b: ℕ} (i: String)
    (h₀: Env.getTy Γ i = some (Ast.Ty.refin Ast.Ty.uint (Ast.Predicate.dep Ast.nu (Ast.Expr.binRel (Ast.Expr.var Ast.nu) Ast.RelOp.lt (Ast.Expr.constN b)))))
    (h₁: @TypeJudgment Δ
      (Env.updateTy Γ (Env.freshName Η indBaseLabel) (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind (Ast.exprEq (.var i) (.constN 0)))))
      ((Env.freshName Η indBaseLabel)::Η) e (Ast.Ty.refin τ (Ast.renameVarinPred φ i (Ast.Expr.constN 0))))
    (h₂: ∀ k: ℕ, k < b - 1 → @TypeJudgment Δ
      (Env.updateTy (Env.updateTy Γ
        (Env.freshName Η indStepPrevLabel) (Ast.Ty.refin Ast.Ty.unit (Ast.renameVarinPred φ i (Ast.Expr.constN k))))
        (Env.freshName Η indStepEqKLabel) (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind (Ast.exprEq (.var i) (.constN k)))))
      ([(Env.freshName Η indStepEqKLabel), (Env.freshName Η indStepPrevLabel), (Env.freshName Η indBaseLabel)] ++ Η) e (Ast.Ty.refin τ (Ast.renameVarinPred φ i (Ast.Expr.constN (k + 1)))))
    : TypeJudgment Γ Η e (Ast.Ty.refin τ φ)
  -/

/--
Creates the initial value (`σ`) and type (`Γ`) environments for verifying a chip's body.
It binds the chip's trace and instance identifiers to their expected types.
-/
def makeEnvs (c : Ast.Chip) (height: ℕ): Env.TyEnv :=
  Env.updateTy (Env.updateTy (Env.updateTy []
    c.ident_t (.refin (.arr (.refin (.arr (.refin .field
      (Ast.Predicate.ind (Ast.Expr.constBool true))) c.width) (Ast.Predicate.ind (Ast.Expr.constBool true))) height) (Ast.Predicate.dep Ast.nu (Ast.exprEq (Ast.Expr.len (.var Ast.nu)) (.constN height)))))
    c.ident_i (Ast.Ty.refin Ast.Ty.uint (Ast.Predicate.dep Ast.nu (Ast.Expr.binRel (Ast.Expr.var Ast.nu) Ast.RelOp.lt (Ast.Expr.constN height)))))
    heightLabel (Ast.Ty.refin Ast.Ty.uint (Ast.Predicate.dep Ast.nu (Ast.exprEq (Ast.Expr.var Ast.nu) (Ast.Expr.constN height))))

/--
Check of the structure of a trace. It ensures the trace is a 2D array
of field elements with the expected dimensions (`height` × `width`).
-/
def checkInputsTrace (c: Ast.Chip) (trace : Ast.Value) (height: ℕ): Prop :=
  match trace with
  | Ast.Value.vArr rows => rows.length == height ∧ ∀ r ∈ rows, match r with
    | Ast.Value.vArr cols => cols.length == c.width ∧ ∀ c ∈ cols, match c with
      | Ast.Value.vF _ => True
      | _ => False
    | _ => False
  | _ => False

/--
  Correctness of a Chip `c`:
  if the input satisfies its refinement, then evaluating `c.body`
  yields a value satisfying the output refinement.
-/
def chipCorrect (Δ : Env.ChipEnv) (c : Ast.Chip) (minimum_height: ℕ) : Prop :=
  ∀ (trace_height: ℕ),
    minimum_height ≤ trace_height →
    let Γ := makeEnvs c trace_height
    let Η := [c.ident_i, c.ident_t]
    @TypeJudgment Δ Γ Η c.body c.goal

end Ty
