import Init.Data.List.Basic
import Init.Data.List.Find
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

/--
  Subtyping judgment between two optional types `τ₁ → τ₂`
  under valuation `σ`, Chips `Δ`, type env `Γ`, and fuel.
-/
inductive SubtypeJudgment :
  Env.ValEnv → Env.ChipEnv → Env.TyEnv → Ast.Ty → Ast.Ty → Prop where
  /-- TSUB-REFL: Reflexivity -/
  | TSub_Refl {σ: Env.ValEnv} {Δ: Env.ChipEnv} {Γ: Env.TyEnv} {τ : Ast.Ty} :
      SubtypeJudgment σ Δ Γ τ τ

  /-- TSUB-TRANS: Transitivity -/
  | TSub_Trans {σ: Env.ValEnv} {Δ: Env.ChipEnv} {Γ: Env.TyEnv} {τ₁ τ₂ τ₃ : Ast.Ty} :
      SubtypeJudgment σ Δ Γ τ₁ τ₂ →
      SubtypeJudgment σ Δ Γ τ₂ τ₃ →
      SubtypeJudgment σ Δ Γ τ₁ τ₃

  /-- TSUB-REFINE: Refinement subtyping -/
  | TSub_Refine {σ: Env.ValEnv} {Δ: Env.ChipEnv} {Γ: Env.TyEnv} {T₁ T₂ : Ast.Ty} {φ₁ φ₂ : Ast.Predicate} :
      SubtypeJudgment σ Δ Γ T₁ T₂ →
      (∀ v: Ast.Expr, PropSemantics.tyenvToProp σ Δ Γ → (PropSemantics.predToProp σ Δ T₁ φ₁ v → PropSemantics.predToProp σ Δ T₂ φ₂ v)) →
      SubtypeJudgment σ Δ Γ (Ast.Ty.refin T₁ φ₁) (Ast.Ty.refin T₂ φ₂)

  /-- TSUB-FUN: Function subtyping -/
  | TSub_Fun {σ: Env.ValEnv} {Δ: Env.ChipEnv} {Γ: Env.TyEnv} {x y : String} {z : Ast.Value} {τx τy τr τs : Ast.Ty} :
      SubtypeJudgment σ Δ Γ τy τx →
      -- Using a fresh variable z to avoid capture
      SubtypeJudgment (Env.updateVal (Env.updateVal σ x z) y z) Δ Γ τr τs →
      SubtypeJudgment σ Δ Γ (Ast.Ty.func x τx τr) (Ast.Ty.func y τy τs)

  /-- TSUB-ARR: Array subtyping -/
  | TSub_Arr {σ: Env.ValEnv} {Δ: Env.ChipEnv} {Γ: Env.TyEnv} {T₁ T₂ : Ast.Ty} {n: Int} :
      SubtypeJudgment σ Δ Γ T₁ T₂ →
      SubtypeJudgment σ Δ Γ (Ast.Ty.arr T₁ n) (Ast.Ty.arr T₂ n)

def lookup_pred (args: List (Ast.Expr × Ast.Expr)) (c: Ast.Chip) (φ: Ast.Predicate) (Η: Env.UsedNames): Ast.Predicate :=
  args.foldl
  (fun acc y => Ast.Predicate.and acc (Ast.Predicate.ind (Ast.exprEq y.fst (Ast.renameVar (Ast.renameVar y.snd c.ident_t (Env.freshName Η c.ident_t) 1000) c.ident_i (Env.freshName Η c.ident_i) 1000))))
  (Ast.renameVarinPred (Ast.renameVarinPred φ c.ident_t (Env.freshName Η c.ident_t))
                        c.ident_i (Env.freshName Η c.ident_i))

def update_UsedNames (c: Ast.Chip) (Η: Env.UsedNames) : Env.UsedNames :=
  [Env.freshName Η c.ident_i, Env.freshName Η c.ident_t] ++ Η

/--
  Typing judgment `Γ ⊢ e : τ`: expression `e` has type `τ`
  under type environment `Γ`, valuation `σ`, Chips `Δ`, and fuel.
-/
inductive TypeJudgment {σ: Env.ValEnv} {Δ: Env.ChipEnv}:
  Env.TyEnv → Env.UsedNames → Ast.Expr → Ast.Ty → Prop where
  -- TE-VAR
  | TE_Var {Γ: Env.TyEnv} {Η: Env.UsedNames} {x : String} {T: Ast.Ty}:
    ∀ φ: Ast.Predicate, Env.lookupTy Γ x = (Ast.Ty.refin T φ) →
    TypeJudgment Γ Η (Ast.Expr.var x) (Ast.Ty.refin T (Ast.Predicate.dep "v" (Ast.exprEq (Ast.Expr.var "v") (Ast.Expr.var x))))

  | TE_VarEnv {Γ: Env.TyEnv} {Η: Env.UsedNames} {x : String} {T: Ast.Ty}:
    ∀ φ: Ast.Predicate, Env.lookupTy Γ x = (Ast.Ty.refin T φ) →
    TypeJudgment Γ Η (Ast.Expr.var x) (Ast.Ty.refin T φ)

  -- TE-VAR-FUNC
  | TE_VarFunc {Γ: Env.TyEnv} {Η: Env.UsedNames} {f x : String} {τ₁ τ₂: Ast.Ty}:
    Env.lookupTy Γ f = (Ast.Ty.func x τ₁ τ₂) →
    TypeJudgment Γ Η (Ast.Expr.var f) (Ast.Ty.func x τ₁ τ₂)

  -- TE-ARRY-INDEX
  | TE_ArrayIndex {Γ: Env.TyEnv} {Η: Env.UsedNames} {e idx: Ast.Expr} {τ: Ast.Ty} {n: Int} {i: ℕ} {φ: Ast.Predicate}:
    TypeJudgment Γ Η e (Ast.Ty.refin (Ast.Ty.arr τ n) φ) →
    Eval.EvalProp σ Δ idx (Ast.Value.vZ i) →
    i < n →
    TypeJudgment Γ Η (Ast.Expr.arrIdx e idx) τ

  -- TE-BRANCH
  | TE_Branch {Γ: Env.TyEnv} {Η: Env.UsedNames} {c e₁ e₂: Ast.Expr} {τ: Ast.Ty}:
    TypeJudgment Γ Η e₁ τ →
    TypeJudgment Γ Η e₂ τ →
    TypeJudgment Γ Η (Ast.Expr.branch c e₁ e₂) τ

  -- TE-CONSTF
  | TE_ConstF {Γ: Env.TyEnv} {Η: Env.UsedNames} {f: F} :
    TypeJudgment Γ Η (Ast.Expr.constF f) (Ast.Ty.refin (Ast.Ty.field) (Ast.Predicate.dep "v" (Ast.exprEq (Ast.Expr.var "v") (Ast.Expr.constF f))))

  -- TE-CONSTZ
  | TE_ConstZ {Γ: Env.TyEnv} {Η: Env.UsedNames} {f: ℕ} :
    TypeJudgment Γ Η (Ast.Expr.constZ f) (Ast.Ty.refin (Ast.Ty.int) (Ast.Predicate.dep "v" (Ast.exprEq (Ast.Expr.var "v") (Ast.Expr.constZ f))))

  -- TE-ASSERT
  | TE_Assert {Γ: Env.TyEnv} {Η: Env.UsedNames} {e₁ e₂: Ast.Expr} {φ₁ φ₂: Ast.Predicate}:
    TypeJudgment Γ Η e₁ (Ast.Ty.refin (Ast.Ty.field) φ₁) →
    TypeJudgment Γ Η e₂ (Ast.Ty.refin (Ast.Ty.field) φ₂) →
    TypeJudgment Γ Η (Ast.Expr.assertE e₁ e₂) (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind (Ast.exprEq e₁ e₂)))

  -- TE-BINOPFIELD
  | TE_BinOpField {Γ: Env.TyEnv} {Η: Env.UsedNames} {e₁ e₂: Ast.Expr} {φ₁ φ₂: Ast.Predicate} {op: Ast.FieldOp}:
    TypeJudgment Γ Η e₁ (Ast.Ty.refin (Ast.Ty.field) φ₁) →
    TypeJudgment Γ Η e₂ (Ast.Ty.refin (Ast.Ty.field) φ₂) →
  TypeJudgment Γ Η (Ast.Expr.fieldExpr e₁ op e₂) ((Ast.Ty.refin (Ast.Ty.field) (Ast.Predicate.dep "v" (Ast.exprEq (Ast.Expr.var "v") (Ast.Expr.fieldExpr e₁ op e₂)))))

  -- TE-BINOPINT
  | TE_BinOpInteger {Γ: Env.TyEnv} {Η: Env.UsedNames} {e₁ e₂: Ast.Expr} {φ₁ φ₂: Ast.Predicate} {op: Ast.IntegerOp}:
    TypeJudgment Γ Η e₁ (Ast.Ty.refin (Ast.Ty.int) φ₁) →
    TypeJudgment Γ Η e₂ (Ast.Ty.refin (Ast.Ty.int) φ₂) →
  TypeJudgment Γ Η (Ast.Expr.integerExpr e₁ op e₂) ((Ast.Ty.refin (Ast.Ty.int) (Ast.Predicate.dep "v" (Ast.exprEq (Ast.Expr.var "v") (Ast.Expr.integerExpr e₁ op e₂)))))

  -- TE-ABS (function abstraction)
  | TE_Abs {Γ: Env.TyEnv} {Η: Env.UsedNames} {x: String} {τ₁ τ₂: Ast.Ty} {e: Ast.Expr}:
    Env.lookupTy (Env.updateTy Γ x τ₁) x = τ₁ →
    TypeJudgment (Env.updateTy Γ x τ₁) Η e (τ₂) →
    TypeJudgment Γ Η (Ast.Expr.lam x τ₁ e) ((Ast.Ty.func x τ₁ τ₂))

  -- TE-APP
  | TE_App {Γ: Env.TyEnv} {Η: Env.UsedNames} {x₁ x₂: Ast.Expr} {s: String} {τ₁ τ₂: Ast.Ty} {x₂_v: Ast.Value}:
    TypeJudgment Γ Η x₁ (Ast.Ty.func s τ₁ τ₂) →
    Eval.EvalProp σ Δ x₂ x₂_v →
    TypeJudgment Γ Η x₂ τ₁ →
    TypeJudgment Γ Η (Ast.Expr.app x₁ x₂) τ₂

  -- TE_SUB
  | TE_SUB {Γ: Env.TyEnv} {Η: Env.UsedNames} {e: Ast.Expr} {τ₁ τ₂: Ast.Ty}
    (h₀ : @SubtypeJudgment σ Δ Γ τ₁ τ₂)
    (ht : @TypeJudgment σ Δ Γ Η e τ₁) :
    TypeJudgment Γ Η e τ₂

  -- TE-LETIN
  | TE_LetIn {Γ: Env.TyEnv} {Η: Env.UsedNames} {x : String} {e₁ e₂ : Ast.Expr} {τ₁ τ₂ : Ast.Ty}
    (h₀: Env.lookupTy (Env.updateTy Γ x τ₁) x = τ₁)
    (h₁: @TypeJudgment σ Δ Γ Η e₁ τ₁)
    (h₂: @TypeJudgment σ Δ (Env.updateTy Γ x τ₁) Η e₂ τ₂):
    TypeJudgment Γ Η (Ast.Expr.letIn x e₁ e₂) τ₂

  -- TE-LOOKUP
  | TE_LookUp {Γ: Env.TyEnv} {Η: Env.UsedNames} {vname cname : String} {args: List (Ast.Expr × Ast.Expr)}
              {c: Ast.Chip} {φ φ': Ast.Predicate} {e: Ast.Expr} {τ: Ast.Ty}
    (hc: c = Env.lookupChip Δ cname)
    (hτ: c.goal = Ast.Ty.refin Ast.Ty.unit φ)
    (hn: φ' = lookup_pred args c φ Η)
    (h₂: @TypeJudgment σ Δ (Env.updateTy Γ vname (Ast.Ty.refin Ast.Ty.unit φ')) (update_UsedNames c Η) e τ):
    TypeJudgment Γ Η (Ast.Expr.lookup vname cname args e) τ

/-
/--
If an expression `e` is typed as the refinement `{ v : τ | φ }`,
then the predicate `φ` holds under `exprToProp`.
(TODO: this is the soundness theorem that we can prove)
-/
axiom typeJudgmentRefinementSound {σ : Env.ValEnv} {Δ : Env.ChipEnv}
 (Γ : Env.TyEnv) (τ : Ast.Ty) (e: Ast.Expr) (φ: Ast.Predicate):
  @Ty.TypeJudgment σ Δ Γ e (Ast.Ty.refin τ φ) → PropSemantics.predToProp σ Δ φ e
-/

def makeEnvs (c : Ast.Chip) (trace : Ast.Value) (i: Ast.Value) (height: ℕ): Env.ValEnv × Env.TyEnv :=
  let σ: Env.ValEnv := Env.updateVal (Env.updateVal [] c.ident_t trace) c.ident_i i
  let Γ: Env.TyEnv := Env.updateTy (Env.updateTy [] c.ident_t
    (.refin (.arr (.refin (.arr (.refin .field
      (Ast.Predicate.ind (Ast.Expr.constBool true))) c.width) (Ast.Predicate.ind (Ast.Expr.constBool true))) height) (Ast.Predicate.ind (Ast.Expr.constBool true))))
    c.ident_i (Ast.Ty.refin Ast.Ty.int (Ast.Predicate.dep "v" (Ast.Expr.binRel (Ast.Expr.var "v") Ast.RelOp.lt (Ast.Expr.constZ height))))
  (σ, Γ)

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
def ChipCorrect (Δ : Env.ChipEnv) (c : Ast.Chip) (minimum_height: ℕ) : Prop :=
  ∀ (trace: List Ast.Value) (i: ℕ),
    minimum_height ≤ trace.length →
    i < trace.length →
    (∃ row: List Ast.Value, (trace.get? i = some (Ast.Value.vArr row))) →
    let (σ, Γ) := makeEnvs c (Ast.Value.vArr trace) (Ast.Value.vZ i) trace.length
    let Η := [c.ident_i, c.ident_t]
    checkInputsTrace c (Ast.Value.vArr trace) trace.length →
    PropSemantics.tyenvToProp σ Δ Γ →
    @TypeJudgment σ Δ Γ Η c.body c.goal

lemma lookupTy_mem (Γ: Env.TyEnv) (x: String) (τ :Ast.Ty) (φ: Ast.Predicate)
  (h : Env.lookupTy Γ x = Ast.Ty.refin τ φ) :
  (x, Ast.Ty.refin τ φ) ∈ Γ := by
  dsimp [Env.lookupTy] at h
  cases hfind : Γ.find? (·.1 = x) with
  | none =>
    simp [hfind] at h
  | some p =>
    simp [hfind] at h
    have eq_p := List.find?_some hfind
    have p_1_eq_x : p.1 = x := by simp_all
    have mem_p : p ∈ Γ := List.mem_of_find?_eq_some hfind
    cases p with
    | mk y τ' =>
      simp_all

lemma tyenvToProp_implies_varToProp
  (σ : Env.ValEnv) (Δ : Env.ChipEnv) (Γ : Env.TyEnv)
  (x : String) (τ : Ast.Ty) (φ : Ast.Predicate)
  (hΓx : Env.lookupTy Γ x = Ast.Ty.refin τ φ)
  (hmt : PropSemantics.tyenvToProp σ Δ Γ) :
  PropSemantics.varToProp σ Δ Γ x := by
  dsimp [PropSemantics.tyenvToProp] at hmt
  apply hmt
  exact hΓx

end Ty
