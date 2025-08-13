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
  3. A conversion of a `Circuit` into a `Prop`
     expressing its correctness w.r.t. its input/output refinements.
-/

namespace Ty

/--
  Subtyping judgment between two optional types `τ₁ → τ₂`
  under valuation `σ`, circuits `Δ`, type env `Γ`, and fuel.
-/
inductive SubtypeJudgment :
  Env.ValEnv → Env.CircuitEnv → Env.TyEnv → Option Ast.Ty → Option Ast.Ty → Prop where
  /-- TSUB-REFL: Reflexivity -/
  | TSub_Refl {σ: Env.ValEnv} {Δ: Env.CircuitEnv} {Γ: Env.TyEnv} {τ : Ast.Ty} :
      SubtypeJudgment σ Δ Γ (pure τ) (pure τ)

  /-- TSUB-TRANS: Transitivity -/
  | TSub_Trans {σ: Env.ValEnv} {Δ: Env.CircuitEnv} {Γ: Env.TyEnv} {τ₁ τ₂ τ₃ : Ast.Ty} :
      SubtypeJudgment σ Δ Γ (pure τ₁) (pure τ₂) →
      SubtypeJudgment σ Δ Γ (pure τ₂) (pure τ₃) →
      SubtypeJudgment σ Δ Γ (pure τ₁) (pure τ₃)

  --| TSub_Field {σ: Env.ValEnv} {Δ: Env.CircuitEnv} {Γ: Env.TyEnv} {φ : Ast.Predicate} :
  --    SubtypeJudgment σ Δ Γ (pure (Ast.Ty.refin Ast.Ty.field φ)) (pure Ast.Ty.field)

  /-- TSUB-REFINE: Refinement subtyping -/
  | TSub_Refine {σ: Env.ValEnv} {Δ: Env.CircuitEnv} {Γ: Env.TyEnv} {T₁ T₂ : Ast.Ty} {φ₁ φ₂ : Ast.Predicate} :
      SubtypeJudgment σ Δ Γ (pure T₁) (pure T₂) →
      (∀ v: Ast.Expr, PropSemantics.tyenvToProp σ Δ Γ → (PropSemantics.predToProp σ Δ φ₁ v → PropSemantics.predToProp σ Δ φ₂ v)) →
      SubtypeJudgment σ Δ Γ (pure (Ast.Ty.refin T₁ φ₁)) (pure (Ast.Ty.refin T₂ φ₂))

  /-- TSUB-FUN: Function subtyping -/
  | TSub_Fun {σ: Env.ValEnv} {Δ: Env.CircuitEnv} {Γ: Env.TyEnv} {x y : String} {z : Ast.Value} {τx τy τr τs : Ast.Ty} :
      SubtypeJudgment σ Δ Γ (pure τy) (pure τx) →
      -- Using a fresh variable z to avoid capture
      SubtypeJudgment (Env.updateVal (Env.updateVal σ x z) y z) Δ Γ (pure τr) (pure τs) →
      SubtypeJudgment σ Δ Γ (pure (Ast.Ty.func x τx τr)) (pure (Ast.Ty.func y τy τs))

  /-- TSUB-ARR: Array subtyping -/
  | TSub_Arr {σ: Env.ValEnv} {Δ: Env.CircuitEnv} {Γ: Env.TyEnv} {T₁ T₂ : Ast.Ty} {n: Int} :
      SubtypeJudgment σ Δ Γ (pure T₁) (pure T₂) →
      SubtypeJudgment σ Δ Γ (pure (Ast.Ty.arr T₁ n)) (pure (Ast.Ty.arr T₂ n))

/--
  Typing judgment `Γ ⊢ e : τ`: expression `e` has type `τ`
  under type environment `Γ`, valuation `σ`, circuits `Δ`, and fuel.
-/
inductive TypeJudgment {σ: Env.ValEnv} {Δ: Env.CircuitEnv}:
  Env.TyEnv → Ast.Expr → Ast.Ty → Prop where
  -- TE-VAR
  | TE_Var {Γ: Env.TyEnv} {x : String} {T: Ast.Ty}:
    ∀ φ: Ast.Predicate, Env.lookupTy Γ x = (Ast.Ty.refin T φ) →
    TypeJudgment Γ (Ast.Expr.var x) (Ast.Ty.refin T (Ast.Predicate.eq (Ast.Expr.var x)))

  | TE_VarEnv {Γ: Env.TyEnv} {x : String} {T: Ast.Ty}:
    ∀ φ: Ast.Predicate, Env.lookupTy Γ x = (Ast.Ty.refin T φ) →
    TypeJudgment Γ (Ast.Expr.var x) (Ast.Ty.refin T φ)

  -- TE-VAR-FUNC
  | TE_VarFunc {Γ: Env.TyEnv} {f x : String} {τ₁ τ₂: Ast.Ty}:
    Env.lookupTy Γ f = (Ast.Ty.func x τ₁ τ₂) →
    TypeJudgment Γ (Ast.Expr.var f) (Ast.Ty.func x τ₁ τ₂)

  --| TE_TriF {Γ: Env.TyEnv} {e: Ast.Expr}:
  --  TypeJudgment Γ e (Ast.Ty.field) →
  --  TypeJudgment Γ e (Ast.Ty.refin Ast.Ty.field (Ast.Predicate.const (Ast.Expr.constBool true)))

  -- TE-ARRY-INDEX
  | TE_ArrayIndex {Γ: Env.TyEnv} {e idx: Ast.Expr} {τ: Ast.Ty} {n: Int} {i: F} {φ: Ast.Predicate}:
    TypeJudgment Γ e (Ast.Ty.refin (Ast.Ty.arr τ n) φ) →
    Eval.EvalProp σ Δ idx (Ast.Value.vF i) →
    i.toNat ≤ n →
    TypeJudgment Γ (Ast.Expr.arrIdx e idx) τ

  -- TE-BRANCH
  | TE_Branch {Γ: Env.TyEnv} {c e₁ e₂: Ast.Expr} {τ: Ast.Ty}:
    TypeJudgment Γ e₁ τ →
    TypeJudgment Γ e₂ τ →
    TypeJudgment Γ (Ast.Expr.branch c e₁ e₂) τ

  -- TE-CONSTF
  | TE_ConstF {Γ: Env.TyEnv} {f: F} :
    TypeJudgment Γ (Ast.Expr.constF f) (Ast.Ty.refin (Ast.Ty.field) (Ast.Predicate.eq (Ast.Expr.constF f)))

  -- TE-ASSERT
  | TE_Assert {Γ: Env.TyEnv} {e₁ e₂: Ast.Expr} {φ₁ φ₂: Ast.Predicate}:
    TypeJudgment Γ e₁ (Ast.Ty.refin (Ast.Ty.field) φ₁) →
    TypeJudgment Γ e₂ (Ast.Ty.refin (Ast.Ty.field) φ₂) →
    TypeJudgment Γ (Ast.Expr.assertE e₁ e₂) (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.const (Ast.exprEq e₁ e₂)))

  -- TE-BINOPFIELD
  | TE_BinOpField {Γ: Env.TyEnv} {e₁ e₂: Ast.Expr} {φ₁ φ₂: Ast.Predicate} {op: Ast.FieldOp}:
    TypeJudgment Γ e₁ (Ast.Ty.refin (Ast.Ty.field) φ₁) →
    TypeJudgment Γ e₂ (Ast.Ty.refin (Ast.Ty.field) φ₂) →
    TypeJudgment Γ (Ast.Expr.fieldExpr e₁ op e₂) ((Ast.Ty.refin (Ast.Ty.field) (Ast.Predicate.eq (Ast.Expr.fieldExpr e₁ op e₂))))

  -- TE-ABS (function abstraction)
  | TE_Abs {Γ: Env.TyEnv} {x: String} {τ₁ τ₂: Ast.Ty} {e: Ast.Expr}:
    TypeJudgment (Env.updateTy Γ x τ₁) e (τ₂) →
    TypeJudgment Γ (Ast.Expr.lam x τ₁ e) ((Ast.Ty.func x τ₁ τ₂))

  -- TE-APP
  | TE_App {Γ: Env.TyEnv} {x₁ x₂: Ast.Expr} {s: String} {τ₁ τ₂: Ast.Ty} {v: Ast.Value}:
    TypeJudgment Γ x₁ (Ast.Ty.func s τ₁ τ₂) →
    Eval.EvalProp σ Δ x₂ v →
    TypeJudgment Γ x₂ τ₁ →
    TypeJudgment Γ (Ast.Expr.app x₁ x₂) τ₂

  -- TE_SUB
  | TE_SUB {Γ: Env.TyEnv} {e: Ast.Expr} {τ₁ τ₂: Ast.Ty}
    (h₀ : @SubtypeJudgment σ Δ Γ (some τ₁) (some τ₂))
    (ht : @TypeJudgment σ Δ Γ e τ₁) :
    TypeJudgment Γ e τ₂

  -- TE-LETIN
  | TE_LetIn {Γ: Env.TyEnv} {x : String} {e₁ e₂ : Ast.Expr} {τ₁ τ₂ : Ast.Ty}
    (h₁: @TypeJudgment σ Δ Γ e₁ τ₁)
    (h₂: @TypeJudgment σ Δ (Env.updateTy Γ x τ₁) e₂ τ₂):
    TypeJudgment Γ (Ast.Expr.letIn x e₁ e₂) τ₂

/--
If an expression `e` is typed as the refinement `{ v : τ | φ }`,
then the predicate `φ` holds under `exprToProp`.
(TODO: this is the soundness theorem that we can prove)
-/
axiom typeJudgmentRefinementSound {σ : Env.ValEnv} {Δ : Env.CircuitEnv}
 (Γ : Env.TyEnv) (τ : Ast.Ty) (e: Ast.Expr) (φ: Ast.Predicate):
  @Ty.TypeJudgment σ Δ Γ e (Ast.Ty.refin τ φ) → PropSemantics.predToProp σ Δ φ e

def makeEnvs (c : Ast.Circuit) (x : Ast.Value) : Env.ValEnv × Env.TyEnv :=
  let σ: Env.ValEnv := Env.updateVal [] c.inputs.fst x
  let Γ: Env.TyEnv := Env.updateTy [] c.inputs.fst c.inputs.snd
  (σ, Γ)

def checkInputsTypes (c : Ast.Circuit) (x: Ast.Value) : Prop :=
  match c.inputs.snd, x with
  | Ast.Ty.field, Ast.Value.vF _ => True
  | Ast.Ty.bool, Ast.Value.vBool _ => True
  | Ast.Ty.refin baseTy _, val =>
    match baseTy, val with
    | Ast.Ty.field,    Ast.Value.vF _          => True
    | Ast.Ty.bool,     Ast.Value.vBool _       => True
    | Ast.Ty.arr _ n,    Ast.Value.vArr elems  => elems.length == n
    | _,               _                       => False
  | Ast.Ty.arr _ n,    Ast.Value.vArr elems    => elems.length == n
  | _, _ => False

/--
  Correctness of a circuit `c`:
  if the input satisfies its refinement, then evaluating `c.body`
  yields a value satisfying the output refinement.
-/
def circuitCorrect (Δ : Env.CircuitEnv) (c : Ast.Circuit) : Prop :=
  ∀ (x : Ast.Value),
    x != Ast.Value.vStar →
    let (σ, Γ) := makeEnvs c x
    checkInputsTypes c x →
    PropSemantics.tyenvToProp σ Δ Γ →
    @TypeJudgment σ Δ Γ c.body c.output.snd

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
  (σ : Env.ValEnv) (Δ : Env.CircuitEnv) (Γ : Env.TyEnv)
  (x : String) (τ : Ast.Ty) (φ : Ast.Predicate)
  (hΓx : Env.lookupTy Γ x = Ast.Ty.refin τ φ)
  (hmt : PropSemantics.tyenvToProp σ Δ Γ) :
  PropSemantics.varToProp σ Δ Γ x := by
  dsimp [PropSemantics.tyenvToProp] at hmt
  have hmem : (x, Ast.Ty.refin τ φ) ∈ Γ := lookupTy_mem Γ x τ φ hΓx
  apply hmt at hmem
  simp at hmem
  exact hmem

end Ty
