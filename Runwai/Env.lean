import Std.Data.HashMap.Basic

import Lean
import Lean.Elab
import Lean.Meta

import Runwai.Ast

open Lean
open Lean.Elab
open Lean.Meta

/-!
  # Environments for Runwai

  This module provides:
  1. A **valuation environment** mapping variable names to runtime values.
  2. A **circuit environment** mapping circuit names to their declarations.
  3. A **type environment** mapping variable names to Runwai types.
-/
namespace Env

/-- A valuation environment: maps variable names to runtime `Value`s. -/
abbrev ValEnv := List (String × Ast.Value)

@[inline]
def lookupVal (σ : ValEnv) (ident : String) : Ast.Value :=
  match σ.find? (·.1 = ident) with
  | some (_, v) => v
  | none        => Ast.Value.vUnit

@[inline]
def updateVal (σ : ValEnv) (ident : String) (val : Ast.Value) : ValEnv :=
  if (σ.find? (fun (x, _) => x = ident)).isSome
  then σ
  else σ ++ [(ident, val)]

/-- A circuit environment: maps circuit names to their `Circuit`. -/
abbrev CircuitEnv := List (String × Ast.Circuit)
deriving instance ToExpr for CircuitEnv

@[inline]
def lookupCircuit (Δ : CircuitEnv) (ident : String) : Ast.Circuit :=
  match Δ.find? (·.1 = ident) with
  | some (_, v) => v
  | none        => Ast.DefaultCircuit

@[inline]
def updateCircuit (Δ: CircuitEnv) (ident: String) (circuit: Ast.Circuit) : CircuitEnv :=
  (ident, circuit) :: Δ

abbrev CircuitEntry := String × Ast.Circuit

initialize circuitExt : Lean.SimplePersistentEnvExtension CircuitEntry CircuitEnv ←
  Lean.registerSimplePersistentEnvExtension {
    addImportedFn := fun as => [],
    addEntryFn := fun m (name, circuit) => (name, circuit) :: m,
    toArrayFn := fun m => m.toArray
  }

def addCircuitToEnv (name : String) (circuit : Ast.Circuit) : Lean.CoreM Unit := do
  Lean.modifyEnv (circuitExt.addEntry · (name, circuit))

def getCircuitEnv : Lean.CoreM CircuitEnv := do
  let env ← Lean.getEnv
  return circuitExt.getState env

def getCircuitFromEnv (name : String) : Lean.CoreM (Option Ast.Circuit) := do
  let env ← Lean.getEnv
  return lookupCircuit (circuitExt.getState env) name

/-- A type environment: maps variable names to Runwai `Ty`s. -/
abbrev TyEnv := List (String × Ast.Ty)

@[inline]
def updateTy (Γ: TyEnv) (ident: String) (τ: Ast.Ty) : TyEnv :=
  if (Γ.find? (fun (x, _) => x = ident)).isSome
  then Γ
  else Γ ++ [(ident, τ)]

@[inline]
def lookupTy (Γ : TyEnv) (ident : String) : Option Ast.Ty :=
  match Γ.find? (·.1 = ident) with
  | some (_, τ) => some τ
  | none        => none

theorem lookup_preserve (Γ: TyEnv) (x y: String) (τ₁ τ₂: Ast.Ty)
  (h: lookupTy Γ x = τ₁):
  lookupTy (updateTy Γ y τ₂) x = τ₁ := by
  unfold lookupTy at h ⊢
  unfold updateTy
  simp_all
  by_cases b₁: (Γ.find? (fun (x₁, _) => x₁ = x)).isSome
  by_cases b₂: (Γ.find? (fun (x₂, _) => x₂ = y)).isSome
  . simp_all
  . by_cases b₃: y = x
    . simp_all
    . simp_all
  . by_cases b₄: (List.find? (fun x ↦ decide (x.1 = y)) Γ).isSome
    . simp_all
    . simp_all
      by_cases b₅: y = x
      . simp_all
        by_cases b₆: (List.find? (fun x_1 ↦ decide (x_1.1 = x)) Γ).isSome
        . simp_all
        . simp_all
          cases hfind : List.find? (fun x_1 => decide (x_1.1 = x)) Γ
          . simp_all
          . simp_all
      . simp_all

end Env
