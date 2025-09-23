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
  2. A **chip environment** mapping Chip names to their declarations.
  3. A **type environment** mapping variable names to Runwai types.
-/
namespace Env

/-- A valuation environment: maps variable names to runtime `Value`s. -/
abbrev ValEnv := List (String × Ast.Value)

@[inline]
def updateVal (σ : ValEnv) (ident : String) (val : Ast.Value) : ValEnv :=
  [(ident, val)] ++ σ

@[inline]
def getVal (σ : ValEnv) (ident : String) : Ast.Value :=
  match σ.find? (·.1 = ident) with
  | some (_, v) => v
  | none        => Ast.Value.vUnit

/-- A Chip environment: maps Chip names to their `Chip`. -/
abbrev ChipEnv := List (String × Ast.Chip)
deriving instance ToExpr for ChipEnv

@[inline]
def getChip (Δ : ChipEnv) (ident : String) : Ast.Chip :=
  match Δ.find? (·.1 = ident) with
  | some (_, v) => v
  | none        => Ast.DefaultChip

@[inline]
def updateChip (Δ: ChipEnv) (ident: String) (Chip: Ast.Chip) : ChipEnv :=
  (ident, Chip) :: Δ

abbrev ChipEntry := String × Ast.Chip

initialize ChipExt : Lean.SimplePersistentEnvExtension ChipEntry ChipEnv ←
  Lean.registerSimplePersistentEnvExtension {
    addImportedFn := fun as => [],
    addEntryFn := fun m (name, Chip) => (name, Chip) :: m,
    toArrayFn := fun m => m.toArray
  }

def addChipToEnv (name : String) (Chip : Ast.Chip) : Lean.CoreM Unit := do
  Lean.modifyEnv (ChipExt.addEntry · (name, Chip))

def getChipEnv : Lean.CoreM ChipEnv := do
  let env ← Lean.getEnv
  return ChipExt.getState env

def getChipFromEnv (name : String) : Lean.CoreM (Option Ast.Chip) := do
  let env ← Lean.getEnv
  return getChip (ChipExt.getState env) name

/-- A type environment: maps variable names to Runwai `Ty`s. -/
abbrev TyEnv := List (String × Ast.Ty)

@[inline]
def updateTy (Γ: TyEnv) (ident: String) (τ: Ast.Ty) : TyEnv :=
  (ident, τ) :: Γ

@[inline]
def getTy (Γ : TyEnv) (ident : String) : Option Ast.Ty :=
  match Γ.find? (·.1 = ident) with
  | some (_, τ) => some τ
  | none        => none

/- A trace environment: maps a chip to a trace-/
abbrev TraceEnv := List (String × Ast.Value)

@[inline]
def getTrace (T: TraceEnv) (c: Ast.Chip) : Option Ast.Value :=
  match T.find? (·.1 = c.name) with
  | some (_, v) => v
  | none        => none

abbrev UsedNames := List String

@[inline]
def freshName (Η: UsedNames) (ident: String) : String :=
  if List.contains Η ident then ident ++ "'" else ident

end Env
