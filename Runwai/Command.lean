import Lean.Meta
import Lean.Elab.Command
import Lean.Parser
import Lean.Elab

import Runwai.Parser

open Lean Parser
open Lean Meta

syntax (name := runwai_register) "#runwai_register" runwai_circuit : command
syntax (name := runwai_check) "#runwai_check" ident : command
syntax (name := runwai_prove) "#runwai_prove" ident ":=" "by" tacticSeq: command

builtin_initialize tempCircuitRef : IO.Ref (Option Ast.Circuit) ← IO.mkRef none

@[command_elab runwai_register]
unsafe def elabLodaCircuitRegister : Elab.Command.CommandElab := fun stx =>
  match stx with
  | `(command| #runwai_register $circ:runwai_circuit) =>
      Elab.Command.runTermElabM fun _ => do
        let ast ← Frontend.elaborateCircuit circ
        logInfo m!"Successfully elaborated circuit {repr ast}"
        Env.addCircuitToEnv ast.name ast
        logInfo m!"Successfully registered circuit '{ast.name}'."
  | _ => Elab.throwUnsupportedSyntax

@[command_elab runwai_check]
unsafe def elabLodaCircuitCheck : Elab.Command.CommandElab
  | `(command| #runwai_check $cName:ident) => do
    let Δ ← Elab.Command.liftCoreM Env.getCircuitEnv
    let circ := Env.lookupCircuit Δ cName.getId.toString
    logInfo m!"{repr circ}"
  | _ => Elab.throwUnsupportedSyntax

@[command_elab runwai_prove]
unsafe def elabLodaProve : Elab.Command.CommandElab
  | `(command| #runwai_prove $cName:ident := by $proof:tacticSeq) => do
    -- Get the circuit from environment
    let Δ ← Elab.Command.liftCoreM Env.getCircuitEnv
    let circ := Env.lookupCircuit Δ cName.getId.toString

    let circExpr := toExpr circ
    let deltaExpr := toExpr Δ

    let circTerm ← Elab.Command.liftTermElabM $ PrettyPrinter.delab circExpr
    let deltaTerm ← Elab.Command.liftTermElabM $ PrettyPrinter.delab deltaExpr

    -- Generate theorem name
    let theoremName := cName.getId.toString ++ "_correct"
    let theoremIdent := mkIdent (Name.mkSimple theoremName)

    -- Generate the theorem syntax
    let theoremStx ← `(command|
      theorem $theoremIdent (Δ: Env.CircuitEnv) (h_delta: Δ = $deltaTerm) : (Ty.circuitCorrect $deltaTerm $circTerm 1) := by
        (unfold Ty.circuitCorrect; intro x i height hs hi ht hσ; set envs := Ty.makeEnvs $circTerm x (Ast.Value.vZ i) height);
        (set σ := envs.1); (set Γ := envs.2); ($proof);
    )
    logInfo m!"Proof state opened for '{theoremName}' - continue with tactics!"
    -- Elaborate the generated theorem command
    Elab.Command.elabCommand theoremStx
  | _ => Elab.throwUnsupportedSyntax
