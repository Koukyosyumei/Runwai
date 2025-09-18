import Lean.Meta
import Lean.Elab.Command
import Lean.Parser
import Lean.Elab

import Runwai.Parser

open Lean Parser
open Lean Meta

syntax (name := runwai_register) "#runwai_register" runwai_chip : command
syntax (name := runwai_check) "#runwai_check" ident : command
syntax (name := runwai_prove) "#runwai_prove" ident ":=" "by" tacticSeq: command

builtin_initialize tempChipRef : IO.Ref (Option Ast.Chip) ← IO.mkRef none

@[command_elab runwai_register]
unsafe def elabLodaChipRegister : Elab.Command.CommandElab := fun stx =>
  match stx with
  | `(command| #runwai_register $circ:runwai_chip) =>
      Elab.Command.runTermElabM fun _ => do
        let ast ← Frontend.elaborateChip circ
        logInfo m!"Successfully elaborated Chip {repr ast}"
        Env.addChipToEnv ast.name ast
        logInfo m!"Successfully registered Chip '{ast.name}'."
  | _ => Elab.throwUnsupportedSyntax

@[command_elab runwai_check]
unsafe def elabLodaChipCheck : Elab.Command.CommandElab
  | `(command| #runwai_check $cName:ident) => do
    let Δ ← Elab.Command.liftCoreM Env.getChipEnv
    let circ := Env.lookupChip Δ cName.getId.toString
    logInfo m!"{repr circ}"
  | _ => Elab.throwUnsupportedSyntax

@[command_elab runwai_prove]
unsafe def elabLodaProve : Elab.Command.CommandElab
  | `(command| #runwai_prove $cName:ident := by $proof:tacticSeq) => do
    -- Get the Chip from environment
    let Δ ← Elab.Command.liftCoreM Env.getChipEnv
    let circ := Env.lookupChip Δ cName.getId.toString

    let circExpr := toExpr circ
    let deltaExpr := toExpr Δ

    let circTerm ← Elab.Command.liftTermElabM $ PrettyPrinter.delab circExpr
    let deltaTerm ← Elab.Command.liftTermElabM $ PrettyPrinter.delab deltaExpr

    -- Generate theorem name
    let theoremName := cName.getId.toString ++ "_correct"
    let theoremIdent := mkIdent (Name.mkSimple theoremName)

    -- Generate the theorem syntax
    let theoremStx ← `(command|
      theorem $theoremIdent (Δ: Env.ChipEnv) (h_delta: Δ = $deltaTerm) : (Ty.chipCorrect $deltaTerm $circTerm 1) := by
        (unfold Ty.chipCorrect; intro i hi Γ Η;);
        ($proof);
    )
    logInfo m!"Proof state opened for '{theoremName}' - continue with tactics!"
    -- Elaborate the generated theorem command
    Elab.Command.elabCommand theoremStx
  | _ => Elab.throwUnsupportedSyntax
