import Lean.Meta
import Lean.Elab.Command
import Lean.Parser
import Lean.Elab

import Runwai.Parser
import Runwai.Json


open Lean Meta IO System
open Json

def main (args : List String) : IO UInt32 := do
  match args with
  | [filePath] =>
    processFile filePath "."
  | [filePath, outDir] =>
    processFile filePath outDir
  | _ =>
    eprintln "Usage: runwai-cli <file.rwai> [output_dir]"
    pure 1

where
  processFile (filePath : String) (outDir : String) : IO UInt32 := do
    let content ← FS.readFile filePath

    --if !(← FS. outDir) then
    IO.println s!"[+] Creating output directory: {outDir}"
    FS.createDirAll outDir

    Lean.initSearchPath (← Lean.findSysroot)
    let env ← Lean.importModules #[{ module := `Runwai.Parser }] {} (loadExts := True)

    let dummyFileName := "<cli>"
    let dummyFileMap := FileMap.ofString ""
    let coreCtx : Core.Context := { fileName := dummyFileName, fileMap := dummyFileMap }
    let coreState : Core.State := { env := env }

    let (chips, _) ← Meta.MetaM.toIO (Frontend.parseRunwaiProgram content) coreCtx coreState

    if chips.isEmpty then
      eprintln "[!] No chips found in input file."
      pure 1
    else
      for cp in chips do
        let jsonStr := exprToJsonStr cp.body
        let fileName := s!"{cp.name}.json"
        let outFile := FilePath.mk outDir / fileName
        IO.println s!"[+] Writing {outFile} ..."
        FS.writeFile outFile.toString jsonStr

      IO.println s!"[✓] Wrote {chips.length} chip(s) to {outDir}"
      pure 0
