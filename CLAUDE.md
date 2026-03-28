# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Overview

Runwai is a refinement-typed DSL for certified AIR (Algebraic Intermediate Representation) constraints in zero-knowledge proof systems. It combines:
- **Lean 4** frontend: parsing, type system, formal verification
- **Rust backend** (`backend/`): Plonky3-based STARK proof generation and verification

## Commands

### Build

```bash
lake build          # Build the main Runwai library
lake build Test     # Build the test suite
```

### Run CLI (compile `.rwai` to JSON)

```bash
lake exe runwai examples/iszero.rwai           # Compiles to examples/IsZero.json
lake exe runwai examples/iszero.rwai <out_dir>  # Output to custom directory
```

### Build Rust backend

```bash
cd backend && cargo build
cd backend && cargo test
```

### Run tests

Tests are Lean files in `Test/` — they execute as part of `lake build Test`. There is no separate test runner; correctness is checked through Lean's elaboration and proof checking.

## Architecture

### Lean 4 Frontend (`Runwai/`)

**Data flow:** `.rwai` source → `Parser.lean` (elaboration) → `Ast.lean` (AST) → `Typing.lean` (type checking) → `Command.lean` (proof generation) → `Json.lean` (JSON serialization)

Key files:
- **`Ast.lean`** — Core types: `Expr` (expressions), `Ty` (types including refinement types `refin`), `Value`, `Predicate`, `Chip` (a named circuit with input/output types and body)
- **`Parser.lean`** — Lean 4 macro/syntax declarations; `elaborateExpr` and `elaborateType` convert DSL syntax to `Ast.Expr`/`Ast.Ty`
- **`Eval.lean`** — Small-step interpreter via `EvalProp` inductive proposition; operates over `ValEnv` (variables), `TraceEnv` (trace rows), `ChipEnv` (registered chips)
- **`Typing.lean`** — `TypeJudgment Δ Γ σ T e τ` assigns type `τ` to `e`; `SubtypeJudgment` handles refinement subtyping; `chipCorrect` is the top-level correctness predicate
- **`PropSemantics.lean`** — `exprToProp` and `predToProp` convert Runwai expressions/predicates into Lean `Prop` for proof obligations
- **`Env.lean`** — `ValEnv`, `ChipEnv`, `TyEnv`, `TraceEnv` definitions and operations
- **`Field.lean`** — Prime field `Fp` implementation; field inversion via Fermat's little theorem
- **`Command.lean`** — User-facing commands: `#runwai_register`, `#runwai_check`, `#runwai_compile_to_json`, `#runwai_prove`
- **`Json.lean`** — AST-to-JSON serialization for Rust backend interop

### Gadget Library (`Runwai/Gadget/`)

Lemmas and automation for proofs:
- **`VCG.lean`** — Verification Condition Generation; the `autoTy` tactic uses this
- **`EvalLemmas.lean`**, **`TypingLemmas.lean`**, **`FieldLemmas.lean`**, **`EnvLemmas.lean`** — reusable lemmas
- **`Func.lean`**, **`PointwisePreserve.lean`** — structural preservation properties

### Rust Backend (`backend/src/`)

Mirrors the Lean AST and implements STARK proving:
- **`ast.rs`** — Serde-deserializable Rust `Expr` mirroring Lean's AST (reads JSON from CLI)
- **`air.rs`** — `RunwaiAir` implements Plonky3's `Air` trait from a deserialized `Expr`
- **`prover.rs`** / **`verify.rs`** — Plonky3 STARK prove/verify wrappers
- **`lookup.rs`** — Lookup argument constraint support

### User-Facing Commands

```haskell
-- Register a chip
#runwai_register chip Name(trace: [[Field: k]: n], i: {v: UInt | v < n})
  -> {Unit| <output_refinement>} { <body_expr> }

-- Inspect elaborated AST
#runwai_check Δ Name

-- Formally prove correctness (produces `Name_correct` theorem)
#runwai_prove Δ Name := by { ... }

-- Emit JSON for Rust backend
#runwai_compile_to_json Name
```

### Proof Pattern

Proofs of `chipCorrect` typically use:
1. `autoTy "<last_let_binding>"` — VCG tactic that discharges typing obligations
2. Circuit-specific soundness lemmas (e.g., `isZero_typing_soundness`)
3. `repeat decide` / `repeat rfl` / `simp[Ast.renameTy]` for remaining goals

### Lean Toolchain

Lean version is pinned in `lean-toolchain` (currently `v4.24.0`). Mathlib4 is the only Lean dependency, pulled from Git in `lakefile.lean`.
