# Runwai:

> [!IMPORTANT]
> This tool is under active development. Usage patterns and features may change over time.

<p align="center">
    <img src="./img/logo-runway-drawio.svg" alt="Loda Logo" height="132">
</p>

<h3>🛬 Where zk Proofs Take Flight 🛫</h3>

Runwai is a refinement-typed DSL for certified AIR constraints in zero-knowledge proof systems.

The working-in-progress documentation paper is available at [link](https://drive.google.com/file/d/15s1s3ecBxd5B5Y06nsZ1sRocjB8CfwHK/view?usp=sharing).

## Quickstart

- Define a Constraint

```haskell
#runwai_register chip IsZero(trace: [[Field: 3]: n], i : {v: UInt | v < n})
  -> {Unit| trace [i][1] == if trace [i][0] == Fp 0 then {Fp 1} else {Fp 0}} {
  let x = trace [i][0];
  let y = trace [i][1];
  let inv = trace [i][2];
  let u₁ = assert_eq(y, ((Fp 0 - x) * inv) + Fp 1);
  let u₂ = assert_eq(x*y, Fp 0);
  u₂
}
```

- Prove Its Correctness

```haskell
#runwai_prove Δ IsZero := by {
  auto_trace_index
  apply isZero_typing_soundness
  repeat apply get_update_ne; simp
  apply Ty.TypeJudgment.TE_VarEnv
  apply get_update_self;
  repeat decide
  repeat rfl
  simp[Ast.renameTy]
}
```

- Compile to JSON

```bash
lake exe runwai examples/iszero.rwai
```

- Integrate with Plonky3 Backend

```rust
use p3_uni_stark::{prove, verify};

use runwai_p3::air::RunwaiAir;
use runwai_p3::ast::Expr;

let expr = Expr::from_json_file("examples/IsZero.json").unwrap();
let air = RunwaiAir::<Val>::new(expr, 3);

let proof = prove(&config, &air, trace, &vec![]);
let result = verify(&config, &air, &proof, &vec![]);
```

## Why use Runwai?

Designing a zero-knowledge proof (ZKP) application is notoriously complex. Developers must not only express computations as field polynomial constraints but also ensure their correctness and efficiency. Existing domain-specific languages (DSLs) for ZK circuits force users into a painful trade-off between **efficiency**, **simplicity**, and **safety** — but Runwai aims to deliver all three.

### 🧩 The Problem: The ZK DSL Trilemma

Most ZK languages fall into one of three unsatisfying paths:

- **The Path of Efficiency**: Low-level DSLs offer fine-grained control over arithmetic constraints, achieving high performance. However, reasoning about correctness (e.g., $1 / 2 = 4 \bmod 7$) becomes unintuitive and error-prone.

- **The Path of Simplicity**: High-level DSLs provide a familiar imperative style with automatic constraints generation, but they often generate bloated, unoptimized circuits — often 3×–300× slower than handcrafted ones.

- **The Path of Safety**: Some DSLs naively integrate formal verification, but either lack support for modern zkVM primitives (like AIR and lookups) or introduce highly abstract semantics that are too difirent from standard languages and hard for normal programmers to learn.

### 🧠 The Runwai Approach: Refinement-Typed ZK Constraints

**Runwai** eliminates this trilemma with a refinement-typed DSL, offering low-level expressivity with an optional rigorous verification layer.

- **Native AIR & Lookup Support** – Designed for modern zkVM, supporting algebraic intermediate representations (AIR) and lookup arguments as first-class primitives.
- **Type-Integrated Specifications** – Correctness conditions are embedded directly in function types via refinement predicates, making specifications local, compositional, and intuitive.
- **Interactive Theorem Proving** – Built on Lean 4, Runwai allows developers to formally prove properties of circuits within the same environment. Proofs can be assisted by automation yet remain fully inspectable and human-guided.
