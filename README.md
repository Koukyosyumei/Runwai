# Runwai:

> [!IMPORTANT]
> This tool is under active development. Usage patterns and features may change over time.

<p align="center">
    <img src="./img/logo-runway-drawio.svg" alt="Loda Logo" height="132">
</p>

<h3>🛬 Where zk Proofs Take Flight 🛫</h3>

Runwai is a refinement-typed DSL for certified AIR constraints in zero-knowledge proof systems.

## Quickstart

- AIR Constraint

```haskell
#runwai_register chip IsZero(trace, i, 3) -> {Unit| y == if x == Fp 0 then {Fp 1} else {Fp 0}} {
  let x = trace [i][0] in
  let y = trace [i][1] in
  let inv = trace [i][2] in
  let u₁ = assert_eq(y, ((Fp 0 - x) * inv) + Fp 1) in
  let u₂ = assert_eq(x*y, Fp 0) in u₂
}
```

- Theorem

```haskell
#runwai_prove IsZero := by {
  auto_trace_index
  apply isZero_typing_soundness
  repeat apply get_update_ne; simp
  apply Ty.TypeJudgment.TE_VarEnv
  apply get_update_self;
  repeat decide
}
```

## Why use Runwai?

Developing zero-knowledge (ZK) circuits is notoriously challenging. Standard approaches, such as directly writing Algebraic Intermediate Representation (AIR) constraints in zkVM frameworks like Plonky3, require encoding low-level, row-by-row polynomial relations. This process is error-prone, unintuitive, and makes reasoning about correctness extremely difficult, especially for complex programs.

Runwai addresses these challenges by providing a **refinement-typed, high-level DSL for AIR circuits**. Here’s why Runwai stands out:

* 🏗️ **High-level abstraction for AIR constraints**
  Runwai lets you express constraints over execution traces directly, without manually handling low-level matrix operations. This makes programs easier to write, read, and maintain.

* ✅ **Refinement types for correctness guarantees**
  Runwai’s type system allows developers to formally specify and statically verify circuit properties. This reduces the risk of subtle bugs that could compromise the security of ZK proofs.

* 📚 **Concise and readable syntax**
  Compared to traditional AIR implementations, Runwai programs are shorter, more expressive, and easier to understand.

In short, Runwai allows ZK developers to **write correct, secure, and maintainable AIR circuits efficiently**, while benefiting from the guarantees of a strong, refinement-based type system.
