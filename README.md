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
circuit IsZeroAir
  ( trace : {[[F; 3]; n] | true } , i: {Z | 0 <= v < n})
  -> {Unit | trace[i][1] = if trace[i][0] == 0 then 1 else 0} {
    let x = trace[i][0] in
      let y = trace[i][1] in
        let inv = trace[i][2] in
          let u₁ = assert_eq(y, -x * inv + 1) in
            let u₂ = assert_eq(x * y, 0) in u₂             
}
```

- Theorem

```lean
theorem iszeroCircuit_correct : Ty.circuitCorrect Δ iszeroCircuit 1 := by
  unfold Ty.circuitCorrect
  intro x i height hs hi ht hσ
  let envs := Ty.makeEnvs iszeroCircuit x (Ast.Value.vZ i) height
  let σ := envs.1
  let Γ := envs.2
  apply Ty.TypeJudgment.TE_LetIn
  · lookup_recent_update
  · auto_judgment
  . apply Ty.TypeJudgment.TE_LetIn
    . lookup_recent_update
    · auto_judgment
    . apply Ty.TypeJudgment.TE_LetIn
      . lookup_recent_update
      · auto_judgment
      . apply isZero_typing_soundness
        repeat apply lookup_update_ne; simp
        apply Ty.TypeJudgment.TE_VarEnv
        lookup_recent_update; simp;
        repeat apply lookup_update_ne; simp
```

## Why use Runwai?

Developing zero-knowledge (ZK) circuits is notoriously challenging. Standard approaches, such as directly writing Algebraic Intermediate Representation (AIR) constraints in zkVM frameworks like Plonky3, require encoding low-level, row-by-row polynomial relations. This process is error-prone, unintuitive, and makes reasoning about correctness extremely difficult, especially for complex programs.

Runwai addresses these challenges by providing a **refinement-typed, high-level DSL for AIR circuits**. Here’s why Runwai stands out:

* 🏗️ **High-level abstraction for AIR constraints**
  Runwai lets you express constraints over execution traces directly, without manually handling low-level matrix operations. This makes programs easier to write, read, and maintain.

* ✅ **Refinement types for correctness guarantees**
  Runwai’s type system allows developers to formally specify and statically verify circuit properties. This reduces the risk of subtle bugs that could compromise the security of ZK proofs.

* 📚 **Concise and readable syntax**
  Compared to traditional AIR implementations, Runwai programs are shorter, more expressive, and easier to understand. For example, a Fibonacci circuit in Runwai clearly encodes the intended constraints without verbose row-slice manipulations.

* 🛡️ **Safer and more secure circuits**
  By catching constraint violations at compile-time, Runwai helps prevent exploitable errors in ZK applications, enhancing both reliability and security.

* **Symbolic reasoning support**
  Runwai supports symbolic row indices and matrix dimensions, enabling verification of circuits even when certain parameters are unknown at compile time.

In short, Runwai allows ZK developers to **write correct, secure, and maintainable AIR circuits efficiently**, while benefiting from the guarantees of a strong, refinement-based type system.
