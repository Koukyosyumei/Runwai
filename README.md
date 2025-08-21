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
  .
  .
```

## Why use Runwai?