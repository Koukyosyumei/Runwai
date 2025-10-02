# Plonky3 — Design Goals & Architecture (Beginner-friendly)

## What is Plonky3?
Plonky3 is a Rust toolkit for building **succinct proof systems**. It gives you the core building blocks—finite fields, hash functions, Merkle commitments, polynomial commitment schemes (PCS), and STARK/PLONK protocol scaffolding—so you can assemble a prover/verifier tailored to your application (e.g., zkVMs, zkEVMs). In practice, most teams use it to build **STARK-based** systems because its PCS and libraries are optimized for that flow.

---

## Design goals
1. **Modularity over “one-true” system**  
   Plonky3 is intentionally *less opinionated* than earlier generations: you can swap fields (BabyBear, KoalaBear, Goldilocks, Mersenne31), hashes (Poseidon2, Keccak, BLAKE3, Rescue), and commitment schemes. This lets you tune for speed, memory, or proof size.

2. **First-class support for STARKs & recursion**  
   It ships with univariate & multivariate STARK frameworks and native recursion support (a fixed recursive verifier + helper crates), so you can aggregate many proofs into one and shrink on-chain verification costs.

3. **Performance on commodity hardware**  
   The codebase includes SIMD-friendly paths (AVX2/AVX-512/NEON) and optimized FFT/interpolation backends to reduce prover latency on typical CPUs.

4. **Open, audited building blocks**  
   The project emphasizes auditable, reusable cryptographic components (fields, codes, hashers, commitment layers) to make it easier to reason about and review each layer independently.

5. **A “toolkit” mindset**  
   Rather than forcing a single proof system, Plonky3 aims to be a *construction kit* for PIOPs (Polynomial IOPs), including PLONK-style flows when needed.

---

## The architecture at a glance

Think of Plonky3 as layers you can mix & match:

### 1) Foundations
- **Fields:** BabyBear/KoalaBear (31-bit families with ~128-bit extensions), Goldilocks, Mersenne31; plus extension fields.
- **Math/FFT/Interpolation:** barycentric interpolation; radix-2 DIF/DIT FFTs; Bowers and four-step FFTs; a “circle-group” FFT for the Mersenne prime.
- **Matrix & utilities:** low-level performance helpers (including SIMD-aware code paths).

### 2) Cryptographic primitives
- **Hashes & permutations:** Poseidon, Poseidon2, Rescue, Keccak-256, BLAKE3, Monolith.  
- **Merkle trees:** generalized vector commitments over different hashers.  
- **Error-correcting codes:** Reed–Solomon; Brakedown-style encodings for PCS internals.

### 3) Commitment layer (PCS)
- **FRI-based PCS:** fold-and-query low-degree testing with Merkle commitments to evaluation oracles.  
- **Adapters:** univariate↔multivariate adapters and a “tensor PCS” to bridge arithmetizations to the PCS in the shape you need.

### 4) Protocol scaffolding (PIOPs)
- **STARK frameworks:** univariate & multivariate STARK “engines” (AIR definition → commitments → queries).  
- **PLONK scaffolding:** traits and components to host PLONK-style circuits if you need SNARK-like custom gates/selector logic.  
- **Challenger (Fiat–Shamir):** transcript/challenge sampling so your interactive protocol becomes non-interactive.

### 5) Recursion stack (native)
- **Fixed recursive verifier:** a small, fixed STARK verifier circuit designed to efficiently verify other Plonky3 proofs.  
- **Circuit builder with runtime policy:** you choose which non-primitive ops (Merkle, FRI, etc.) are allowed; use `AllowAll` for experimentation or a restricted profile in production.  
- **AIRs for recursion:** helper crates (e.g., `fri-air`, `merkle-tree-air`, `symmetric-air`) implement the inside-the-proof checks the recursive verifier needs.

> **Mental model:**  
> *AIR (constraints) → PCS (commit to polynomial/coded views) → Fiat–Shamir (get random challenges) → open/check at random points → (optionally) feed the resulting proof into a small fixed verifier circuit → prove *that* circuit again to aggregate many proofs into one.*

---

## The proving pipeline

1. **Arithmetize your program as an AIR**  
   Define trace columns and transition/boundary constraints (e.g., a Fibonacci step or a VM instruction’s semantics).

2. **Encode & commit**  
   Encode the trace (e.g., with Reed–Solomon/Brakedown) and **commit** to it via the FRI-based PCS (Merkle roots at each folding round).

3. **Fiat–Shamir challenges**  
   The **Challenger** derives pseudo-random challenges from the transcript to choose evaluation points & mixing coefficients.

4. **Queries & openings**  
   The prover opens specific rows/points of the committed oracles and returns Merkle decommitments and evaluation values consistent with constraints.

5. **Verify (and recurse if desired)**  
   The verifier checks the low-degree test (FRI) and constraint satisfaction; optionally, a **recursive verifier circuit** inside another proof attests to these checks, enabling aggregation.

---

## Usage

- **Build zkVMs faster:** batteries-included crates for AIRs, FRI PCS, Merkle, hashers, and a recursion stack.  
- **Tunable:** choose field/hash/PCS to meet your speed or proof-size target.  
- **Ecosystem adoption:** used or referenced by zkVM projects and libraries; a good “center of gravity” for modern STARK work.  
- **Production posture:** active development with external audits; Polygon positions Plonky3 as a production-ready, next-gen successor to Plonky2’s ideas.

---

## Plonky3 vs. Plonky2 
- **Modularity:** Plonky3 is *less opinionated*—fewer fixed properties, more room to swap components.  
- **Recursion design:** Plonky3 ships a focused, fixed recursive verifier stack for efficient aggregation.  
- **CPU tuning:** more explicit SIMD/CPU feature pathways and updated primitives/fields.  
- **Scope:** designed as a general **PIOP toolkit** (STARK-first but PLONK-capable) rather than a single pipeline.

