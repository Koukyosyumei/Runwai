# Contribution Guide

## 1. Installation

**Fork the Repository**

- Head over to the Runwai [repository](https://github.com/Koukyosyumei/Runwai) on GitHub.
- Click the "Fork" button to create your own copy of the repository.

**Clone Your Fork**

- Open your terminal and navigate to your desired local directory.
- Use the git clone command to clone your forked repository:

```bash
git clone https://github.com/<your-username>/Runwai.git
# Replace <your-username> with your GitHub username and <project-name> with the actual project name.
```

**Build from Source**

```bash
cd Runwai

lake build
lake test Test
```

## 2. Code Walkthough

### 2.1. Abstract Syntax Tree (AST)

The AST of Runwai language is defined in [`Runwai/Ast.lean`](Runwai/Ast.lean). The AST provideds a structual representation of Runwai programs, encompassing expressions, types, and values.

**Key AST Elements:**

  * **`Expr`:** This inductive type defines the core expression syntax of Runwai, including constants, variables, arithmetic and boolean operations, array indexing, and control flow constructs like `if-then-else` and `let-in` bindings.
  * **`Ty`:** This represents the types in Runwai, including basic types like `field`, `int`, and `bool`, as well as more complex types like arrays (`arr`), refinement types (`refin`), and function types (`func`).
  * **`Value`:** This defines the runtime values that Runwai expressions can evaluate to, such as field elements (`vF`), signed integers (`vN`), booleans (`vBool`), and arrays (`vArr`).

### 2.2. Parser

The parser, defined in [`Runwai/Parser.lean`](Runwai/Parser.lean), is responsible for transforming the textual representation of a Runwai program into the AST. It uses Lean's built-in parsing capabilities to define a custom syntax for Runwai expressions and types.

**Parser Features:**

  * **Custom Syntax:** The parser defines a user-friendly syntax for Runwai's types and expressions, including familiar notations for arithmetic and boolean operators.
  * **Elaboration:** The `elaborateExpr` and `elaborateType` functions recursively traverse the parsed syntax tree and construct the corresponding `Ast.Expr` and `Ast.Ty` objects.

### 2.3. Evaluator

The evaluator, implemented in [`Runwai/Eval.lean`](Runwai/Eval.lean), is a small-step interpreter that computes the value of a Runwai expression. It operates on the AST and uses a set of evaluation rules to determine the result of each expression.

**Evaluation Logic:**

  * **`EvalProp`:** The core of the evaluator is the `EvalProp` inductive proposition, which defines the evaluation rules for each type of expression in the AST. For example, the `Let` constructor specifies how to evaluate a `let-in` binding by first evaluating the bound expression and then substituting the result into the body.
  * **`evalFieldOp`, `evalIntegerOp`, `evalRelOp`, `evalBoolOp`:** These helper functions define how to evaluate the primitive operations in Runwai, such as addition, multiplication, and comparison.

### 2.4. Type System and Verification

The type system, defined in [`Runwai/Typing.lean`](Runwai/Typing.lean), is a crucial component for ensuring the correctness of Runwai programs. It uses a set of typing rules to assign a type to each expression and to verify that the program adheres to the specified refinement types.

**Key Aspects of the Type System:**

  * **`TypeJudgment`:** This inductive proposition defines the typing rules for Runwai. For each expression in the AST, there is a corresponding constructor in `TypeJudgment` that specifies the conditions under which the expression is well-typed. For example, the `TE_LetIn` rule states that a `let-in` expression is well-typed if the bound expression has the specified type, and the body is well-typed in an environment that includes the new binding.
  * **`SubtypeJudgment`:** This defines the subtyping relationship between Runwai types. It includes rules for reflexivity, transitivity, and, most importantly, for refinement types. The `TSub_Refine` rule allows for subtyping between two refinement types if their base types are in a subtyping relationship and if the refinement of the first type implies the refinement of the second.
  * **`chipCorrect`:** This proposition formally defines the correctness of a Runwai "chip" (a self-contained circuit). A chip is considered correct if its body, when executed in an environment that satisfies the input refinements, produces a result that satisfies the output refinement.

### 2.5. Commands

The [`Runwai/Command.lean`](Runwai/Command.lean) file defines the user-facing commands for interacting with the Runwai system. These commands allow you to register, check, and prove the correctness of your ZK circuits.

**Main Commands:**

  * **`#runwai_register`:** This command is used to define and register a new Runwai chip. You provide the chip's name, its input and output specifications (including refinement types), and its body as a Runwai expression.
  * **`#runwai_check`:** This command allows you to check the elaborated AST of a registered chip, which can be useful for debugging.
  * **`#runwai_prove`:** This is the most important command, as it allows you to formally prove the correctness of a registered chip. You provide the name of the chip and a proof script written in Lean's tactic language. The command then generates a theorem stating the correctness of the chip and enters an interactive proof mode where you can use tactics to complete the proof.

### 2.6. Example Usage

The [`Test/CommandTest.lean`](Test/CommandTest.lean) and [`Test/CircuitTest.lean`](Test/CircuitTest.lean) files provide several examples of how to use Runwai to define and prove the correctness of simple ZK circuits.

**Example: `IsZero` Chip**

The `IsZero` chip is a classic example of a ZK circuit that checks if a given input `x` is equal to zero. Here's how it's defined and proven in Runwai:

```lean
#runwai_register chip IsZero(trace, i, 3) -> {Unit| y == if x == Fp 0 then {Fp 1} else {Fp 0}} {
  let x = trace [i][0] in
  let y = trace [i][1] in
  let inv = trace [i][2] in
  let u₁ = assert_eq(y, ((Fp 0 - x) * inv) + Fp 1) in
  let u₂ = assert_eq(x*y, Fp 0) in u₂
}

#runwai_prove IsZero := by {
  auto_trace_index
  apply isZero_typing_soundness
  repeat apply get_update_ne; simp
  apply Ty.TypeJudgment.TE_VarEnv
  apply get_update_self;
  repeat decide
}
```

In this example:

1.  `#runwai_register` defines a chip named `IsZero` that takes a 3-column trace as input. The refinement type on the output specifies that the value `y` should be `1` if `x` is `0`, and `0` otherwise.
2.  The body of the chip defines the constraints that enforce this logic.
3.  `#runwai_prove` starts a proof of the `IsZero` chip's correctness. The proof script then uses a combination of custom tactics (like `auto_trace_index`) and standard Lean tactics to complete the proof

