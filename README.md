# Norito

User-Friendly DSL for AIR constraints of Zero-Knowledge Circuits with Refinement Types

## Design Memo

Air constraints are essentially constraints on the trace, which is a matrix on the finite field.

- Example

```c
circuit Fib {
  // _NUM_COLS should be able to deduced from `columns` section
  // _NUM_ROWS can be symbolic, but users might be able to assign a concrete value.
  // _trace: [F, _NUM_COLS] × _NUM_ROWS;

  // auxiliary values
  auxiliary_values {
    final_value: F
  }

  // this section defins the columns alias.
  // in this example, `x1 = 0`, and `x2 = 1`.
  // _NUM_COLS is deduced to 2.
  columns {
    x1: F;
    x2: F;
  }
	
  // this section defins the constraints for _trace[i] and _trace[i+1].
  // `curr` is the alias of `_trace[i]` and `next` is the alias of `_trace[i+1].` 
  // The bellow constraints are equivalent to 
  // for _i in 0.._NUM_ROWS {
  //    if _i == 0 {
  //      assert_eq(_trace[_i][0], 0);
  //      assert_eq(_trace[_i][1], 1);
  //    }
  //
  //    if _i < _NUM_ROWS - 1 {
  //      assert_eq(_trace[_i+1][0], _trace[_i][1]);
  //      assert_eq(_trace[_i+1][1], _trace[_i][0] + _trace[_i][1]);
  //    }
  //
  //    if _i == _NUM_ROWS - 1 {
  //      assert_eq(_trace[_i][1], final_value);
  //    }
  // }
  //
  constraints {	
    if is_first_row() {
      assert_eq(curr.x1, 0);
      assert_eq(curr.x2, 1);
    }
		
    if is_transition() {
      assert_eq(next.x1, curr.x2);
      assert_eq(next.x2, curr.x1 + curr.x2);
    }
		
    if is_last_row() {
      assert_eq(curr.x2, final_value);
    }
  }
		
  // We want to prove that
  // `curr.x2: {v : F | 2 * v = (_i + 1) * (_i + 2)}`
  // `final_value : {v : F | 2 * v = (_NUM_ROWS) * (_NUM_ROWS + 1)}`
}
```

```c
circuit CloClz {
  // this section defins the columns alias.
  // in this example, 
  //    `a = [0, 1, 2, 3]`
  //    `b = [4, 5, 6, 7]`
  //    `bb = [8, 9, 10, 11]`
  //    `sr1 = 12`
  //    `is_clz = 13`
  //    `is_col = 14`
  //    `is_real = 15`
  columns {
    a: [F]^4    // results
    b: [F]^4    // inputs
    bb: [F]^4;
    sr1: [F]^4;
    is_clz: F;
    is_clo: F;
    is_real: F;
  }
	
  constraints {
    for j in 0..4 {
      if (cur.is_clo) {
        assert_eq(curr.b[j] + curr.bb[j], 255);
      }
      if (cur.is_clz) {
        assert_eq(curr.b[j], curr.bb[j]);
      }
    }
    // TODO: range check of curr.bb
		
    // ensure result < 33
    // Send the comparison lookup.
    if (curr.is_real) {
      lookup(LTU, (curr.a[0], 33));
      // We should be able to derive `curr.a[0] : {v: F | toNat(v) < 33}` from this lookup
      // The type of lookup(LTU, (x, y)) can be (F × F) -> {v: F × F | v.1 < v.2} 
      assert_eq(curr.a[1], 0);
      assert_eq(curr.a[2], 0);
      assert_eq(curr.a[3], 0);
    }
    
    // curr.is_bb_zero is boolean
    // `assert_bool(x)` is the alias of `assert_eq(x * (x - 1), 0)`
    assert_bool(curr.is_bb_zero);
    
    if (curr.is_bb_zero) {
	    assert(curr.bb.reduce() == 0);
	    assert(curr.a[0] == 32);
    }
    
    // check sr1 = bb >> (31 - result)
    lookup(SRL, (sr1, bb, (31 - curr.a[0])));
    
    // `sr1.reduce() is the alias of sr[0] + sr[1] + sr[2] + sr[3]`
    if (!curr.is_bb_zero) {
      assert(curr.sr1.reduce() == 1);
    }
    
    assert_bool(curr.is_clo);
    assert_bool(curr.is_clz);
    assert_eq(curr.is_clo + curr.is_clz, 1);
    
    // We want to prove that `curr.a[0] | {v: F | if is_clz == 1 then (b >> (32 - curr.a[0] + 1)) == 1 && b >> (32 - result) == 0 else ..}`
    // We need to allow non-quadratic operations inside the predicate of the refinment types.
	}
}
```

## Syntax

- Program Structure

```c
program               ::= circuit_def*

circuit_def           ::= "circuit" ID "{" 
                            auxiliary_values_decl?
                            columns_decl
                            constraints_decl
                          "}"
 
auxiliary_values_decl ::= "auxiliary_values" "{" 
                            (ID ":" refinment_type ";")*
                          "}"

columns_decl          ::= "columns" "{"
                            (ID ":" refinment_type ";")*
                          "}"

constraints_decl      ::= "constraints" "{" statement* "}"
```

- Expression Syntax

```c
expr ::= ID                                // Variable reference
       | field_literal                     // Field constant  
       | "curr" "." ID                     // Current row
       | "next" "." ID                     // Next row
       | "lookup" "(" ID "," expr_list ")" // Lookup operation
       | expr bin_op expr                  // Binary operations
       | "assert_eq" "(" expr "," expr ")" // Constraint assertion
       | "if" "{" expr "}"                 // If-branch 
       | "(" expr ")"                      // Parentheses
       | array_expr                        // Array operations
       | builtin_fn "(" ")"                // Built-in predicates

array_expr ::= expr "[" expr "]"           // Array indexing
             | expr "." "reduce" "(" ")"   // Array reduction (sum)
             | expr "." "len" "(" ")"      // Array length

builtin_fn ::= "is_first_row" | "is_transition" | "is_last_row"

bin_op ::= "+" | "-" | "*" | "==" | "!="

statement ::= "assert_eq" "(" expr "," expr ")" ";"
            | "if" "(" expr ")" "{" statement* "}"
            | "for" ID "in" range "{" statement* "}"
            | lookup_stmt ";"

lookup_stmt ::= "lookup" "(" ID "," expr_list ")"

range ::= field_literal ".." field_literal // Exclusive range
```

- Type System

```c
// Basic Types
T ::= "F"                                  // Field element
    | "Bool"                               // Boolean (alias for {v: F | v * (v - 1) == 0})
    | T1 × · · · × Tn                      // Product (Unit denotes empty)
    | "[" T "]" "^" nat                    // Fixed-size array
    | "{" ID ":" base_type "|" formula "}" // Refinment type

function_type ::= T
                | x: function_type "→" function_type

formula ::= expr                                        // Boolean expression
          | refinment_terms
          | formula "∧" formula                        // Conjunction
          | formula "∨" formula                        // Disjunction  
          | "∀" ID ":" base_type "." formula           // Universal quantification
          | "if" formula "then" formula "else" formula  // Conditional

refinment_terms ::= true | false
                  | expr
                  | "toNat" "(" refinment_terms ")"
                  | refinment_terms rel_op refinment_terms
                  | refinment_terms nonquadratic_op refinment_terms

rel_op ::= "<" | "<=" | ">" | ">=" | "==" | "!="
nonquadratic_op ::= "/" | "<<" | ">>"
```

## Typing Rule

```c
// Variable reference
Γ(x) = {ν: T | φ}
──────────────────── (T-VAR)
Γ ⊢ x : {ν: T | ν = x}

// Constant Field
f \in F
──────────────────────── (T-CONSTF)
Γ ⊢ f : {ν: F | ν = f}

// Field operations  
Γ ⊢ e₁ : {ν: F | φ₁}    Γ ⊢ e₂ : {ν: F | φ₂}
──────────────────────────────────────────── (T-FIELD-OP)
Γ ⊢ e₁ ⊕ e₂ : {ν: F | ν = e₁ ⊕ e₂}

// Lookup operation
Γ.lookups(table) = T₁ → T₂,    Γ ⊢ key : T₁
──────────────────────────────────────────── (T-LOOKUP)
Γ ⊢ lookup(table, key) : T₂

// Constraint assertion
Γ ⊢ e₁ : {ν: F | φ₁}, Γ ⊢ e₂ : {ν: F | φ₂}
──────────────────────────────────────────── (T-ASSERT)
Γ ⊢ assert e : {ν: Unit | e₁ = e₂}

// Sub-Type
Γ ⊢ e : T'          Γ ⊢ T' <: T
──────────────────────────────────── (T-SUB)
Γ ⊢ e : T

// Mathematical Induction
Γ ⊢ _trace[0] : {ν: T | φ}    
Γ ⊢ _trace[i] : {ν: T | φ} \to Γ ⊢ _trace[i+1] : {ν: T | φ}
────────────────────────────────────────────────────────── (T-INDUCTION)
\forall{i}. Γ ⊢ _trace[i] : {ν: T | φ}   
```

## Subtyping Rule

```c
────────────────────────────────── (SUB-REFL)
Γ ⊢ T <: T

Γ ⊢ T1 <: T2  Γ ⊢ T2 <: T3 
────────────────────────────────── (SUB-TRANS)
Γ ⊢ T1 <: T3

Γ ⊢ T₁ <: T₂    P ≡ φ₁ → φ₂
∀v. Encode(Γ) → P
────────────────────────────────── (SUB-REFINE)
Γ ⊢ {ν: T₁ | φ₁} <: {ν: T₂ | φ₂}

Γ ⊢ Ti <: Ti' for all i \in {0, ..., n}
───────────────────────────────────────── (SUB-PRODUCT)
Γ ⊢ T1 × . . . × Tn <: T1' × . . . × Tn'
```
