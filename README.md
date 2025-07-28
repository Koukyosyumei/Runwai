# Norito

User-Friendly DSL for AIR constraints of Zero-Knowledge Circuits with Refinement Types

## Design Memo

Air constraints are essentially constraints on the trace, which is a matrix on the finite field.

`curr` can be viewd as `row[i]`, where the type of `row[i]` is exactly the tuple of columns defined in `columns` section.

For example, if columns is `columns {a: F, b: [F]^2}`, the base type of `row[i]` is `(F, [F]^2)`.

`next` can be viewd as `row[i+1]`.

`is_first_row` means `i == 0`.

`is_last_row` means `i == NUM_ROW - 1`, where `NUM_ROW` can be defined as symbolic variable (or a constant number).

`is_transition` means that `i < NUM_ROW - 1`.

It might be interesting to introduce `mathematical-induction` typing rule (something like the bellow)

```
Γ ⊢ row[0] : {ν: F | φ}    
Γ ⊢ row[i] : {ν: F | φ} \to Γ ⊢ row[i+1] : {ν: F | φ}
────────────────────────────────────────────────────────── (T-INDUCTION)
\forall{i}. Γ ⊢ row[i] : {ν: F | φ}   
```

## Syntax

- Program Structure

```c
program            ::= circuit_def*

circuit_def        ::= "circuit" ID "{" 
                          public_values_decl?
                          columns_decl
                          constraints_decl
                       "}"
 
public_values_decl ::= "public_values" "{" 
                          (ID ":" refinment_type ";")*
                       "}"

columns_decl       ::= "columns" "{"
                          (ID ":" refinment_type ";")*
                       "}"

constraints_decl   ::= "constraints" "{" statement* "}"
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
refinement_type ::= base_type
                  | "{" ID ":" base_type "|" formula "}"

base_type ::= "F"                       // Field element
            | "[" base_type "]" "^" nat // Fixed-size array
            | "Bool"                    // Boolean (sugar for {v: F | binary(v)})

function_type ::= base_type
                | x: function_type "→" function_type

formula ::= expr                                        // Boolean expression
          | "binary" "(" expr ")"                       // Binary constraint  
          | "range" "(" expr "," expr ")"               // Range constraint [min, max)
          | "toNat" "(" expr ")" rel_op expr            // Conversion + comparison
          | formula "∧" formula                        // Conjunction
          | formula "∨" formula                        // Disjunction  
          | "∀" ID ":" base_type "." formula           // Universal quantification
          | "if" formula "then" formula "else" formula  // Conditional

rel_op ::= "<" | "<=" | ">" | ">=" | "==" | "!="
```

## Typing Rule

```c
// Variable reference
Γ(x) = {ν: T | φ}
──────────────────── (T-VAR)
Γ ⊢ x : {ν: T | ν = x}

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
```

## Subtyping Rule

```c
──────────────────────────── (S-REFL)
Γ ⊢ T <: T

Γ ⊢ T₁ <: T₂    P ≡ φ₁ → φ₂
∀v. Encode(Γ) → P
──────────────────────────── (S-REFINE)
Γ ⊢ {ν: T₁ | φ₁} <: {ν: T₂ | φ₂}


```

## Example

```c
// Example

circuit Fib {
  public_values {
		final_value: F;
	}

	columns {
		// there is an unexplicit column `row_id`
		// define registers
		x1: F;
		x2: F;
	}
	
	constraints {
		// curr is equivalent to row[i]
		// next is equivalent to row[i+1]
	
	  // is_first_row() is equivalent to curr.row_id == 0
		if is_first_row() {
			assert(curr.x1 == 0);
			assert(curr.x2 == 1);
		}
		
		
		// is_transition() is equivalent to curr.row_id < NUM_ROW - 1
		if is_transition() {
			// when is_transition, the existence of next should be gurantted
			assert(next.x1 == curr.x2);
			assert(next.x2 == curr.x1 + curr.x2);
		}
		
		// is_last_row() is equivalent to curr.row_id == NUM_ROW - 1, where NUM_ROW is a symbolic var
		if is_last_row() {
			// should not be able to access `next`.
			assert(curr.x2 == final_value);
		}
		
		// We want to prove that `curr.x2: {v : F | \forall{curr.row_id} 2 * v = clk * (clk + 1)}`
}

circuit CloClz {
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
		for i in 0..4 {
			if (cur.is_clo) {
				assert(curr.b[0] + curr.b[1] == 255);
			}
			if (cur.is_clz) {
				assert(curr.b[0], curr.b[1]);
			}
		}
		// TODO: range check of curr.bb
		
    // ensure result < 33
    // Send the comparison lookup.
    if (curr.is_real) {
	    lookup(LTU, curr.a[0], 33);
	    // We should be able to derive `curr.a[0] : {v: F | toNat(v) < 33}` from this lookup
	    assert(curr.a[1] == 0);
	    assert(curr.a[2] == 0);
	    assert(curr.a[3] == 0);
    }
    
    // curr.is_bb_zero is boolean
    assert(curr.is_bb_zero * (curr.is_bb_zero - 1) == 0);
    
    if (curr.is_bb_zero) {
	    assert(curr.bb.reduce() == 0);
	    assert(curr.a[0] == 32);
    }
    
    // check sr1 = bb >> (31 - result)
    lookup(SRL, sr1, bb, (31 - curr.a[0]));
    
    if (!curr.is_bb_zero) {
	    assert(curr.sr1.reduce() == 1);
    }
    
    assert(curr.is_clo * (curr.is_clo - 1) == 0);
    assert(curr.is_clz * (curr.is_clz - 1) == 0);
    assert(curr.is_clo + curr.is_clz == 1);
    
    // We want to prove that `curr.a[0] | {v: F | if is_clz == 1 then (b >> (32 - curr.a[0] + 1)) == 1 && b >> (32 - result) == 0 else ..}`
	}
}
```
