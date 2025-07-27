# Norito

User-Friendly DSL for AIR constraints of Zero-Knowledge Circuits with Refinement Types

- Program Structure

```c
program            ::= circuit_def*

circuit_def        ::= "circuit" ID "{" 
                          public_values_decl?
                          columns_decl
                          constraints_decl
                       "}"
 
public_values_decl ::= "public_values" "{" 
                          (ID ":" type ";")*
                       "}"

columns_decl       ::= "columns" "{"
                          (ID ":" type ";")*
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
       | "assert" "(" expr ")"             // Constraint assertion
       | "(" expr ")"                      // Parentheses
       | array_expr                        // Array operations
       | builtin_fn "(" ")"                // Built-in predicates

array_expr ::= expr "[" expr "]"           // Array indexing
             | expr "." "reduce" "(" ")"   // Array reduction (sum)
             | expr "." "len" "(" ")"      // Array length

builtin_fn ::= "is_first_row" | "is_transition" | "is_last_row"

bin_op ::= "+" | "-" | "*" | "==" | "!="

statement ::= "assert" "(" expr ")" ";"
            | "if" "(" expr ")" "{" statement* "}"
            | "for" ID "in" range "{" statement* "}"
            | lookup_stmt ";"

lookup_stmt ::= "lookup" "(" ID "," expr_list ")"

range ::= field_literal ".." field_literal // Exclusive range
```
