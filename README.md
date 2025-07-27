# Norito

User-Friendly DSL for AIR constraints of Zero-Knowledge Circuits with Refinement Types

- Program Structure

```
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
