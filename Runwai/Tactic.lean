import Runwai.Ast
import Runwai.Typing
import Runwai.Gadget

syntax "auto_trace_index" : tactic
macro_rules
| `(tactic| auto_trace_index) => `(tactic|
    repeat
      apply Ty.TypeJudgment.TE_LetIn
      · apply get_update_self
      · apply Ty.TypeJudgment.TE_ArrayIndex
        apply Ty.TypeJudgment.TE_ArrayIndex
        apply var_has_type_in_tyenv
        apply get_update_ne
        try (simp)
        try (simp [Ast.nu])
        apply var_has_type_in_tyenv
        try (apply get_update_self)
        try (apply get_update_ne)
        try (simp)
        try (simp [Ast.nu])
        apply constZ_refine_lt
        try (simp)
  )

syntax "auto_let_assert" : tactic
macro_rules
| `(tactic| auto_let_assert) => `(tactic|
    apply Ty.TypeJudgment.TE_LetIn;
    apply get_update_self;
    apply Ty.TypeJudgment.TE_Assert;
  )

syntax "auto_resolve_varenv" : tactic
macro_rules
| `(tactic| auto_resolve_varenv) => `(tactic|
    apply var_has_type_in_tyenv;
    apply get_update_ne;
    simp;
    try (simp [Ast.nu]);
  )

syntax "repeatConstructorAtMost" num : tactic
macro_rules
| `(tactic| repeatConstructorAtMost $n:num) => `(tactic|
  (first |
    try (constructor);
    try (apply get_update_self);
    try (apply get_update_ne);
    try (simp[Η, Env.freshName, Ty.branchLabel, Ty.heightLabel]);
    try (simp)
  );
  (iterate $n (
    try constructor;
    try (apply get_update_self);
    try (apply get_update_ne);
    try (simp[Η, Env.freshName, Ty.branchLabel, Ty.heightLabel]);
    try (simp)
  ))
  )

/-
    apply Ty.TypeJudgment.TE_VarEnv
    apply get_update_ne
    simp
-/
