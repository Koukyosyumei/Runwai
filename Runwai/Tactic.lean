import Runwai.Typing
import Runwai.Gadget

syntax "auto_trace_index" : tactic
macro_rules
| `(tactic| auto_trace_index) => `(tactic|
    repeat
      apply Ty.TypeJudgment.TE_LetIn
      · apply lookup_update_self
      · apply Ty.TypeJudgment.TE_ArrayIndex
        apply Ty.TypeJudgment.TE_ArrayIndex
        apply Ty.TypeJudgment.TE_VarEnv
        simp
        apply lookup_update_ne
        simp
        apply Ty.TypeJudgment.TE_VarEnv
        try (apply lookup_update_self)
        try (apply lookup_update_ne)
        try (simp)
        apply constZ_refine_lt
        simp
  )
