syntax "auto_judgment" : tactic
macro_rules
| `(tactic| auto_judgment) => `(tactic|
    {
      repeat constructor
      simp_all
      constructor;
      simp_all
    }
  )
