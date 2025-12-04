import Runwai.Typing
import Runwai.Gadget.Utils
import Runwai.Gadget.EnvLemmas
import Runwai.Gadget.EvalLemmas
import Runwai.Gadget.TypingLemmas
import Runwai.Gadget.FieldLemmas

open Ast
open Lean Meta Elab Tactic

/--
`tryLean tac` runs the tactic `tac : TacticM Unit` and returns `true` on success
and `false` on failure.

This helper is convenient when building "best-effort" automation where some
steps may fail but should not abort the entire tactic script.
-/
def tryLean (tac : TacticM Unit) : TacticM Bool := do
  try
    tac
    pure true
  catch _ =>
    pure false

/--
Return `true` iff the expression `e` has the form:
	Ty.TypeJudgment ...arguments...
-/
def isTyTypeJudgment (e : Lean.Expr) : Bool :=
  match e.getAppFn with
  | Expr.const n _ => n == ``Ty.TypeJudgment
  | _ => false

/--
`isTargetVarX e target_varname` checks whether the expression `e` is the AST node and whether `name = target_varname`.
-/
def isTargetVarX (e : Lean.Expr) (target_varname: String) : Bool :=
  if e.isAppOfArity ``Ast.Expr.var 1 then
    match e.appArg! with
    | Expr.lit (Literal.strVal name) => target_varname == name
    | _ => false
  else
    false

/--
`tactic autoTy target` is an automation tactic specialized for goals of the form
`Ty.TypeJudgment ...`.

Behavior summary:

* If the goal *is* a `Ty.TypeJudgment`, try `constructor`.
* Otherwise, attempt several auxiliary lemmas heuristically:
  - `var_has_subtype_in_tyenv`
  - `constZ_refine_lt`
  - `get_update_self`
  - `get_update_ne`
  - `assumption`
  - `simp [Ast.nu]`
* Automatically stops when the fourth argument of the judgment matches the
  user-provided `target` string (typically the variable `"x"` you want to stop at).
* Uses a bounded recursion depth (default: 512) to avoid non-termination.

This tactic is intended as a lightweight, heuristic "auto" for typing judgments
in small developments.
-/
elab "autoTy" target:str : tactic => do
  let rec loop (depth : Nat) : TacticM Unit := do
    if depth == 0 then return ()
    let g ← Tactic.getMainGoal
    let t ← g.getType >>= instantiateMVars

    let args := t.getAppArgs
    if args.size > 3 then
        let targetExpr := args[3]!
        if isTargetVarX targetExpr target.getString then
          return ()
          --Lean.logInfo "Target variable 'x' found. Stopping autoTy."

    let _ ← tryLean (evalTactic (← `(tactic| apply var_has_subtype_in_tyenv)))
    let _ ← tryLean (evalTactic (← `(tactic| apply constZ_refine_lt)))
    let _ ← tryLean (evalTactic (← `(tactic| simp [Ast.nu])))
    let _ ← tryLean (evalTactic (← `(tactic| assumption)))
    let applied ←
      if isTyTypeJudgment t then
        do
          --Lean.logInfo m!"constructor applied!"
          evalTactic (← `(tactic| constructor))
          pure true
      else pure false
    if ¬applied then
      let success ← tryLean (evalTactic (← `(tactic| apply get_update_self)))
      if ¬success then
        let success' ← tryLean (evalTactic (← `(tactic| apply get_update_ne)))
        if success' then
          let _ ← tryLean (evalTactic (← `(tactic| simp)))
        if ¬success' then
          let _ ← tryLean (evalTactic (← `(tactic| assumption)))
          pure ()
    loop (depth - 1)
  loop 512

/-- Step result -/
inductive VCGStepResult
  | done
  | progress (goals : List MVarId)
  | noAction

/--
Infer the expected Value constructor from the AST expression.
-/
def getExpectedValueCtor (e : Lean.Expr) : Option Name :=
  let fn := e.getAppFn
  if fn.isConst then
    let n := fn.constName!
    if n == ``Ast.Expr.fieldExpr || n == ``Ast.Expr.constF || n == ``Ast.Expr.toF then
      some ``Ast.Value.vF
    else if n == ``Ast.Expr.uintExpr || n == ``Ast.Expr.constN || n == ``Ast.Expr.len || n == ``Ast.Expr.toN || n == ``Ast.Expr.StoU then
      some ``Ast.Value.vN
    else if n == ``Ast.Expr.sintExpr || n == ``Ast.Expr.constInt || n == ``Ast.Expr.UtoS then
      some ``Ast.Value.vInt
    else if n == ``Ast.Expr.boolExpr || n == ``Ast.Expr.binRel || n == ``Ast.Expr.constBool then
      some ``Ast.Value.vBool
    else if n == ``Ast.Expr.arr then
      some ``Ast.Value.vArr
    else if n == ``Ast.Expr.lam then
      some ``Ast.Value.vClosure
    else
      none
  else
    none

/--
Expressions that represent a computation step to be broken down.
-/
def isDestructibleExpr (e : Lean.Expr) : Bool :=
  let fn := e.getAppFn
  if fn.isConst then
    let n := fn.constName!
    n == ``Ast.Expr.letIn ||
    n == ``Ast.Expr.assertE ||
    n == ``Ast.Expr.fieldExpr ||
    n == ``Ast.Expr.uintExpr ||
    n == ``Ast.Expr.sintExpr ||
    n == ``Ast.Expr.boolExpr ||
    n == ``Ast.Expr.binRel ||
    n == ``Ast.Expr.branch ||
    n == ``Ast.Expr.app ||
    n == ``Ast.Expr.arrIdx ||
    n == ``Ast.Expr.len ||
    n == ``Ast.Expr.toN ||
    n == ``Ast.Expr.toF ||
    n == ``Ast.Expr.constF ||
    n == ``Ast.Expr.lookup
  else
    false

/--
Canonicalize a value variable `v` into `Ctor x` if the `EvalProp` dictates it.
Example: `EvalProp ... (fieldExpr ...) v` => `v` becomes `Value.vF ...`.
-/
def canonicalizeValueFromExpr (mvarId : MVarId) (hypFVarId : FVarId) : TacticM VCGStepResult := do
  let ctx ← mvarId.withContext getLCtx
  let some decl := ctx.find? hypFVarId | return .noAction
  let type ← instantiateMVars decl.type

  if !type.isAppOfArity ``Eval.EvalProp 5 then return .noAction
  let rawExprArg := type.getArg! 3
  let exprArg ← whnf rawExprArg
  let valArg := type.getArg! 4
  if !valArg.isFVar then return .noAction

  let some ctorName := getExpectedValueCtor exprArg | return .noAction

  try
    let (nextGoal, eqName) ← mvarId.withContext do
      -- 1. Prove ∃ x, v = Ctor x
      let shapeThm ← mkFreshExprMVar none
      let (_, shapeGoal) ← shapeThm.mvarId!.intro1
      shapeGoal.withContext do
         let casesGoals ← shapeGoal.cases hypFVarId
         casesGoals.forM fun s => do
           let (vars, s') ← s.mvarId.intros
           let witnesses := vars.map Expr.fvar
           let s'' ← s'.existsi witnesses.toList
           s''.refl

      -- 2. Assert theorem and decompose
      let shapeType ← inferType shapeThm
      let mvarId2 ← mvarId.assert (Name.mkSimple "h_shape") shapeType shapeThm
      let (hExistsFVarId, mvarId3) ← mvarId2.intro1P

      let subgoals ← mvarId3.cases hExistsFVarId
      if let some subgoal := subgoals[0]? then
        if let some hEqExpr := subgoal.fields.back? then
           if hEqExpr.isFVar then
             let decl ← hEqExpr.fvarId!.getDecl
             return (subgoal.mvarId, decl.userName)
           else failure
        else failure
      else failure

    replaceMainGoal [nextGoal]
    evalTactic (← `(tactic| simp only [$(mkIdent eqName):term] at *))
    let newGoals ← getGoals
    if newGoals.isEmpty then return .done else return .progress newGoals
  catch _ => return .noAction

/-- Destruct an EvalProp hypothesis using cases. -/
def destructEvalProp (mvarId : MVarId) (hypFVarId : FVarId) : TacticM VCGStepResult := do
  try
    let subgoals ← mvarId.withContext do
      let (newGoals) ← mvarId.cases hypFVarId
      return newGoals.map (·.mvarId) |>.toList

    replaceMainGoal subgoals
    if subgoals.isEmpty then return .done else return .progress subgoals
  catch _ => return .noAction

/--
  Look for equalities `v = Value.vF ...` (or reversed) in context and use them
  to rewrite everything. This cleans up what `cases` might leave behind.
-/
def propagateEqualities (mvarId : MVarId) : TacticM VCGStepResult := do
  let ctx ← mvarId.withContext getLCtx
  for decl in ctx do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    if let some (_, lhs, rhs) := type.eq? then
       -- Check if one side is a variable and the other is a Value constructor
       let isValCtor (e : Lean.Expr) := e.isApp && e.getAppFn.isConst && e.getAppFn.constName!.toString.startsWith "Runwai.Ast.Value.v"

       if lhs.isFVar && isValCtor rhs then
         try
           evalTactic (← `(tactic| simp only [$(mkIdent decl.userName):term] at *))
           return .progress (← getGoals)
         catch _ => continue

       if rhs.isFVar && isValCtor lhs then
          try
           evalTactic (← `(tactic| simp only [← $(mkIdent decl.userName):term] at *))
           return .progress (← getGoals)
         catch _ => continue
  return .noAction

/--
  **Fallback**: Identify variables caught in `match` expressions (common in EvalRelOp)
  and brute-force split them with `cases`. This resolves stuck `evalRelOp` proofs.
-/
def splitMatchVariables (mvarId : MVarId) : TacticM VCGStepResult := do
  let ctx ← mvarId.withContext getLCtx
  for decl in ctx do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type

    -- Heuristic: If hypothesis is `lhs = some true` (typical for success flags)
    if let some (_, lhs, rhs) := type.eq? then
       if rhs.isAppOfArity ``Option.some 1 &&
          (rhs.getArg! 0).isAppOfArity ``Bool.true 0 then

          -- Find a generic Value-typed variable in the lhs
          let foundVal ← lhs.withApp fun fn args => do
             for arg in args do
               if arg.isFVar then
                 let argType ← inferType arg
                 if argType.isConstOf ``Ast.Value then
                    return some arg.fvarId!
             return none

          if let some fvarId := foundVal then
             try
               let subgoals ← mvarId.withContext do
                  let (newGoals) ← mvarId.cases fvarId
                  return newGoals.map (·.mvarId) |>.toList

               replaceMainGoal subgoals
               -- After splitting, simplify immediately to kill invalid branches
               evalTactic (← `(tactic|
                  all_goals (try simp only [
                    Eval.evalRelOp, Option.some.injEq, decide_eq_true_eq,
                    Bool.true_eq_false, Bool.false_eq_true
                  ] at *)
               ))
               return .progress (← getGoals)
             catch _ => continue
  return .noAction

/--
Normalize an expression enough that two expressions representing the same
evaluation key will compare equal modulo definitional equality.

This performs:
* instantiation of metavariables,
* weak-head normalization (`whnf`),
* full β/η reduction (`reduce`).

The result is a canonical form suitable for hashing or for use as a key
when comparing `EvalProp` premises.
-/
def normalizeExpr (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← instantiateMVars e
  let e ← whnf e
  -- βη簡約を追加
  let e ← reduce e
  return e

/--
`unifyEvaluations` scans the local context for hypotheses of the form `Eval.EvalProp _ _ _ e v` and attempts to detect whether two such hypotheses evaluate the *same* expression `e` (up to definitional equality). If duplicates are found, the tactic invokes the determinism lemma to derive an equality between the two result values, introduces that equality as a new hypothesis, and then simplifies the goal using `simp_all`.

1. Traverse the local context.
2. For each `EvalProp` hypothesis, extract the expression argument `e`
   and normalize it via `normalizeExpr`.
3. Maintain a hashmap `(normalized e) ↦ (value, fvarId)` recording the
   first occurrence of each expression.
4. When encountering a second hypothesis whose expression is
   definitionally equal (`isDefEq`) to a previously seen one,
   use `evalprop_deterministic` to obtain an equality between the two
   result values.
5. Insert that equality into the context, simplify the goal, and return
   progress.
6. If no duplicates are detected, the tactic returns `.noAction`.

The result indicates whether the tactic made progress or completely
resolved the goal.
-/
def unifyEvaluations (mvarId : MVarId) : TacticM VCGStepResult := do
  let ctx ← mvarId.withContext getLCtx
  -- Store: normalized expression ↦ (value, hypothesis-id)
  -- Used to detect duplicate evaluations modulo defEq.
  let mut seen : Std.HashMap Lean.Expr (Lean.Expr × FVarId) := {}

  for decl in ctx do
    -- Skip implementation-detail local hypotheses created by Lean
    if decl.isImplementationDetail then continue
    try
      let type ← instantiateMVars decl.type
      if type.isAppOfArity ``Eval.EvalProp 5 then
        -- The 4th argument is the expression `e`
        let rawExprArg := type.getArg! 3
        let eNorm ← normalizeExpr rawExprArg

    -- The 5th argument is the value `v`
        let v := type.getArg! 4

        -- Look for a previously seen expression `defEq` to this one
        let mut found? : Option (Lean.Expr × FVarId) := none
        for (k, entry) in seen.toList do
          if ← isDefEq eNorm k then
            found? := some entry
            break

        match found? with
        | none =>
            seen := seen.insert eNorm (v, decl.fvarId)

        | some (v_prev, h_prev) =>
      -- Found a duplicate evaluation: apply determinism lemma.
            let (nextGoal, eqName) ← mvarId.withContext do
              let hCurr := Expr.fvar decl.fvarId
              let hPrev := Expr.fvar h_prev
              let proof ← mkAppM ``evalprop_deterministic #[hCurr, hPrev]
              let eqType ← inferType proof

        -- Introduce equality as a fresh hypothesis
              let g ← mvarId.assert (Name.mkSimple "h_det") eqType proof
              let (_, g') ← g.intro1P
              return (g', decl.fvarId)

            replaceMainGoal [nextGoal]

      -- Rewrite everything using the derived equality
            evalTactic (← `(tactic| simp_all))

            let goals ← getGoals
            if goals.isEmpty then
              return .done
            else
              return .progress goals

    catch _ => continue

  return .noAction

partial def vcgLoop : TacticM Unit := do
  let mvarId ← getMainGoal
  if (← mvarId.isAssigned) then return ()

  let ctx ← mvarId.withContext getLCtx

  -- 1. Canonicalize value shapes from expression types
  for decl in ctx do
    if decl.isImplementationDetail then continue
    match (← canonicalizeValueFromExpr mvarId decl.fvarId) with
    | .done => replaceMainGoal []; return ()
    | .progress gs => replaceMainGoal gs; return (← vcgLoop)
    | .noAction => continue

  -- 2. Unification using `evalprop_deterministic`
  match (← unifyEvaluations mvarId) with
  | .done => replaceMainGoal []; return ()
  | .progress gs => replaceMainGoal gs; return (← vcgLoop)
  | .noAction => pure ()

  -- 2. Propagate known equalities
  match (← propagateEqualities mvarId) with
  | .done => replaceMainGoal []; return ()
  | .progress gs => replaceMainGoal gs; return (← vcgLoop)
  | .noAction => pure ()

  -- 3. Destruct EvalProp hypotheses
  for decl in ctx do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    if type.isAppOfArity ``Eval.EvalProp 5 then
      let rawExprArg := type.getArg! 3
      let exprArg ← whnf rawExprArg

      if isDestructibleExpr exprArg then
        match (← destructEvalProp mvarId decl.fvarId) with
        | .done => replaceMainGoal []; return ()
        | .progress gs => replaceMainGoal gs; return (← vcgLoop)
        | .noAction => continue

  -- 4. Fallback: Split variables stuck in matches
  match (← splitMatchVariables mvarId) with
  | .done => replaceMainGoal []; return ()
  | .progress gs => replaceMainGoal gs; return (← vcgLoop)
  | .noAction => pure ()

  return ()

elab "runwai_vcg" : tactic => do
  vcgLoop
  -- Final arithmetic simplification
  evalTactic (← `(tactic|
    try simp only [
      Eval.evalFieldOp, Eval.evalUIntOp, Eval.evalSIntOp,
      Eval.evalRelOp, Eval.evalBoolOp,
      Env.getVal, Env.updateVal, Env.getTy,
      Option.some.injEq, if_true, if_false,
      decide_eq_true_eq
    ] at *
  ))

theorem vcg_branch_intro {σ T Δ c t f vc vt vf v}
    (hc : Eval.EvalProp σ T Δ c (Ast.Value.vBool vc))
    (ht : Eval.EvalProp σ T Δ t vt)
    (hf : Eval.EvalProp σ T Δ f vf)
    (hv : v = if vc then vt else vf) :
    Eval.EvalProp σ T Δ (Ast.Expr.branch c t f) v := by
  subst hv
  split
  · apply Eval.EvalProp.IfTrue
    rename_i h
    rw[h] at hc
    exact hc
    exact ht
  · apply Eval.EvalProp.IfFalse
    rename_i h
    simp at h
    rw[h] at hc
    exact hc
    exact hf

theorem vcg_rel_intro {σ T Δ e1 e2 v1 v2 op v_bool v}
    (h1 : Eval.EvalProp σ T Δ e1 v1)
    (h2 : Eval.EvalProp σ T Δ e2 v2)
    (hop : Eval.evalRelOp op v1 v2 = some v_bool)
    (hv : v = Ast.Value.vBool v_bool) :
    Eval.EvalProp σ T Δ (Ast.Expr.binRel e1 op e2) v := by
  subst hv
  apply Eval.EvalProp.Rel
  · exact h1
  · exact h2
  · exact hop

theorem vcg_constF_intro {σ T Δ f v}
    (hv : v = Ast.Value.vF f) :
    Eval.EvalProp σ T Δ (Ast.Expr.constF f) v := by
  subst hv; apply Eval.EvalProp.ConstF

theorem vcg_var_intro {σ T Δ x v}
    (hv : Env.getVal σ x = v) :
    Eval.EvalProp σ T Δ (Ast.Expr.var x) v := by
  apply Eval.EvalProp.Var; assumption
