import Runwai.Typing
import Runwai.Gadget.Utils
import Runwai.Gadget.EnvLemmas
import Runwai.Gadget.EvalLemmas
import Runwai.Gadget.TypingLemmas
import Runwai.Gadget.FieldLemmas

open Ast
open Lean Meta Elab Tactic

-- ヘルパー
def tryLean (tac : TacticM Unit) : TacticM Bool := do
  try
    tac
    pure true
  catch _ =>
    pure false

def isTyTypeJudgment (e : Lean.Expr) : Bool :=
  match e.getAppFn with
  | Expr.const n _ => n == ``Ty.TypeJudgment
  | _ => false

def isTargetVarX (e : Lean.Expr) (target_varname: String) : Bool :=
  -- Expr.var (小文字) か Expr.Var (大文字) かは定義に合わせてください
  -- ここでは Ast.Expr.var と仮定しています
  if e.isAppOfArity ``Ast.Expr.var 1 then
    match e.appArg! with
    | Expr.lit (Literal.strVal name) => target_varname == name
    | _ => false
  else
    false

/--
Ty.TypeJudgment 専用の自動化 tactic。
- ゴールが Ty.TypeJudgment 型なら constructor
- それ以外は try get_update_self や assumption
- repeat で繰り返す
-/
elab "autoTy" x:ident : tactic => do
  let target_varname := x.getId.toString

  let rec loop (depth : Nat) : TacticM Unit := do
    if depth == 0 then return ()
    let g ← Tactic.getMainGoal
    let t ← g.getType >>= instantiateMVars

    let args := t.getAppArgs
    if args.size > 3 then
        let targetExpr := args[3]!
        if isTargetVarX targetExpr target_varname then
          return ()
          --Lean.logInfo "Target variable 'x' found. Stopping autoTy."

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

/-- ゴールの EvalProp (Branch) を if文の等式に変換する補題 -/
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

/-- ゴールの EvalProp (Rel) を decide の等式に変換する補題 -/
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

/-- ゴールの EvalProp (ConstF) を値の等式に変換する補題 -/
theorem vcg_constF_intro {σ T Δ f v}
    (hv : v = Ast.Value.vF f) :
    Eval.EvalProp σ T Δ (Ast.Expr.constF f) v := by
  subst hv; apply Eval.EvalProp.ConstF

/-- ゴールの EvalProp (Var) を環境の等式に変換する補題 -/
theorem vcg_var_intro {σ T Δ x v}
    (hv : Env.getVal σ x = v) :
    Eval.EvalProp σ T Δ (Ast.Expr.var x) v := by
  apply Eval.EvalProp.Var; assumption

/--
EvalProp 形式のゴールを、これらの補題を使って数式（値の等式）に分解・変換する
-/
syntax "runwai_goal_to_math" : tactic
macro_rules
| `(tactic| runwai_goal_to_math) => `(tactic|
    repeat (first
      | apply vcg_constF_intro
      | apply vcg_var_intro; assumption -- 変数は環境にあれば即解決
      | apply vcg_rel_intro; assumption; assumption -- 引数の評価はコンテキストから探す
      | apply vcg_branch_intro; assumption; assumption; assumption -- 条件分岐もコンテキストから探す
      -- それ以外のケースは EvalProp のまま残すか、通常の apply で処理
    )
  )

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

def splitMatchVariables' (mvarId : MVarId) : TacticM VCGStepResult := do
  let ctx ← mvarId.withContext getLCtx
  for decl in ctx do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    if let some (_, lhs, rhs) := type.eq? then
       let isSome (e : Lean.Expr) := e.isAppOfArity ``Option.some 1

       if isSome rhs || isSome lhs then
          let targetExpr := if isSome rhs then lhs else rhs

          let candidatesRef ← IO.mkRef ([] : List FVarId)

          -- 式中の変数を収集
          targetExpr.forEach fun e => do
             if e.isFVar then
                -- 型チェックはMetaM内で行う必要があるためここでは収集だけ
                candidatesRef.modify (fun cs => e.fvarId! :: cs)
             --return ()

          let foundVal ← candidatesRef.get
          let foundVal := foundVal.eraseDups

          for fvarId in foundVal do
             try
               let subgoals ← mvarId.withContext do
                  let type ← inferType (Expr.fvar fvarId)
                  if type.isConstOf ``Ast.Value then
                    let (newGoals) ← mvarId.cases fvarId
                    return some (newGoals.map (·.mvarId) |>.toList)
                  else
                    return none

               if let some newGoals := subgoals then
                 replaceMainGoal newGoals
                 -- 分解直後に矛盾する枝(None = Some等)を消すためにsimpする
                 evalTactic (← `(tactic|
                    all_goals (try simp only [
                      Eval.evalRelOp, Eval.evalFieldOp, Eval.evalUIntOp, Eval.evalSIntOp, Eval.evalBoolOp,
                      Option.some.injEq, Option.noConfusion,
                      decide_eq_true_eq, Bool.true_eq_false, Bool.false_eq_true
                    ] at *)
                 ))
                 return .progress (← getGoals)
             catch _ => continue
  return .noAction

/-- normalize an expression enough to compare evaluation keys -/
def normalizeExpr (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← instantiateMVars e
  let e ← whnf e
  -- βη簡約を追加
  let e ← reduce e
  return e

def unifyEvaluations (mvarId : MVarId) : TacticM VCGStepResult := do
  let ctx ← mvarId.withContext getLCtx
  -- Expr のキー比較には reduce 後のノーマルフォームを使う
  let mut seen : Std.HashMap Lean.Expr (Lean.Expr × FVarId) := {}

  for decl in ctx do
    if decl.isImplementationDetail then continue
    try
      let type ← instantiateMVars decl.type
      if type.isAppOfArity ``Eval.EvalProp 5 then
        -- e を取り出して正規化
        let rawExprArg := type.getArg! 3
        let eNorm ← normalizeExpr rawExprArg
        let v := type.getArg! 4

        -- ★ defEq による式一致チェックに変更
        let mut found? : Option (Lean.Expr × FVarId) := none
        for (k, entry) in seen.toList do
          if ← isDefEq eNorm k then
            found? := some entry
            break

        match found? with
        | none =>
            seen := seen.insert eNorm (v, decl.fvarId)

        | some (v_prev, h_prev) =>
            -- すでに defEq な e が存在したので決定性定理を使う
            --if ← isDefEq v v_prev then
            --  continue

            let (nextGoal, eqName) ← mvarId.withContext do
              let hCurr := Expr.fvar decl.fvarId
              let hPrev := Expr.fvar h_prev
              let proof ← mkAppM ``evalprop_deterministic #[hCurr, hPrev]
              let eqType ← inferType proof
              let g ← mvarId.assert (Name.mkSimple "h_det") eqType proof
              let (_, g') ← g.intro1P
              return (g', decl.fvarId)

            replaceMainGoal [nextGoal]

            -- 得られた等式で全体を書き換える
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

  -- 2. 評価結果の統合 (Unification using evalprop_deterministic)
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

partial def vcgLoop' : TacticM Unit := do
  let mvarId ← getMainGoal
  if (← mvarId.isAssigned) then return ()

  match (← unifyEvaluations mvarId) with
  | .done => replaceMainGoal []; return ()
  | .progress gs => replaceMainGoal gs; return (← vcgLoop)
  | .noAction => pure ()

  -- 4. Fallback: Split variables stuck in matches
  match (← splitMatchVariables' mvarId) with
  | .done => replaceMainGoal []; return ()
  | .progress gs => replaceMainGoal gs; return (← vcgLoop)
  | .noAction => pure ()


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

elab "runwai_vcga" : tactic => do
  vcgLoop'

abbrev iszero_func: Ast.Expr :=
  (.lam "x" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "y" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "inv" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (.letIn "u₁" (.assertE (.var "y") (.fieldExpr (.fieldExpr (.fieldExpr (.constF 0) .sub (.var "x")) .mul (.var "inv")) (.add) (.constF 1)))
    (.letIn "u₂" (.assertE (.fieldExpr (.var "x") .mul (.var "y")) (.constF 0)) (.var "u₂"))))))

lemma isZero_eval_eq_branch_semantics {x y inv: Ast.Expr} {σ: Env.ValEnv} {T: Env.TraceEnv} {Δ: Env.ChipEnv}
  (h₁ : Eval.EvalProp σ T Δ (exprEq y ((((Expr.constF 0).fieldExpr FieldOp.sub x).fieldExpr FieldOp.mul inv).fieldExpr
                  FieldOp.add (Expr.constF 1))) (Value.vBool true))
  (h₂ : Eval.EvalProp σ T Δ (exprEq (x.fieldExpr FieldOp.mul y) (Expr.constF 0)) (Value.vBool true))
  (hx : Eval.EvalProp σ T Δ x xv) (hy : Eval.EvalProp σ T Δ y yv) (hinv : Eval.EvalProp σ T Δ inv invv) :
  Eval.EvalProp σ T Δ (exprEq y (.branch (x.binRel RelOp.eq (Expr.constF 0)) (Expr.constF 1) (Expr.constF 0))) (Value.vBool true) := by {
  runwai_vcg
  rename_i v₁ v₂ ih₁ ih₂ r v₃ v₄ v₅ ih₄ ih₅ ih₆ ih₇ f₁ f₂ h₂ h₃ h₄ x_val h₅
  rw[← ih₆] at ih₁
  rw[← h₄] at ih₁
  rw[← ih₄] at ih₇
  simp_all
  rw[← h₄] at hy
  apply Eval.EvalProp.Rel; exact hy
  have h₃: x_val = 0 → Eval.EvalProp σ T Δ ((x.binRel RelOp.eq (Expr.constF 0)).branch (Expr.constF 1) (Expr.constF 0)) (Value.vF 1) := by {
    intro h
    apply Eval.EvalProp.IfTrue; apply Eval.EvalProp.Rel; exact hx
    apply Eval.EvalProp.ConstF; simp [Eval.evalRelOp]
    rw[← h_det]
    simp_all;
    apply Eval.EvalProp.ConstF
  }
  have h₄: x_val ≠ 0 → Eval.EvalProp σ T Δ ((x.binRel RelOp.eq (Expr.constF 0)).branch (Expr.constF 1) (Expr.constF 0)) (Value.vF 0) := by {
    intro h
    apply Eval.EvalProp.IfFalse; apply Eval.EvalProp.Rel; exact hx
    apply Eval.EvalProp.ConstF; simp [Eval.evalRelOp]
    rw[← h_det]
    simp_all;
    apply Eval.EvalProp.ConstF
  }
  have h₅: Eval.EvalProp σ T Δ ((x.binRel RelOp.eq (Expr.constF 0)).branch (Expr.constF 1) (Expr.constF 0)) (if x_val = 0 then (Value.vF 1) else (Value.vF 0)) := by {
    by_cases h : x_val = 0
    . simp_all
    . simp_all
  }
  exact h₅
  by_cases hz: x_val = 0
  . simp_all; rw[← h₄]; simp; rw[← h₅] at h₂; rw [zero_mul] at h₂; rw[← h₂];
  . simp_all; rw[← h₄]; simp; simp [← h_det] at ih₅; simp_all;
}

lemma isZero_typing_soundness (Δ: Env.ChipEnv) (Η: Env.UsedNames) (Γ: Env.TyEnv) (φ₁ φ₂ φ₃: Ast.Predicate)
  (x y inv u₁ u₂: String)
  (htx: Env.getTy Γ x = (Ty.refin Ast.Ty.field φ₁))
  (hty: Env.getTy Γ y = (Ty.refin Ast.Ty.field φ₂))
  (htinv: @Ty.TypeJudgment Δ Γ Η (.var inv) (Ty.refin Ast.Ty.field φ₃))
  (hne₁: ¬ x = u₁)
  (hne₂: ¬ y = u₁)
  (hne₃: ¬ u₁ = u₂)
  (hne₄: ¬ y = u₂)
  (hne₅: ¬ x = u₂)
  (hne₇: u₂ ≠ nu):
  @Ty.TypeJudgment Δ Γ Η
    (Ast.Expr.letIn u₁ (.assertE (.var y) (.fieldExpr (.fieldExpr (.fieldExpr (.constF 0) .sub (.var x)) .mul (.var inv)) (.add) (.constF 1)))
      (Ast.Expr.letIn u₂ (.assertE (.fieldExpr (.var x) .mul (.var y)) (.constF 0)) (.var u₂)))
    (Ty.refin Ast.Ty.unit (Ast.Predicate.ind (exprEq (.var y) (.branch (.binRel (.var x) (.eq) (.constF 0)) (.constF 1) (.constF 0))))) := by {
    autoTy u₂
    rw[← htx]; apply get_update_ne; exact hne₁
    apply Ty.TypeJudgment.TE_Var
    rw[← hty]; apply get_update_ne; exact hne₂
    apply Ty.TypeJudgment.TE_ConstF
    have h_sub : @Ty.SubtypeJudgment Δ (Env.updateTy
      (Env.updateTy Γ u₁
        (Ty.unit.refin
          (Ast.Predicate.ind
            (exprEq (Expr.var y)
              ((((Expr.constF 0).fieldExpr FieldOp.sub (.var x)).fieldExpr FieldOp.mul (Expr.var inv)).fieldExpr FieldOp.add
                (Expr.constF 1))))))
      u₂ (Ty.unit.refin (Ast.Predicate.ind (exprEq ((Expr.var x).fieldExpr FieldOp.mul (Expr.var y)) (Expr.constF 0)))))
      (Ty.unit.refin (Ast.Predicate.ind (exprEq ((Expr.var x).fieldExpr FieldOp.mul (Expr.var y)) (Expr.constF 0))))
      (Ty.unit.refin
        (Ast.Predicate.ind (exprEq (Expr.var y) (((Expr.var x).binRel RelOp.eq (Expr.constF 0)).branch (Expr.constF 1) (Expr.constF 0))))) := by {
        apply Ty.SubtypeJudgment.TSub_Refine
        apply Ty.SubtypeJudgment.TSub_Refl
        unfold PropSemantics.tyenvToProp
        simp[PropSemantics.predToProp]
        intro σ T e h₂
        set φ₁ := (Ast.Predicate.ind
          (exprEq (Expr.var y)
            ((((Expr.constF 0).fieldExpr FieldOp.sub (Expr.var x)).fieldExpr FieldOp.mul (Expr.var inv)).fieldExpr FieldOp.add
              (Expr.constF 1))))
        set φ₂ := (Ast.Predicate.ind (exprEq ((Expr.var x).fieldExpr FieldOp.mul (Expr.var y)) (Expr.constF 0)))
        have h₃ := h₂ u₁ (Ty.unit.refin φ₁)
        have h₄: Env.getTy (Env.updateTy (Env.updateTy Γ u₁ (Ty.unit.refin φ₁)) u₂ (Ty.unit.refin φ₂)) u₁ = (Ty.unit.refin φ₁) := by {
          apply get_update_ne_of_get
          exact hne₃
          apply get_update_self
        }
        have h₅ := h₃ h₄
        rw[h₄] at h₅
        simp at h₅
        unfold PropSemantics.predToProp PropSemantics.exprToProp at h₅
        intro h₁
        apply isZero_eval_eq_branch_semantics h₅ h₁
        repeat apply Eval.EvalProp.Var; rfl
      }
    apply Ty.TypeJudgment.TE_SUB
    apply var_has_type_in_tyenv
    apply get_update_self
    simp [hne₇]
    exact h_sub
    rfl
    simp [renameTy, renameVar]
    rw [if_neg hne₄, if_neg hne₅]
    simp [renameVar]
    exact ⟨hne₂, hne₁⟩
}

lemma iszero_func_typing_soundness (Δ: Env.ChipEnv) (Η: Env.UsedNames) (Γ: Env.TyEnv) :
  @Ty.TypeJudgment Δ Γ Η iszero_func
    (Ty.func "x" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ty.func "y" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ty.func "inv" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
      (Ty.refin Ast.Ty.unit (Ast.Predicate.ind (exprEq (.var "y") (.branch (.binRel (.var "x") (.eq) (.constF 0)) (.constF 1) (.constF 0)))))))) := by {
      repeat
        apply Ty.TypeJudgment.TE_Abs
        apply get_update_self
      apply isZero_typing_soundness
      apply get_update_ne_of_get
      simp
      apply get_update_ne_of_get
      simp
      apply get_update_self
      apply get_update_ne_of_get
      simp
      apply get_update_self
      apply Ty.TypeJudgment.TE_Var
      apply get_update_self
      repeat simp; simp [Ast.nu]
    }

abbrev koalabear_word_range_checker_func: Ast.Expr :=
  (.lam "value_0" (field_lt_const 256)
  (.lam "value_1" (field_lt_const 256)
  (.lam "value_2" (field_lt_const 256)
  (.lam "value_3" (field_lt_const 256)
  (.lam "most_sig_byte_decomp_0" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "most_sig_byte_decomp_1" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "most_sig_byte_decomp_2" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "most_sig_byte_decomp_3" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "most_sig_byte_decomp_4" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "most_sig_byte_decomp_5" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "most_sig_byte_decomp_6" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "most_sig_byte_decomp_7" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "and_most_sig_byte_decomp_0_to_2" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "and_most_sig_byte_decomp_0_to_3" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "and_most_sig_byte_decomp_0_to_4" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "and_most_sig_byte_decomp_0_to_5" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "and_most_sig_byte_decomp_0_to_6" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "and_most_sig_byte_decomp_0_to_7" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (.letIn "b₀" (.assertE (.fieldExpr (.var "most_sig_byte_decomp_0") .mul (.fieldExpr (.var "most_sig_byte_decomp_0") .sub (.constF 1))) (.constF 0))
    (.letIn "b₁" (.assertE (.fieldExpr (.var "most_sig_byte_decomp_1") .mul (.fieldExpr (.var "most_sig_byte_decomp_1") .sub (.constF 1))) (.constF 0))
    (.letIn "b₂" (.assertE (.fieldExpr (.var "most_sig_byte_decomp_2") .mul (.fieldExpr (.var "most_sig_byte_decomp_2") .sub (.constF 1))) (.constF 0))
    (.letIn "b₃" (.assertE (.fieldExpr (.var "most_sig_byte_decomp_3") .mul (.fieldExpr (.var "most_sig_byte_decomp_3") .sub (.constF 1))) (.constF 0))
    (.letIn "b₄" (.assertE (.fieldExpr (.var "most_sig_byte_decomp_4") .mul (.fieldExpr (.var "most_sig_byte_decomp_4") .sub (.constF 1))) (.constF 0))
    (.letIn "b₅" (.assertE (.fieldExpr (.var "most_sig_byte_decomp_5") .mul (.fieldExpr (.var "most_sig_byte_decomp_5") .sub (.constF 1))) (.constF 0))
    (.letIn "b₆" (.assertE (.fieldExpr (.var "most_sig_byte_decomp_6") .mul (.fieldExpr (.var "most_sig_byte_decomp_6") .sub (.constF 1))) (.constF 0))
    (.letIn "b₇" (.assertE (.fieldExpr (.var "most_sig_byte_decomp_7") .mul (.fieldExpr (.var "most_sig_byte_decomp_7") .sub (.constF 1))) (.constF 0))
    (.letIn "u₁"
      (.assertE (bits_to_byte_expr "most_sig_byte_decomp_0" "most_sig_byte_decomp_1" "most_sig_byte_decomp_2" "most_sig_byte_decomp_3"
                                  "most_sig_byte_decomp_4" "most_sig_byte_decomp_5" "most_sig_byte_decomp_6" "most_sig_byte_decomp_7")
        (.var "value_3")
      )
      (.letIn "u₂" (.assertE (.var "most_sig_byte_decomp_7") (.constF 0))
      (.letIn "u₃" (.assertE (.var "and_most_sig_byte_decomp_0_to_2") (.fieldExpr (.var "most_sig_byte_decomp_0") .mul (.var "most_sig_byte_decomp_1")))
      (.letIn "u₄" (.assertE (.var "and_most_sig_byte_decomp_0_to_3") (.fieldExpr (.var "and_most_sig_byte_decomp_0_to_2") .mul (.var "most_sig_byte_decomp_2")))
      (.letIn "u₅" (.assertE (.var "and_most_sig_byte_decomp_0_to_4") (.fieldExpr (.var "and_most_sig_byte_decomp_0_to_3") .mul (.var "most_sig_byte_decomp_3")))
      (.letIn "u₆" (.assertE (.var "and_most_sig_byte_decomp_0_to_5") (.fieldExpr (.var "and_most_sig_byte_decomp_0_to_4") .mul (.var "most_sig_byte_decomp_4")))
      (.letIn "u₇" (.assertE (.var "and_most_sig_byte_decomp_0_to_6") (.fieldExpr (.var "and_most_sig_byte_decomp_0_to_5") .mul (.var "most_sig_byte_decomp_5")))
      (.letIn "u₈" (.assertE (.var "and_most_sig_byte_decomp_0_to_7") (.fieldExpr (.var "and_most_sig_byte_decomp_0_to_6") .mul (.var "most_sig_byte_decomp_6")))
      (.letIn "u₉" (.assertE (.constF 0) (.fieldExpr (.var "and_most_sig_byte_decomp_0_to_7") .mul (.var "value_0")))
      (.letIn "u₁₀" (.assertE (.constF 0) (.fieldExpr (.var "and_most_sig_byte_decomp_0_to_7") .mul (.var "value_1")))
      (.letIn "u₁₁" (.assertE (.constF 0) (.fieldExpr (.var "and_most_sig_byte_decomp_0_to_7") .mul (.var "value_2")))
        (.var "u₁₁"))))))))))))))))))))))))))))))))))))))

lemma koalabear_word_range_checker_subtype_soundness {Γ Δ}
  (hb₁: Env.getTy Γ "b₀" = some (bit_value_type "most_sig_byte_decomp_0"))
  (hb₂ : Env.getTy Γ "b₁" = some (bit_value_type "most_sig_byte_decomp_1"))
  (hb₃: Env.getTy Γ "b₂" = some (bit_value_type "most_sig_byte_decomp_2"))
  (hb₄ : Env.getTy Γ "b₃" = some (bit_value_type "most_sig_byte_decomp_3"))
  (hb₅: Env.getTy Γ "b₄" = some (bit_value_type "most_sig_byte_decomp_4"))
  (hb₆ : Env.getTy Γ "b₅" = some (bit_value_type "most_sig_byte_decomp_5"))
  (hb₇: Env.getTy Γ "b₆" = some (bit_value_type "most_sig_byte_decomp_6"))
  (hb₈ : Env.getTy Γ "b₇" = some (bit_value_type "most_sig_byte_decomp_7"))
  (hu₁: Env.getTy Γ "u₁" = some (Ast.Ty.unit.refin
                                  (Ast.Predicate.ind
                                    (Ast.exprEq
                                      (bits_to_byte_expr "most_sig_byte_decomp_0" "most_sig_byte_decomp_1" "most_sig_byte_decomp_2" "most_sig_byte_decomp_3"
                                                        "most_sig_byte_decomp_4" "most_sig_byte_decomp_5" "most_sig_byte_decomp_6" "most_sig_byte_decomp_7")
                                      (Ast.Expr.var "value_3")))))
  (hu₂: Env.getTy Γ "u₂" = some                               (Ast.Ty.unit.refin
                                (Ast.Predicate.ind
                                  (Ast.exprEq (Ast.Expr.var "most_sig_byte_decomp_7") (Ast.Expr.constF 0)))))
  (hu₃: Env.getTy Γ "u₃" = some (eq_mul_refinement "and_most_sig_byte_decomp_0_to_2" "most_sig_byte_decomp_0" "most_sig_byte_decomp_1"))
  (hu₄: Env.getTy Γ "u₄" = some (eq_mul_refinement "and_most_sig_byte_decomp_0_to_3" "and_most_sig_byte_decomp_0_to_2" "most_sig_byte_decomp_2"))
  (hu₅: Env.getTy Γ "u₅" = some (eq_mul_refinement "and_most_sig_byte_decomp_0_to_4" "and_most_sig_byte_decomp_0_to_3" "most_sig_byte_decomp_3"))
  (hu₆: Env.getTy Γ "u₆" = some (eq_mul_refinement "and_most_sig_byte_decomp_0_to_5" "and_most_sig_byte_decomp_0_to_4" "most_sig_byte_decomp_4"))
  (hu₇: Env.getTy Γ "u₇" = some (eq_mul_refinement "and_most_sig_byte_decomp_0_to_6" "and_most_sig_byte_decomp_0_to_5" "most_sig_byte_decomp_5"))
  (hu₈: Env.getTy Γ "u₈" = some (eq_mul_refinement "and_most_sig_byte_decomp_0_to_7" "and_most_sig_byte_decomp_0_to_6" "most_sig_byte_decomp_6"))
  (hu₉: Env.getTy Γ "u₉" = some                           (Ast.Ty.unit.refin
                  (Ast.Predicate.ind
                    (Ast.exprEq (Ast.Expr.constF 0)
                      ((Ast.Expr.var "and_most_sig_byte_decomp_0_to_7").fieldExpr Ast.FieldOp.mul
                        (Ast.Expr.var "value_0"))))))
  (hu₁₀: Env.getTy Γ "u₁₀" = some                           (Ast.Ty.unit.refin
                (Ast.Predicate.ind
                  (Ast.exprEq (Ast.Expr.constF 0)
                    ((Ast.Expr.var "and_most_sig_byte_decomp_0_to_7").fieldExpr Ast.FieldOp.mul
                      (Ast.Expr.var "value_1"))))))
  (hu₁₁: Env.getTy Γ "u₁₁" = some                           (Ast.Ty.unit.refin
                (Ast.Predicate.ind
                  (Ast.exprEq (Ast.Expr.constF 0)
                    ((Ast.Expr.var "and_most_sig_byte_decomp_0_to_7").fieldExpr Ast.FieldOp.mul
                      (Ast.Expr.var "value_2"))))))
  ( hl₀: Env.getTy Γ "value_0" = some (field_lt_const 256))
  ( hl₁: Env.getTy Γ "value_1" = some (field_lt_const 256))
  ( hl₂: Env.getTy Γ "value_2" = some (field_lt_const 256))
  ( hl₃: Env.getTy Γ "value_3" = some (field_lt_const 256))
  : @Ty.SubtypeJudgment Δ Γ
      (Ty.unit.refin (Predicate.ind (exprEq (Expr.constF 0) ((Expr.var "and_most_sig_byte_decomp_0_to_7").fieldExpr FieldOp.mul (Expr.var "value_2")))))
      (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind
              (.binRel (.uintExpr (.uintExpr (.uintExpr
                (.toN (.var "value_0")) .add (.uintExpr (.toN (.var "value_1")) .mul (.constN 256)))
                                        .add (.uintExpr (.toN (.var "value_2")) .mul (.constN (256^2))))
                                        .add (.uintExpr (.toN (.var "value_3")) .mul (.constN (256^3))))
              .lt (.constN 2130706433)))) := by {
    apply Ty.SubtypeJudgment.TSub_Refine
    apply Ty.SubtypeJudgment.TSub_Refl
    intro σ T v h₁ h₂

    have hb₁' := tyenv_to_eval_expr h₁ hb₁
    have hb₂' := tyenv_to_eval_expr h₁ hb₂
    have hb₃' := tyenv_to_eval_expr h₁ hb₃
    have hb₄' := tyenv_to_eval_expr h₁ hb₄
    have hb₅' := tyenv_to_eval_expr h₁ hb₅
    have hb₆' := tyenv_to_eval_expr h₁ hb₆
    have hb₇' := tyenv_to_eval_expr h₁ hb₇
    have hb₈' := tyenv_to_eval_expr h₁ hb₈
    have hu₁' := tyenv_to_eval_expr h₁ hu₁
    have hu₂' := tyenv_to_eval_expr h₁ hu₂
    have hu₃' := tyenv_to_eval_expr h₁ hu₃
    have hu₄' := tyenv_to_eval_expr h₁ hu₄
    have hu₅' := tyenv_to_eval_expr h₁ hu₅
    have hu₆' := tyenv_to_eval_expr h₁ hu₆
    have hu₇' := tyenv_to_eval_expr h₁ hu₇
    have hu₈' := tyenv_to_eval_expr h₁ hu₈
    have hu₉' := tyenv_to_eval_expr h₁ hu₉
    have hu₁₀' := tyenv_to_eval_expr h₁ hu₁₀
    have hu₁₁' := tyenv_to_eval_expr h₁ hu₁₁
    have hl₀' := tyenv_dep_to_eval_expr h₁ hl₀
    have hl₁' := tyenv_dep_to_eval_expr h₁ hl₁
    have hl₂' := tyenv_dep_to_eval_expr h₁ hl₂
    have hl₃' := tyenv_dep_to_eval_expr h₁ hl₃

    have hb₁'' := eval_bit_expr_val hb₁'
    have hb₂'' := eval_bit_expr_val hb₂'
    have hb₃'' := eval_bit_expr_val hb₃'
    have hb₄'' := eval_bit_expr_val hb₄'
    have hb₅'' := eval_bit_expr_val hb₅'
    have hb₆'' := eval_bit_expr_val hb₆'
    have hb₇'' := eval_bit_expr_val hb₇'
    have hb₈'' := eval_bit_expr_val hb₈'
    have hu₁' := eval_bits_to_byte_expr_val hu₁'
    have hu₃'' := eval_mul_expr_val hu₃'
    have hu₄'' := eval_mul_expr_val hu₄'
    have hu₅'' := eval_mul_expr_val hu₅'
    have hu₆'' := eval_mul_expr_val hu₆'
    have hu₇'' := eval_mul_expr_val hu₇'
    have hu₈'' := eval_mul_expr_val hu₈'
    have hu₉'' := eval_eq_const_mul_val hu₉'
    have hu₁₀'' := eval_eq_const_mul_val hu₁₀'
    have hu₁₁'' := eval_eq_const_mul_val hu₁₁'

    have hvl₀ := eval_lt_lam_val hl₀'
    have hvl₁ := eval_lt_lam_val hl₁'
    have hvl₂ := eval_lt_lam_val hl₂'
    have hvl₃ := eval_lt_lam_val hl₃'

    cases hu₂'
    rename_i v₁ u₁ ih₁ ih₂ h_most_sig_byte_decomp_7_is_0
    cases ih₁
    cases ih₂
    simp [Eval.evalRelOp] at h_most_sig_byte_decomp_7_is_0
    cases v₁ <;> simp at h_most_sig_byte_decomp_7_is_0
    rename_i most_sig_byte_decomp_7 h_most_sig_byte_decomp_7_env

    unfold PropSemantics.predToProp PropSemantics.exprToProp

    obtain ⟨most_sig_byte_decomp_0, h⟩ := hb₁''
    obtain ⟨h_most_sig_byte_decomp_0_env, h_most_sig_byte_decomp_0⟩ := h
    obtain ⟨most_sig_byte_decomp_1, h⟩ := hb₂''
    obtain ⟨h_most_sig_byte_decomp_1_env, h_most_sig_byte_decomp_1⟩ := h
    obtain ⟨most_sig_byte_decomp_2, h⟩ := hb₃''
    obtain ⟨h_most_sig_byte_decomp_2_env, h_most_sig_byte_decomp_2⟩ := h
    obtain ⟨most_sig_byte_decomp_3, h⟩ := hb₄''
    obtain ⟨h_most_sig_byte_decomp_3_env, h_most_sig_byte_decomp_3⟩ := h
    obtain ⟨most_sig_byte_decomp_4, h⟩ := hb₅''
    obtain ⟨h_most_sig_byte_decomp_4_env, h_most_sig_byte_decomp_4⟩ := h
    obtain ⟨most_sig_byte_decomp_5, h⟩ := hb₆''
    obtain ⟨h_most_sig_byte_decomp_5_env, h_most_sig_byte_decomp_5⟩ := h
    obtain ⟨most_sig_byte_decomp_6, h⟩ := hb₇''
    obtain ⟨h_most_sig_byte_decomp_6_env, h_most_sig_byte_decomp_6⟩ := h
    obtain ⟨most_sig_byte_decomp_7', h⟩ := hb₈''
    obtain ⟨h_most_sig_byte_decomp_7_env', h_most_sig_byte_decomp_7⟩ := h
    rw[h_most_sig_byte_decomp_7_env] at h_most_sig_byte_decomp_7_env'
    simp at h_most_sig_byte_decomp_7_env'
    rw[← h_most_sig_byte_decomp_7_env'] at h_most_sig_byte_decomp_7

    obtain ⟨v₀, v₁, v₂, v₃, v₄, v₅, v₆, v₇, value_3, h⟩ := hu₁'
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h_value_3_env, h_msb_rec⟩ := h
    simp at h_most_sig_byte_decomp_0_env h_most_sig_byte_decomp_1_env
            h_most_sig_byte_decomp_2_env h_most_sig_byte_decomp_3_env
            h_most_sig_byte_decomp_4_env h_most_sig_byte_decomp_5_env
            h_most_sig_byte_decomp_6_env h_most_sig_byte_decomp_7_env
    rw[h_most_sig_byte_decomp_0_env] at h₁
    rw[h_most_sig_byte_decomp_1_env] at h₂
    rw[h_most_sig_byte_decomp_2_env] at h₃
    rw[h_most_sig_byte_decomp_3_env] at h₄
    rw[h_most_sig_byte_decomp_4_env] at h₅
    rw[h_most_sig_byte_decomp_5_env] at h₆
    rw[h_most_sig_byte_decomp_6_env] at h₇
    rw[h_most_sig_byte_decomp_7_env] at h₈
    simp at h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h_value_3_env
    rw[← h₁, ← h₂, ← h₃, ← h₄, ← h₅, ← h₆, ← h₇, ← h₈] at h_msb_rec

    obtain ⟨and_most_sig_byte_decomp_0_to_2, v₂, v₃, h⟩ := hu₃''
    obtain ⟨h_and_most_sig_byte_decomp_0_to_2_env, h₂, h₃, hamm₁⟩ := h
    simp at h_and_most_sig_byte_decomp_0_to_2_env h₂ h₃ hamm₁
    rw[h_most_sig_byte_decomp_0_env] at h₂
    rw[h_most_sig_byte_decomp_1_env] at h₃
    simp at h₂ h₃ hamm₁
    rw[← h₂, ← h₃] at hamm₁


    obtain ⟨and_most_sig_byte_decomp_0_to_3, v₂, v₃, h⟩ := hu₄''
    obtain ⟨h_and_most_sig_byte_decomp_0_to_3_env, h₂, h₃, hamm₂⟩ := h
    simp at h_and_most_sig_byte_decomp_0_to_3_env h₂ h₃ hamm₂
    rw[h_and_most_sig_byte_decomp_0_to_2_env] at h₂
    rw[h_most_sig_byte_decomp_2_env] at h₃
    simp at h₂ h₃ hamm₂
    rw[← h₂, ← h₃] at hamm₂

    obtain ⟨and_most_sig_byte_decomp_0_to_4, v₂, v₃, h⟩ := hu₅''
    obtain ⟨h_and_most_sig_byte_decomp_0_to_4_env, h₂, h₃, hamm₃⟩ := h
    simp at h_and_most_sig_byte_decomp_0_to_4_env h₂ h₃ hamm₃
    rw[h_and_most_sig_byte_decomp_0_to_3_env] at h₂
    rw[h_most_sig_byte_decomp_3_env] at h₃
    simp at h₂ h₃ hamm₃
    rw[← h₂, ← h₃] at hamm₃

    obtain ⟨and_most_sig_byte_decomp_0_to_5, v₂, v₃, h⟩ := hu₆''
    obtain ⟨h_and_most_sig_byte_decomp_0_to_5_env, h₂, h₃, hamm₄⟩ := h
    simp at h_and_most_sig_byte_decomp_0_to_5_env h₂ h₃ hamm₄
    rw[h_and_most_sig_byte_decomp_0_to_4_env] at h₂
    rw[h_most_sig_byte_decomp_4_env] at h₃
    simp at h₂ h₃ hamm₄
    rw[← h₂, ← h₃] at hamm₄

    obtain ⟨and_most_sig_byte_decomp_0_to_6, v₂, v₃, h⟩ := hu₇''
    obtain ⟨h_and_most_sig_byte_decomp_0_to_6_env, h₂, h₃, hamm₅⟩ := h
    simp at h_and_most_sig_byte_decomp_0_to_6_env h₂ h₃ hamm₅
    rw[h_and_most_sig_byte_decomp_0_to_5_env] at h₂
    rw[h_most_sig_byte_decomp_5_env] at h₃
    simp at h₂ h₃ hamm₅
    rw[← h₂, ← h₃] at hamm₅

    obtain ⟨and_most_sig_byte_decomp_0_to_7, v₂, v₃, h⟩ := hu₈''
    obtain ⟨h_and_most_sig_byte_decomp_0_to_7_env, h₂, h₃, hamm₆⟩ := h
    simp at h_and_most_sig_byte_decomp_0_to_7_env h₂ h₃ hamm₆
    rw[h_and_most_sig_byte_decomp_0_to_6_env] at h₂
    rw[h_most_sig_byte_decomp_6_env] at h₃
    simp at h₂ h₃ hamm₆
    rw[← h₂, ← h₃] at hamm₆

    obtain ⟨v₁, value_0, h⟩ := hu₉''
    obtain ⟨h₁, h_value_0_env, hav₀⟩ := h
    simp at h₁ h_value_0_env hav₀
    rw[h_and_most_sig_byte_decomp_0_to_7_env] at h₁
    simp at h₁
    rw[← h₁] at hav₀


    obtain ⟨v₁, value_1, h⟩ := hu₁₀''
    obtain ⟨h₁, h_value_1_env, hav₁⟩ := h
    simp at h₁ h_value_1_env hav₁
    rw[h_and_most_sig_byte_decomp_0_to_7_env] at h₁
    simp at h₁
    rw[← h₁] at hav₁

    obtain ⟨v₁, value_2, h⟩ := hu₁₁''
    obtain ⟨h₁, h_value_2_env, hav₂⟩ := h
    simp at h₁ h_value_2_env hav₂
    rw[h_and_most_sig_byte_decomp_0_to_7_env] at h₁
    simp at h₁
    rw[← h₁] at hav₂

    obtain ⟨v₁, h₁, hvl₀⟩ := hvl₀
    simp at h₁
    rw[h_value_0_env] at h₁
    simp at h₁
    rw[← h₁] at hvl₀

    obtain ⟨v₁, h₁, hvl₁⟩ := hvl₁
    simp at h₁
    rw[h_value_1_env] at h₁
    simp at h₁
    rw[← h₁] at hvl₁

    obtain ⟨v₁, h₁, hvl₂⟩ := hvl₂
    simp at h₁
    rw[h_value_2_env] at h₁
    simp at h₁
    rw[← h₁] at hvl₂

    obtain ⟨v₁, h₁, hvl₃⟩ := hvl₃
    simp at h₁
    rw[h_value_3_env] at h₁
    simp at h₁
    rw[← h₁] at hvl₃

    repeat
      repeat constructor
      assumption
    repeat constructor
    simp

    apply word32_range_under_koalabear
      (bit_value_mul_zero h_most_sig_byte_decomp_0) (bit_value_mul_zero h_most_sig_byte_decomp_1)
      (bit_value_mul_zero h_most_sig_byte_decomp_2) (bit_value_mul_zero h_most_sig_byte_decomp_3)
      (bit_value_mul_zero h_most_sig_byte_decomp_4) (bit_value_mul_zero h_most_sig_byte_decomp_5)
      (bit_value_mul_zero h_most_sig_byte_decomp_6) (bit_value_mul_zero h_most_sig_byte_decomp_7)
      h_msb_rec h_most_sig_byte_decomp_7_is_0 hamm₁ hamm₂ hamm₃ hamm₄ hamm₅ hamm₆
    simp
    exact hav₀
    simp
    exact hav₁
    simp
    repeat assumption
}

lemma koalabear_word_range_checker_func_typing_soundness (Δ: Env.ChipEnv) (Η: Env.UsedNames) (Γ: Env.TyEnv) :
  @Ty.TypeJudgment Δ Γ Η koalabear_word_range_checker_func
    (Ast.Ty.func "value_0" (field_lt_const 256)
    (Ast.Ty.func "value_1" (field_lt_const 256)
    (Ast.Ty.func "value_2" (field_lt_const 256)
    (Ast.Ty.func "value_3" (field_lt_const 256)
    (Ast.Ty.func "most_sig_byte_decomp_0" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "most_sig_byte_decomp_1" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "most_sig_byte_decomp_2" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "most_sig_byte_decomp_3" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "most_sig_byte_decomp_4" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "most_sig_byte_decomp_5" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "most_sig_byte_decomp_6" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "most_sig_byte_decomp_7" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "and_most_sig_byte_decomp_0_to_2" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "and_most_sig_byte_decomp_0_to_3" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "and_most_sig_byte_decomp_0_to_4" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "and_most_sig_byte_decomp_0_to_5" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "and_most_sig_byte_decomp_0_to_6" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "and_most_sig_byte_decomp_0_to_7" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
      (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind
        (.binRel (.uintExpr (.uintExpr (.uintExpr
          (.toN (.var "value_0")) .add (.uintExpr (.toN (.var "value_1")) .mul (.constN 256)))
                                  .add (.uintExpr (.toN (.var "value_2")) .mul (.constN (256^2))))
                                  .add (.uintExpr (.toN (.var "value_3")) .mul (.constN (256^3))))
        .lt (.constN 2130706433)))))))))))))))))))))) := by {
  autoTy u₁₁
  apply Ty.TypeJudgment.TE_SUB
  apply var_has_type_in_tyenv
  apply get_update_self
  simp [Ast.nu]
  apply koalabear_word_range_checker_subtype_soundness
  repeat
    apply get_update_ne
    simp
  apply get_update_self
  repeat
    apply get_update_ne
    simp
  repeat
    rfl
  simp [renameTy]
}
