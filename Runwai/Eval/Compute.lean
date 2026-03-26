import Runwai.Eval

/-!
# Computable Evaluator for Runwai

## Design Philosophy

`EvalProp` is an **inductive relation**: proving things about it requires manually
constructing proof trees — one `cases`/`constructor` call per AST node.  For an
expression with k operations, a proof that it evaluates to some value takes O(k)
lines.  Lemmas like `eval_bits_to_byte_expr_val` run to 90+ lines because each
nested `fieldExpr`/`binRel` forces its own case split.

`evalC` is a **computable function** implementing the same semantics.  Because it
is a plain `def`, Lean's kernel can reduce it, and `simp [evalC_letIn, evalC_fieldExpr]`
unfolds the whole expression in one step.  The key bridge:

    EvalProp σ T Δ e v  ↔  ∃ fuel, evalC fuel σ T Δ e = some v

Once you have this, proofs that previously required 80 lines of
`cases …; rename_i …; simp` become:

    rw [← evalC_iff_EvalProp] at h
    obtain ⟨n, h⟩ := h
    simp only [evalC_letIn, evalC_fieldExpr, evalC_var, evalFieldOp,
               evalRelOp, Env.getVal, Env.updateVal,
               Option.bind_eq_some_iff] at h
    obtain ⟨xv, hxv, yv, hyv, heq⟩ := h
    ring  -- or omega

-/

open Ast Env Eval

namespace Eval

/-! ## Computable fuel-based evaluator -/

/--
`evalC fuel σ T Δ e` computes the value of expression `e` under valuation `σ`,
trace environment `T`, and chip environment `Δ`.  The `fuel` parameter bounds
the recursion depth; if it reaches 0 the function returns `none`.
-/
def evalC : ℕ → ValEnv → TraceEnv → ChipEnv → Ast.Expr → Option Ast.Value
  | 0, _, _, _, _ => none
  | _+1, _, _, _, .constF  v   => some (.vF v)
  | _+1, _, _, _, .constN  v   => some (.vN v)
  | _+1, _, _, _, .constInt v  => some (.vInt v)
  | _+1, _, _, _, .constBool b => some (.vBool b)
  | _+1, σ, _, _, .var x       => some (getVal σ x)
  | _+1, σ, _, _, .lam x _ b  => some (.vClosure x b σ)
  | n+1, σ, T, Δ, .arr elems  =>
      (elems.mapM (evalC n σ T Δ)).map .vArr
  | n+1, σ, T, Δ, .letIn x e₁ e₂ =>
      (evalC n σ T Δ e₁).bind (fun v₁ => evalC n (updateVal σ x v₁) T Δ e₂)
  | n+1, σ, T, Δ, .app f a =>
      (evalC n σ T Δ f).bind fun vf =>
      (evalC n σ T Δ a).bind fun va =>
      match vf with
      | .vClosure x body σ' => evalC n (updateVal σ' x va) T Δ body
      | _                   => none
  | n+1, σ, T, Δ, .fieldExpr e₁ op e₂ =>
      (evalC n σ T Δ e₁).bind fun v₁ =>
      (evalC n σ T Δ e₂).bind fun v₂ =>
      evalFieldOp op v₁ v₂
  | n+1, σ, T, Δ, .uintExpr e₁ op e₂ =>
      (evalC n σ T Δ e₁).bind fun v₁ =>
      (evalC n σ T Δ e₂).bind fun v₂ =>
      evalUIntOp op v₁ v₂
  | n+1, σ, T, Δ, .sintExpr e₁ op e₂ =>
      (evalC n σ T Δ e₁).bind fun v₁ =>
      (evalC n σ T Δ e₂).bind fun v₂ =>
      evalSIntOp op v₁ v₂
  | n+1, σ, T, Δ, .binRel e₁ op e₂ =>
      (evalC n σ T Δ e₁).bind fun v₁ =>
      (evalC n σ T Δ e₂).bind fun v₂ =>
      (evalRelOp op v₁ v₂).map .vBool
  | n+1, σ, T, Δ, .boolExpr e₁ op e₂ =>
      (evalC n σ T Δ e₁).bind fun v₁ =>
      (evalC n σ T Δ e₂).bind fun v₂ =>
      (evalBoolOp op v₁ v₂).map .vBool
  | n+1, σ, T, Δ, .branch c e₁ e₂ =>
      (evalC n σ T Δ c).bind fun vc =>
      match vc with
      | .vBool true  => evalC n σ T Δ e₁
      | .vBool false => evalC n σ T Δ e₂
      | _            => none
  | n+1, σ, T, Δ, .assertE e₁ e₂ =>
      (evalC n σ T Δ e₁).bind fun v₁ =>
      (evalC n σ T Δ e₂).bind fun v₂ =>
      match v₁, v₂ with
      | .vF a, .vF b => if a = b then some .vUnit else none
      | _, _         => none
  | n+1, σ, T, Δ, .arrIdx a i =>
      (evalC n σ T Δ a).bind fun va =>
      (evalC n σ T Δ i).bind fun vi =>
      match va, vi with
      | .vArr vs, .vN j => vs[j]?
      | _, _            => none
  | n+1, σ, T, Δ, .len e =>
      (evalC n σ T Δ e).bind fun v =>
      match v with
      | .vArr vs => some (.vN vs.length)
      | _        => none
  | n+1, σ, T, Δ, .toN e =>
      (evalC n σ T Δ e).bind fun v =>
      match v with
      | .vF x => some (.vN x.val)
      | _     => none
  | n+1, σ, T, Δ, .toF e =>
      (evalC n σ T Δ e).bind fun v =>
      match v with
      | .vN x => some (.vF x)
      | _     => none
  | n+1, σ, T, Δ, .UtoS e =>
      (evalC n σ T Δ e).bind fun v =>
      match v with
      | .vN x => some (.vInt x)
      | _     => none
  | n+1, σ, T, Δ, .StoU e =>
      (evalC n σ T Δ e).bind fun v =>
      match v with
      | .vInt x => some (.vN x.natAbs)
      | _       => none
  -- Lookup: verify all EvalProp.LookUp conditions, search for a valid witness row,
  -- then evaluate the body.
  | n+1, σ, T, Δ, .lookup _vname cname args e =>
      let c := getChip Δ cname
      match getTrace T c with
      | some (.vArr rows) =>
          -- (1) Check callee validity for all trace rows
          if !(List.range rows.length).all (fun j =>
                let σ' := updateVal (updateVal σ c.ident_t (.vArr rows)) c.ident_i (.vN j)
                match evalC n σ' T Δ c.body with
                | some .vUnit => true
                | _           => false)
          then none
          else
          -- (2) Evaluate caller-side argument expressions to obtain witness values vs
          match (args.map Prod.fst).mapM (fun callerE =>
                match evalC n σ T Δ callerE with
                | some (.vF v) => some v
                | _            => none) with
          | none    => none
          | some vs =>
              -- (3) Find a witness row index i where all assertions hold
              if !(List.range rows.length).any (fun i =>
                    let σ' := updateVal (updateVal σ c.ident_t (.vArr rows)) c.ident_i (.vN i)
                    (List.zip vs (args.map Prod.snd)).all (fun ⟨v, colE⟩ =>
                      match evalC n σ' T Δ (.assertE (.constF v) colE) with
                      | some .vUnit => true
                      | _           => false))
              then none
              -- (4) Evaluate the body
              else evalC n σ T Δ e
      | _ => none

/-! ## simp unfolding lemmas
These let `simp [evalC_letIn, evalC_fieldExpr, ...]` reduce evalC goals to
arithmetic, replacing the old manual `cases EvalProp` boilerplate. -/

@[simp] theorem evalC_zero    : evalC 0 σ T Δ e = none := by cases e <;> simp [evalC]
@[simp] theorem evalC_constF  : evalC (n+1) σ T Δ (.constF v)   = some (.vF v)      := rfl
@[simp] theorem evalC_constN  : evalC (n+1) σ T Δ (.constN v)   = some (.vN v)      := rfl
@[simp] theorem evalC_constInt: evalC (n+1) σ T Δ (.constInt i) = some (.vInt i)    := rfl
@[simp] theorem evalC_constBool:evalC (n+1) σ T Δ (.constBool b)= some (.vBool b)   := rfl
@[simp] theorem evalC_var     : evalC (n+1) σ T Δ (.var x)      = some (getVal σ x) := rfl
@[simp] theorem evalC_lam     : evalC (n+1) σ T Δ (.lam x τ b)  = some (.vClosure x b σ) := rfl

@[simp] theorem evalC_arr :
    evalC (n+1) σ T Δ (.arr elems) = (elems.mapM (evalC n σ T Δ)).map .vArr := rfl

@[simp] theorem evalC_letIn :
    evalC (n+1) σ T Δ (.letIn x e₁ e₂) =
    (evalC n σ T Δ e₁).bind (fun v₁ => evalC n (updateVal σ x v₁) T Δ e₂) := rfl

@[simp] theorem evalC_app :
    evalC (n+1) σ T Δ (.app f a) =
    (evalC n σ T Δ f).bind (fun vf =>
    (evalC n σ T Δ a).bind (fun va =>
    match vf with
    | .vClosure x body σ' => evalC n (updateVal σ' x va) T Δ body
    | _                   => none)) := rfl

@[simp] theorem evalC_fieldExpr :
    evalC (n+1) σ T Δ (.fieldExpr e₁ op e₂) =
    (evalC n σ T Δ e₁).bind (fun v₁ =>
    (evalC n σ T Δ e₂).bind (fun v₂ =>
    evalFieldOp op v₁ v₂)) := rfl

@[simp] theorem evalC_uintExpr :
    evalC (n+1) σ T Δ (.uintExpr e₁ op e₂) =
    (evalC n σ T Δ e₁).bind (fun v₁ =>
    (evalC n σ T Δ e₂).bind (fun v₂ =>
    evalUIntOp op v₁ v₂)) := rfl

@[simp] theorem evalC_sintExpr :
    evalC (n+1) σ T Δ (.sintExpr e₁ op e₂) =
    (evalC n σ T Δ e₁).bind (fun v₁ =>
    (evalC n σ T Δ e₂).bind (fun v₂ =>
    evalSIntOp op v₁ v₂)) := rfl

@[simp] theorem evalC_binRel :
    evalC (n+1) σ T Δ (.binRel e₁ op e₂) =
    (evalC n σ T Δ e₁).bind (fun v₁ =>
    (evalC n σ T Δ e₂).bind (fun v₂ =>
    (evalRelOp op v₁ v₂).map .vBool)) := rfl

@[simp] theorem evalC_boolExpr :
    evalC (n+1) σ T Δ (.boolExpr e₁ op e₂) =
    (evalC n σ T Δ e₁).bind (fun v₁ =>
    (evalC n σ T Δ e₂).bind (fun v₂ =>
    (evalBoolOp op v₁ v₂).map .vBool)) := rfl

@[simp] theorem evalC_branch :
    evalC (n+1) σ T Δ (.branch c e₁ e₂) =
    (evalC n σ T Δ c).bind (fun vc =>
    match vc with
    | .vBool true  => evalC n σ T Δ e₁
    | .vBool false => evalC n σ T Δ e₂
    | _            => none) := rfl

@[simp] theorem evalC_assertE :
    evalC (n+1) σ T Δ (.assertE e₁ e₂) =
    (evalC n σ T Δ e₁).bind (fun v₁ =>
    (evalC n σ T Δ e₂).bind (fun v₂ =>
    match v₁, v₂ with
    | .vF a, .vF b => if a = b then some .vUnit else none
    | _, _         => none)) := rfl

@[simp] theorem evalC_arrIdx :
    evalC (n+1) σ T Δ (.arrIdx a i) =
    (evalC n σ T Δ a).bind (fun va =>
    (evalC n σ T Δ i).bind (fun vi =>
    match va, vi with
    | .vArr vs, .vN j => vs[j]?
    | _, _            => none)) := rfl

@[simp] theorem evalC_len :
    evalC (n+1) σ T Δ (.len e) =
    (evalC n σ T Δ e).bind (fun v =>
    match v with | .vArr vs => some (.vN vs.length) | _ => none) := rfl

@[simp] theorem evalC_toN :
    evalC (n+1) σ T Δ (.toN e) =
    (evalC n σ T Δ e).bind (fun v =>
    match v with | .vF x => some (.vN x.val) | _ => none) := rfl

@[simp] theorem evalC_toF :
    evalC (n+1) σ T Δ (.toF e) =
    (evalC n σ T Δ e).bind (fun v =>
    match v with | .vN x => some (.vF x) | _ => none) := rfl

@[simp] theorem evalC_UtoS :
    evalC (n+1) σ T Δ (.UtoS e) =
    (evalC n σ T Δ e).bind (fun v =>
    match v with | .vN x => some (.vInt x) | _ => none) := rfl

@[simp] theorem evalC_StoU :
    evalC (n+1) σ T Δ (.StoU e) =
    (evalC n σ T Δ e).bind (fun v =>
    match v with | .vInt x => some (.vN x.natAbs) | _ => none) := rfl

@[simp] theorem evalC_lookup :
    evalC (n+1) σ T Δ (.lookup vn cn args e) =
    let c := getChip Δ cn
    match getTrace T c with
    | some (.vArr rows) =>
        if !(List.range rows.length).all (fun j =>
              let σ' := updateVal (updateVal σ c.ident_t (.vArr rows)) c.ident_i (.vN j)
              match evalC n σ' T Δ c.body with
              | some .vUnit => true | _ => false)
        then none
        else match (args.map Prod.fst).mapM (fun callerE =>
              match evalC n σ T Δ callerE with
              | some (.vF v) => some v | _ => none) with
             | none => none
             | some vs =>
                 if !(List.range rows.length).any (fun i =>
                       let σ' := updateVal (updateVal σ c.ident_t (.vArr rows)) c.ident_i (.vN i)
                       (List.zip vs (args.map Prod.snd)).all (fun ⟨v, colE⟩ =>
                         match evalC n σ' T Δ (.assertE (.constF v) colE) with
                         | some .vUnit => true | _ => false))
                 then none
                 else evalC n σ T Δ e
    | _ => none := rfl

/-! ## Auxiliary List.mapM lemmas -/

/-- Monotonicity for `List.mapM` over `Option`: if `f x = some v → g x = some v` pointwise,
    then `l.mapM f = some vs → l.mapM g = some vs`. -/
private theorem List.mapM_Option_mono {α β : Type*} {l : List α} {f g : α → Option β}
    (hfg : ∀ x v, f x = some v → g x = some v) :
    ∀ {vs : List β}, l.mapM f = some vs → l.mapM g = some vs := by
  induction l with
  | nil =>
    intro vs h
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    simp [List.mapM_nil]
  | cons x xs ihl =>
    intro vs h
    rw [List.mapM_cons] at h
    cases hfx : f x with
    | none => simp [hfx] at h
    | some vx =>
      rw [hfx] at h
      simp only [bind, Option.bind] at h
      cases hxs : xs.mapM f with
      | none => simp [hxs] at h
      | some vs' =>
        simp only [hxs] at h
        simp only [pure, Option.some.injEq] at h
        subst h
        rw [List.mapM_cons]
        simp only [bind, Option.bind, hfg x vx hfx]
        simp only [ihl hxs]
        simp

/-- Inversion for `List.mapM` over `Option`: if the result is `some vs`, then every element
    evaluates successfully, and we can recover per-element witnesses. -/
private theorem List.mapM_Option_inv {α β : Type*} {l : List α} {f : α → Option β}
    {vs : List β} (h : l.mapM f = some vs) :
    l.length = vs.length ∧ ∀ p ∈ List.zip l vs, f p.1 = some p.2 := by
  induction l generalizing vs with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    simp
  | cons x xs ihl =>
    rw [List.mapM_cons] at h
    cases hfx : f x with
    | none => simp [hfx] at h
    | some vx =>
      rw [hfx] at h
      simp only [bind, Option.bind] at h
      cases hxs : xs.mapM f with
      | none => simp [hxs] at h
      | some vs' =>
        simp only [hxs] at h
        simp only [pure, Option.some.injEq] at h
        subst h
        obtain ⟨hlen, hzip⟩ := ihl hxs
        constructor
        · simp [hlen]
        · intro p hp
          simp only [List.zip_cons_cons, List.mem_cons] at hp
          rcases hp with rfl | hmem
          · exact hfx
          · exact hzip p hmem

/-! ## Auxiliary lemmas for lookup monotonicity -/

/-- If `f x = true → g x = true` for all `x ∈ l`, then `l.all f = true → l.all g = true`. -/
private theorem List.all_mono' {α : Type*} {l : List α} {f g : α → Bool}
    (hfg : ∀ x ∈ l, f x = true → g x = true) :
    l.all f = true → l.all g = true := by
  simp only [List.all_eq_true]
  intro h x hx; exact hfg x hx (h x hx)

/-- If `f x = true → g x = true` for all `x ∈ l`, then `l.any f = true → l.any g = true`. -/
private theorem List.any_mono' {α : Type*} {l : List α} {f g : α → Bool}
    (hfg : ∀ x ∈ l, f x = true → g x = true) :
    l.any f = true → l.any g = true := by
  simp only [List.any_eq_true]
  intro ⟨x, hx, hfx⟩; exact ⟨x, hx, hfg x hx hfx⟩

/-- From `∀ x ∈ l, ∃ fuel, f fuel x = true` and fuel-monotonicity, derive
    `∃ N, l.all (f N) = true`. -/
private theorem exists_uniform_fuel_all {α : Type*} {l : List α} {f : ℕ → α → Bool}
    (hmono : ∀ n m, n ≤ m → ∀ x, f n x = true → f m x = true)
    (h : ∀ x ∈ l, ∃ fuel, f fuel x = true) :
    ∃ N, l.all (f N) = true := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons y ys ih =>
    obtain ⟨ny, hny⟩ := h y (List.mem_cons_self ..)
    obtain ⟨nys, hnys⟩ := ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
    refine ⟨max ny nys, ?_⟩
    rw [List.all_cons, Bool.and_eq_true]
    constructor
    · exact hmono ny _ (Nat.le_max_left ..) y hny
    · exact List.all_mono' (fun x hx hfx =>
        hmono nys _ (Nat.le_max_right ..) x hfx) hnys

/-! ## Monotonicity -/

/--
`evalC` is monotone in fuel: if an expression evaluates successfully at fuel `n`,
it also evaluates to the same value at any larger fuel `m`.
-/
theorem evalC_mono {n m : ℕ} (hnm : n ≤ m) :
    ∀ {σ T Δ e v}, evalC n σ T Δ e = some v → evalC m σ T Δ e = some v := by
  induction n generalizing m with
  | zero => intro σ T Δ e v h; simp at h
  | succ n ih =>
    intro σ T Δ e v h
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hnm' : n ≤ m' := by omega
    -- The simp unfolding lemmas allow the following case analysis
    match e with
    | .constF _ | .constN _ | .constInt _ | .constBool _ | .var _ | .lam _ _ _ => exact h
    | .arr elems =>
        simp only [evalC_arr, Option.map_eq_some_iff] at *
        obtain ⟨vs, hvs, rfl⟩ := h
        exact ⟨vs, List.mapM_Option_mono (fun e ve he => ih hnm' he) hvs, rfl⟩
    | .letIn x e₁ e₂ =>
        simp only [evalC_letIn, Option.bind_eq_some_iff] at h ⊢
        obtain ⟨v₁, hv₁, hv₂⟩ := h
        exact ⟨v₁, ih hnm' hv₁, ih hnm' hv₂⟩
    | .app f a =>
        simp only [evalC_app, Option.bind_eq_some_iff] at h ⊢
        obtain ⟨vf, hvf, va, hva, rest⟩ := h
        refine ⟨vf, ih hnm' hvf, va, ih hnm' hva, ?_⟩
        split at rest <;> simp_all [ih hnm']
    | .fieldExpr e₁ op e₂ =>
        simp only [evalC_fieldExpr, Option.bind_eq_some_iff] at h ⊢
        obtain ⟨v₁, hv₁, v₂, hv₂, hop⟩ := h
        exact ⟨v₁, ih hnm' hv₁, v₂, ih hnm' hv₂, hop⟩
    | .uintExpr e₁ op e₂ =>
        simp only [evalC_uintExpr, Option.bind_eq_some_iff] at h ⊢
        obtain ⟨v₁, hv₁, v₂, hv₂, hop⟩ := h
        exact ⟨v₁, ih hnm' hv₁, v₂, ih hnm' hv₂, hop⟩
    | .sintExpr e₁ op e₂ =>
        simp only [evalC_sintExpr, Option.bind_eq_some_iff] at h ⊢
        obtain ⟨v₁, hv₁, v₂, hv₂, hop⟩ := h
        exact ⟨v₁, ih hnm' hv₁, v₂, ih hnm' hv₂, hop⟩
    | .binRel e₁ op e₂ =>
        simp only [evalC_binRel, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
        obtain ⟨v₁, hv₁, v₂, hv₂, b, hop, rfl⟩ := h
        exact ⟨v₁, ih hnm' hv₁, v₂, ih hnm' hv₂, b, hop, rfl⟩
    | .boolExpr e₁ op e₂ =>
        simp only [evalC_boolExpr, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
        obtain ⟨v₁, hv₁, v₂, hv₂, b, hop, rfl⟩ := h
        exact ⟨v₁, ih hnm' hv₁, v₂, ih hnm' hv₂, b, hop, rfl⟩
    | .branch c e₁ e₂ =>
        simp only [evalC_branch, Option.bind_eq_some_iff] at h ⊢
        obtain ⟨vc, hvc, rest⟩ := h
        refine ⟨vc, ih hnm' hvc, ?_⟩
        split at rest <;> simp_all [ih hnm']
    | .assertE e₁ e₂ =>
        simp only [evalC_assertE, Option.bind_eq_some_iff] at h ⊢
        obtain ⟨v₁, hv₁, v₂, hv₂, rest⟩ := h
        refine ⟨v₁, ih hnm' hv₁, v₂, ih hnm' hv₂, ?_⟩
        split at rest <;> simp_all [ih hnm']
    | .arrIdx a i =>
        simp only [evalC_arrIdx, Option.bind_eq_some_iff] at h ⊢
        obtain ⟨va, hva, vi, hvi, rest⟩ := h
        refine ⟨va, ih hnm' hva, vi, ih hnm' hvi, ?_⟩
        split at rest <;> simp_all [ih hnm']
    | .len e =>
        simp only [evalC_len, Option.bind_eq_some_iff] at h ⊢
        obtain ⟨v, hv, rest⟩ := h
        refine ⟨v, ih hnm' hv, ?_⟩; split at rest <;> simp_all [ih hnm']
    | .toN e =>
        simp only [evalC_toN, Option.bind_eq_some_iff] at h ⊢
        obtain ⟨v, hv, rest⟩ := h
        refine ⟨v, ih hnm' hv, ?_⟩; split at rest <;> simp_all [ih hnm']
    | .toF e =>
        simp only [evalC_toF, Option.bind_eq_some_iff] at h ⊢
        obtain ⟨v, hv, rest⟩ := h
        refine ⟨v, ih hnm' hv, ?_⟩; split at rest <;> simp_all [ih hnm']
    | .UtoS e =>
        simp only [evalC_UtoS, Option.bind_eq_some_iff] at h ⊢
        obtain ⟨v, hv, rest⟩ := h
        refine ⟨v, ih hnm' hv, ?_⟩; split at rest <;> simp_all [ih hnm']
    | .StoU e =>
        simp only [evalC_StoU, Option.bind_eq_some_iff] at h ⊢
        obtain ⟨v, hv, rest⟩ := h
        refine ⟨v, ih hnm' hv, ?_⟩; split at rest <;> simp_all [ih hnm']
    | .lookup _vn cn args e =>
        simp only [evalC_lookup] at h ⊢
        set c := getChip Δ cn
        -- Propagate getTrace (fuel-independent)
        rcases htr : getTrace T c with _ | rv
        · simp [htr] at h
        · simp only [htr] at h ⊢
          rcases rv with _ | _ | _ | _ | _ | rows | _
          all_goals simp only at h
          -- close non-vArr cases (h : none = some v → contradiction)
          all_goals try contradiction
          -- vArr rows case
          · -- (1) Propagate row-validity check
            have hall : (List.range rows.length).all (fun j =>
                let σ' := updateVal (updateVal σ c.ident_t (.vArr rows)) c.ident_i (.vN j)
                match evalC n σ' T Δ c.body with
                | some .vUnit => true | _ => false) = true := by
              by_contra h'
              simp only [Bool.not_eq_true] at h'
              simp [h'] at h
            have hall_m : (List.range rows.length).all (fun j =>
                let σ' := updateVal (updateVal σ c.ident_t (.vArr rows)) c.ident_i (.vN j)
                match evalC m' σ' T Δ c.body with
                | some .vUnit => true | _ => false) = true :=
              List.all_mono' (fun j _ hj => by
                simp only at hj ⊢
                set σ' := updateVal (updateVal σ c.ident_t (.vArr rows)) c.ident_i (.vN j)
                rcases heval : evalC n σ' T Δ c.body with _ | v
                · simp [heval] at hj
                · cases v <;> simp [heval] at hj
                  simp [ih hnm' heval]) hall
            -- (2) Extract args mapM result
            have hmap : ∃ vs, (args.map Prod.fst).mapM (fun callerE =>
                match evalC n σ T Δ callerE with
                | some (.vF v) => some v | _ => none) = some vs := by
              simp only [hall, Bool.not_true, ite_false] at h
              rcases hm : (args.map Prod.fst).mapM _ with _ | vs
              · simp [hm] at h
              · exact ⟨vs, rfl⟩
            obtain ⟨vs, hvs⟩ := hmap
            have hmap_m : (args.map Prod.fst).mapM (fun callerE =>
                match evalC m' σ T Δ callerE with
                | some (.vF v) => some v | _ => none) = some vs :=
              List.mapM_Option_mono (fun callerE v' hv' => by
                rcases heval : evalC n σ T Δ callerE with _ | val
                · simp [heval] at hv'
                · rcases val with _ | _ | _ | _ | _ | _ | _
                  all_goals simp [heval] at hv'
                  simp [ih hnm' heval, hv']) hvs
            -- (3) Propagate any-check for witness row
            have hany : (List.range rows.length).any (fun i =>
                let σ' := updateVal (updateVal σ c.ident_t (.vArr rows)) c.ident_i (.vN i)
                (List.zip vs (args.map Prod.snd)).all (fun ⟨v, colE⟩ =>
                  match evalC n σ' T Δ (.assertE (.constF v) colE) with
                  | some .vUnit => true | _ => false)) = true := by
              by_contra h'
              push_neg at h'
              simp [hall, hvs, h'] at h
            have hany_m : (List.range rows.length).any (fun i =>
                let σ' := updateVal (updateVal σ c.ident_t (.vArr rows)) c.ident_i (.vN i)
                (List.zip vs (args.map Prod.snd)).all (fun ⟨v, colE⟩ =>
                  match evalC m' σ' T Δ (.assertE (.constF v) colE) with
                  | some .vUnit => true | _ => false)) = true :=
              List.any_mono' (fun i _ hi => List.all_mono' (fun ⟨v, colE⟩ _ hpair => by
                set σ' := updateVal (updateVal σ c.ident_t (.vArr rows)) c.ident_i (.vN i)
                rcases heval : evalC n σ' T Δ (.assertE (.constF v) colE) with _ | val
                · simp [heval] at hpair
                · cases val <;> simp [heval] at hpair
                  simp [ih hnm' heval]) hi) hany
            -- Simplify h (fuel n) to just the body
            simp only [hall, hvs, hany, Bool.not_true, ite_false] at h
            -- Simplify goal (fuel m') to just the body
            simp only [hall_m, hmap_m, hany_m, Bool.not_true, ite_false]
            -- (4) Propagate body
            exact ih hnm' h

/-! ## Soundness: evalC → EvalProp

Every successful `evalC` computation corresponds to a valid `EvalProp` derivation.
-/
theorem evalC_sound : ∀ {fuel σ T Δ e v},
    evalC fuel σ T Δ e = some v → EvalProp σ T Δ e v := by
  intro fuel
  induction fuel with
  | zero => intro; simp
  | succ n ih =>
    intro σ T Δ e v h
    match e with
    | .constF f    => simp at h; subst h; exact .ConstF
    | .constN x    => simp at h; subst h; exact .ConstN
    | .constInt x  => simp at h; subst h; exact .ConstInt
    | .constBool b => simp at h; subst h; exact .ConstBool
    | .var x       => simp at h; subst h; exact .Var rfl
    | .lam x _ body => simp at h; subst h; exact .Lam
    | .arr elems =>
        simp only [evalC_arr, Option.map_eq_some_iff] at h
        obtain ⟨vs, hvs, rfl⟩ := h
        obtain ⟨hlen, hzip⟩ := List.mapM_Option_inv hvs
        exact .ConstArr hlen (fun ⟨xe, xv⟩ hmem => ih (hzip ⟨xe, xv⟩ hmem))
    | .letIn x e₁ e₂ =>
        simp only [evalC_letIn, Option.bind_eq_some_iff] at h
        obtain ⟨v₁, hv₁, hv₂⟩ := h
        exact .Let (ih hv₁) (ih hv₂)
    | .app f a =>
        simp only [evalC_app, Option.bind_eq_some_iff] at h
        obtain ⟨vf, hvf, va, hva, rest⟩ := h
        split at rest
        · rename_i x body σ'
          exact .App (ih hvf) (ih hva) (ih rest)
        · simp at rest
    | .fieldExpr e₁ op e₂ =>
        simp only [evalC_fieldExpr, Option.bind_eq_some_iff] at h
        obtain ⟨v₁, hv₁, v₂, hv₂, hop⟩ := h
        -- hop : evalFieldOp op v₁ v₂ = some v; v₁ and v₂ must be vF
        rcases v₁ with _ | _ | _ | _ | _ | _ | _
        all_goals (first
          | (rcases v₂ with _ | _ | _ | _ | _ | _ | _
             all_goals (first
               | exact .FBinOp (ih hv₁) (ih hv₂) hop
               | simp [evalFieldOp] at hop))
          | simp [evalFieldOp] at hop)
    | .uintExpr e₁ op e₂ =>
        simp only [evalC_uintExpr, Option.bind_eq_some_iff] at h
        obtain ⟨v₁, hv₁, v₂, hv₂, hop⟩ := h
        rcases v₁ with _ | _ | _ | _ | _ | _ | _
        all_goals (first
          | (rcases v₂ with _ | _ | _ | _ | _ | _ | _
             all_goals (first
               | exact .NBinOp (ih hv₁) (ih hv₂) hop
               | simp [evalUIntOp] at hop))
          | simp [evalUIntOp] at hop)
    | .sintExpr e₁ op e₂ =>
        simp only [evalC_sintExpr, Option.bind_eq_some_iff] at h
        obtain ⟨v₁, hv₁, v₂, hv₂, hop⟩ := h
        rcases v₁ with _ | _ | _ | _ | _ | _ | _
        all_goals (first
          | (rcases v₂ with _ | _ | _ | _ | _ | _ | _
             all_goals (first
               | exact .SIntBinOp (ih hv₁) (ih hv₂) hop
               | simp [evalSIntOp] at hop))
          | simp [evalSIntOp] at hop)
    | .binRel e₁ op e₂ =>
        simp only [evalC_binRel, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
        obtain ⟨v₁, hv₁, v₂, hv₂, b, hop, rfl⟩ := h
        exact .Rel (ih hv₁) (ih hv₂) hop
    | .boolExpr e₁ op e₂ =>
        simp only [evalC_boolExpr, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
        obtain ⟨v₁, hv₁, v₂, hv₂, b, hop, rfl⟩ := h
        rcases v₁ with _ | _ | _ | _ | _ | _ | b₁
        all_goals (first
          | (rcases v₂ with _ | _ | _ | _ | _ | _ | b₂
             all_goals (first
               | exact .BoolOp (ih hv₁) (ih hv₂) hop
               | simp [evalBoolOp] at hop))
          | simp [evalBoolOp] at hop)
    | .branch c e₁ e₂ =>
        simp only [evalC_branch, Option.bind_eq_some_iff] at h
        obtain ⟨vc, hvc, rest⟩ := h
        split at rest
        · exact .IfTrue (ih hvc) (ih rest)
        · exact .IfFalse (ih hvc) (ih rest)
        · simp at rest
    | .assertE e₁ e₂ =>
        simp only [evalC_assertE, Option.bind_eq_some_iff] at h
        obtain ⟨v₁, hv₁, v₂, hv₂, rest⟩ := h
        -- specialize v₁/v₂ to vF; other constructors make rest absurd
        rcases v₁ with _ | _ | _ | _ | _ | _ | fv₁ <;> try simp at rest
        rcases v₂ with _ | _ | _ | _ | _ | _ | fv₂ <;> try simp at rest
        -- simp normalised rest to: fv₁ = fv₂ ∧ v = .vUnit
        obtain ⟨heq, rfl⟩ := rest
        subst heq
        exact .Assert (ih hv₁) (ih hv₂)
    | .arrIdx a i =>
        simp only [evalC_arrIdx, Option.bind_eq_some_iff] at h
        obtain ⟨va, hva, vi, hvi, rest⟩ := h
        split at rest
        · rename_i vs j; exact .ArrIdx (ih hva) (ih hvi) rest
        · simp at rest
    | .len e =>
        simp only [evalC_len, Option.bind_eq_some_iff] at h
        obtain ⟨v, hv, rest⟩ := h
        split at rest
        · simp at rest; subst rest; exact .Len (ih hv)
        · simp at rest
    | .toN e =>
        simp only [evalC_toN, Option.bind_eq_some_iff] at h
        obtain ⟨v, hv, rest⟩ := h
        split at rest
        · simp at rest; subst rest; exact .toN (ih hv)
        · simp at rest
    | .toF e =>
        simp only [evalC_toF, Option.bind_eq_some_iff] at h
        obtain ⟨v, hv, rest⟩ := h
        split at rest
        · simp at rest; subst rest; exact .toF (ih hv)
        · simp at rest
    | .UtoS e =>
        simp only [evalC_UtoS, Option.bind_eq_some_iff] at h
        obtain ⟨v, hv, rest⟩ := h
        split at rest
        · simp at rest; subst rest; exact .UtoS (ih hv)
        · simp at rest
    | .StoU e =>
        simp only [evalC_StoU, Option.bind_eq_some_iff] at h
        obtain ⟨v, hv, rest⟩ := h
        split at rest
        · simp at rest; subst rest; exact .StoU (ih hv)
        · simp at rest
    | .lookup vname cname args e =>
        simp only [evalC_lookup] at h
        -- Step 1: extract rows from getTrace
        set c := getChip Δ cname with hc_def
        have htr : ∃ rows, getTrace T c = some (.vArr rows) := by
          rcases hgettr : getTrace T c with _ | rv
          · simp [hgettr] at h
          · rcases rv with _ | _ | _ | _ | _ | rows | _
            all_goals simp only [hgettr] at h
            all_goals try simp at h
            exact ⟨rows, rfl⟩
        obtain ⟨rows, hrows⟩ := htr
        -- Rewrite getTrace result in h to trigger the match reduction
        simp only [hrows] at h
        -- Step 2: extract row-validity check
        have hall : (List.range rows.length).all (fun j =>
            let σ' := updateVal (updateVal σ c.ident_t (.vArr rows)) c.ident_i (.vN j)
            match evalC n σ' T Δ c.body with
            | some .vUnit => true | _ => false) = true := by
          rcases hb : (List.range rows.length).all _ with _ | _
          · simp [hb] at h
          · rfl
        -- Step 3: extract args witness values vs
        have hmap : ∃ vs, (args.map Prod.fst).mapM (fun callerE =>
            match evalC n σ T Δ callerE with
            | some (.vF v) => some v | _ => none) = some vs := by
          -- Simplify the if-check using hall (all-rows check holds)
          simp only [hall, Bool.not_true, ite_false] at h
          rcases hm : (args.map Prod.fst).mapM _ with _ | vs
          · simp [hm] at h
          · exact ⟨vs, rfl⟩
        obtain ⟨vs, hvs⟩ := hmap
        -- Step 4: extract witness row i (simplify using hall + hvs)
        simp only [hall, hvs, Bool.not_true, ite_false] at h
        -- h now: (if !any_check then none else evalC n σ T Δ e) = some v
        have hany : (List.range rows.length).any (fun i =>
            let σ' := updateVal (updateVal σ c.ident_t (.vArr rows)) c.ident_i (.vN i)
            (List.zip vs (args.map Prod.snd)).all (fun ⟨v, colE⟩ =>
              match evalC n σ' T Δ (.assertE (.constF v) colE) with
              | some .vUnit => true | _ => false)) = true := by
          by_contra h'; push_neg at h'
          simp [hvs, h'] at h
        -- Step 5: extract body evaluation (simplify using hany)
        have hbody : evalC n σ T Δ e = some v := by
          simp only [hany, Bool.not_true, ite_false] at h; exact h
        -- Build EvalProp.LookUp
        -- h_callee_validity
        have h_callee_validity : ∀ j : ℕ, j < rows.length →
            let σ' := updateVal (updateVal σ c.ident_t (.vArr rows)) c.ident_i (.vN j)
            EvalProp σ' T Δ c.body .vUnit := by
          intro j hj
          have hmem : j ∈ List.range rows.length := List.mem_range.mpr hj
          have := (List.all_eq_true.mp hall) j hmem
          simp only at this
          set σ' := updateVal (updateVal σ c.ident_t (.vArr rows)) c.ident_i (.vN j)
          rcases heval : evalC n σ' T Δ c.body with _ | v'
          · simp [heval] at this
          · cases v' <;> simp [heval] at this
            exact ih heval
        -- Extract witness i
        rw [List.any_eq_true] at hany
        obtain ⟨i, hi_mem, hi_check⟩ := hany
        have h_bound : i < rows.length := List.mem_range.mp hi_mem
        -- h_evals: each arg expression evaluates to vF
        obtain ⟨hargs_len, hzip_evals⟩ := List.mapM_Option_inv hvs
        have h_evals : ∀ p ∈ List.zip (args.map Prod.fst) vs,
            EvalProp σ T Δ p.fst (.vF p.snd) := by
          intro ⟨callerE, fv⟩ hpair
          have := hzip_evals ⟨callerE, fv⟩ hpair
          simp only at this
          rcases heval : evalC n σ T Δ callerE with _ | val
          · simp [heval] at this
          · rcases val with _ | _ | _ | _ | _ | _ | _
            all_goals simp [heval] at this
            -- only the vF branch survives; this : fval = fv
            rename_i fval
            subst this
            exact ih heval
        -- h_args_len
        have h_args_len : args.length = vs.length := by
          rw [← hargs_len]; simp [List.length_map]
        -- h_asserts: assertions hold at witness row i
        have h_asserts : let σ' := updateVal (updateVal σ c.ident_t (.vArr rows)) c.ident_i (.vN i)
            ∀ p ∈ List.zip vs (args.map Prod.snd),
              EvalProp σ' T Δ (.assertE (.constF p.fst) p.snd) .vUnit := by
          intro σ' ⟨fv, colE⟩ hpair
          have := (List.all_eq_true.mp hi_check) ⟨fv, colE⟩ hpair
          change (match evalC n σ' T Δ (.assertE (.constF fv) colE) with
              | some .vUnit => true | _ => false) = true at this
          rcases heval : evalC n σ' T Δ (.assertE (.constF fv) colE) with _ | val
          · simp [heval] at this
          · cases val <;> simp [heval] at this
            exact ih heval
        exact .LookUp (ih hbody) hc_def hrows h_callee_validity i vs h_bound h_args_len
          h_evals h_asserts

/-! ## Completeness: EvalProp → ∃ fuel, evalC -/

/--
Every `EvalProp` derivation can be witnessed by a finite fuel value.
Proved by structural induction on the derivation.
-/
theorem evalC_complete : ∀ {σ T Δ e v},
    EvalProp σ T Δ e v → ∃ fuel, evalC fuel σ T Δ e = some v := by
  intro σ T Δ e v h
  induction h with
  | ConstF      => exact ⟨1, rfl⟩
  | ConstN      => exact ⟨1, rfl⟩
  | ConstInt    => exact ⟨1, rfl⟩
  | ConstBool   => exact ⟨1, rfl⟩
  | Var hv      => exact ⟨1, by simp [hv]⟩
  | Lam         => exact ⟨1, rfl⟩
  | toN _ ih =>
      obtain ⟨n, hn⟩ := ih; exact ⟨n+1, by simp [hn]⟩
  | toF _ ih =>
      obtain ⟨n, hn⟩ := ih; exact ⟨n+1, by simp [hn]⟩
  | UtoS _ ih =>
      obtain ⟨n, hn⟩ := ih; exact ⟨n+1, by simp [hn]⟩
  | StoU _ ih =>
      obtain ⟨n, hn⟩ := ih; exact ⟨n+1, by simp [hn]⟩
  | @ConstArr σ' T' Δ' xs es hlen hih ih_ih =>
      -- ih_ih : ∀ xe ∈ List.zip xs es, ∃ fuel, evalC fuel σ' T' Δ' xe.1 = some xe.2
      -- We need: ∃ fuel, (xs.mapM (evalC fuel σ' T' Δ')).map .vArr = some (.vArr es)
      -- Strategy: show ∃ fuel, xs.mapM (evalC fuel σ' T' Δ') = some es, then wrap with +1.
      suffices h : ∃ fuel, (xs.mapM (evalC fuel σ' T' Δ')) = some es by
        obtain ⟨fuel, hfuel⟩ := h
        exact ⟨fuel + 1, by simp [hfuel]⟩
      -- Induction on xs/es simultaneously.
      induction xs generalizing es with
      | nil =>
        have hes : es = [] := by cases es with | nil => rfl | cons _ _ => simp at hlen
        subst hes
        exact ⟨0, by simp [List.mapM_nil]⟩
      | cons x xs' ihl =>
        cases es with
        | nil => simp at hlen
        | cons e es' =>
          have hx_ep : EvalProp σ' T' Δ' x e := hih ⟨x, e⟩ (by simp [List.zip_cons_cons])
          have hlen' : xs'.length = es'.length := by simpa using hlen
          have hih' : ∀ xe ∈ List.zip xs' es', EvalProp σ' T' Δ' xe.fst xe.snd := by
            intro xe hxe; exact hih xe (by simp [List.zip_cons_cons]; exact Or.inr hxe)
          have ih_ih' : ∀ xe ∈ List.zip xs' es', ∃ fuel, evalC fuel σ' T' Δ' xe.fst = some xe.snd := by
            intro xe hxe; exact ih_ih xe (by simp [List.zip_cons_cons]; exact Or.inr hxe)
          obtain ⟨nx, hnx⟩ := ih_ih ⟨x, e⟩ (by simp [List.zip_cons_cons])
          obtain ⟨nxs, hnxs⟩ := ihl hlen' hih' ih_ih'
          refine ⟨max nx nxs + 1, ?_⟩
          have hnx' := evalC_mono (show nx ≤ max nx nxs + 1 by omega) hnx
          have hnxs' := List.mapM_Option_mono
            (f := evalC nxs σ' T' Δ')
            (g := evalC (max nx nxs + 1) σ' T' Δ')
            (fun e' ve' he' => evalC_mono (show nxs ≤ max nx nxs + 1 by omega) he')
            hnxs
          rw [List.mapM_cons]
          simp only [bind, Option.bind, hnx', hnxs', pure]
  | Let _ _ ih₁ ih₂ =>
      obtain ⟨n₁, hn₁⟩ := ih₁; obtain ⟨n₂, hn₂⟩ := ih₂
      exact ⟨max n₁ n₂ + 1, by
        simp only [evalC_letIn, Option.bind_eq_some_iff]
        exact ⟨_, evalC_mono (Nat.le_max_left n₁ n₂) hn₁,
                  evalC_mono (Nat.le_max_right n₁ n₂) hn₂⟩⟩
  | App _ _ _ ih_f ih_a ih_b =>
      obtain ⟨nf, hnf⟩ := ih_f; obtain ⟨na, hna⟩ := ih_a; obtain ⟨nb, hnb⟩ := ih_b
      refine ⟨max (max nf na) nb + 1, ?_⟩
      simp only [evalC_app, Option.bind_eq_some_iff]
      exact ⟨_, evalC_mono (by omega) hnf,
             _, evalC_mono (by omega) hna,
             evalC_mono (by omega) hnb⟩
  | FBinOp _ _ r ih₁ ih₂ =>
      obtain ⟨n₁, hn₁⟩ := ih₁; obtain ⟨n₂, hn₂⟩ := ih₂
      exact ⟨max n₁ n₂ + 1, by
        simp only [evalC_fieldExpr, Option.bind_eq_some_iff]
        exact ⟨_, evalC_mono (Nat.le_max_left n₁ n₂) hn₁,
               _, evalC_mono (Nat.le_max_right n₁ n₂) hn₂, r⟩⟩
  | NBinOp _ _ r ih₁ ih₂ =>
      obtain ⟨n₁, hn₁⟩ := ih₁; obtain ⟨n₂, hn₂⟩ := ih₂
      exact ⟨max n₁ n₂ + 1, by
        simp only [evalC_uintExpr, Option.bind_eq_some_iff]
        exact ⟨_, evalC_mono (Nat.le_max_left n₁ n₂) hn₁,
               _, evalC_mono (Nat.le_max_right n₁ n₂) hn₂, r⟩⟩
  | SIntBinOp _ _ r ih₁ ih₂ =>
      obtain ⟨n₁, hn₁⟩ := ih₁; obtain ⟨n₂, hn₂⟩ := ih₂
      exact ⟨max n₁ n₂ + 1, by
        simp only [evalC_sintExpr, Option.bind_eq_some_iff]
        exact ⟨_, evalC_mono (Nat.le_max_left n₁ n₂) hn₁,
               _, evalC_mono (Nat.le_max_right n₁ n₂) hn₂, r⟩⟩
  | BoolOp _ _ bv ih₁ ih₂ =>
      obtain ⟨n₁, hn₁⟩ := ih₁; obtain ⟨n₂, hn₂⟩ := ih₂
      exact ⟨max n₁ n₂ + 1, by
        simp only [evalC_boolExpr, Option.bind_eq_some_iff, Option.map_eq_some_iff]
        exact ⟨_, evalC_mono (Nat.le_max_left n₁ n₂) hn₁,
               _, evalC_mono (Nat.le_max_right n₁ n₂) hn₂, _, bv, rfl⟩⟩
  | Rel _ _ r ih₁ ih₂ =>
      obtain ⟨n₁, hn₁⟩ := ih₁; obtain ⟨n₂, hn₂⟩ := ih₂
      exact ⟨max n₁ n₂ + 1, by
        simp only [evalC_binRel, Option.bind_eq_some_iff, Option.map_eq_some_iff]
        exact ⟨_, evalC_mono (Nat.le_max_left n₁ n₂) hn₁,
               _, evalC_mono (Nat.le_max_right n₁ n₂) hn₂, _, r, rfl⟩⟩
  | IfTrue _ _ ihc ih₁ =>
      obtain ⟨nc, hnc⟩ := ihc; obtain ⟨n₁, hn₁⟩ := ih₁
      exact ⟨max nc n₁ + 1, by
        simp only [evalC_branch, Option.bind_eq_some_iff]
        exact ⟨_, evalC_mono (Nat.le_max_left nc n₁) hnc,
               by simp [evalC_mono (Nat.le_max_right nc n₁) hn₁]⟩⟩
  | IfFalse _ _ ihc ih₁ =>
      obtain ⟨nc, hnc⟩ := ihc; obtain ⟨n₁, hn₁⟩ := ih₁
      exact ⟨max nc n₁ + 1, by
        simp only [evalC_branch, Option.bind_eq_some_iff]
        exact ⟨_, evalC_mono (Nat.le_max_left nc n₁) hnc,
               by simp [evalC_mono (Nat.le_max_right nc n₁) hn₁]⟩⟩
  | Assert _ _ ih₁ ih₂ =>
      obtain ⟨n₁, hn₁⟩ := ih₁; obtain ⟨n₂, hn₂⟩ := ih₂
      exact ⟨max n₁ n₂ + 1, by
        simp only [evalC_assertE, Option.bind_eq_some_iff]
        exact ⟨_, evalC_mono (Nat.le_max_left n₁ n₂) hn₁,
               _, evalC_mono (Nat.le_max_right n₁ n₂) hn₂, by simp⟩⟩
  | ArrIdx _ _ idx iha ihi =>
      obtain ⟨na, hna⟩ := iha; obtain ⟨ni, hni⟩ := ihi
      exact ⟨max na ni + 1, by
        simp only [evalC_arrIdx, Option.bind_eq_some_iff]
        exact ⟨_, evalC_mono (Nat.le_max_left na ni) hna,
               _, evalC_mono (Nat.le_max_right na ni) hni, by simp [idx]⟩⟩
  | Len _ ih =>
      obtain ⟨n, hn⟩ := ih; exact ⟨n+1, by simp [hn]⟩
  | @LookUp σ' T' Δ' vname cname args e v c rows
        h_body h_chip h_trace h_callee i vs h_bound h_args_len h_evals h_asserts
        ih_body ih_callee ih_evals ih_asserts =>
      obtain ⟨n_body, hn_body⟩ := ih_body
      -- (1) Uniform fuel for callee-validity all-check over all rows
      have hrc_h : ∀ j ∈ List.range rows.length, ∃ fuel,
          (match evalC fuel
              (updateVal (updateVal σ' c.ident_t (.vArr rows)) c.ident_i (.vN j))
              T' Δ' c.body with
           | some .vUnit => true | _ => false) = true := fun j hj => by
        obtain ⟨n_j, hn_j⟩ := ih_callee j (List.mem_range.mp hj); exact ⟨n_j, by simp [hn_j]⟩
      obtain ⟨n_rows, hn_rows⟩ := exists_uniform_fuel_all
        (fun n m hnm j h_flt => by
          set σ_j := updateVal (updateVal σ' c.ident_t (.vArr rows)) c.ident_i (.vN j)
          rcases hev : evalC n σ_j T' Δ' c.body with _ | val
          · simp [hev] at h_flt
          · cases val <;> simp [hev] at h_flt ⊢
            simp [evalC_mono hnm hev])
        hrc_h
      -- (2) Uniform fuel for args mapM to produce vs
      -- Build per-element witnesses from ih_evals
      have hmap_elems : ∀ p ∈ List.zip (args.map Prod.fst) vs,
          ∃ fuel, (match evalC fuel σ' T' Δ' p.fst with
                   | some (.vF v') => some v' | _ => none) = some p.snd := fun p hp =>
        let ⟨n_p, hn_p⟩ := ih_evals p hp; ⟨n_p, by simp [hn_p]⟩
      -- Get uniform fuel for the mapM via ConstArr-style induction on the zip
      have hmapM_exists : ∃ n_args, (args.map Prod.fst).mapM (fun callerE =>
          match evalC n_args σ' T' Δ' callerE with
          | some (.vF v') => some v' | _ => none) = some vs := by
        suffices ∀ l vs', (∀ p ∈ List.zip l vs', ∃ fuel,
              (match evalC fuel σ' T' Δ' p.fst with
               | some (.vF v') => some v' | _ => none) = some p.snd) →
            l.length = vs'.length →
            ∃ N, l.mapM (fun callerE =>
              match evalC N σ' T' Δ' callerE with
              | some (.vF v') => some v' | _ => none) = some vs' by
          exact this _ _ hmap_elems (by simp [List.length_map, h_args_len])
        intro l
        induction l with
        | nil =>
          intro vs' _ hlen
          cases vs' with
          | nil => exact ⟨0, by simp⟩
          | cons _ _ => simp at hlen
        | cons x xs ihl =>
          intro vs' hpairs hlen
          cases vs' with
          | nil => simp at hlen
          | cons fv fvs =>
            obtain ⟨nx, hnx⟩ := hpairs ⟨x, fv⟩ (by simp [List.zip_cons_cons])
            have hpairs' : ∀ p ∈ List.zip xs fvs, ∃ fuel,
                (match evalC fuel σ' T' Δ' p.fst with
                 | some (.vF v') => some v' | _ => none) = some p.snd :=
              fun p hp => hpairs p (by simp [List.zip_cons_cons]; exact Or.inr hp)
            obtain ⟨nxs, hnxs⟩ := ihl fvs hpairs' (by simpa using hlen)
            refine ⟨max nx nxs, ?_⟩
            rw [List.mapM_cons]
            simp only [bind, Option.bind]
            have hnx_m : (match evalC (max nx nxs) σ' T' Δ' x with
                | some (.vF v') => some v' | _ => none) = some fv := by
              rcases hevx : evalC nx σ' T' Δ' x with _ | val
              · simp [hevx] at hnx
              · rcases val with _ | _ | _ | _ | _ | _ | _
                all_goals simp [hevx] at hnx
                rename_i fval
                subst hnx
                simp [evalC_mono (Nat.le_max_left nx nxs) hevx]
            have hnxs_m : xs.mapM (fun callerE => match evalC (max nx nxs) σ' T' Δ' callerE with
                | some (.vF v') => some v' | _ => none) = some fvs :=
              List.mapM_Option_mono (fun e' ve' he' => by
                rcases heve : evalC nxs σ' T' Δ' e' with _ | val
                · simp [heve] at he'
                · rcases val with _ | _ | _ | _ | _ | _ | _
                  all_goals simp [heve] at he'
                  rename_i fval
                  subst he'
                  simp [evalC_mono (Nat.le_max_right nx nxs) heve]) hnxs
            simp only [hnx_m, hnxs_m, pure]
      obtain ⟨n_args, hn_args⟩ := hmapM_exists
      -- (3) Uniform fuel for assertion all-check at witness row i
      have hasc_h : ∀ p ∈ List.zip vs (args.map Prod.snd), ∃ fuel,
          (match evalC fuel
              (updateVal (updateVal σ' c.ident_t (.vArr rows)) c.ident_i (.vN i))
              T' Δ' (.assertE (.constF p.fst) p.snd) with
           | some .vUnit => true | _ => false) = true := fun p hp => by
        obtain ⟨n_a, hn_a⟩ := ih_asserts p hp; exact ⟨n_a, by simp [hn_a]⟩
      obtain ⟨n_asserts, hn_asserts⟩ := exists_uniform_fuel_all
        (fun n m hnm p h_flt => by
          set σ_i := updateVal (updateVal σ' c.ident_t (.vArr rows)) c.ident_i (.vN i)
          rcases hev : evalC n σ_i T' Δ' (.assertE (.constF p.fst) p.snd) with _ | val
          · simp [hev] at h_flt
          · cases val <;> simp [hev] at h_flt ⊢
            simp [evalC_mono hnm hev])
        hasc_h
      -- (4) Combine all fuels and construct the evalC result
      set N := max (max (max n_rows n_args) n_asserts) n_body
      refine ⟨N + 1, ?_⟩
      -- Unfold lookup and resolve chip/trace lookups (fuel-independent)
      simp only [evalC_lookup, h_chip, h_trace]
      -- All-rows check holds at N (≥ n_rows)
      have hall_N : (List.range rows.length).all (fun j =>
          let σ'' := updateVal (updateVal σ' c.ident_t (.vArr rows)) c.ident_i (.vN j)
          match evalC N σ'' T' Δ' c.body with
          | some .vUnit => true | _ => false) = true :=
        List.all_mono' (fun j _ hj => by
          set σ_j := updateVal (updateVal σ' c.ident_t (.vArr rows)) c.ident_i (.vN j)
          show (match evalC N σ_j T' Δ' c.body with | some .vUnit => true | _ => false) = true
          rcases hev : evalC n_rows σ_j T' Δ' c.body with _ | val
          · simp [hev] at hj
          · cases val <;> simp [hev] at hj ⊢
            simp [evalC_mono (by omega : n_rows ≤ N) hev]) hn_rows
      simp only [hall_N, Bool.not_true, ite_false]
      -- mapM at N (≥ n_args) gives vs
      have hmap_N : (args.map Prod.fst).mapM (fun callerE =>
          match evalC N σ' T' Δ' callerE with
          | some (.vF v') => some v' | _ => none) = some vs :=
        List.mapM_Option_mono (fun callerE v' hv' => by
          rcases hev : evalC n_args σ' T' Δ' callerE with _ | val
          · simp [hev] at hv'
          · rcases val with _ | _ | _ | _ | _ | _ | _
            all_goals simp [hev] at hv'
            simp [evalC_mono (by omega : n_args ≤ N) hev, hv']) hn_args
      simp only [hmap_N]
      -- Any-check at witness row i holds at N (≥ n_asserts)
      have hany_N : (List.range rows.length).any (fun i' =>
          let σ'' := updateVal (updateVal σ' c.ident_t (.vArr rows)) c.ident_i (.vN i')
          (List.zip vs (args.map Prod.snd)).all (fun ⟨fv, colE⟩ =>
            match evalC N σ'' T' Δ' (.assertE (.constF fv) colE) with
            | some .vUnit => true | _ => false)) = true := by
        rw [List.any_eq_true]
        refine ⟨i, List.mem_range.mpr h_bound, ?_⟩
        exact List.all_mono' (fun p _ hp => by
          set σ_i := updateVal (updateVal σ' c.ident_t (.vArr rows)) c.ident_i (.vN i)
          show (match evalC N σ_i T' Δ' (.assertE (.constF p.fst) p.snd) with
              | some .vUnit => true | _ => false) = true
          rcases hev : evalC n_asserts σ_i T' Δ' (.assertE (.constF p.fst) p.snd) with _ | val
          · simp [hev] at hp
          · cases val <;> simp [hev] at hp ⊢
            simp [evalC_mono (by omega : n_asserts ≤ N) hev]) hn_asserts
      simp only [hany_N, Bool.not_true, ite_false]
      exact evalC_mono (by omega : n_body ≤ N) hn_body

/-! ## The Fundamental Equivalence -/

/--
**Key theorem**: `EvalProp` and `evalC` express the same semantics.

```lean
-- Convert an EvalProp hypothesis to evalC form for simp:
rw [← evalC_iff_EvalProp] at h
obtain ⟨fuel, h⟩ := h
simp only [evalC_letIn, evalC_fieldExpr, evalC_var, evalC_constF,
           evalFieldOp, Env.getVal, Env.updateVal,
           Option.bind_eq_some_iff] at h
-- h is now pure arithmetic; finish with ring / omega
```
-/
theorem evalC_iff_EvalProp {σ T Δ e v} :
    (∃ fuel, evalC fuel σ T Δ e = some v) ↔ EvalProp σ T Δ e v :=
  ⟨fun ⟨_, h⟩ => evalC_sound h, evalC_complete⟩

end Eval
