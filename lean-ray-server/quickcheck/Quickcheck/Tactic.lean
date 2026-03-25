/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Kim Morrison
-/

import Quickcheck.Testable
import Quickcheck.Attr
import Quickcheck.SafeNorm
import Quickcheck.Preprocess
import Lean.Meta.Tactic.Split


/-!
## Finding counterexamples automatically using `quickcheck`

A proposition can be tested by writing it out as:

```lean
example (xs : List Nat) (w : ∃ x ∈ xs, x < 3) : ∀ y ∈ xs, y < 5 := by quickcheck
-- ===================
-- Found problems!

-- xs := [0, 5]
-- x := 0
-- y := 5
-- -------------------

example (x : Nat) (h : 2 ∣ x) : x < 100 := by quickcheck
-- ===================
-- Found problems!

-- x := 258
-- -------------------

example (α : Type) (xs ys : List α) : xs ++ ys = ys ++ xs := by quickcheck
-- ===================
-- Found problems!

-- α := Int
-- xs := [-4]
-- ys := [1]
-- -------------------

example : ∀ x ∈ [1,2,3], x < 4 := by quickcheck
-- Success
```

In the first example, `quickcheck` is called on the following goal:

```lean
xs : List Nat,
h : ∃ (x : Nat) (H : x ∈ xs), x < 3
⊢ ∀ (y : Nat), y ∈ xs → y < 5
```

The local constants are reverted and an instance is found for
`Testable (∀ (xs : List Nat), (∃ x ∈ xs, x < 3) → (∀ y ∈ xs, y < 5))`.
The `Testable` instance is supported by instances of `Sampleable (List Nat)`,
`Decidable (x < 3)` and `Decidable (y < 5)`. `quickcheck` builds a
`Testable` instance step by step with:

```
- Testable (∀ (xs : List Nat), (∃ x ∈ xs, x < 3) → (∀ y ∈ xs, y < 5))
                                     -: Sampleable (List xs)
- Testable ((∃ x ∈ xs, x < 3) → (∀ y ∈ xs, y < 5))
- Testable (∀ x ∈ xs, x < 3 → (∀ y ∈ xs, y < 5))
- Testable (x < 3 → (∀ y ∈ xs, y < 5))
                                     -: Decidable (x < 3)
- Testable (∀ y ∈ xs, y < 5)
                                     -: Decidable (y < 5)
```

`Sampleable (List Nat)` lets us create random data of type `List Nat` in a way that
helps find small counter-examples.  Next, the test of the proposition
hinges on `x < 3` and `y < 5` to both be decidable. The
implication between the two could be tested as a whole but it would be
less informative. Indeed, if we generate lists that only contain numbers
greater than `3`, the implication will always trivially hold but we should
conclude that we haven't found meaningful examples. Instead, when `x < 3`
does not hold, we reject the example (i.e.  we do not count it toward
the 100 required positive examples) and we start over. Therefore, when
`quickcheck` prints `Success`, it means that a hundred suitable lists
were found and successfully tested.

If no counter-examples are found, `quickcheck` behaves like `admit`.

`quickcheck` can also be invoked using `#eval`:

```lean
#eval Quickcheck.Testable.check (∀ (α : Type) (xs ys : List α), xs ++ ys = ys ++ xs)
-- ===================
-- Found problems!

-- α := Int
-- xs := [-4]
-- ys := [1]
-- -------------------
```

For more information on writing your own `Sampleable` and `Testable`
instances, see `Testing.Quickcheck.Testable`.
-/

open Lean Elab Meta Tactic
open Parser.Tactic
open Quickcheck Decorations

/--
`quickcheck` considers a proof goal and tries to generate examples
that would contradict the statement.

Let's consider the following proof goal.

```lean
xs : List Nat,
h : ∃ (x : Nat) (H : x ∈ xs), x < 3
⊢ ∀ (y : Nat), y ∈ xs → y < 5
```

The local constants will be reverted and an instance will be found for
`Testable (∀ (xs : List Nat), (∃ x ∈ xs, x < 3) → (∀ y ∈ xs, y < 5))`.
The `Testable` instance is supported by an instance of `Sampleable (List Nat)`,
`Decidable (x < 3)` and `Decidable (y < 5)`.

Examples will be created in ascending order of size (more or less)

The first counter-examples found will be printed and will result in an error:

```
===================
Found problems!
xs := [1, 28]
x := 1
y := 28
-------------------
```

If `quickcheck` successfully tests 100 examples, it acts like
admit. If it gives up or finds a counter-example, it reports an error.

For more information on writing your own `Sampleable` and `Testable`
instances, see `Testing.Quickcheck.Testable`.

Optional arguments given with `quickcheck (config : { ... })`
* `numInst` (default 100): number of examples to test properties with
* `maxSize` (default 100): final size argument

Options:
* `set_option trace.quickcheck.decoration true`: print the proposition with quantifier annotations
* `set_option trace.quickcheck.discarded true`: print the examples discarded because they do not
  satisfy assumptions
* `set_option trace.quickcheck.shrink.steps true`: trace the shrinking of counter-example
* `set_option trace.quickcheck.shrink.candidates true`: print the lists of candidates considered
  when shrinking each variable
* `set_option trace.quickcheck.instance true`: print the instances of `testable` being used to test
  the proposition
* `set_option trace.quickcheck.success true`: print the tested samples that satisfy a property
* `set_option trace.quickcheck.constructor true`: print the number of times `constructor` is used
  in `quickcheck_all` (only applies to `quickcheck_all`)
* `set_option trace.quickcheck.split true`: print the number of times `split` is used
  in `quickcheck_all` (only applies to `quickcheck_all`)
* `set_option trace.quickcheck.adaptive true`: trace adaptive mode maxSize reductions when timeouts occur
-/
syntax (name := quickcheckSyntax) "quickcheck" (config)? : tactic

-- Internal function: recursively apply preprocess until no more splits occur
-- This ensures all goals are fully split before calling quickcheckCore
private def preprocessRecursive : TacticM Unit := do
  let mut maxIterations := 20
  let mut anySplit := true
  while maxIterations > 0 && anySplit do
    maxIterations := maxIterations - 1
    anySplit := false
    let goalsBefore ← getGoals
    try
      evalTactic (← `(tactic| all_goals preprocess))
      let goalsAfter ← getGoals
      if goalsAfter.length > goalsBefore.length then
        anySplit := true
    catch _ =>
      break

-- Core quickcheck logic: skip preprocess, directly execute the main flow
private def quickcheckCore (cfg : Configuration) : TacticM Unit := withMainContext do
  -- Step 2: Revert all hypotheses
  let (_, g) ← (← getMainGoal).revert ((← getLocalHyps).map (Expr.fvarId!))
  g.withContext do
  let tgt ← g.getType
  trace[quickcheck] "The target after revert is: {tgt}"

  -- Step 3: Apply safe normalization if enabled
  let tgt ← if cfg.enableSafeNorm then do
    let normCfg : SafeNorm.Config := {
      trace := true
      maxDepth := 5
    }
    let (normalized, appliedRules) ← SafeNorm.normalize SafeNorm.defaultRules normCfg tgt
    if appliedRules.length > 0 then
      trace[quickcheck] "Safe normalization applied rules: {appliedRules}"
      trace[quickcheck] "Before normalization: {tgt}"
      trace[quickcheck] "After normalization: {normalized}"
    pure normalized
  else
    pure tgt

  let tgt' ← addDecorations tgt

  -- Safety check: verify that any getLast! calls have provably non-empty lists
  -- This prevents runtime panics during testing
  -- Only run if enableSafeGuard is true in config
  if cfg.enableSafeGuard then
    try
      -- We reduce the target with reducible transparency to see through @[reducible] definitions
      let tgtReduced ← Meta.withTransparency .reducible (Meta.reduce tgt')
      SafeGuard.checkGetLastSafety tgtReduced
    catch e =>
      throwError "\
        [Quickcheck Safety Error]\
        \n{e.toMessageData}\
        \n\
        \nTo fix: wrap partial functions with guards like `if l.length > 0 then ... else True`\
        \nOr disable SafeGuard: quickcheck (config := \{ enableSafeGuard := false })"

  let cfg := { cfg with
    traceDiscarded := cfg.traceDiscarded || (← isTracingEnabledFor `quickcheck.discarded),
    traceSuccesses := cfg.traceSuccesses || (← isTracingEnabledFor `quickcheck.success),
    traceShrink := cfg.traceShrink || (← isTracingEnabledFor `quickcheck.shrink.steps),
    traceShrinkCandidates := cfg.traceShrinkCandidates
      || (← isTracingEnabledFor `quickcheck.shrink.candidates) }

  -- If decidableBound is set, transform unbounded foralls INSIDE And/Or to bounded ones
  -- We don't touch the outer foralls (which are sampled), only inner ones
  let tgt' ← if let some bound := cfg.decidableBound then
    -- Transform ∀ x : Int/Nat, P x to bounded version, but only inside logical connectives
    let rec addBoundsInner (maxDepth : Nat) (e : Expr) : MetaM Expr := do
      match maxDepth with
      | 0 =>
          return e  -- Safety: prevent infinite recursion
      | maxDepth + 1 =>
          let d := maxDepth
          match e with
          | .forallE name ty body bi =>
              let tyWhnf ← whnf ty
              -- Check if this is ∀ x : Int or ∀ x : Nat (not a Prop, i.e., not implication)
              if !(← Meta.isProp ty) then
                Meta.withLocalDecl name bi ty fun x => do
                  let body' ← addBoundsInner d (body.instantiate1 x)
                  if tyWhnf.isConstOf ``Int then
                    -- Transform to: ∀ x : Int, -bound ≤ x ∧ x ≤ bound → P x
                    let boundExpr := mkNatLit bound
                    let intBound  := mkApp (mkConst ``Int.ofNat) boundExpr
                    let negBound  ← mkAppM ``Neg.neg #[intBound]
                    let lowerBound ← mkAppM ``LE.le #[negBound, x]
                    let upperBound ← mkAppM ``LE.le #[x, intBound]
                    let boundCond ← mkAppM ``And #[lowerBound, upperBound]
                    let guardedBody := Expr.forallE `h boundCond body' .default
                    Meta.mkForallFVars #[x] guardedBody
                  else if tyWhnf.isConstOf ``Nat then
                    -- Transform to: ∀ x : Nat, x ≤ bound → P x
                    let boundExpr := mkNatLit bound
                    let upperBound ← mkAppM ``LE.le #[x, boundExpr]
                    let guardedBody := Expr.forallE `h upperBound body' .default
                    Meta.mkForallFVars #[x] guardedBody
                  else
                    -- Other types: just recurse into body
                    Meta.mkForallFVars #[x] body'
              else
                -- This is an implication, recurse into both sides
                let ty' ← addBoundsInner d ty
                Meta.withLocalDecl name bi ty' fun x => do
                  let body' ← addBoundsInner d (body.instantiate1 x)
                  Meta.mkForallFVars #[x] body'
          | .app (.app (.const ``And _) p) q =>
              let p' ← addBoundsInner d p
              let q' ← addBoundsInner d q
              mkAppM ``And #[p', q']
          | .app (.app (.const ``Or _) p) q =>
              let p' ← addBoundsInner d p
              let q' ← addBoundsInner d q
              mkAppM ``Or #[p', q']
          | .app (.const ``Not _) p =>
              let p' ← addBoundsInner d p
              mkAppM ``Not #[p']
          | _ => pure e
    termination_by maxDepth
    decreasing_by
      all_goals simp only [Nat.succ_eq_add_one, Nat.lt_add_one]

    -- Process the target, but skip outer NamedBinder-wrapped foralls
    let rec addBoundsOuter (maxDepth : Nat) (e : Expr) : MetaM Expr := do
      match maxDepth with
      | 0 =>
        return e  -- Safety: prevent infinite recursion
      | maxDepth + 1 =>
        let d := maxDepth
        -- If this is a NamedBinder, preserve it and recurse
        if e.isAppOf ``Quickcheck.NamedBinder then
          let args := e.getAppArgs
          if args.size >= 2 then
            let inner' ← addBoundsOuter d args[1]!
            return mkAppN (mkConst ``Quickcheck.NamedBinder) #[args[0]!, inner']
          else
            return e

        match e with
        | .forallE name ty body bi =>
          if !(← Meta.isProp ty) then
            -- This is an outer ∀ x : α, ... (will be sampled)
            -- Just recurse into body, but use addBoundsInner for the atomic propositions
            Meta.withLocalDecl name bi ty fun x => do
              let body' ← addBoundsOuter d (body.instantiate1 x)
              Meta.mkForallFVars #[x] body'
          else
            -- This is an implication P → Q
            -- Apply addBoundsInner to P (as it's an atomic prop), but addBoundsOuter to Q
            let ty' ← addBoundsInner d ty
            Meta.withLocalDecl name bi ty' fun x => do
              let body' ← addBoundsOuter d (body.instantiate1 x)
              Meta.mkForallFVars #[x] body'
        | _ =>
          -- For everything else (And, Or, etc. at top level), use addBoundsInner
          addBoundsInner d e
    termination_by maxDepth
    decreasing_by
      all_goals simp only [Nat.succ_eq_add_one, Nat.lt_add_one]
    addBoundsOuter 100 tgt'  -- Use maxDepth = 100 to prevent infinite recursion
  else
    pure tgt'

  -- If onlyDecidable is enabled, we *used* to aggressively check every atomic
  -- proposition for a Decidable instance here. That recursive check relied on
  -- Decidable.rec and can trigger codegen limitations on some targets.
  -- For now, we rely on the combination of:
  -- * SafeNorm.normalize (which uses @[quickcheck] lemmas like split_imp_cases)
  -- * The later Testable synthesis with onlyDecidable := true
  -- and skip the extra recursive Decidable check to avoid Decidable.rec in codegen.
  --
  -- if cfg.onlyDecidable then
  --   ... recursive Decidable check (removed) ...

  let inst ← try
    -- Use reducible transparency to allow type class inference to see through @[reducible] definitions
    -- This enables automatic Decidable instance synthesis for reducible Prop definitions
    Meta.withTransparency .reducible do
      synthInstance (← mkAppM ``Testable #[tgt'])
  catch _ =>
    throwError s!"\
      Failed to create a `testable` instance for `{tgt}`.\
    \nWhat to do:\
    \n1. make sure that the types you are using have `Quickcheck.SampleableExt` instances\
    \n (you can use `#sample my_type` if you are unsure);\
    \n2. make sure that the relations and predicates that your proposition use are decidable;\
    \n3. make sure that instances of `Quickcheck.Testable` exist that, when combined,\
    \n  apply to your decorated proposition:\
    \n```\
    \n" ++ toString tgt' ++ "\
    \n```\
    \n\
    \nUse `set_option trace.Meta.synthInstance true` to understand what instances are missing.\
    \n\
    \nTry this:\
    \nset_option trace.Meta.synthInstance true\
    \n#synth Quickcheck.Testable (" ++ toString tgt' ++ ")"
  let e ← mkAppOptM ``Testable.check #[tgt, toExpr cfg, tgt', inst]
  trace[quickcheck.decoration] s!"[testable decoration]\n  {tgt'}"
  -- Porting note: I have not ported support for `trace.quickcheck.instance`.
  -- See the commented out code below from mathlib3 if you would like to implement this.
  --   when_tracing `quickcheck.instance   <| do
  --   { inst ← summarize_instance inst >>= pp,
  --     trace!"\n[testable instance]{format.indent inst 2}" },
  let code ← unsafe evalExpr (CoreM PUnit) (mkApp (mkConst ``CoreM) (mkConst ``PUnit [1])) e
  _ ← code
  admitGoal g

-- Main quickcheck tactic: first recursively preprocess all goals, then call quickcheckCore
elab_rules : tactic | `(tactic| quickcheck $[$cfgStx]?) => withMainContext do
  let cfg ← elabConfig (mkOptionalNode cfgStx)

  -- Step 1: Recursively apply preprocess until all goals are fully split
  -- This ensures each goal is atomic before revert happens in quickcheckCore
  -- This prevents Bool/Prop mixing issues in type inference
  preprocessRecursive

  -- Step 2: Call quickcheckCore on all goals (which will handle revert and Testable synthesis)
  let goals ← getGoals
  trace[quickcheck] "The goals after preprocess are: {goals}"
  for goal in goals do
    setGoals [goal]
    quickcheckCore cfg
  setGoals []

-- Porting note: below is the remaining code from mathlib3 which supports the
-- `trace.quickcheck.instance` trace option, and which has not been ported.

-- namespace tactic.interactive
-- open tactic quickcheck

-- open expr

-- /-- Tree structure representing a `testable` instance. -/
-- meta inductive instance_tree
-- | node : name → expr → list instance_tree → instance_tree

-- /-- Gather information about a `testable` instance. Given
-- an expression of type `testable ?p`, gather the
-- name of the `testable` instances that it is built from
-- and the proposition that they test. -/
-- meta def summarize_instance : expr → tactic instance_tree
-- | (lam n bi d b) := do
--    v ← mk_local' n bi d,
--    summarize_instance <| b.instantiate_var v
-- | e@(app f x) := do
--    `(testable %%p) ← infer_type e,
--    xs ← e.get_app_args.mmap_filter (try_core ∘ summarize_instance),
--    pure <| instance_tree.node e.get_app_fn.const_name p xs
-- | e := do
--   failed

-- /-- format an `instance_tree` -/
-- meta def instance_tree.to_format : instance_tree → tactic format
-- | (instance_tree.node n p xs) := do
--   xs ← format.join <$> (xs.mmap <| λ t, flip format.indent 2 <$> instance_tree.to_format t),
--   ys ← pformat!"testable ({p})",
--   pformat!"+ {n} :{format.indent ys 2}\n{xs}"

-- meta instance instance_tree.has_to_tactic_format : has_to_tactic_format instance_tree :=
-- ⟨ instance_tree.to_format ⟩
