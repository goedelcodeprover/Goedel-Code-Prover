/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Kim Morrison
-/

import Quickcheck.Testable
import Quickcheck.Attr
import Quickcheck.SafeNorm
import Lean.Elab.Tactic
import Lean.Meta.Tactic.Split

/-!
## Preprocessing tactics for quickcheck

This module provides the `preprocess` tactic that splits And/Or conjunctions
and match expressions before running quickcheck. This allows manual control
over when splitting happens.
-/

open Lean Elab.Tactic Parser.Tactic Lean.Meta

/-- Check if an expression is And (we don't split Or, let quickcheck handle it) -/
private def isAnd (e : Expr) : MetaM Bool := do
  let eWhnf ← Meta.whnf e
  match eWhnf.getAppFn with
  | .const ``And _ =>
    if eWhnf.getAppNumArgs >= 2 then
      return true
    else return false
  | _ => return false

/-- Syntactic check (after whnf): does the expression mention a `Decidable` recursor?

We over-approximate a bit and flag any application whose head constant lives in
the `Decidable` namespace (e.g. `Decidable.rec`, `Decidable.recOn`, etc.).

We first put the expression in weak head normal form so that definitional
equalities (like `if` implemented via `Decidable.rec`) are visible.
-/
private def containsDecidableRec (e : Expr) : MetaM Bool := do
  let eWhnf ← Meta.whnf e
  return (eWhnf.find? fun t =>
    match t.getAppFn with
    | .const n _ => n == `Decidable.rec
    | _ => false).isSome

/-- Try to split match expressions and And in the goal.

   Returns `true` if splitting occurred, `false` otherwise.

   For And: uses `constructor` to split into multiple goals (all must be proven)
   For Or: does NOT split - let quickcheck's orTestable instance handle it
   For match: uses `split` tactic
-/
def trySplit : TacticM Bool := withMainContext do
  let savedState ← saveState
  let goalsBeforeSplit ← getGoals
  trace[quickcheck.preprocess] s!"[trySplit] Trying to split, current goals: {goalsBeforeSplit.length}"

  -- First check if the goal is And
  let mvarId ← getMainGoal
  let target ← mvarId.getType
  let targetReduced ← Meta.withTransparency .reducible (Meta.whnf target)

  if ← isAnd targetReduced then
    trace[quickcheck.preprocess] "[trySplit] Found And, using constructor"
    try
      evalTactic (← `(tactic| constructor))
      let goalsAfterSplit ← getGoals
      if goalsAfterSplit.length > goalsBeforeSplit.length then
        -- After splitting an And, make sure we didn't accidentally introduce
        -- `Decidable.rec` into any of the new goal types. If we did, roll back.
        let mut bad := false
        for g in goalsAfterSplit do
          let ty ← g.getType
          if ← containsDecidableRec ty then
            bad := true
        if bad then
          trace[quickcheck.preprocess] "[trySplit] constructor introduced Decidable.rec; rolling back."
          savedState.restore
          setGoals goalsBeforeSplit
          return false
        else
          trace[quickcheck.preprocess] s!"[trySplit] ✓ And split successful! Split into {goalsAfterSplit.length} goals"
          return true
      else
        trace[quickcheck.preprocess] "[trySplit] constructor did not create new goals"
        return false
    catch e =>
      trace[quickcheck.preprocess] "[trySplit] constructor failed: {e.toMessageData}"
      return false

  -- If not And, try regular split for match expressions
  -- Note: We don't split Or - quickcheck's orTestable will try all branches
  try
    evalTactic (← `(tactic| split))
    let goalsAfterSplit ← getGoals
    if goalsAfterSplit.length > goalsBeforeSplit.length then
      -- Check if any of the new goals' types contain `Decidable.rec`. If so,
      -- we roll back this split to avoid introducing recursors that codegen
      -- cannot handle.
      let mut bad := false
      for g in goalsAfterSplit do
        let ty ← g.getType
        if ← containsDecidableRec ty then
          bad := true
      if bad then
        trace[quickcheck.preprocess] "[trySplit] split introduced Decidable.rec; rolling back."
        savedState.restore
        setGoals goalsBeforeSplit
        return false
      else
        trace[quickcheck.preprocess] s!"[trySplit] ✓ Split successful! Split into {goalsAfterSplit.length} goals"
        return true
    else
      trace[quickcheck.preprocess] "[trySplit] split did not create new goals"
      return false
  catch e =>
    trace[quickcheck.preprocess] "[trySplit] split failed: {e.toMessageData}"
    return false

/-- `preprocess` tactic: applies a set of preprocessing tactics to simplify goals -/
syntax (name := preprocessSyntax) "preprocess" : tactic

/-- Preprocess tactic: splits And conjunctions and match expressions before quickcheck.

   This is useful when you want to manually control when splitting happens,
   or when you want to split without immediately running quickcheck.

   Behavior:
   - And (∧): Splits into multiple goals, all must be proven
   - Or (∨): Does NOT split - quickcheck will test all branches automatically
   - match: Splits into cases for each pattern

   Usage:
   ```lean
   preprocess
   -- Now goals are split, you can apply quickcheck to each one
   all_goals quickcheck
   ```
-/
elab_rules : tactic | `(tactic| preprocess) => withMainContext do
  let goalsBefore ← getGoals
  let initialGoalCount := goalsBefore.length

  -- Try to split repeatedly until no more splits occur
  -- Use a maximum iteration count to prevent infinite loops
  let mut maxIterations := 20
  let mut anySplit := false

  while maxIterations > 0 do
    maxIterations := maxIterations - 1

    -- Try to split the main goal
    if ← trySplit then
      anySplit := true
      let goalsAfter ← getGoals
      trace[quickcheck.preprocess] s!"[preprocess] Iteration: split into {goalsAfter.length} goals"

      -- Continue to next iteration to try splitting the new goals
      continue
    else
      -- No split occurred on main goal
      -- Try to split other goals if there are multiple
      let allGoals ← getGoals
      if allGoals.length > 1 then
        -- Process each remaining goal
        let mut foundSplit := false
        for i in [:allGoals.length] do
          if foundSplit then break

          let goal := allGoals[i]!
          let otherGoals := allGoals.toArray.toList.filter (fun g => g != goal)

          -- Make this goal the main goal and try to split
          setGoals [goal]
          if ← trySplit then
            foundSplit := true
            anySplit := true
            let splitGoals ← getGoals
            -- Combine split goals with other goals
            setGoals (splitGoals ++ otherGoals)
            let goalsAfterSplit ← getGoals
            trace[quickcheck.preprocess] s!"[preprocess] Iteration: split non-main goal, now have {goalsAfterSplit.length} goals"
            break
          else
            -- Restore all goals if split failed
            setGoals allGoals

        if not foundSplit then
          -- No more goals can be split
          break
      else
        -- Only one goal and it can't be split
        break

  if anySplit then
    let goalsAfter ← getGoals
    let finalGoalCount := goalsAfter.length
    trace[quickcheck.preprocess] s!"[preprocess] ✓ Final result: Split from {initialGoalCount} goal(s) into {finalGoalCount} goal(s)"
  else
    trace[quickcheck.preprocess] s!"[preprocess] No split occurred"

  return
