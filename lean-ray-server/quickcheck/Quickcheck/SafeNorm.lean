/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zenali
-/

import Lean
import Lean.Meta.Tactic.Simp
import Quickcheck.Lemma.Attribute
import Quickcheck.Lemma.ArrayLogics
import Quickcheck.Lemma.Logic

/-!
# Safe Normalization Rules for Quickcheck

Inspired by Aesop's safe rule mechanism, this module provides a system of
"safe" preprocessing rules that can be eagerly applied to simplify goals
before quickcheck testing, without changing the semantic meaning.

A rule is "safe" if:
1. It always preserves equivalence (doesn't change the property's validity)
2. It reduces computational complexity
3. It never needs to be backtracked

## Main Use Cases

### 1. Simplifying Nested Quantifiers
Transform complex nested ∀/∃ patterns into simpler forms.

Example:
```lean
-- Before: (∀ k, k < i → isOdd (a[k]!)) ∧ (∀ k, k < j → isEven (a[k]!))
-- After: Bounded search space or decidable predicates
```

### 2. Eliminating Redundant Conditions
Remove conditions that are implied by others or always true.

### 3. Rewriting Expensive Operations
Transform operations with high complexity into equivalent cheaper ones.

-/

namespace Quickcheck.SafeNorm

open Lean Meta Elab Tactic

/-- Configuration for safe normalization -/
structure Config where
  /-- Enable simplification of nested universal quantifiers over bounded ranges -/
  simplifyBoundedForall : Bool := true
  /-- Enable rewriting of redundant array bounds checks -/
  eliminateRedundantBounds : Bool := true
  /-- Enable transformation of nested quantifiers to computable forms -/
  makeQuantifiersComputable : Bool := true
  /-- Maximum depth for quantifier simplification to prevent infinite loops -/
  maxDepth : Nat := 10
  /-- Enable tracing of normalization steps -/
  trace : Bool := false
  deriving Inhabited

/-- Result of applying a safe normalization rule -/
inductive NormResult where
  /-- Normalization succeeded and simplified the expression -/
  | simplified (newExpr : Expr)
  /-- Expression is already in normal form -/
  | unchanged
  /-- Normalization failed or is not applicable -/
  | failed (reason : String)
  deriving Inhabited

/-- Result of applying simp to a goal (inspired by Aesop) -/
inductive SimpResult where
  /-- Goal was solved -/
  | solved
  /-- Goal was unchanged -/
  | unchanged
  /-- Goal was simplified to a new expression -/
  | simplified (newExpr : Expr)
  deriving Inhabited

/-- Safe normalization rule: a function that transforms expressions -/
structure SafeRule where
  name : String
  /-- Priority: higher priority rules are applied first -/
  priority : Nat := 50
  /-- The normalization function -/
  apply : Expr → MetaM NormResult

/--
Safe rule: Simplify bounded universal quantifiers.

Transforms patterns like `∀ k, k < n → P k` where `n` is a small constant
into a computable conjunction: `P 0 ∧ P 1 ∧ ... ∧ P (n-1)`.

This is safe because:
- It's semantically equivalent
- It's computable (decidable)
- It reduces the complexity from O(n × |P|) with potential backtracking
  to a single decidable check
-/
def simplifyBoundedForallRule (maxUnroll : Nat := 10) : SafeRule where
  name := "simplifyBoundedForall"
  priority := 100
  apply := fun e => do
    -- Match pattern: ∀ k, k < n → P k
    match e with
    | .forallE varName varTy body _ =>
      -- Check if varTy is Nat
      let varTyWhnf ← whnf varTy
      if varTyWhnf.isConstOf ``Nat then
        -- Check if body is an implication k < n → ...
        match body with
        | .forallE _ (.app (.app (.const ``LT.lt _) (.bvar 0)) bound) innerBody _ =>
          -- Try to evaluate bound to a constant
          if let some boundVal ← Meta.evalNat bound then
            if boundVal > 0 && boundVal <= maxUnroll then
              -- Unroll the quantifier
              trace[quickcheck.safenorm] "Unrolling bounded ∀ k < {boundVal}"

              withLocalDecl varName .default varTy fun _k => do
                let mut conditions : Array Expr := #[]
                for i in [:boundVal] do
                  let kVal := mkNatLit i
                  let condition := innerBody.instantiate1 kVal
                  conditions := conditions.push condition

                -- Combine with And
                let mut result := conditions[0]!
                for i in [1:conditions.size] do
                  result ← mkAppM ``And #[result, conditions[i]!]

                return .simplified result
            else
              return .unchanged
          else
            return .unchanged
        | _ => return .unchanged
      else
        return .unchanged
    | _ => return .unchanged

-- NOTE: Older experimental rules (redundant bounds, first-witness, array access,
-- match-to-ite, etc.) have been removed in the minimal version to keep the
-- behaviour of `safe_norm` simple and predictable. Currently we only keep
-- bounded-forall unrolling and existential-to-Array.any conversion.

/--
Get all theorem names marked with @[quickcheck] attribute.
-/
def getAllQuickcheckTheoremNames : MetaM (SimpTheorems) := do
  let simpTheorems ← Quickcheck.quickcheckExt.getTheorems
  let num_lemmas : Nat := simpTheorems.lemmaNames.toList.length
  trace[quickcheck.safenorm] "mkQuickcheckSimpContext: loaded {num_lemmas} simp theorems from @[quickcheck]"
  let print_count := min num_lemmas 3
  for i in [:print_count] do
    let origin := simpTheorems.lemmaNames.toList[i]!
    trace[quickcheck.safenorm] "Lemma name: {toString origin.key}"
  return simpTheorems

/--
Recursively simplify an expression, including inside ∀ and → binders.
This allows simp theorems that require local context (like get!_to_get!!) to work.
-/
partial def simpExprRecursive (e : Expr) (ctx : Simp.Context) : MetaM Expr := do
  let ctx := ctx.setFailIfUnchanged false
  match e with
  | .forallE name ty body bi =>
    -- Simplify the type
    let ty' ← simpExprRecursive ty ctx
    -- Introduce the variable and simplify the body in a goal context
    withLocalDecl name bi ty' fun fv => do
      -- Create a goal with the body as type, so we can use simpAll
      let bodyType := body.instantiate1 fv
      let mvar ← mkFreshExprMVar bodyType
      let goal := mvar.mvarId!
      goal.withContext do
        -- Use simpAll to simplify the entire goal (including expressions inside →)
        let (result, _) ← Lean.Meta.simpAll goal ctx #[]
        match result with
        | none =>
          -- Goal solved, but we need to return the body type
          return bodyType
        | some newGoal =>
          let newType ← newGoal.getType
          -- Recursively simplify the new type to handle nested binders
          let body' ← simpExprRecursive newType ctx
          mkForallFVars #[fv] body'
  | .lam name ty body bi =>
    -- Similar to forallE
    let ty' ← simpExprRecursive ty ctx
    withLocalDecl name bi ty' fun fv => do
      let bodyType := body.instantiate1 fv
      let mvar ← mkFreshExprMVar bodyType
      let goal := mvar.mvarId!
      goal.withContext do
        let (result, _) ← Lean.Meta.simpAll goal ctx #[]
        match result with
        | none => return bodyType
        | some newGoal =>
          let newType ← newGoal.getType
          let body' ← simpExprRecursive newType ctx
          mkLambdaFVars #[fv] body'
  | _ =>
    -- For non-binding expressions, use simp directly
    let (result, _) ← Lean.Meta.simp e ctx
    return result.expr

/--
Simplify an expression using simp theorems in a goal context.
This allows simp theorems that require local context (like get!_to_get!!) to work.
-/
def simpExprQuickcheck (e : Expr) (ctx : Simp.Context) : MetaM SimpResult := do
  let beforeType := e
  trace[quickcheck.safenorm] "    simpExprQuickcheck: beforeType = {beforeType}"

  -- Recursively simplify, introducing binders as needed
  let afterType ← simpExprRecursive e ctx

  trace[quickcheck.safenorm] "    simpExprQuickcheck: afterType = {afterType}"

  if afterType != beforeType then
    return .simplified afterType
  else
    return .unchanged



/--
Safe rule: Apply all @[quickcheck] marked simp theorems to simplify expressions.

This rule applies simp with all @[quickcheck] marked theorems, which can include:
- `get!_eq_get`: Convert `arr[i]!` to `arr[i]` when bounds are available
- Other simplification lemmas marked with @[quickcheck]

This is safe because:
- It only uses theorems explicitly marked as safe for quickcheck
- It preserves semantic equivalence
- It can simplify expressions to make them more testable

Uses Simp.mkContext and simpAll directly, avoiding evalTactic.
-/
def applyQuickcheckSimpRule (showApplied : Bool := false) : SafeRule where
  name := "applyQuickcheckSimp"
  priority := 90  -- Lower than simplifyBoundedForallRule but higher than makeExistentialsComputableRule
  apply := fun e => do
    trace[quickcheck.safenorm] "applyQuickcheckSimpRule: Trying to apply @[quickcheck] simp theorems..."
    trace[quickcheck.safenorm] "  Input expression: {e}"

    -- Expand reducible definitions to expose patterns
    let eReduced ← withTransparency .reducible (whnf e)
    if eReduced != e then
      trace[quickcheck.safenorm] "  After whnf (reducible): {eReduced}"

    -- Get @[quickcheck] simp theorems
    let simpTheorems ← getAllQuickcheckTheoremNames

    if simpTheorems.lemmaNames.isEmpty then
      trace[quickcheck.safenorm] "  No @[quickcheck] theorems found"
      return .unchanged

    -- Create Simp.Context with only @[quickcheck] simp theorems
    let ctx ← Simp.mkContext Simp.neutralConfig
      (simpTheorems := #[simpTheorems])
      (congrTheorems := ← getSimpCongrTheorems)

    -- Simplify the expression directly
    match ← simpExprQuickcheck eReduced ctx with
    | .unchanged =>
      trace[quickcheck.safenorm] "  Result: unchanged"
      return .unchanged
    | .simplified newExpr =>
      trace[quickcheck.safenorm] "  Result: simplified!"
      trace[quickcheck.safenorm] "    New expression: {newExpr}"
      if showApplied then
        let theoremNames := simpTheorems.lemmaNames.toList.map (fun origin => origin.key)
        logInfo m!"Applied @[quickcheck] theorems: {theoremNames.map toString |>.toArray}"
      return .simplified newExpr
    | .solved =>
      -- This shouldn't happen for expressions, but handle it anyway
      trace[quickcheck.safenorm] "  Result: solved (returning unchanged)"
      return .unchanged

/-- Default set of safe normalization rules (minimal version).

Currently we only enable:
- `simplifyBoundedForallRule`: unroll small bounded ∀ over `Nat`
- `applyQuickcheckSimpRule`: apply @[quickcheck] marked simp theorems
-/
def defaultRules (showApplied : Bool := false) : List SafeRule :=
  [ simplifyBoundedForallRule 10,
    applyQuickcheckSimpRule showApplied
  ]

/--
Apply safe normalization rules to an expression.

Rules are applied in priority order. The function returns the normalized
expression and a list of rules that were applied.
-/
def normalize (rules : List SafeRule := defaultRules) (cfg : Config := {}) (e : Expr)
    : MetaM (Expr × List String) := do
  trace[quickcheck.safenorm] "SafeNorm.normalize starting..."
  trace[quickcheck.safenorm] "  Input expression: {e}"
  trace[quickcheck.safenorm] "  Number of rules: {rules.length}"

  let sortedRules := rules.toArray.qsort (fun r1 r2 => r1.priority > r2.priority) |>.toList

  if cfg.trace then
    trace[quickcheck.safenorm] "  Rule priorities:"
    for rule in sortedRules do
      trace[quickcheck.safenorm] "    - {rule.name}: {rule.priority}"

  let mut current := e
  let mut appliedRules : List String := []
  let mut depth := 0
  let mut changed := true

  while changed && depth < cfg.maxDepth do
    changed := false
    depth := depth + 1
    trace[quickcheck.safenorm] "  Iteration {depth}:"

    for rule in sortedRules do
      trace[quickcheck.safenorm] "    Trying rule: {rule.name}"
      match ← rule.apply current with
      | .simplified newExpr =>
        trace[quickcheck.safenorm] "      ✓ Applied rule: {rule.name}"
        current := newExpr
        appliedRules := rule.name :: appliedRules
        changed := true
      | .unchanged =>
        trace[quickcheck.safenorm] "      - Unchanged"
        continue
      | .failed reason =>
        trace[quickcheck.safenorm] "      ✗ Failed: {reason}"
        continue

  -- Final "core" simp pass, analogous to `simp only []`:
  -- we do not use any additional simp theorems here, only the built‑in
  -- β/ι/δ simplifications and congruence rules, plus the local context.
  trace[quickcheck.safenorm] "  Running final core simp pass (builtin reductions only)..."
  let coreCtxBase ←
    Simp.mkContext Simp.neutralConfig
      (simpTheorems := #[])
      (congrTheorems := ← getSimpCongrTheorems)
  let coreCtx := coreCtxBase.setFailIfUnchanged false
  let mvarCore ← mkFreshExprMVar current
  let goalCore := mvarCore.mvarId!
  let (current', appliedRules') ← goalCore.withContext do
    match ← Lean.Meta.simpAll goalCore coreCtx #[] with
    | (none, _) =>
      trace[quickcheck.safenorm] "    core simp: goal solved (ignored for expression result)."
      return (current, appliedRules)
    | (some mvarNew, _) =>
      let newType ← mvarNew.getType
      if newType != current then
        trace[quickcheck.safenorm] "    core simp simplified expression."
        trace[quickcheck.safenorm] "      New expression: {newType}"
        return (newType, "coreSimp" :: appliedRules)
      else
        trace[quickcheck.safenorm] "    core simp: expression unchanged."
        return (current, appliedRules)

  current := current'
  appliedRules := appliedRules'

  trace[quickcheck.safenorm] "SafeNorm.normalize completed:"
  trace[quickcheck.safenorm] "  Applied {appliedRules.length} rules: {appliedRules.reverse}"
  trace[quickcheck.safenorm] "  Final expression: {current}"
  return (current, appliedRules.reverse)

/--
Tactic: Apply safe normalization to the goal.

Usage:
```lean
example : complex_property := by
  safe_norm
  quickcheck
```
-/
elab "safe_norm" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  trace[quickcheck.safenorm] "Before normalization: {← Meta.ppExpr target}"

  -- Get @[quickcheck] simp theorems
  let simpTheorems ← getAllQuickcheckTheoremNames

  if !simpTheorems.lemmaNames.isEmpty then
    -- Build simp_all only [theorem1, theorem2, ...] using evalTactic
    let theoremNames := simpTheorems.lemmaNames.toList.map (fun origin => origin.key)
    let simpLemmas ← theoremNames.toArray.mapM fun name => do
      let ident := mkIdent name
      `(Parser.Tactic.simpLemma| $ident:ident)

    evalTactic (← `(tactic| simp_all only [$simpLemmas,*]))

/--
Tactic: Apply safe normalization to the goal and show which theorems were applied.

This is similar to `simp?` - it shows which @[quickcheck] marked theorems
were used during normalization.

Usage:
```lean
example : complex_property := by
  safe_norm?
  quickcheck
```
-/
elab "safe_norm?" : tactic => withMainContext do
  -- Get @[quickcheck] simp theorems
  let simpTheorems ← getAllQuickcheckTheoremNames

  if simpTheorems.lemmaNames.isEmpty then
    logInfo "No normalization rules were applicable"
  else
    let theoremNames := simpTheorems.lemmaNames.toList.map (fun origin => origin.key)
    let simpLemmas ← theoremNames.toArray.mapM fun name => do
      let ident := mkIdent name
      `(Parser.Tactic.simpLemma| $ident:ident)

    evalTactic (← `(tactic| simp_all? only [$simpLemmas,*]))

    -- let theoremNameStrs := theoremNames.map toString
    -- logInfo m!"Applied @[quickcheck] theorems: {theoremNameStrs.toArray}"

end Quickcheck.SafeNorm
