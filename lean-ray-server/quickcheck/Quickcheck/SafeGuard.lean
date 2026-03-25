/-
Safe guards for Quickcheck to prevent runtime panics from partial functions.

This module provides a mechanism to automatically verify safety conditions
(like list non-emptiness) before evaluating Decidable instances.
-/

import Lean

namespace Quickcheck.SafeGuard

open Lean Meta Elab Term

/-- List of partial function names to check -/
def partialFunctions : List Name := [
  ``List.getLast!,
  ``List.head!,
  ``List.tail!,
  ``GetElem?.getElem!
]

/-- Check if an expression contains Float type -/
partial def containsFloatType (e : Expr) : MetaM Bool := do
  let rec visit (e : Expr) : MetaM Bool := do
    -- Check if this expression's type is Float
    try
      let ty ← inferType e
      let tyWhnf ← whnf ty
      if tyWhnf.isConstOf ``Float then
        return true
    catch _ =>
      pure ()

    -- Check if the expression itself is the Float constant
    if e.isConstOf ``Float then
      return true

    -- Recursively check subexpressions
    match e with
    | .app f a =>
      let fHasFloat ← visit f
      if fHasFloat then return true
      visit a
    | .lam _ d b _ =>
      let dHasFloat ← visit d
      if dHasFloat then return true
      visit b
    | .forallE _ d b _ =>
      let dHasFloat ← visit d
      if dHasFloat then return true
      visit b
    | .letE _ t v b _ =>
      let tHasFloat ← visit t
      if tHasFloat then return true
      let vHasFloat ← visit v
      if vHasFloat then return true
      visit b
    | .mdata _ e' =>
      visit e'
    | .proj _ _ e' =>
      visit e'
    | _ => return false

  visit e

/--
Context for tracking guarded indices.
Maps (array expression, index expression) pairs to whether they are guarded by a bounds check.
-/
structure GuardContext where
  /-- Set of (array, index) pairs that are guarded by `index < array.size` -/
  guardedIndices : Std.HashSet (UInt64 × UInt64) := {}
  deriving Inhabited

/-- Check if an expression is a bounds check like `i < a.size` -/
def isBoundsCheck (e : Expr) : MetaM (Option (Expr × Expr)) := do
  -- Match pattern: LT.lt i (Array.size a) or similar
  match e with
  | .app (.app (.app (.app (.const ``LT.lt _) _) _) idx) bound =>
    -- Check if bound is of form Array.size a or List.length l
    match bound with
    | .app (.app (.const ``Array.size _) _) arr =>
      return some (arr, idx)
    | .app (.app (.const ``List.length _) _) lst =>
      return some (lst, idx)
    | .proj ``Array 0 arr =>  -- Array.size can be projected as .0
      return some (arr, idx)
    | _ => return none
  | _ => return none

/-- Extract array and index from a getElem! call -/
def extractGetElemInfo (e : Expr) : Option (Expr × Expr) :=
  -- getElem! takes: coll, idx, (implicit type args)...
  -- The first explicit arg is the collection, second is the index
  if e.isAppOf ``GetElem?.getElem! then
    let args := e.getAppArgs
    -- args[4] is collection, args[5] is index (after implicit type args)
    if args.size >= 6 then
      some (args[4]!, args[5]!)
    else
      none
  else
    none

/-- Create a hash for an expression (for use in HashSet) -/
def exprHash (e : Expr) : UInt64 := hash e

/-- Check if a getElem! call is guarded by a bounds check in context -/
def isGuardedGetElem (ctx : GuardContext) (e : Expr) : Bool :=
  match extractGetElemInfo e with
  | some (arr, idx) =>
    let key := (exprHash arr, exprHash idx)
    ctx.guardedIndices.contains key
  | none => false

/-- Add a bounds check to the guard context -/
def addBoundsGuard (ctx : GuardContext) (arr : Expr) (idx : Expr) : GuardContext :=
  let key := (exprHash arr, exprHash idx)
  { ctx with guardedIndices := ctx.guardedIndices.insert key }

/-- Extract bounds checks from an expression (e.g., from the left side of ∧) -/
partial def extractBoundsChecks (e : Expr) : MetaM (List (Expr × Expr)) := do
  match e with
  | .app (.app (.const ``And _) left) right =>
    let leftBounds ← extractBoundsChecks left
    let rightBounds ← extractBoundsChecks right
    return leftBounds ++ rightBounds
  | _ =>
    match ← isBoundsCheck e with
    | some (arr, idx) => return [(arr, idx)]
    | none => return []

/-- Helper to collect partial function calls for a given function name -/
def collectPartialCalls (e : Expr) (ctx : GuardContext) : Array (Name × Expr) :=
  partialFunctions.foldl (init := #[]) fun acc fnName =>
    if e.isAppOf fnName then
      -- Check if this call is guarded
      let isGuarded := fnName == ``GetElem?.getElem! && isGuardedGetElem ctx e
      if !isGuarded && e.getAppNumArgs >= 1 then
        acc.push (fnName, e)
      else
        acc
    else
      acc

/-- Extract all applications of partial functions in an expression, respecting guards -/
partial def findPartialFunctionCalls (e : Expr) : MetaM (Array (Name × Expr)) := do
  let rec visit (e : Expr) (ctx : GuardContext) : MetaM (Array (Name × Expr)) := do
    -- Check if this is a call to any partial function
    let directCalls := collectPartialCalls e ctx

    -- Recursively visit all subexpressions, updating context as needed
    let subCalls ← match e with
    | .app (.app (.const ``And _) left) right =>
      -- For conjunctions, bounds checks on the left guard the right side
      let leftBounds ← extractBoundsChecks left
      let newCtx := leftBounds.foldl (fun acc (arr, idx) => addBoundsGuard acc arr idx) ctx

      let leftCalls ← visit left ctx
      let rightCalls ← visit right newCtx
      pure (leftCalls ++ rightCalls)

    | .app (.app (.const ``Exists _) _) (.lam _ ty body _) =>
      -- For existentials ∃ i : T, P i, the body may contain bounds checks
      -- We need to handle patterns like ∃ i, i < a.size ∧ ...
      Meta.withLocalDeclD `x ty fun x => do
        let bodyInst := body.instantiate1 x
        -- Check if body is i < a.size ∧ ...
        match bodyInst with
        | .app (.app (.const ``And _) boundsCheck) innerBody =>
          match ← isBoundsCheck boundsCheck with
          | some (arr, idx) =>
            -- Add this guard to context for the inner body
            let newCtx := addBoundsGuard ctx arr idx
            let boundsCalls ← visit boundsCheck ctx
            let innerCalls ← visit innerBody newCtx
            pure (boundsCalls ++ innerCalls)
          | none =>
            visit bodyInst ctx
        | _ =>
          visit bodyInst ctx

    | .forallE _ d body _ =>
      -- For implications/foralls like (i < a.size) → P i
      -- Check if domain is a bounds check
      match ← isBoundsCheck d with
      | some (arr, idx) =>
        -- Add this guard to context for the body
        let newCtx := addBoundsGuard ctx arr idx
        let dCalls ← visit d ctx
        let bCalls ← visit body newCtx
        pure (dCalls ++ bCalls)
      | none =>
        let dCalls ← visit d ctx
        let bCalls ← visit body ctx
        pure (dCalls ++ bCalls)

    | .app f a =>
      let fCalls ← visit f ctx
      let aCalls ← visit a ctx
      pure (fCalls ++ aCalls)

    | .lam _ _ b _ =>
      visit b ctx

    | .letE _ t v b _ =>
      let tCalls ← visit t ctx
      let vCalls ← visit v ctx
      let bCalls ← visit b ctx
      pure (tCalls ++ vCalls ++ bCalls)

    | .mdata _ e' =>
      visit e' ctx

    | .proj _ _ e' =>
      visit e' ctx

    | _ => pure #[]

    return directCalls ++ subCalls

  visit e {}

/-- Maximum depth for unfolding function definitions -/
def maxUnfoldDepth : Nat := 3

/-- Collect all constants (function names) used in an expression -/
partial def collectConstants (e : Expr) : Array Name :=
  let rec visit (e : Expr) (acc : Array Name) : Array Name :=
    let acc := if let .const name _ := e then acc.push name else acc
    match e with
    | .app f a => visit a (visit f acc)
    | .lam _ _ b _ => visit b acc
    | .forallE _ d b _ => visit b (visit d acc)
    | .letE _ t v b _ => visit b (visit v (visit t acc))
    | .mdata _ e' => visit e' acc
    | .proj _ _ e' => visit e' acc
    | _ => acc
  visit e #[]

/-- Unfold function definitions recursively to check their bodies -/
partial def unfoldAndCheck (e : Expr) (depth : Nat := 0) (visited : Std.HashSet Name := {}) : MetaM (Array (Name × Expr)) := do
  if depth >= maxUnfoldDepth then
    return #[]

  let mut allCalls := #[]

  -- First check the current expression
  let directCalls ← findPartialFunctionCalls e
  allCalls := allCalls ++ directCalls

  -- Then collect all constants and try to unfold them
  let constants := collectConstants e

  for constName in constants do
    -- Skip if we've already visited this function
    if visited.contains constName then
      continue

    -- Try to get the function's definition
    try
      let constInfo ← getConstInfo constName
      match constInfo with
      | .defnInfo info =>
        -- We found a function definition, check its body recursively
        let newVisited := visited.insert constName
        let bodyCalls ← unfoldAndCheck info.value (depth + 1) newVisited
        allCalls := allCalls ++ bodyCalls
      | _ => pure ()  -- Not a definition, skip
    catch _ =>
      pure ()  -- Couldn't get definition, skip

  return allCalls

/-- Check if an expression contains unsafe calls to partial functions and report them -/
def checkGetLastSafety (e : Expr) : MetaM Unit := do
  -- First check for Float usage
  let hasFloat ← containsFloatType e
  if hasFloat then
    throwError "\
      [Quickcheck Float Warning]\
      \nDetected Float type in proposition.\
      \n\
      \nFloating-point numbers are problematic for formal verification:\
      \n  • Precision issues: 0.1 + 0.2 ≠ 0.3\
      \n  • Rounding errors accumulate in calculations\
      \n  • Non-associative: (a + b) + c ≠ a + (b + c)\
      \n  • Special values: NaN, Infinity behavior\
      \n\
      \nRecommendations:\
      \n  1. Use Rat (rational numbers) instead for exact arithmetic\
      \n  2. Use Int or Nat if fractional parts aren't needed\
      \n  3. Define a custom fixed-point type for controlled precision\
      \n\
      \nIf you must use Float, ensure you have defined:\
      \n  • instance : Repr Float\
      \n  • instance : Quickcheck.Shrinkable Float\
      \n  • instance : Quickcheck.Arbitrary Float\
      \n\
      \nSee Test/verina/float_analysis.lean for an example."

  -- Then check for partial function calls
  let calls ← unfoldAndCheck e

  if calls.isEmpty then
    return ()

  -- Conservative approach: report ALL partial function uses (deduplicated)
  let mut fnSet : Std.HashSet Name := {}

  for (fnName, _) in calls do
    fnSet := fnSet.insert fnName

  if !fnSet.isEmpty then
    let mut errors := #[]
    for fnName in fnSet.toArray do
      let safeName := match fnName with
        | ``List.getLast! => "List.getLast?"
        | ``List.head! => "List.head?"
        | ``List.tail! => "List.tail?"
        | ``GetElem?.getElem! => "getElem? or get?"
        | _ => "safe alternative (?)"
      errors := errors.push s!"Partial function `{fnName}` can panic.\nSafe alternative: {safeName}"

    let errorMsg := String.intercalate "\n\n" errors.toList
    throwError errorMsg

end Quickcheck.SafeGuard
