/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/

import Lean.Elab.Tactic.Config

namespace Quickcheck

/-- Preset configuration modes for quickcheck. -/
inductive Setting where
  | Adaptive
  | Extensive
  | Normal
  | Fast
  | Minimal
  | None
  deriving Inhabited, BEq, Repr

open Lean in
instance : ToExpr Setting where
  toTypeExpr := mkConst `Setting
  toExpr s := match s with
    | Setting.Adaptive => mkConst ``Setting.Adaptive
    | Setting.Extensive => mkConst ``Setting.Extensive
    | Setting.Normal => mkConst ``Setting.Normal
    | Setting.Fast => mkConst ``Setting.Fast
    | Setting.Minimal => mkConst ``Setting.Minimal
    | Setting.None => mkConst ``Setting.None

/-- Configuration for testing a property. -/
structure Configuration where
  /--
  How many test instances to generate.
  -/
  numInst : Nat := 100
  /--
  The maximum size of the values to generate.
  -/
  maxSize : Nat := 100
  numRetries : Nat := 10
  /--
  Maximum depth of shrinking to prevent excessive computation.
  Set to `none` for unlimited shrinking.
  -/
  maxShrinkDepth : Option Nat := some 100
  /--
  Enable tracing of values that didn't fulfill preconditions and were thus discarded.
  -/
  traceDiscarded : Bool := false
  /--
  Enable tracing of values that fulfilled the property and were thus discarded.
  -/
  traceSuccesses : Bool := false
  /--
  Enable basic tracing of shrinking.
  -/
  traceShrink : Bool := false
  /--
  Enable tracing of all attempted values during shrinking.
  -/
  traceShrinkCandidates : Bool := false
  /--
  Hard code the seed to use for the RNG
  -/
  randomSeed : Option Nat := none
  /--
  Disable output.
  -/
  quiet : Bool := false
  /--
  Enable SafeGuard to detect partial functions like `getLast!`, `head!`, etc.
  When enabled, quickcheck will check for unsafe partial function usage before testing.
  -/
  enableSafeGuard : Bool := false
  /--
  Only use Decidable instances for testing.
  When enabled, quickcheck will fail if the proposition is not Decidable,
  rather than falling back to random sampling with Testable instances.
  This ensures O(1) decision time per test case.
  -/
  onlyDecidable : Bool := false
  /--
  Bound for unbounded forall quantifiers when using onlyDecidable mode.
  When set to `some n`, `∀ x : Int` is tested as `∀ x : Int, -n ≤ x ∧ x ≤ n → ...`
  and `∀ x : Nat` is tested as `∀ x : Nat, x ≤ n → ...`.
  This makes infinite quantifiers decidable by limiting the search space.
  -/
  decidableBound : Option Nat := none
  /--
  Enable safe normalization preprocessing before testing.
  When enabled, quickcheck applies safe rewrite rules to simplify the goal:
  - Simplifies nested quantifiers (∀ k < n → P k becomes P 0 ∧ ... ∧ P (n-1) for small n)
  - Eliminates redundant conditions
  - Transforms expensive patterns to decidable forms
  This is "safe" because it preserves semantic equivalence.
  Inspired by Aesop's safe rule mechanism.
  -/
  enableSafeNorm : Bool := true
  /--
  Maximum value for unrolling bounded quantifiers in safe normalization.
  For example, `∀ k < n → P k` with n ≤ safeNormUnrollBound will be expanded to
  `P 0 ∧ P 1 ∧ ... ∧ P (n-1)`, making it decidable and much faster to test.
  Set this based on available memory and performance requirements.
  -/
  safeNormUnrollBound : Nat := 20
  /--
  Number of parallel workers for concurrent test execution.
  Set to 1 for sequential execution (default).
  Set to a number > 1 to enable parallel testing.
  Each worker uses a different random seed for independent test generation.
  Experimental: it may cause memory leaks if not used carefully.
  -/
  numWorkers : Nat := 1
  /--
  Timeout for each worker in seconds.
  If a worker exceeds this time, it will be killed and treated as "gave up".
  Set to `none` for no timeout.
  timeout in seconds.
  -/
  workerTimeout : Option Nat := some 5
  /--
  Setting for the configuration.
  -/
  setting : Setting := Setting.None
  deriving Inhabited

open Lean in
instance : ToExpr Configuration where
  toTypeExpr := mkConst `Configuration
  toExpr cfg := mkAppN (mkConst ``Configuration.mk)
    #[toExpr cfg.numInst, toExpr cfg.maxSize, toExpr cfg.numRetries, toExpr cfg.maxShrinkDepth,
      toExpr cfg.traceDiscarded, toExpr cfg.traceSuccesses, toExpr cfg.traceShrink,
      toExpr cfg.traceShrinkCandidates, toExpr cfg.randomSeed, toExpr cfg.quiet,
      toExpr cfg.enableSafeGuard, toExpr cfg.onlyDecidable, toExpr cfg.decidableBound,
      toExpr cfg.enableSafeNorm, toExpr cfg.safeNormUnrollBound, toExpr cfg.numWorkers,
      toExpr cfg.workerTimeout, toExpr cfg.setting]

/--
Allow elaboration of `Configuration` arguments to tactics.
-/
declare_config_elab elabConfig Configuration

namespace Configuration

/-- A configuration with all the trace options enabled, useful for debugging. -/
def verbose : Configuration where
  traceDiscarded := true
  traceSuccesses := true
  traceShrink := true
  traceShrinkCandidates := true
  setting : Setting := Setting.None

/-- A fast configuration with reduced test instances and smaller sizes for better performance. -/
def fast : Configuration where
  numInst := 20
  maxSize := 30
  numRetries := 3
  maxShrinkDepth := some 20
  setting : Setting := Setting.Fast

/-- A minimal configuration for smoke testing. -/
def minimal : Configuration where
  numInst := 5
  maxSize := 10
  numRetries := 1
  maxShrinkDepth := some 5
  setting : Setting := Setting.Minimal

/-- A normal/standard configuration for regular testing. This is a balanced default. -/
def normal : Configuration where
  numInst := 100
  maxSize := 100
  numRetries := 10
  maxShrinkDepth := some 100
  setting : Setting := Setting.Normal

/-- An extensive configuration for thorough testing with maximum test instances and larger sizes. -/
def extensive : Configuration where
  numInst := 1000
  maxSize := 100
  numRetries := 20
  maxShrinkDepth := some 200
  setting : Setting := Setting.Extensive

/-- An adaptive configuration that dynamically reduces maxSize when timeouts occur. -/
def adaptive : Configuration where
  numInst := 1000
  maxSize := 100
  numRetries := 20
  maxShrinkDepth := some 200
  setting : Setting := Setting.Adaptive

end Configuration

namespace Adaptive

/-!
# Adaptive Testing Strategy

This module provides adaptive maxSize reduction during testing.
When timeouts occur, the adaptive strategy automatically reduces maxSize
and retries, allowing tests to make progress even with expensive properties.

## Main Components

- `AdaptiveState`: Tracks current maxSize and number of reductions
- `AdaptiveDecision`: Decision on whether to retry or give up after timeout
- `makeAdaptiveDecision`: Core decision logic (runs in MetaM for tracing)
- `reportAdaptiveStats`: Reports final statistics

## Usage

```lean
-- Enable adaptive tracing
set_option trace.quickcheck.adaptive true

-- The adaptive strategy activates automatically when using Configuration.adaptive
#test property (Configuration.adaptive)
```
-/

/-! ## Configuration Check -/

/-- Check if a configuration matches the adaptive preset.
    This allows detecting adaptive mode even when other fields are customized. -/
def isAdaptiveConfig (cfg : Configuration) : Bool :=
  cfg.setting == Setting.Adaptive

/-! ## Adaptive State -/

/-- State for adaptive testing strategy -/
structure AdaptiveState where
  /-- Current maximum size for test generation -/
  currentMaxSize : Nat
  /-- Number of times maxSize has been reduced -/
  reductions : Nat
  deriving Inhabited, Repr

/-- Initial adaptive state from configuration -/
def AdaptiveState.initial (cfg : Configuration) : AdaptiveState :=
  { currentMaxSize := cfg.maxSize, reductions := 0 }

/-! ## Adaptive Decision -/

/-- Decision on how to proceed after a timeout -/
inductive AdaptiveDecision where
  /-- Retry with a new (reduced) maxSize -/
  | retry (newMaxSize : Nat)
  /-- Give up (maxSize too small or not in adaptive mode) -/
  | giveUp
  deriving Inhabited, Repr

/-! ## Core Adaptive Logic (in MetaM for tracing) -/

/-- Make adaptive decision based on timeout.
    Runs in MetaM so we can use trace[quickcheck.adaptive].

    Strategy:
    - If in adaptive mode and maxSize > 10: reduce maxSize by half and retry
    - Otherwise: give up
-/
def makeAdaptiveDecision (state : AdaptiveState) (cfg : Configuration) :
    Lean.MetaM (AdaptiveDecision × AdaptiveState) := do
  if isAdaptiveConfig cfg && state.currentMaxSize > 10 then
    let newMaxSize := state.currentMaxSize / 2
    let newState := {
      currentMaxSize := newMaxSize,
      reductions := state.reductions + 1
    }
    -- Use standard Lean trace
    trace[quickcheck.adaptive] m!"Reduced maxSize from {state.currentMaxSize} to {newMaxSize} (reduction #{newState.reductions}) since it exceeded the timeout"
    return (.retry newMaxSize, newState)
  else
    return (.giveUp, state)

/-- Report adaptive statistics at the end of testing.
    Runs in MetaM so we can use trace[quickcheck.adaptive]. -/
def reportAdaptiveStats (state : AdaptiveState) (cfg : Configuration) :
    Lean.MetaM Unit := do
  if isAdaptiveConfig cfg && state.reductions > 0 then
    trace[quickcheck.adaptive] m!"Total maxSize reductions: {state.reductions}"

/-! ## IO-friendly adaptive helpers -/

/-- Make adaptive decision in IO context (simplified version without MetaM tracing).
    Returns the new state and whether to retry. -/
def makeAdaptiveDecisionIO (state : AdaptiveState) (cfg : Configuration) :
    IO (Bool × AdaptiveState) := do
  if isAdaptiveConfig cfg && state.currentMaxSize > 10 then
    let newMaxSize := state.currentMaxSize / 2
    let newState := {
      currentMaxSize := newMaxSize,
      reductions := state.reductions + 1
    }
    if !cfg.quiet then
      IO.println s!"[Quickcheck] Adaptive: reduced maxSize from {state.currentMaxSize} to {newMaxSize} (reduction #{newState.reductions})"
    return (true, newState)
  else
    return (false, state)

/-- Report adaptive statistics in IO context. -/
def reportAdaptiveStatsIO (state : AdaptiveState) (cfg : Configuration) : IO Unit := do
  if isAdaptiveConfig cfg && state.reductions > 0 then
    if !cfg.quiet then
      IO.println s!"[Quickcheck] Adaptive: total maxSize reductions: {state.reductions}"

end Adaptive

end Quickcheck
