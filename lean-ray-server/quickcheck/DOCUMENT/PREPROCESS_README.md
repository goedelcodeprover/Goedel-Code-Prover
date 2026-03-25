# Preprocess tactic

## Overview

The `preprocess` tactic splits goals before `quickcheck` runs. It handles:
- `match` expressions
- conjunction (`∧`)
- disjunction (`∨`)

## Behavior

### 1. And (`∧`) — every conjunct must be proved

For `A ∧ B`, `preprocess` uses `constructor` to produce two goals:
- Goal 1: prove `A`
- Goal 2: prove `B`

**Both must succeed**, matching quickcheck semantics: all conditions must hold.

```lean
theorem test_and : (x = 0) ∧ (y = 0) := by
  preprocess
  -- Now 2 goals:
  -- 1. ⊢ x = 0
  -- 2. ⊢ y = 0
  all_goals sorry
```

### 2. Or (`∨`) — do not split; let quickcheck handle it

For `A ∨ B`, `preprocess` **does not split**.

**Why?** Quickcheck has `orTestable`, which:
1. Tests `A` first
2. If `A` succeeds, succeeds overall
3. If `A` fails, tests `B`
4. Fails only if both fail

That **explores both sides**. If `preprocess` kept only the first branch, a valid second branch could be missed.

```lean
theorem test_or : (x = 0) ∨ (x = 1) := by
  preprocess
  -- Goal unchanged:
  -- ⊢ (x = 0) ∨ (x = 1)
  quickcheck  -- quickcheck tries both branches
```

### 3. `match` — one goal per arm

For `match`, `preprocess` uses `split` to create one goal per pattern.

```lean
def f (x : Nat) : Nat :=
  match x with
  | 0 => 0
  | _ => 1

theorem test_match : f 0 = 0 := by
  unfold f
  preprocess
  -- 2 goals (one per match arm)
  all_goals sorry
```

## Recursion

`preprocess` recurses through nested structure until nothing splits further (up to 20 iterations).

### Example: And + Or

```lean
theorem test_complex : (x = 0 ∨ x = 1) ∧ (y = 0 ∨ y = 1) := by
  preprocess
  -- Steps:
  -- 1. And splits into 2 goals
  -- 2. Or inside each goal is not split
  -- Final: 2 goals:
  -- 1. ⊢ x = 0 ∨ x = 1
  -- 2. ⊢ y = 0 ∨ y = 1
  all_goals quickcheck  -- each Or tested by orTestable
```

## When to use

### 1. Manual split timing

```lean
theorem my_theorem : complex_property := by
  unfold some_definition
  simp
  preprocess
  all_goals quickcheck
```

### 2. Automatic with quickcheck

`quickcheck` calls `preprocess` internally, so you usually do not need to call it yourself:

```lean
theorem my_theorem : complex_property := by
  quickcheck  -- preprocess runs inside
```

## Why Or is not split

Consider:

```lean
theorem test : (x = 999) ∨ (x < 100) := by
  quickcheck
```

- If we only kept `x = 999`, quickcheck would likely find a counterexample
- Yet `x < 100` is easy to satisfy

By **not splitting Or**, `orTestable`:
1. Tries `x = 999` (may fail)
2. Then tries `x < 100` (may succeed)
3. Succeeds if either side can hold

That preserves completeness of testing across disjuncts.

## Debugging

Enable tracing:

```lean
set_option trace.quickcheck.split true in
theorem my_theorem : my_property := by
  preprocess
  sorry
```

Example output:
```
[quickcheck.split] [trySplit] Trying to split, current goals: 1
[quickcheck.split] [trySplit] Found And, using constructor
[quickcheck.split] [trySplit] ✓ And split successful! Split into 2 goals
[quickcheck.split] [preprocess] Iteration: split into 2 goals
[quickcheck.split] [preprocess] ✓ Final result: Split from 1 goal(s) into 2 goal(s)
```

Or does not appear in the trace because it is never split.

## Summary table

| Structure | preprocess | quickcheck | Effect |
|-----------|------------|------------|--------|
| `A ∧ B` | 2 goals | each goal tested | both must pass |
| `A ∨ B` | **not split** | try A, then B | at least one must pass |
| `match x` | N goals (arms) | each tested | all arms covered |

## SafeNorm and Or

### Concern

Because Or is not split, you might worry SafeNorm cannot simplify inside Or.

### Answer

**SafeNorm runs after `preprocess`** and still sees the full expression, including Or.

Order:
1. `preprocess` — splits And and match, **not Or**
2. `revert` — locals become universal quantifiers
3. **SafeNorm** — works on the whole goal, can recurse under Or

### Deeper Or normalization

For stronger Or handling, use `SafeNormOr`:

```lean
import Quickcheck.SafeNormOr

set_option trace.quickcheck.safenorm true in
theorem my_theorem : (complex_expr_1) ∨ (complex_expr_2) := by
  quickcheck (config := { enableSafeNorm := true })
```

`SafeNormOr` adds:
- `normalizeOrBranchesRule`: recurse into both sides of Or
- `simplifyTrivialOrRule`: e.g. `False ∨ P` → `P`, `P ∨ True` → `True`
- `defaultRulesWithOr`: extended rule set

See `test_safenorm_or.lean` for examples.

## Test files

- `test_multiple_splits.lean` — basic preprocess (nested match, And+Or, Or completeness)
- `test_safenorm_or.lean` — SafeNorm with Or
