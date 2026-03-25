# Or, And, and SafeNorm

## Question

If `preprocess` does not split Or (for test completeness), how can SafeNorm simplify **inside** Or?

## Answer

SafeNorm runs **after** `preprocess` and still sees the full goal, including Or.

## Pipeline

```
quickcheck tactic:

1. preprocess
   ├─ split And → multiple goals (all must pass)
   ├─ split match → multiple goals (all must pass)
   └─ do not split Or (orTestable handles it)

2. revert
   └─ locals become universal quantifiers

3. SafeNorm (if enableSafeNorm = true)
   ├─ works on the whole expression
   ├─ can recurse under Or
   └─ applies simplification rules

4. quickcheck
   └─ orTestable tries all Or branches
```

## Rationale

### And

```lean
theorem test : A ∧ B := by
  quickcheck
```

1. `preprocess` → two goals
2. quickcheck on each
3. Both must pass — matches “all conjuncts true”

### Or

```lean
theorem test : A ∨ B := by
  quickcheck
```

1. `preprocess` does **not** split
2. Goal stays `A ∨ B`
3. `orTestable`: try A; on failure try B; fail only if both fail

Only one disjunct needs to hold; splitting to the first branch only would be wrong.

### Where SafeNorm sits

SafeNorm runs after preprocess, before testing:

```lean
theorem test : (∀ k < 3, P k) ∨ (x = 0) := by
  quickcheck (config := { enableSafeNorm := true })
```

1. Or not split by preprocess
2. SafeNorm sees `(∀ k < 3, P k) ∨ (x = 0)`
3. Can unfold `∀ k < 3` → `(P 0 ∧ P 1 ∧ P 2) ∨ (x = 0)`
4. `orTestable` tests both sides

## Deeper Or rules

```lean
import Quickcheck.SafeNormOr

-- Extra rules:
-- 1. normalizeOrBranchesRule — recurse into both sides
-- 2. simplifyTrivialOrRule — False ∨ P, P ∨ True, etc.

theorem test : complex_or_expression := by
  quickcheck (config := { enableSafeNorm := true })
```

## Examples

### 1. Or completeness

```lean
theorem test : (x = 999) ∨ (x < 100) := by
  quickcheck
```

**Wrong (first branch only):** test `x = 999` → almost always fails.

**Correct:** `orTestable` tries `x = 999`, then `x < 100` → can succeed.

### 2. SafeNorm + Or

```lean
theorem test : (∀ k < 3, k < x) ∨ (x = 0) := by
  quickcheck (config := { enableSafeNorm := true })
```

SafeNorm: `(0 < x ∧ 1 < x ∧ 2 < x) ∨ (x = 0)`  
Quickcheck: try left, then right.

### 3. Trivial Or

```lean
theorem test : False ∨ (x < 100) := by
  quickcheck (config := { enableSafeNorm := true })
```

With SafeNormOr, `simplifyTrivialOrRule` can reduce to `x < 100`.

## Summary

| Structure | preprocess | SafeNorm | quickcheck | Outcome |
|-----------|------------|----------|------------|---------|
| `A ∧ B` | 2 goals | per goal | per goal | all pass |
| `A ∨ B` | **no split** | can go inside | all branches | at least one passes |
| `match` | N goals | per goal | per goal | all pass |

## Practices

1. Default: use `quickcheck` — And/Or/match handled automatically
2. Deeper Or: import `Quickcheck.SafeNormOr`
3. Debug: `trace.quickcheck.safenorm` and `trace.quickcheck.split`

## Related

- `PREPROCESS_README.md`
- `test_multiple_splits.lean`
- `test_safenorm_or.lean`
- `Quickcheck/SafeNormOr.lean`
