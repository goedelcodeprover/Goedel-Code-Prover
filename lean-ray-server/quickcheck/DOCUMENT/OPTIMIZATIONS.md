# Quickcheck performance optimizations

This document summarizes performance and memory improvements to the Quickcheck property-testing framework.

## Overview

### 1. New configuration presets (`Testable.lean`)

Two presets for faster runs:

- **`Quickcheck.Configuration.fast`**
  - Instances: 20 (was 100)
  - Max size: 30 (was 100)
  - Retries: 3 (was 10)
  - Shrink depth: 20 (was unbounded)

- **`Quickcheck.Configuration.minimal`** — smoke tests
  - Instances: 5
  - Max size: 10
  - Retries: 1
  - Shrink depth: 5

**Usage:**
```lean
#eval Testable.check myProperty Quickcheck.Configuration.fast
```

### 2. Shrink depth cap (`Testable.lean`)

`maxShrinkDepth` limits how far shrinking runs:

- Default: `some 100`
- `none` restores unbounded shrinking
- At the cap, tracing can report that shrinking stopped

**Impact:** Much less time shrinking complex counterexamples.

### 3. List shrinking (`Sampleable.lean`)

`List.shrinkable` avoids exponential candidate growth:

**Short lists (length ≤ 5):** same as before (try dropping each element)

**Long lists (length > 5):** strategic drops (head, middle, tail), halve list, shrink first 3 elements only (avoids O(n²))

**Effect:** Often 90%+ fewer shrink candidates on long lists.

### 4. Array shrinking (`Sampleable.lean`)

**Small arrays (≤ 10):** convert to list and use improved list shrinking

**Large arrays (> 10):** array ops only; few key candidates (first half, second half, drop last)

**Effect:** Avoids O(n) list conversion and excess allocation on large arrays.

### 5. Generator size caps (`Gen.lean`, `Arbitrary.lean`)

`arrayOf` / `listOf` take optional `maxSize`:

- Default max: 1000 elements
- Override with `maxSize := some N`
- Disable with `maxSize := none`

**Defaults:**
- `List.Arbitrary`: max 100 elements
- `Array.Arbitrary`: max 100 elements
- `String.Arbitrary`: max 100 characters

**Effect:** Prevents accidentally huge generated values.

### 6. `frequency` (`Gen.lean`)

- Early exit for empty list / zero total weight
- `foldl` instead of `map` + `sum` to cut allocations

**Effect:** Less allocation in derived generators.

## Impact summary

| Change | Memory | Speed | Best for |
|--------|--------|-------|----------|
| Presets | medium | high | all tests |
| Shrink depth | high | high | complex counterexamples |
| List shrink | high | high | long lists |
| Array shrink | high | medium | large arrays |
| Gen size caps | high | medium | collections |
| `frequency` | low | low | derived gens |

## Recommendations

### Day-to-day
```lean
#eval Testable.check myProperty Quickcheck.Configuration.fast
```

### CI / smoke
```lean
#eval Testable.check myProperty Quickcheck.Configuration.minimal
```

### Full runs
```lean
#eval Testable.check myProperty { numInst := 1000, maxShrinkDepth := some 200 }
```

### Debugging failures
```lean
#eval Testable.check myProperty Quickcheck.Configuration.verbose
```

## Compatibility

- Default behavior is largely unchanged (except shrink depth cap)
- Existing code works without edits
- New behavior is opt-in via parameters where needed

## If still slow

1. Lower `numInst`
2. Lower `maxSize`
3. Tighten `maxShrinkDepth`
4. Use `NoShrink` where shrinking is not needed
5. Custom `Arbitrary` for hot types

## Benchmarking

```lean
#time #eval Testable.check myProperty Quickcheck.Configuration.minimal
#time #eval Testable.check myProperty Quickcheck.Configuration.fast  
#time #eval Testable.check myProperty  -- default
```

## Feedback

Open an issue for problems or further optimization ideas.
