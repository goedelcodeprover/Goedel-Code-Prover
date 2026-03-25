# Safe normalization user guide

## Overview

Safe normalization is a preprocessing layer inspired by Aesop’s safe rules. It simplifies propositions before quickcheck runs, reducing cost.

## Ideas (Aesop-style)

- **Safe rule:** If a transformation always preserves equivalence and never needs backtracking, apply it eagerly.
- **Normalization:** Turn the goal into a simpler equivalent form before testing.
- **Performance:** Remove expensive patterns to shorten test time.

## When you need it

### 1. Nested universal quantifiers

**Problem:**
```lean
def postcondition (a : Array Int) (result: Int) :=
  ∃ i j, i < a.size ∧ j < a.size ∧ 
    P i ∧ Q j ∧ 
    result = f i j ∧
    (∀ k, k < i → ¬P k) ∧  -- 🔴 O(i)
    (∀ k, k < j → ¬Q k)    -- 🔴 O(j)
```

**Why slow:** For each `(i,j)`, up to O(i×j) checks; size 10 can mean ~10⁴ checks per test; nested quantifiers blow up search.

**Mitigations:**

**A. Simplify the spec (recommended)**
```lean
-- If you only need existence, drop the “first witness” ∀s
def postcondition_simplified (a : Array Int) (result: Int) :=
  ∃ i j, i < a.size ∧ j < a.size ∧ 
    P i ∧ Q j ∧ 
    result = f i j
```

**B. Safe normalization (automatic for small bounds)**
```lean
-- ∀ k < 5 → P k  ===>  P 0 ∧ P 1 ∧ … ∧ P 4
theorem spec (a: Array Int) :
    postcondition a (impl a) := by
    quickcheck (config := { 
      enableSafeNorm := true,
      safeNormUnrollBound := 10
    })
```

### 2. Redundant bounds

**Problem:**
```lean
∃ i, i < a.size ∧ P (a[i]!) ∧ i < a.size ∧ Q i
```

**Safe norm can drop duplicates:**
```lean
∃ i, i < a.size ∧ P (a[i]!) ∧ Q i
```

## Configuration

```lean
structure Configuration where
  -- ... other fields ...
  
  /-- Enable safe-normalization preprocessing -/
  enableSafeNorm : Bool := false
  
  /-- Max bound for bounded-quantifier unfolding -/
  safeNormUnrollBound : Nat := 20
```

**Examples:**
```lean
theorem my_spec : spec_holds := by
  quickcheck (config := { enableSafeNorm := true })

theorem my_spec : spec_holds := by
  quickcheck (config := { 
    enableSafeNorm := true,
    safeNormUnrollBound := 5
  })

theorem my_spec : spec_holds := by
  quickcheck (config := { 
    enableSafeNorm := true,
    safeNormUnrollBound := 10,
    onlyDecidable := true,
    numInst := 20
  })
```

## Built-in safe rules

### 1. `simplifyBoundedForall` (priority 100)

**Pattern:**
```lean
∀ k : Nat, k < n → P k
```

**When n ≤ safeNormUnrollBound:**
```lean
P 0 ∧ P 1 ∧ … ∧ P (n-1)
```

**Benefits:** Finite conjunction, often decidable, predictable cost after elaboration.

### 2. `eliminateRedundantBounds` (priority 80)

**Pattern:**
```lean
i < a.size ∧ … ∧ i < a.size
```
**→**
```lean
i < a.size ∧ …
```

### 3. `simplifyFirstWitness` (priority 90)

**Detects:**
```lean
∃ i, … ∧ (∀ k < i, ¬P k)
```
**Action:** Suggest weakening the spec (drop “first witness” if you do not need it).

## Case study: `verina_basic_24`

### Original (timeout)

```lean
@[reducible, simp]
def ccc (a : Array Int) (result: Int) (h_precond : aaa (a)) :=
  ∃ i j, i < a.size ∧ j < a.size ∧ isEven (a[i]!) ∧ isOdd (a[j]!) ∧
    result = a[i]! - a[j]! ∧
    (∀ k, k < i → isOdd (a[k]!)) ∧
    (∀ k, k < j → isEven (a[k]!))

theorem spec (a: Array Int) (h_precond : aaa (a)) :
    ccc (a) (bbbb (a) h_precond) h_precond := by
    quickcheck  -- ⏱️ ~537s or timeout
```

### Fix 1: Simpler spec (best)

```lean
@[reducible, simp]
def ccc_simplified (a : Array Int) (result: Int) (h_precond : aaa (a)) :=
  ∃ i j, i < a.size ∧ j < a.size ∧ 
    isEven (a[i]!) ∧ isOdd (a[j]!) ∧
    result = a[i]! - a[j]!

theorem spec (a: Array Int) (h_precond : aaa (a)) :
    ccc_simplified (a) (bbbb (a) h_precond) h_precond := by
    quickcheck  -- ⏱️ expect < 10s
```

### Fix 2: Safe normalization

```lean
theorem spec (a: Array Int) (h_precond : aaa (a)) :
    ccc (a) (bbbb (a) h_precond) h_precond := by
    quickcheck (config := { 
      enableSafeNorm := true,
      safeNormUnrollBound := 10,
      maxSize := 20
    })
```

### Fix 3: `decidableBound`

```lean
theorem spec (a: Array Int) (h_precond : aaa (a)) :
    ccc (a) (bbbb (a) h_precond) h_precond := by
    quickcheck (config := { 
      onlyDecidable := true,
      decidableBound := some 20
    })
```

## Soundness

### Why it is safe

1. **Equivalence** — truth is preserved (`∀ k < 3 → P k` ≡ `P 0 ∧ P 1 ∧ P 2`)
2. **No false positives** — if the original holds, so does the normalized goal; counterexamples transfer back
3. **Deterministic** — no search; same input ⇒ same output
4. **Auditable** — `set_option trace.quickcheck.safenorm true`

### Not guaranteed

1. **Complete** — not every pattern simplifies
2. **Always faster** — unfolding can grow the goal
3. **Finds bugs** — it speeds testing; it does not guarantee finding counterexamples

## vs Aesop

| | Aesop safe rules | Quickcheck safe norm |
|--|------------------|----------------------|
| Role | Proof search | Pre-test simplification |
| Backtracking | Never | N/A (one-way) |
| User rules | ✅ | 🔄 planned |
| Priority | ✅ | ✅ |
| Correctness | Preserves provability | Preserves truth |

## Best practices

### 1. Start with a clear spec

```lean
-- ❌ Avoid if you only need existence
def spec := ∃ i, P i ∧ (∀ k < i, ¬P k)

-- ✅ Prefer
def spec := ∃ i, P i
```

### 2. Turn optimizations on gradually

```lean
theorem test1 : spec := by quickcheck
theorem test2 : spec := by 
  quickcheck (config := { enableSafeNorm := true })
theorem test3 : spec := by 
  quickcheck (config := { 
    enableSafeNorm := true,
    safeNormUnrollBound := 5
  })
```

### 3. Trace

```lean
set_option trace.quickcheck.safenorm true
theorem test : spec := by 
  quickcheck (config := { enableSafeNorm := true })
```

### 4. Combine strategies

```lean
quickcheck (config := { 
  enableSafeNorm := true,
  onlyDecidable := true,
  decidableBound := some 10,
  numInst := 50,
  maxSize := 30
})
```

## Troubleshooting

### No speedup

- Bound larger than `safeNormUnrollBound`
- Pattern not covered
- Bottleneck elsewhere (e.g. `Sampleable`)

```lean
set_option trace.quickcheck.safenorm true
-- Or raise bound carefully:
quickcheck (config := { safeNormUnrollBound := 30 })
```

### Higher memory

Large unfolds grow the goal — lower `safeNormUnrollBound` or `maxSize`.

### Still times out

1. Simplify the spec
2. Use `quickcheck_all` to split
3. Stronger preconditions
4. Faster preset

```lean
theorem test : complex_spec := by 
  dsimp [def1, def2, def3]
  quickcheck_all (config := { 
    enableSafeNorm := true,
    numInst := 20
  })
```

## References

- [Aesop](https://github.com/leanprover-community/aesop)
- [Quickcheck optimizations](OPTIMIZATIONS.md)
- [Testable instances](README.md)

## Roadmap

- [ ] User-defined safe rules
- [ ] More built-ins (arrays, strings, …)
- [ ] Auto-suggestions for slow patterns
- [ ] `simp` integration
- [ ] Profiling tools
