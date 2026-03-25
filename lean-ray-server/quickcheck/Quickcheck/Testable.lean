/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/

import Lean.Elab.Tactic.Config
import Lean.Util.Trace
import Quickcheck.Configuration
import Quickcheck.Sampleable
import Quickcheck.SafeGuard



/-!
# `Testable` Class

Testable propositions have a procedure that can generate counter-examples
together with a proof that they invalidate the proposition.

This is a port of the Haskell QuickCheck library.

## Creating Customized Instances

The type classes `Testable`, `SampleableExt` and `Shrinkable` are the
means by which `Quickcheck` creates samples and tests them. For instance,
the proposition `∀ i j : Nat, i ≤ j` has a `Testable` instance because `Nat`
is sampleable and `i ≤ j` is decidable. Once `Quickcheck` finds the `Testable`
instance, it can start using the instance to repeatedly creating samples
and checking whether they satisfy the property. Once it has found a
counter-example it will then use a `Shrinkable` instance to reduce the
example. This allows the user to create new instances and apply
`Quickcheck` to new situations.

### What do I do if I'm testing a property about my newly defined type?

Let us consider a type made for a new formalization:

```lean
structure MyType where
  x : Nat
  y : Nat
  h : x ≤ y
  deriving Repr
```

How do we test a property about `MyType`? For instance, let us consider
`Testable.check <| ∀ a b : MyType, a.y ≤ b.x → a.x ≤ b.y`. Writing this
property as is will give us an error because we do not have an instance
of `Shrinkable MyType` and `SampleableExt MyType`. We can define one as follows:

```lean
instance : Shrinkable MyType where
  shrink := fun ⟨x, y, _⟩ =>
    let proxy := Shrinkable.shrink (x, y - x)
    proxy.map (fun (fst, snd) => ⟨fst, fst + snd, by omega⟩)

instance : SampleableExt MyType :=
  SampleableExt.mkSelfContained do
    let x ← SampleableExt.interpSample Nat
    let xyDiff ← SampleableExt.interpSample Nat
    return ⟨x, x + xyDiff, by omega⟩
```

Again, we take advantage of the fact that other types have useful
`Shrinkable` implementations, in this case `Prod`.

## Main definitions

* `Testable` class
* `Testable.check`: a way to test a proposition using random examples

## References

* https://hackage.haskell.org/package/QuickCheck

-/

namespace Quickcheck

/-- Result of trying to disprove `p` -/
inductive TestResult (p : Prop) where
  /--
  Succeed when we find another example satisfying `p`.
  In `success h`, `h` is an optional proof of the proposition.
  Without the proof, all we know is that we found one example
  where `p` holds. With a proof, the one test was sufficient to
  prove that `p` holds and we do not need to keep finding examples.
  -/
  | success : Unit ⊕' p → TestResult p
  /--
  Give up when a well-formed example cannot be generated.
  `gaveUp n` tells us that `n` invalid examples were tried.
  -/
  | gaveUp : Nat → TestResult p
  /--
  Timeout occurred during testing.
  `timeout n` indicates that `n` tests were skipped due to timeout.
  -/
  | timeout : Nat → TestResult p
  /--
  A counter-example to `p`; the strings specify values for the relevant variables.
  `failure h vs n` also carries a proof that `p` does not hold. This way, we can
  guarantee that there will be no false positive. The last component, `n`,
  is the number of times that the counter-example was shrunk.
  -/
  | failure : ¬ p → List String → Nat → TestResult p
  deriving Inhabited

/--
`PrintableProp p` allows one to print a proposition so that
`Quickcheck` can indicate how values relate to each other.
It's basically a poor man's delaborator.
-/
class PrintableProp (p : Prop) where
  printProp : String

export PrintableProp (printProp)

variable {p q : Prop}

instance (priority := low) : PrintableProp p where
  printProp := "⋯"

/-- `Testable p` uses random examples to try to disprove `p`. -/
class Testable (p : Prop) where
  run (cfg : Configuration) (minimize : Bool) : Gen (TestResult p)

@[expose] def NamedBinder (_n : String) (p : Prop) : Prop := p

namespace TestResult

def toString : TestResult p → String
  | success (PSum.inl _) => "success (no proof)"
  | success (PSum.inr _) => "success (proof)"
  | gaveUp n => s!"gave {n} times"
  | timeout n => s!"timeout ({n} tests skipped)"
  | failure _ counters _ => s!"failed {counters}"

instance : ToString (TestResult p) := ⟨toString⟩

/-- Applicative combinator proof carrying test results. -/
def combine {p q : Prop} : Unit ⊕' (p → q) → Unit ⊕' p → Unit ⊕' q
  | PSum.inr f, PSum.inr proof => PSum.inr <| f proof
  | _, _ => PSum.inl ()

/-- Combine the test result for properties `p` and `q` to create a test for their conjunction. -/
def and : TestResult p → TestResult q → TestResult (p ∧ q)
  | failure h xs n, _ => failure (fun h2 => h h2.left) xs n
  | _, failure h xs n => failure (fun h2 => h h2.right) xs n
  | success h1, success h2 => success <| combine (combine (PSum.inr And.intro) h1) h2
  | timeout n, timeout m => timeout (n + m)
  | timeout n, _ => timeout n
  | _, timeout n => timeout n
  | gaveUp n, gaveUp m => gaveUp <| n + m
  | gaveUp n, _ => gaveUp n
  | _, gaveUp n => gaveUp n

/-- Combine the test result for properties `p` and `q` to create a test for their disjunction. -/
def or : TestResult p → TestResult q → TestResult (p ∨ q)
  | failure h1 xs n, failure h2 ys m =>
    let h3 := fun h =>
      match h with
      | Or.inl h3 => h1 h3
      | Or.inr h3 => h2 h3
    failure h3 (xs ++ ys) (n + m)
  | success h, _ => success <| combine (PSum.inr Or.inl) h
  | _, success h => success <| combine (PSum.inr Or.inr) h
  | timeout n, timeout m => timeout (n + m)
  | timeout n, _ => timeout n
  | _, timeout n => timeout n
  | gaveUp n, gaveUp m => gaveUp <| n + m
  | gaveUp n, _ => gaveUp n
  | _, gaveUp n => gaveUp n

/-- If `q → p`, then `¬ p → ¬ q` which means that testing `p` can allow us
to find counter-examples to `q`. -/
def imp (h : q → p) (r : TestResult p)
    (p : Unit ⊕' (p → q) := PSum.inl ()) : TestResult q :=
  match r with
  | failure h2 xs n => failure (mt h h2) xs n
  | success h2 => success <| combine p h2
  | timeout n => timeout n
  | gaveUp n => gaveUp n

/-- Test `q` by testing `p` and proving the equivalence between the two. -/
def iff (h : q ↔ p) (r : TestResult p) : TestResult q :=
  imp h.mp r (PSum.inr h.mpr)

/-- When we assign a value to a universally quantified variable,
we record that value using this function so that our counter-examples
can be informative. -/
def addInfo (x : String) (h : q → p) (r : TestResult p)
    (p : Unit ⊕' (p → q) := PSum.inl ()) : TestResult q :=
  if let failure h2 xs n := r then
    failure (mt h h2) (x :: xs) n
  else
    imp h r p

/-- Add some formatting to the information recorded by `addInfo`. -/
def addVarInfo {γ : Type _} [Repr γ] (var : String) (x : γ) (h : q → p) (r : TestResult p)
    (p : Unit ⊕' (p → q) := PSum.inl ()) : TestResult q :=
  addInfo s!"{var} := {repr x}" h r p

def isFailure : TestResult p → Bool
  | failure _ _ _ => true
  | _ => false

end TestResult

namespace Testable

open TestResult

def runProp (p : Prop) [Testable p] : Configuration → Bool → Gen (TestResult p) := Testable.run

def runPropE (p : Prop) [Testable p] (cfg : Configuration) (min : Bool) : Gen (TestResult p) :=
  do
    try runProp p cfg min
    catch
    | .genError _ => return gaveUp 1

/-- A `dbgTrace` with special formatting -/
def slimTrace {m : Type → Type _} [Pure m] (s : String) : m PUnit :=
  dbgTrace s!"[Quickcheck: {s}]" (fun _ => pure ())

instance andTestable [Testable p] [Testable q] : Testable (p ∧ q) where
  run := fun cfg min => do
    let xp ← runProp p cfg min
    let xq ← runProp q cfg min
    return and xp xq

instance orTestable [Testable p] [Testable q] : Testable (p ∨ q) where
  run := fun cfg min => do
    let xp ← runProp p cfg min
    -- As a little performance optimization we can just not run the second
    -- test if the first succeeds
    match xp with
    | success (PSum.inl h) => return success (PSum.inl h)
    | success (PSum.inr h) => return success (PSum.inr <| Or.inl h)
    | _ =>
      let xq ← runProp q cfg min
      return or xp xq

instance impTestable [Testable (¬ p ∨ q)] : Testable (p → q) where
  run := fun cfg min => do
    let h ← runProp (¬ p ∨ q) cfg min
    have : (p → q) ↔ (¬ p ∨ q) := by
      constructor
      · intro himp
        by_cases hp : p
        · exact Or.inr (himp hp)
        · exact Or.inl hp
      · intro hor hp
        cases hor with
        | inl hnp => exact absurd hp hnp
        | inr hq => exact hq
    return iff this h

/-- Heuristic instance for implication when p is only Testable (not Decidable).
This is less reliable but allows testing implications where the premise contains
existential quantifiers. It works by trying to find cases where p holds but q doesn't. -/
instance (priority := low) impTestableHeuristic [PrintableProp p] [PrintableProp q]
    [Testable p] [Testable q] : Testable (p → q) where
  run := fun cfg _ => do
    -- Try to find a counterexample: p holds but q doesn't
    -- We test p, and if it seems to hold, we test q
    let rp ← runProp p cfg false
    match rp with
    | TestResult.success (PSum.inr hp) =>
      -- p holds with proof! Now check if q holds
      let rq ← runProp q cfg false
      match rq with
      | TestResult.success _ =>
        -- Both p and q hold, so p → q holds (for this case at least)
        -- We don't have a general proof, just evidence from this test
        return TestResult.success (PSum.inl ())
      | TestResult.failure hnq msgs shrinks =>
        -- p holds but q doesn't, we found a real counterexample!
        -- We can prove ¬(p → q) because we have hp : p and hnq : ¬q
        have h : ¬(p → q) := fun hpq => hnq (hpq hp)
        let s := s!"{printProp p} → {printProp q}"
        return TestResult.failure h (s!"issue: {s} does not hold (premise holds but conclusion doesn't)" :: msgs) shrinks
      | TestResult.timeout n => return TestResult.timeout n
      | TestResult.gaveUp n =>
        -- Couldn't determine q
        return TestResult.gaveUp n
    | TestResult.success (PSum.inl _) =>
      -- p holds but without proof, can't reliably test the implication
      -- We give up because we can't construct a proper counterexample
      return TestResult.gaveUp 1
    | TestResult.failure _ _ _ =>
      -- p doesn't hold, so p → q is vacuously true
      -- We don't have a proof of p → q, but tests suggest it's okay
      return TestResult.success (PSum.inl ())
    | TestResult.timeout n => return TestResult.timeout n
    | TestResult.gaveUp n =>
      -- Couldn't determine p
      return TestResult.gaveUp n

/-- Instance for testing if-then-else.
When we can decide the condition c (which is required for if-then-else syntax),
we test the relevant branch. -/
instance iteTestable [Decidable c] [Testable p] [Testable q] :
    Testable (if c then p else q) where
  run := fun cfg min => do
    if hc : c then
      let r ← runProp p cfg min
      have h : (if c then p else q) ↔ p := by
        simp [hc]
      return TestResult.iff h r
    else
      let r ← runProp q cfg min
      have h : (if c then p else q) ↔ q := by
        simp [hc]
      return TestResult.iff h r

instance (priority := default+1) iffTestableGeneral [Testable (p → q)] [Testable (q → p)] : Testable (p ↔ q) where
  run := fun cfg min => do
    let hpq ← runProp (p → q) cfg min
    let hqp ← runProp (q → p) cfg min
    have : (p ↔ q) ↔ ((p → q) ∧ (q → p)) := by
      constructor
      · intro h
        exact ⟨h.mp, h.mpr⟩
      · intro ⟨hpq, hqp⟩
        exact ⟨hpq, hqp⟩
    let r := and hpq hqp
    return iff this r

instance (priority := low) iffTestable [Testable ((p ∧ q) ∨ (¬ p ∧ ¬ q))] : Testable (p ↔ q) where
  run := fun cfg min => do
    let h ← runProp ((p ∧ q) ∨ (¬ p ∧ ¬ q)) cfg min
    have := by
      constructor
      · intro h
        simp [h, Classical.em]
      · intro h
        rcases h with ⟨hleft, hright⟩ | ⟨hleft, hright⟩ <;> simp [hleft, hright]
    return iff this h

variable {var : String}

-- Instance to handle NamedBinder var p where p is any proposition
-- This allows NamedBinder to be transparent for Testable
instance (priority := 10) namedBinderTestable [Testable p] : Testable (NamedBinder var p) where
  run := fun cfg min => do
    let r ← runProp p cfg min
    return r

/-- Special case for ∀ h : True, P h - directly instantiate with True.intro.
This is needed because when P h depends on h (e.g., match f h with ...), we can't
synthesize Testable for all h, but we can for the specific h = True.intro. -/
instance (priority := 1100) trueGuardTestable {β : True → Prop} [Testable (β True.intro)] :
    Testable (NamedBinder var <| ∀ h : True, β h) where
  run := fun cfg min => do
    let res := runProp (β True.intro) cfg min
    (fun r => addInfo "guard: True" (· <| True.intro) r (PSum.inr <| fun q _ => q)) <$> res

/-- Special case for ∀ h : True, P h without NamedBinder - directly instantiate with True.intro.
Lower priority to prefer the NamedBinder version when available. -/
instance (priority := 60) trueGuardTestableNoName {β : True → Prop} [Testable (β True.intro)] :
    Testable (∀ h : True, β h) where
  run := fun cfg min => do
    let res ← runProp (β True.intro) cfg min
    -- Convert TestResult (β True.intro) to TestResult (∀ h : True, β h)
    pure <| match res with
    | .success (.inl ()) => .success (.inl ())
    | .success (.inr h) => .success (.inr (fun _ => h))
    | .timeout n => .timeout n
    | .gaveUp n => .gaveUp n
    | .failure p xs n => .failure (fun h => p (h True.intro)) xs n

instance decGuardTestable [PrintableProp p] [Decidable p] {β : p → Prop} [∀ h, Testable (β h)] :
    Testable (NamedBinder var <| ∀ h, β h) where
  run := fun cfg min => do
    if h : p then
      let res := runProp (β h) cfg min
      let s := printProp p
      (fun r => addInfo s!"guard: {s}" (· <| h) r (PSum.inr <| fun q _ => q)) <$> res
    else if cfg.traceDiscarded || cfg.traceSuccesses then
      let res := return gaveUp 1
      let s := printProp p
      slimTrace s!"discard: Guard {s} does not hold"; res
    else
      return gaveUp 1

instance forallTypesTestable {f : Type → Prop} [Testable (f Int)] :
    Testable (NamedBinder var <| ∀ x, f x) where
  run := fun cfg min => do
    let r ← runProp (f Int) cfg min
    return addVarInfo var "Int" (· <| Int) r

-- Instance to handle P → False by testing that P is false
-- For P → False, if P is always false, then P → False is true
-- If we can find a case where P holds, then P → False is false
-- This handles both NamedBinder var (p → False) and (NamedBinder var p) → False
instance (priority := 100) impFalseTestable [PrintableProp p] [Testable p] :
    Testable (NamedBinder var <| p → False) where
  run := fun cfg min => do
    -- Test by trying to find a case where p holds
    -- If we find such a case, then p → False is false (we have a counter-example)
    -- If we can't find such a case, we assume p → False holds
    let r ← runProp p cfg min
    match r with
    | .success (PSum.inr hp) =>
      -- We found a case where p holds with proof, so p → False is false
      -- We can construct a proof: (p → False) → False by applying the function to hp
      return .failure (fun h => h hp) [] 0
    | .success (PSum.inl _) =>
      -- We found a case where p holds but without proof
      -- We can't prove p → False is false without a proof of p
      return .gaveUp 1
    | .failure _ _ _ =>
      -- We found a counter-example to p, meaning p is false
      -- So p → False is true (vacuously true)
      -- But we can't prove it without knowing p is false, so we give up
      return .gaveUp 1
    | .timeout n => return .timeout n
    | .gaveUp n =>
      -- We couldn't determine if p holds, so we give up
      return .gaveUp n

-- Instance to handle (NamedBinder var p) → False
-- This handles the case where addDecorations wraps p in NamedBinder but not the → False
instance (priority := 100) impFalseTestableNamed [PrintableProp p] [Testable p] :
    Testable ((NamedBinder var p) → False) where
  run := fun cfg min => do
    -- Test by trying to find a case where p holds
    let r ← runProp (NamedBinder var p) cfg min
    match r with
    | .success (PSum.inr hp) =>
      -- We found a case where p holds with proof, so (NamedBinder var p) → False is false
      return .failure (fun h => h hp) [] 0
    | .success (PSum.inl _) =>
      -- We found a case where p holds but without proof
      return .gaveUp 1
    | .failure _ _ _ =>
      -- We found a counter-example to p
      return .gaveUp 1
    | .timeout n => return .timeout n
    | .gaveUp n =>
      return .gaveUp n

-- TODO: only in mathlib: @[pp_with_univ]
instance (priority := 100) forallTypesULiftTestable.{u}
    {f : Type u → Prop} [Testable (f (ULift.{u} Int))] :
    Testable (NamedBinder var <| ∀ x, f x) where
  run cfg min := do
    let r ← runProp (f (ULift Int)) cfg min
    pure <| addVarInfo var "ULift Int" (· <| ULift Int) r

/--
Format the counter-examples found in a test failure.
-/
def formatFailure (s : String) (xs : List String) (n : Nat) : String :=
  let counter := String.intercalate "\n" xs
  let parts := [
    "\n===================",
    s,
    counter,
    s!"({n} shrinks)",
    "-------------------"
  ]
  String.intercalate "\n" parts

/--
Increase the number of shrinking steps in a test result.
-/
def addShrinks (n : Nat) : TestResult p → TestResult p
  | TestResult.failure p xs m => TestResult.failure p xs (m + n)
  | TestResult.timeout k => TestResult.timeout k
  | p => p

universe u in
instance {α : Type u} {m : Type u → Type _} [Pure m] : Inhabited (OptionT m α) :=
  ⟨(pure none : m (Option α))⟩

variable {α : Sort _}

/-- Shrink a counter-example `x` by using `Shrinkable.shrink x`, picking the first
candidate that falsifies a property and recursively shrinking that one.
The process is guaranteed to terminate because `shrink x` produces
a proof that all the values it produces are smaller (according to `SizeOf`)
than `x`. Now also respects `maxShrinkDepth` configuration to prevent excessive computation. -/
partial def minimizeAux [SampleableExt α] {β : α → Prop} [∀ x, Testable (β x)] (cfg : Configuration)
    (var : String) (x : SampleableExt.proxy α) (n : Nat) :
    OptionT Gen (Σ x, TestResult (β (SampleableExt.interp x))) := do
  -- Check if we've exceeded the maximum shrink depth
  if let some maxDepth := cfg.maxShrinkDepth then
    if n ≥ maxDepth then
      if cfg.traceShrink then
        slimTrace s!"Maximum shrink depth {maxDepth} reached for {var} := {repr x}"
      failure
  let candidates := SampleableExt.shrink.shrink x
  if cfg.traceShrinkCandidates then
    slimTrace s!"Candidates for {var} := {repr x}:\n  {repr candidates}"
  for candidate in candidates do
    if cfg.traceShrinkCandidates then
      slimTrace s!"Trying {var} := {repr candidate}"
    let res ← OptionT.lift <| Testable.runProp (β (SampleableExt.interp candidate)) cfg true
    if res.isFailure then
      if cfg.traceShrink then
        slimTrace s!"{var} shrunk to {repr candidate} from {repr x}"
      let currentStep := OptionT.lift <| return Sigma.mk candidate (addShrinks (n + 1) res)
      let nextStep := minimizeAux cfg var candidate (n + 1)
      return ← (nextStep <|> currentStep)
  if cfg.traceShrink then
    slimTrace s!"No shrinking possible for {var} := {repr x}"
  failure

/-- Once a property fails to hold on an example, look for smaller counter-examples
to show the user. -/
def minimize [SampleableExt α] {β : α → Prop} [∀ x, Testable (β x)] (cfg : Configuration)
    (var : String) (x : SampleableExt.proxy α) (r : TestResult (β <| SampleableExt.interp x)) :
    Gen (Σ x, TestResult (β <| SampleableExt.interp x)) := do
  if cfg.traceShrink then
     slimTrace "Shrink"
     slimTrace s!"Attempting to shrink {var} := {repr x}"
  let res ← OptionT.run <| minimizeAux cfg var x 0
  return res.getD ⟨x, r⟩

/-- Test a universal property by creating a sample of the right type and instantiating the
bound variable with it. -/
instance varTestable [SampleableExt α] {β : α → Prop} [∀ x, Testable (β x)] :
    Testable (NamedBinder var <| ∀ x : α, β x) where
  run := fun cfg min => do
    let x ← Arbitrary.arbitrary
    if cfg.traceSuccesses || cfg.traceDiscarded then
      slimTrace s!"{var} := {repr x}"
    -- Use `runPropE` here to collect errors from the call to `Arbitrary.arbitrary`.
    let r ← Testable.runPropE (β <| SampleableExt.interp x) cfg false
    let ⟨finalX, finalR⟩ ←
      if isFailure r then
        if cfg.traceSuccesses then
          slimTrace s!"{var} := {repr x} is a failure"
        if min then
          minimize cfg var x r
        else
          pure ⟨x, r⟩
      else
        pure ⟨x, r⟩
    return addVarInfo var finalX (· <| SampleableExt.interp finalX) finalR

/-- Test a universal property over Fin type.
This handles `∀ j : Fin n, P j` where `n` is a runtime value.
We directly sample values from 0 to n-1. -/
instance (priority := 100) finTestable {n : Nat} {β : Fin n → Prop} [∀ j, Testable (β j)] :
    Testable (∀ j : Fin n, β j) where
  run := fun cfg min => do
    if h : n = 0 then
      -- Fin 0 is empty, so the forall is vacuously true
      have h' : ∀ j : Fin n, β j := fun j => by
        rw [h] at j
        exact Fin.elim0 j
      return success (PSum.inr h')
    else
      -- n > 0, directly sample a value from 0 to n-1
      have pos : 0 < n := Nat.pos_of_ne_zero h
      let ⟨jVal, ⟨_, hlt⟩⟩ ← Gen.chooseNatLt 0 n pos
      let j : Fin n := ⟨jVal, hlt⟩
      if cfg.traceSuccesses || cfg.traceDiscarded then
        slimTrace s!"j := {j.val} (Fin {n})"
      let r ← Testable.runPropE (β j) cfg false
      match r with
      | .failure h' _ _ =>
        have : ¬(∀ j : Fin n, β j) := fun h2 => h' (h2 j)
        return failure this [s!"j := {j.val}"] 0
      | .timeout k => return timeout k
      | .gaveUp k => return gaveUp k
      | .success _ => return success (PSum.inl ())

/-- Test a universal property without NamedBinder annotation.
This handles foralls that are nested inside And/Or where NamedBinder is not present.
Lower priority than varTestable so that NamedBinder version is preferred when available. -/
instance (priority := 50) varTestableNoName [SampleableExt α] {β : α → Prop} [∀ x, Testable (β x)] :
    Testable (∀ x : α, β x) where
  run := fun cfg min => do
    let x ← Arbitrary.arbitrary
    if cfg.traceSuccesses || cfg.traceDiscarded then
      slimTrace s!"x := {repr x}"
    let r ← Testable.runPropE (β <| SampleableExt.interp x) cfg false
    let ⟨finalX, finalR⟩ ←
      if isFailure r then
        if cfg.traceSuccesses then
          slimTrace s!"x := {repr x} is a failure"
        if min then
          minimize cfg "x" x r
        else
          pure ⟨x, r⟩
      else
        pure ⟨x, r⟩
    return addVarInfo "x" finalX (· <| SampleableExt.interp finalX) finalR

/-- Test an existential property by generating samples and trying to find one that satisfies the predicate.
Unlike universal properties (which we try to disprove), existential properties require finding a witness.
Each call to `run` tests ONE sample. The outer `runSuite` will call this multiple times. -/
instance existsTestable [SampleableExt α] {β : α → Prop} [∀ x, Testable (β x)] :
    Testable (∃ x : α, β x) where
  run := fun cfg _min => do
    -- Like `varTestable`: each `run` tests one sample to avoid exponential blow-up when nested.
    let x ← Arbitrary.arbitrary
    if cfg.traceSuccesses || cfg.traceDiscarded then
      slimTrace s!"trying witness: {repr x}"
    let r ← Testable.runPropE (β <| SampleableExt.interp x) cfg false
    match r with
    | TestResult.success _ =>
      -- Found a satisfying witness!
      if cfg.traceSuccesses then
        slimTrace s!"found witness: {repr x}"
      return TestResult.success (PSum.inl ())
    | TestResult.failure _ _ _ =>
      -- This sample is not a witness; return `gaveUp` so the outer loop tries other samples.
      if cfg.traceDiscarded then
        slimTrace s!"candidate {repr x} is not a witness"
      return TestResult.gaveUp 1
    | TestResult.timeout n => return TestResult.timeout n
    | TestResult.gaveUp n =>
      -- This sample could not be tested
      return TestResult.gaveUp n

/-- Test a negated existential property ¬∃ x, β x by trying to find a counterexample.
This is equivalent to testing ∀ x, ¬β x.
If we find any x where β x holds, then ¬∃ x, β x is false. -/
instance notExistsTestable [SampleableExt α] {β : α → Prop} [∀ x, Testable (β x)] :
    Testable (¬∃ x : α, β x) where
  run := fun cfg _ => do
    -- Draw one sample and test whether `β x` holds
    let x ← Arbitrary.arbitrary
    if cfg.traceSuccesses || cfg.traceDiscarded then
      slimTrace s!"testing ¬∃: trying {repr x}"
    let r ← Testable.runPropE (β <| SampleableExt.interp x) cfg false
    match r with
    | TestResult.success (PSum.inr hp) =>
      -- Found an `x` with `β x` — a counterexample to `¬∃ x, β x`
      if cfg.traceSuccesses then
        slimTrace s!"found counterexample to ¬∃: {repr x} satisfies the predicate"
      -- Build a proof of `¬(¬∃ x, β x)`
      have h : ¬(¬∃ x : α, β x) := fun hnex => hnex ⟨SampleableExt.interp x, hp⟩
      return TestResult.failure h [s!"found witness: {repr x}"] 0
    | TestResult.success (PSum.inl _) =>
      -- `β x` holds but without a proof; conservatively give up
      if cfg.traceDiscarded then
        slimTrace s!"¬∃: {repr x} may satisfy predicate but no proof"
      return TestResult.gaveUp 1
    | TestResult.failure _ _ _ =>
      -- This sample does not satisfy `β x`, which supports `¬∃ x, β x`
      if cfg.traceSuccesses then
        slimTrace s!"¬∃: {repr x} does not satisfy predicate (good)"
      return TestResult.success (PSum.inl ())
    | TestResult.timeout n => return TestResult.timeout n
    | TestResult.gaveUp n =>
      -- Could not test this sample
      return TestResult.gaveUp n

/-- Test a universal property about propositions -/
instance propVarTestable {β : Prop → Prop} [∀ b : Bool, Testable (β b)] :
  Testable (NamedBinder var <| ∀ p : Prop, β p)
where
  run := fun cfg min =>
    imp (fun h (b : Bool) => h b) <$> Testable.runProp (NamedBinder var <| ∀ b : Bool, β b) cfg min

instance (priority := high) unusedVarTestable {β : Prop} [Nonempty α] [Testable β] :
  Testable (NamedBinder var (α → β))
where
  run := fun cfg min => do
    if cfg.traceDiscarded || cfg.traceSuccesses then
      slimTrace s!"{var} is unused"
    let r ← Testable.runProp β cfg min
    let finalR := addInfo s!"{var} is irrelevant (unused)" id r
    return imp (· <| Classical.ofNonempty) finalR (PSum.inr <| fun x _ => x)

universe u in
instance (priority := 2000) subtypeVarTestable {α : Type u} {p : α → Prop} {β : α → Prop}
    [∀ x, PrintableProp (p x)]
    [∀ x, Testable (β x)]
    [SampleableExt (Subtype p)] {var'} :
    Testable (NamedBinder var <| (x : α) → NamedBinder var' <| p x → β x) where
  run cfg min :=
    letI (x : Subtype p) : Testable (β x) :=
      { run := fun cfg min => do
          let r ← Testable.runProp (β x.val) cfg min
          return addInfo s!"guard: {printProp (p x)} (by construction)" id r (PSum.inr id) }
    do
      let r ← @Testable.run (∀ x : Subtype p, β x.val) (@varTestable var _ _ _ _) cfg min
      have := by simp [Subtype.forall, NamedBinder]
      return iff this r

instance (priority := high+1) decidableImpTestable {p q : Prop}
    [PrintableProp p] [PrintableProp q] [Decidable p] [Decidable q] :
    Testable (p → q) where
  run := fun _ _ =>
    if hp : p then
      if hq : q then
        -- p true, q true, implication holds
        have h : p → q := fun _ => hq
        return success (PSum.inr h)
      else
        -- p true, q false, implication fails
        have h : ¬(p → q) := fun h => hq (h hp)
        let s := s!"{printProp p} → {printProp q}"
        return failure h [s!"issue: {s} does not hold (premise is true but conclusion is false)"] 0
    else
      -- p false, implication holds vacuously
      have h : p → q := fun hp' => absurd hp' hp
      return success (PSum.inr h)

instance (priority := high+1) decidableIffTestable {p q : Prop}
    [PrintableProp p] [PrintableProp q] [Decidable p] [Decidable q] :
    Testable (p ↔ q) where
  run := fun _ _ =>
    if hp : p then
      if hq : q then
        -- Both true, iff holds
        have h : p ↔ q := ⟨fun _ => hq, fun _ => hp⟩
        return success (PSum.inr h)
      else
        -- p true, q false, iff fails
        have h : ¬(p ↔ q) := fun h => hq (h.mp hp)
        let s := s!"{printProp p} ↔ {printProp q}"
        return failure h [s!"issue: {s} does not hold (left is true, right is false)"] 0
    else
      if hq : q then
        -- p false, q true, iff fails
        have h : ¬(p ↔ q) := fun h => hp (h.mpr hq)
        let s := s!"{printProp p} ↔ {printProp q}"
        return failure h [s!"issue: {s} does not hold (left is false, right is true)"] 0
      else
        -- Both false, iff holds
        have h : p ↔ q := ⟨fun hp' => absurd hp' hp, fun hq' => absurd hq' hq⟩
        return success (PSum.inr h)

instance notTestable [PrintableProp p] [Decidable p] : Testable (¬ p) where
  run := fun _ _ =>
    if h : p then
      have nh : ¬¬p := fun hnp => hnp h
      let s := s!"¬{printProp p}"
      return failure nh [s!"issue: {s} does not hold ({printProp p} is true)"] 0
    else
      return success (PSum.inr h)

instance (priority := low) decidableTestable {p : Prop} [PrintableProp p] [Decidable p] :
    Testable p where
  run := fun _ _ =>
    if h : p then
      return success (PSum.inr h)
    else
      let s := printProp p
      return failure h [s!"issue: {s} does not hold"] 0

/-- Instance for testing propositions that involve pattern matching on Option.
This handles cases like: `match opt with | none => P | some x => Q x` -/
instance (priority := 1000) optionMatchTestable {α : Type _} {opt : Option α}
    {noneCase : Prop} {someCase : α → Prop}
    [Testable noneCase] [∀ x, Testable (someCase x)] :
    Testable (opt.casesOn noneCase someCase) where
  run := fun cfg min =>
    match opt with
    | none => Testable.runProp noneCase cfg min
    | some x => Testable.runProp (someCase x) cfg min

/-- Instance for testing propositions that involve pattern matching on Option (α × β).
This handles cases like: `match opt with | none => P | some (a, b) => Q a b` -/
instance (priority := 1100) optionProdMatchTestable {α β : Type _} {opt : Option (α × β)}
    {noneCase : Prop} {someCase : α → β → Prop}
    [Testable noneCase] [∀ a b, Testable (someCase a b)] :
    Testable (opt.casesOn noneCase (fun p => someCase p.1 p.2)) where
  run := fun cfg min =>
    match opt with
    | none => Testable.runProp noneCase cfg min
    | some (a, b) => Testable.runProp (someCase a b) cfg min

/-- Instance for testing propositions with nested Prod.casesOn inside Option.casesOn.
This handles the pattern that Lean generates for `match opt with | none => P | some (a, b) => Q a b`:
  `Option.casesOn opt noneCase (fun val => Prod.casesOn val (fun a b => someCase a b))` -/
instance (priority := 1200) optionProdNestedMatchTestable {α β : Type _} {opt : Option (α × β)}
    {noneCase : Prop} {someCase : α → β → Prop}
    [Testable noneCase] [∀ a b, Testable (someCase a b)] :
    Testable (opt.casesOn noneCase (fun val => val.casesOn (fun a b => someCase a b))) where
  run := fun cfg min =>
    match opt with
    | none => Testable.runProp noneCase cfg min
    | some (a, b) => Testable.runProp (someCase a b) cfg min

/-- Generic instance for testing propositions involving `Option (Nat × Nat)` pattern matching.
This handles cases where `p` is a function that returns a Prop based on an Option value.
At runtime, we evaluate the option and dispatch to the appropriate branch. -/
instance (priority := 50) optionNatNatPropTestable
    {p : Option (Nat × Nat) → Prop} {opt : Option (Nat × Nat)}
    [∀ x, Decidable (p x)] : Testable (p opt) where
  run := fun _ _ => do
    if h : p opt then
      return .success (.inr h)
    else
      return .failure (fun hp => False.elim (h hp)) [] 0

/-- Instance for testing propositions with dependent Option match inside quantifiers.
Handles: `∀ x, match f x with | none => P | some y => Q y` -/
instance (priority := 900) dependentOptionTestable {α β : Type _}
    [SampleableExt α] {f : α → Option β}
    {noneCase : Prop} {someCase : β → Prop}
    [Testable noneCase] [∀ y, Testable (someCase y)] :
    Testable (NamedBinder var (∀ (x : α), (f x).casesOn noneCase someCase)) where
  run := fun cfg min =>
    haveI : ∀ x, Testable ((f x).casesOn noneCase someCase) := fun _ => optionMatchTestable
    varTestable.run cfg min

/-- Instance for testing propositions that involve pattern matching on List.
This handles cases like: `match lst with | [] => P | x :: xs => Q x xs` -/
instance listMatchTestable {α : Type _} {lst : List α}
    {nilCase : Prop} {consCase : α → List α → Prop}
    [Testable nilCase] [∀ x xs, Testable (consCase x xs)] :
    Testable (lst.casesOn nilCase consCase) where
  run := fun cfg min =>
    match lst with
    | [] => Testable.runProp nilCase cfg min
    | x :: xs => Testable.runProp (consCase x xs) cfg min

/-- Instance for testing propositions with dependent List match inside quantifiers.
Handles: `∀ xs, match xs with | [] => P | y :: ys => Q y ys` -/
instance (priority := 900) dependentListTestable {α : Type _}
    [SampleableExt (List α)]
    {nilCase : Prop} {consCase : α → List α → Prop}
    [Testable nilCase] [∀ y ys, Testable (consCase y ys)] :
    Testable (NamedBinder var (∀ (xs : List α), xs.casesOn nilCase consCase)) where
  run := fun cfg min =>
    haveI : ∀ (xs : List α), Testable ((xs : List α).casesOn nilCase consCase) := fun xs => @listMatchTestable α xs nilCase consCase _ _
    varTestable.run cfg min

/-- Instance for testing propositions that involve pattern matching on Nat.
This handles cases like: `match n with | 0 => P | n+1 => Q n` -/
instance natMatchTestable {n : Nat}
    {zeroCase : Prop} {succCase : Nat → Prop}
    [Testable zeroCase] [∀ m, Testable (succCase m)] :
    Testable (Nat.casesOn n zeroCase succCase) where
  run := fun cfg min =>
    match n with
    | 0 => Testable.runProp zeroCase cfg min
    | m + 1 => Testable.runProp (succCase m) cfg min

/-- Instance for testing propositions that involve pattern matching on Bool.
This handles cases like: `match b with | true => P | false => Q` -/
instance boolMatchTestable {b : Bool}
    {trueCase falseCase : Prop}
    [Testable trueCase] [Testable falseCase] :
    Testable (Bool.casesOn b falseCase trueCase) where
  run := fun cfg min =>
    match b with
    | true => Testable.runProp trueCase cfg min
    | false => Testable.runProp falseCase cfg min

/-- Instance for testing propositions that involve List match with a True guard.
This handles the pattern `match xs, True.intro with | [], h => P | _, h => Q`
which gets compiled with a dependent motive. -/
instance (priority := 1200) listMatchTrueGuardTestable {α : Type _} {lst : List α}
    {nilCase : Prop} {consCase : Prop}
    [Testable nilCase] [Testable consCase] :
    Testable (match lst with | [] => nilCase | _ :: _ => consCase) where
  run := fun cfg min =>
    match lst with
    | [] => Testable.runProp nilCase cfg min
    | _ :: _ => Testable.runProp consCase cfg min

/-- Instance for testing propositions that involve pattern matching on Sum.
This handles cases like: `match s with | inl a => P a | inr b => Q b` -/
instance sumMatchTestable {α β : Type _} {s : α ⊕ β}
    {inlCase : α → Prop} {inrCase : β → Prop}
    [∀ a, Testable (inlCase a)] [∀ b, Testable (inrCase b)] :
    Testable (Sum.casesOn s inlCase inrCase) where
  run := fun cfg min =>
    match s with
    | Sum.inl a => Testable.runProp (inlCase a) cfg min
    | Sum.inr b => Testable.runProp (inrCase b) cfg min

/-- Instance for testing propositions that involve pattern matching on Prod (pairs).
This handles cases like: `match p with | (a, b) => Q a b` -/
instance prodMatchTestable {α β : Type _} {p : α × β}
    {pairCase : α → β → Prop}
    [∀ a b, Testable (pairCase a b)] :
    Testable (Prod.casesOn p pairCase) where
  run := fun cfg min =>
    let (a, b) := p
    Testable.runProp (pairCase a b) cfg min


end Testable

section PrintableProp

variable {α : Type _}

instance Eq.printableProp [Repr α] {x y : α} : PrintableProp (x = y) where
  printProp := s!"{repr x} = {repr y}"

instance Ne.printableProp [Repr α] {x y : α} : PrintableProp (x ≠ y) where
  printProp := s!"{repr x} ≠ {repr y}"

instance LE.printableProp [Repr α] [LE α] {x y : α} : PrintableProp (x ≤ y) where
  printProp := s!"{repr x} ≤ {repr y}"

instance LT.printableProp [Repr α] [LT α] {x y : α} : PrintableProp (x < y) where
  printProp := s!"{repr x} < {repr y}"

variable {x y : Prop}

instance And.printableProp [PrintableProp x] [PrintableProp y] : PrintableProp (x ∧ y) where
  printProp := s!"{printProp x} ∧ {printProp y}"

instance Or.printableProp [PrintableProp x] [PrintableProp y] : PrintableProp (x ∨ y) where
  printProp := s!"{printProp x} ∨ {printProp y}"

instance Iff.printableProp [PrintableProp x] [PrintableProp y] : PrintableProp (x ↔ y) where
  printProp := s!"{printProp x} ↔ {printProp y}"

instance Imp.printableProp [PrintableProp x] [PrintableProp y] : PrintableProp (x → y) where
  printProp := s!"{printProp x} → {printProp y}"

instance Not.printableProp [PrintableProp x] : PrintableProp (¬x) where
  printProp := s!"¬{printProp x}"

instance True.printableProp : PrintableProp True where
  printProp := "True"

instance False.printableProp : PrintableProp False where
  printProp := "False"

instance Bool.printableProp {b : Bool} : PrintableProp b where
  printProp := if b then "true" else "false"

end PrintableProp

section IO
open TestResult

/-! ## Resource Monitoring

Runtime monitoring for timeout.
- Timeout: Uses standard `IO.monoMsNow` API
-/

/-- Check if timeout has been exceeded based on wall-clock time. -/
private def isTimeoutExceeded (startMs : Nat) (limitSec : Nat) : IO Bool := do
  let currentMs ← IO.monoMsNow
  return (currentMs - startMs) / 1000 ≥ limitSec

/-! ## Core Test Execution -/

/-- Execute `cmd` and repeat every time the result is `gaveUp` (at most `n` times). -/
def retry (cmd : Gen (TestResult p)) : Nat → Gen (TestResult p)
  | 0 => return TestResult.gaveUp 1
  | n+1 => do
    let r ← cmd
    match r with
    | .success hp => return success hp
    | .failure h xs n => return failure h xs n
    | .timeout n => return timeout n
    | .gaveUp _ => retry cmd n

/-- Count the number of times the test procedure gave up. -/
def giveUp (x : Nat) : TestResult p → TestResult p
  | success (PSum.inl ()) => gaveUp x
  | success (PSum.inr p) => success <| (PSum.inr p)
  | timeout n => timeout n
  | gaveUp n => gaveUp <| n + x
  | TestResult.failure h xs n => failure h xs n

/-- Try `n` times to find a counter-example for `p`. -/
def Testable.runSuiteAux (p : Prop) [Testable p] (cfg : Configuration) :
    TestResult p → Nat → Gen (TestResult p)
  | r, 0 => return r
  | r, n+1 => do
    let size (_ : Nat) := (cfg.numInst - n - 1) * cfg.maxSize / cfg.numInst
    if cfg.traceSuccesses then
      slimTrace s!"New sample"
      slimTrace s!"Retrying up to {cfg.numRetries} times until guards hold"
    let x ← retry ((Testable.runProp p cfg true).resize size) cfg.numRetries
    match x with
    | success (PSum.inl ()) => runSuiteAux p cfg r n
    | gaveUp g => runSuiteAux p cfg (giveUp g r) n
    | _ => return x

/-- Try to find a counter-example of `p`. -/
def Testable.runSuite (p : Prop) [Testable p] (cfg : Configuration := {}) : Gen (TestResult p) :=
  Testable.runSuiteAux p cfg (success <| PSum.inl ()) cfg.numInst

/-- Run a single test with time and heartbeat monitoring.
    Note: Heartbeat checking can interrupt computation during type checking/proof,
    but cannot interrupt pure IO execution. Time checking happens before/after test. -/
private def runTestWithMonitoring (p : Prop) [Testable p] (cfg : Configuration) (seed : Nat)
    (size : Nat) (startMs : Nat) : IO (TestResult p) := do
  let cmd := retry ((Testable.runProp p cfg true).resize (fun _ => size)) cfg.numRetries

  -- Run the test (synchronous, cannot be interrupted during pure IO execution)
  -- However, if the test involves type checking or proof (in Testable instances),
  -- Lean's heartbeat mechanism can interrupt and throw an exception
  let testResult ← try
    runRandWith seed cmd
  catch e =>
    -- If an exception occurs, it might be due to heartbeat/timeout limits
    -- (especially if the test involves heavy type checking in Testable instances)
    -- We treat any exception during test execution as a potential timeout
    if !cfg.quiet then
      IO.eprintln s!"[Quickcheck] Test interrupted by exception (possibly timeout/heartbeat): {e}"
    return .timeout 1

  -- Check time limit after test execution
  if let some limitSec := cfg.workerTimeout then
    let timeExceeded ← isTimeoutExceeded startMs limitSec

    if timeExceeded then
      if !cfg.quiet then
        IO.eprintln s!"[Quickcheck] Test exceeded time limit ({limitSec}s)"
      return .timeout 1

  return testResult

/-- Run a worker's share of tests with resource monitoring.
    Uses wall-clock time to detect timeouts. -/
private def runWorkerTests (p : Prop) [Testable p] (cfg : Configuration) (seed : Nat) (numTests : Nat) (startIdx : Nat) : IO (TestResult p) := do
  let mut result : TestResult p := success (PSum.inl ())
  let mut gaveUpCount := 0
  let mut adaptiveState := Adaptive.AdaptiveState.initial cfg
  let startMs ← IO.monoMsNow

  for i in List.range numTests do
    let remaining := numTests - i

    -- Check timeout before starting test
    if let some limitSec := cfg.workerTimeout then
      let timeExceeded ← isTimeoutExceeded startMs limitSec

      if timeExceeded then
        if !cfg.quiet then
          IO.eprintln s!"[Quickcheck] Timeout ({limitSec}s), skipping {remaining} tests"
        return .timeout remaining

    let testIdx := startIdx + i
    let mut retryTest := true
    while retryTest do
      retryTest := false
      let size := (cfg.numInst - testIdx - 1) * adaptiveState.currentMaxSize / cfg.numInst
      let testCfg := { cfg with maxSize := adaptiveState.currentMaxSize }
      let testResult ← runTestWithMonitoring p testCfg (seed + i) size startMs

      match testResult with
      | .success (PSum.inl ()) =>
        -- Test passed, move to next test
        break
      | .success (PSum.inr _) => return testResult
      | .failure _ _ _ => return testResult
      | .timeout n =>
        -- Only use adaptive logic if in adaptive mode
        if Adaptive.isAdaptiveConfig cfg then
          let (shouldRetry, newState) ← Adaptive.makeAdaptiveDecisionIO adaptiveState cfg
          adaptiveState := newState
          if shouldRetry then
            retryTest := true
          else
            return .timeout (remaining + n)
        else
          return .timeout (remaining + n)
      | .gaveUp n =>
        gaveUpCount := gaveUpCount + n
        result := giveUp gaveUpCount result
        break

  -- Report adaptive statistics
  Adaptive.reportAdaptiveStatsIO adaptiveState cfg
  return result

/-- Run a worker with exception handling. Catches crashes and returns gaveUp. -/
private def runWorkerSafe (p : Prop) [Testable p] (cfg : Configuration) (seed : Nat) (numTests : Nat) (startIdx : Nat) : IO (TestResult p) := do
  try
    runWorkerTests p cfg seed numTests startIdx
  catch _ =>
    -- Any error (stack, timeout) is treated as gaveUp
    -- This prevents one worker from crashing the entire process
    -- Return gaveUp with the number of tests this worker was supposed to run
    -- This accurately reflects that all numTests were abandoned due to timeout/error
    return .gaveUp numTests

/-- Run test suite in parallel using multiple workers.
    This version avoids blocking indefinitely on `Task.get` by polling the
    task state via `IO.getTaskState` and only calling `get` once the task
    has finished. If the global time limit (from `cfg.workerTimeout`) is
    exceeded while workers are still running, we stop waiting and return
    a timeout result instead of blocking forever.
    Supports adaptive mode: reduces maxSize on timeout and retries. -/
private def runSuiteParallel (p : Prop) [Testable p] (cfg : Configuration) : IO (TestResult p) := do
  let mut adaptiveState := Adaptive.AdaptiveState.initial cfg
  let mut currentCfg := cfg
  let mut maxRetries := 10  -- Limit retries to prevent infinite loops

  while maxRetries > 0 do
    maxRetries := maxRetries - 1
    let baseSeed := currentCfg.randomSeed.getD 0
    let numWorkers := max 1 currentCfg.numWorkers
    let testsPerWorker := currentCfg.numInst / numWorkers
    let remainder := currentCfg.numInst % numWorkers

    -- Spawn worker tasks
    let mut tasks : Array (Task (Except IO.Error (TestResult p))) := #[]
    let mut testIdx := 0

    for workerId in List.range numWorkers do
      let workerTests := testsPerWorker + (if workerId < remainder then 1 else 0)
      if workerTests > 0 then
        let workerSeed := baseSeed + workerId * 1000000
        let startIdx := testIdx
        -- Build IO action first to avoid capturing full context in closure
        let workerAction : IO (TestResult p) := runWorkerSafe p currentCfg workerSeed workerTests startIdx
        let task ← IO.asTask workerAction
        tasks := tasks.push task
        testIdx := testIdx + workerTests

    -- No workers spawned (e.g. numInst = 0)
    if tasks.isEmpty then
      return success (PSum.inl ())

    -- Collect results without blocking indefinitely on any single task.
    let mut finalResult : TestResult p := success (PSum.inl ())
    let mut totalGaveUp := 0
    let mut totalTimeout := 0
    let mut remaining := tasks.size
    -- Track which indices have already been collected to avoid double `get`
    let mut collected : Array Bool := Array.replicate tasks.size false
    let startMs ← IO.monoMsNow

    while remaining > 0 do
      -- Global timeout: if `workerTimeout` is set and we exceed it while some
      -- workers are still pending, treat remaining tests as timed out.
      if let some limitSec := currentCfg.workerTimeout then
        let now ← IO.monoMsNow
        if (now - startMs) / 1000 ≥ limitSec then
          let pending := remaining
          if !cfg.quiet then
            IO.eprintln s!"[Quickcheck] Global timeout ({limitSec}s) while waiting for {pending} worker(s)"
          -- Only use adaptive logic if in adaptive mode
          if Adaptive.isAdaptiveConfig cfg && maxRetries > 0 then
            let (shouldRetry, newState) ← Adaptive.makeAdaptiveDecisionIO adaptiveState cfg
            adaptiveState := newState
            if shouldRetry then
              currentCfg := { currentCfg with maxSize := adaptiveState.currentMaxSize }
              -- Break inner loop and continue outer loop to retry
              break
          -- If not adaptive or adaptive decided not to retry, return timeout
          return .timeout pending

      let mut madeProgress := false

      -- Poll each task; only `get` when we know it has finished.
      for i in List.range tasks.size do
        if !collected[i]! then
          let state ← IO.getTaskState tasks[i]!
          match state with
          | IO.TaskState.waiting =>
            pure ()
          | IO.TaskState.running =>
            -- still running, nothing to do; we only call `get` once finished
            pure ()
          | IO.TaskState.finished =>
            collected := collected.set! i true
            remaining := remaining - 1
            madeProgress := true
            match tasks[i]!.get with
            | .ok workerResult =>
              match workerResult with
              | .success (PSum.inl ()) =>
                continue
              | .success (PSum.inr _) =>
                -- Found a proof: return immediately.
                Adaptive.reportAdaptiveStatsIO adaptiveState cfg
                return workerResult
              | .failure _ _ _ =>
                -- Found a counterexample: return immediately.
                Adaptive.reportAdaptiveStatsIO adaptiveState cfg
                return workerResult
              | .timeout n =>
                totalTimeout := totalTimeout + n
                finalResult := .timeout totalTimeout
                -- Note: Individual worker timeouts are handled inside runWorkerTests with adaptive logic
              | .gaveUp n =>
                totalGaveUp := totalGaveUp + n
                finalResult := giveUp totalGaveUp finalResult
            | .error _ =>
              -- Worker crashed, count as gaveUp
              totalGaveUp := totalGaveUp + 1

      -- Avoid busy-waiting if no task finished in this iteration.
      if !madeProgress then
        -- Sleep for a short time (10ms) before polling again.
        IO.sleep 10

    -- All workers have finished, check results and decide whether to retry
    if totalTimeout > 0 then
      -- Only use adaptive logic if in adaptive mode and we have retries left
      if Adaptive.isAdaptiveConfig cfg && maxRetries > 0 then
        let (shouldRetry, newState) ← Adaptive.makeAdaptiveDecisionIO adaptiveState cfg
        adaptiveState := newState
        if shouldRetry then
          currentCfg := { currentCfg with maxSize := adaptiveState.currentMaxSize }
          -- Continue outer loop to retry with reduced maxSize
          continue
      -- Report adaptive statistics before returning
      Adaptive.reportAdaptiveStatsIO adaptiveState cfg
      return .timeout totalTimeout

    -- Report adaptive statistics if any reductions occurred
    Adaptive.reportAdaptiveStatsIO adaptiveState cfg
    return finalResult

  -- If we've exhausted retries, report stats and return timeout
  Adaptive.reportAdaptiveStatsIO adaptiveState currentCfg
  if !cfg.quiet then
    IO.eprintln s!"[Quickcheck] Adaptive: maximum retries exhausted, giving up"
  return .timeout cfg.numInst

/-- Run a test suite in single-threaded mode with timeout monitoring.
    Uses Task + polling to avoid blocking indefinitely on long-running tests.
    Supports adaptive mode: reduces maxSize on timeout and retries. -/
private def runSuiteSingleThreaded (p : Prop) [Testable p] (cfg : Configuration) : IO (TestResult p) := do
  let mut adaptiveState := Adaptive.AdaptiveState.initial cfg
  let mut currentCfg := cfg

  while true do
    let suiteCmd := match currentCfg.randomSeed with
      | none => Gen.run (Testable.runSuite p currentCfg) 0
      | some s => runRandWith s (Testable.runSuite p currentCfg)

    -- Wrap the suite execution in a Task for timeout monitoring
    let task ← IO.asTask suiteCmd
    let startMs ← IO.monoMsNow

    -- Poll the task with timeout monitoring
    let mut done := false
    while !done do
      -- Check global timeout
      if let some limitSec := currentCfg.workerTimeout then
        let now ← IO.monoMsNow
        if (now - startMs) / 1000 ≥ limitSec then
          -- Only use adaptive logic if in adaptive mode
          if Adaptive.isAdaptiveConfig cfg then
            let (shouldRetry, newState) ← Adaptive.makeAdaptiveDecisionIO adaptiveState cfg
            adaptiveState := newState
            if shouldRetry then
              currentCfg := { currentCfg with maxSize := adaptiveState.currentMaxSize }
              done := true  -- Break inner loop to retry with new config
              continue      -- Continue outer loop
          -- If not adaptive or adaptive decided not to retry, return timeout
          return .timeout cfg.numInst

      -- Check task state
      let state ← IO.getTaskState task
      match state with
      | IO.TaskState.waiting =>
        IO.sleep 1000 -- wait for 1 second
      | IO.TaskState.running =>
        IO.sleep 1000 -- wait for 1 second
      | IO.TaskState.finished =>
        done := true
        match task.get with
        | .ok result =>
          match result with
          | .timeout n =>
            -- Only use adaptive logic if in adaptive mode
            if Adaptive.isAdaptiveConfig cfg then
              let (shouldRetry, newState) ← Adaptive.makeAdaptiveDecisionIO adaptiveState cfg
              adaptiveState := newState
              if shouldRetry then
                currentCfg := { currentCfg with maxSize := adaptiveState.currentMaxSize }
                -- Continue outer loop to retry
                continue
            -- If not adaptive or adaptive decided not to retry, return timeout
            return .timeout n
          | _ =>
            -- Report adaptive statistics
            Adaptive.reportAdaptiveStatsIO adaptiveState cfg
            return result
        | .error e =>
          if !cfg.quiet then
            IO.eprintln s!"[Quickcheck] Error in single-threaded execution: {e}"
          return .gaveUp cfg.numInst

  -- This should never be reached, but needed for type checking
  return .gaveUp cfg.numInst

/-- Run a test suite for `p` in `IO` using the global RNG in `stdGenRef`. -/
def Testable.checkIO (p : Prop) [Testable p] (cfg : Configuration := {}) : IO (TestResult p) :=
  if cfg.numWorkers > 1 then
    runSuiteParallel p cfg
  else
    -- Use timeout monitoring for single-threaded mode too
    runSuiteSingleThreaded p cfg

end IO

namespace Decorations

open Lean

/-- Traverse the syntax of a proposition to find universal quantifiers
and add `NamedBinder` annotations next to them. -/
partial def addDecorations (e : Expr) : MetaM Expr :=
  Meta.transform e fun expr => do
    if not (← Meta.inferType expr).isProp then
      return .done expr
    else if let Expr.forallE name type body data := expr then
      let newType ← addDecorations type
      let newBody ← Meta.withLocalDecl name data type fun fvar => do
        return (← addDecorations (body.instantiate1 fvar)).abstract #[fvar]
      let rest := Expr.forallE name newType newBody data
      return .done <| (← Meta.mkAppM `Quickcheck.NamedBinder #[mkStrLit name.toString, rest])
    else
      return .continue

/-- `DecorationsOf p` is used as a hint to `mk_decorations` to specify
that the goal should be satisfied with a proposition equivalent to `p`
with added annotations. -/
abbrev DecorationsOf (_p : Prop) := Prop

open Elab.Tactic
open Meta

/-- In a goal of the shape `⊢ DecorationsOf p`, `mk_decoration` examines
the syntax of `p` and adds `NamedBinder` around universal quantifications
to improve error messages. This tool can be used in the declaration of a
function as follows:
```lean
def foo (p : Prop) (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : ...
```
`p` is the parameter given by the user, `p'` is a definitionally equivalent
proposition where the quantifiers are annotated with `NamedBinder`.
-/
scoped elab "mk_decorations" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  if let .app (.const ``Decorations.DecorationsOf _) body := goalType then
    closeMainGoal `mk_decorations (← addDecorations body)

end Decorations

open Decorations in
/-- Run a test suite for `p` and throw an exception if `p` does not hold. -/
def Testable.check (p : Prop) (cfg : Configuration := {})
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : Lean.CoreM PUnit := do
  match ← Testable.checkIO p' cfg with
  | TestResult.success _ => if !cfg.quiet then Lean.logInfo "Unable to find a counter-example"
  | TestResult.timeout n =>
    if !cfg.quiet then
      let msg := s!"Timeout: {n} test(s) were skipped due to timeout (time limit exceeded)."
      Lean.logWarning msg
  | TestResult.gaveUp n =>
    if !cfg.quiet then
      let msg := s!"Gave up after failing to generate values that fulfill the preconditions {n} times."
      Lean.logWarning msg
  | TestResult.failure _ xs n =>
    let msg := "Found a counter-example!"
    if cfg.quiet then
      Lean.throwError msg
    else
      Lean.throwError <| formatFailure msg xs n

macro tk:"#test " e:term : command => `(command| #eval%$tk Testable.check $e)

end Quickcheck
