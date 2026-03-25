import Quickcheck.Attr
import Quickcheck.Arbitrary
import Quickcheck.DeriveArbitrary
import Quickcheck.Testable

open Quickcheck Gen

set_option guard_msgs.diff true

/-- An inductive datatype representing regular expressions (where "characters" are `Nat`s).
   Adapted from the Inductive Propositions chapter of Software Foundations, volume 1:
   See https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html
   and search for "Case Study: Regular Expressions".
   The `RegExp`s below are non-polymorphic in the character type. -/
inductive RegExp : Type where
  | EmptySet : RegExp
  | EmptyStr : RegExp
  | Char : Nat → RegExp -- using Nat instead of Char
  | App : RegExp → RegExp → RegExp
  | Union : RegExp → RegExp → RegExp
  | Star : RegExp → RegExp
  deriving Repr, BEq

set_option trace.quickcheck.deriving.arbitrary true in
/--
trace: [quickcheck.deriving.arbitrary] ⏎
    [mutual
       def arbitraryRegExp✝ : Nat → Quickcheck.Gen (@RegExp✝) :=
         let rec aux_arb (fuel✝ : Nat) : Quickcheck.Gen (@RegExp✝) :=
           match fuel✝ with
           | Nat.zero =>
             Quickcheck.Gen.oneOfWithDefault (pure RegExp.EmptySet)
               [(pure RegExp.EmptySet), (pure RegExp.EmptyStr),
                 (do
                   let a✝ ← Quickcheck.Arbitrary.arbitrary
                   return RegExp.Char a✝)]
           | fuel'✝ + 1 =>
             Quickcheck.Gen.frequency (pure RegExp.EmptySet)
               [(1, (pure RegExp.EmptySet)), (1, (pure RegExp.EmptyStr)),
                 (1,
                   (do
                     let a✝ ← Quickcheck.Arbitrary.arbitrary
                     return RegExp.Char a✝)),
                 (fuel'✝ + 1,
                   (do
                     let a✝¹ ← aux_arb fuel'✝
                     let a✝² ← aux_arb fuel'✝
                     return RegExp.App a✝¹ a✝²)),
                 (fuel'✝ + 1,
                   (do
                     let a✝³ ← aux_arb fuel'✝
                     let a✝⁴ ← aux_arb fuel'✝
                     return RegExp.Union a✝³ a✝⁴)),
                 (fuel'✝ + 1,
                   (do
                     let a✝⁵ ← aux_arb fuel'✝
                     return RegExp.Star a✝⁵))]
         fun fuel✝ => aux_arb fuel✝
     end,
     instance : Quickcheck.ArbitraryFueled✝ (@RegExp✝) :=
       ⟨arbitraryRegExp✝⟩]
-/
#guard_msgs in
deriving instance Arbitrary for RegExp

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitraryFueled`

/-- info: instArbitraryFueledRegExp -/
#guard_msgs in
#synth ArbitraryFueled RegExp

/-- info: instArbitraryOfArbitraryFueled -/
#guard_msgs in
#synth Arbitrary RegExp

/-!
Test that we can use the derived generator to find counterexamples.

We construct a faulty property, which (erroneously) states that
all regular expressions never accept any string. (Example taken from
UPenn CIS 5520 https://www.seas.upenn.edu/~cis5520/current/hw/hw04/RegExp.html)

```lean
∀ r : RegExp, neverMatchesAnyString r == True
```

(This property is faulty, since there exist regular expressions, e.g. `EmptyString`
which do match some string!)

We then test that the derived generator for `Tree`s succesfully
generates a counterexample (e.g. `EmptyString`) which refutes the property.
-/

/-- Determines whether a regular expression *never* matches any string -/
def neverMatchesAnyString (r : RegExp) : Bool :=
  match r with
  | .EmptySet => true
  | .EmptyStr | .Char _ | .Star _ => false       -- Note that `Star` can always match the empty string
  | .App r1 r2 => neverMatchesAnyString r1 || neverMatchesAnyString r2
  | .Union r1 r2 => neverMatchesAnyString r1 && neverMatchesAnyString r2

/-- A shrinker for regular expressions -/
def shrinkRegExp (r : RegExp) : List RegExp :=
  match r with
  | .EmptySet | .EmptyStr => []
  | .Char _ => [.EmptyStr]
  | .Star r' => .Star <$> shrinkRegExp r'
  | .App r1 r2 | .Union r1 r2 => shrinkRegExp r1 ++ shrinkRegExp r2

/-- `Shrinkable` instance for `RegExp` -/
instance : Shrinkable RegExp where
  shrink := shrinkRegExp

/-- `SampleableExt` instance for `RegExp` -/
instance : SampleableExt RegExp :=
  SampleableExt.mkSelfContained Arbitrary.arbitrary

/-- error: Found a counter-example! -/
#guard_msgs in
#eval Testable.check (∀ r : RegExp, neverMatchesAnyString r == True)
  (cfg := {numInst := 10, maxSize := 5, quiet := true})
