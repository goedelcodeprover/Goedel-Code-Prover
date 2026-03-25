import Quickcheck.Arbitrary
import Quickcheck.DeriveArbitrary
import Quickcheck.Attr
import Quickcheck.Testable

open Quickcheck Gen

set_option guard_msgs.diff true

/-!

To test whether the derived generator can handle `structure`s with named fields,
we define a dummy `structure`:

```lean
structure Foo where
  stringField : String
  boolField : Bool
  natField : Nat
```

To test whether the derived generator finds counterexamples,
we create a faulty property:

```lean
∀ foo : Foo, foo.stringField.isEmpty || !foo.boolField || foo.natField == 0)
```

The derived generator should be able to generate inhabitants of `Foo`
where `stringField` is non-empty, where `boolField` is false
and `natField` is non-zero.

-/

/-- Dummy `structure` with named fields -/
structure Foo where
  stringField : String
  boolField : Bool
  natField : Nat
  deriving Repr

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitraryFueled`
set_option trace.quickcheck.deriving.arbitrary true in
/--
trace: [quickcheck.deriving.arbitrary] ⏎
    [mutual
       def arbitraryFoo✝ : Nat → Quickcheck.Gen (@Foo✝) :=
         let rec aux_arb (fuel✝ : Nat) : Quickcheck.Gen (@Foo✝) :=
           match fuel✝ with
           | Nat.zero =>
             Quickcheck.Gen.oneOfWithDefault
               (do
                 let a✝ ← Quickcheck.Arbitrary.arbitrary
                 let a✝¹ ← Quickcheck.Arbitrary.arbitrary
                 let a✝² ← Quickcheck.Arbitrary.arbitrary
                 return Foo.mk a✝ a✝¹ a✝²)
               [(do
                   let a✝ ← Quickcheck.Arbitrary.arbitrary
                   let a✝¹ ← Quickcheck.Arbitrary.arbitrary
                   let a✝² ← Quickcheck.Arbitrary.arbitrary
                   return Foo.mk a✝ a✝¹ a✝²)]
           | fuel'✝ + 1 =>
             Quickcheck.Gen.frequency
               (do
                 let a✝ ← Quickcheck.Arbitrary.arbitrary
                 let a✝¹ ← Quickcheck.Arbitrary.arbitrary
                 let a✝² ← Quickcheck.Arbitrary.arbitrary
                 return Foo.mk a✝ a✝¹ a✝²)
               [(1,
                   (do
                     let a✝ ← Quickcheck.Arbitrary.arbitrary
                     let a✝¹ ← Quickcheck.Arbitrary.arbitrary
                     let a✝² ← Quickcheck.Arbitrary.arbitrary
                     return Foo.mk a✝ a✝¹ a✝²)),
                 ]
         fun fuel✝ => aux_arb fuel✝
     end,
     instance : Quickcheck.ArbitraryFueled✝ (@Foo✝) :=
       ⟨arbitraryFoo✝⟩]
-/
#guard_msgs in
deriving instance Arbitrary for Foo

/-- info: instArbitraryFueledFoo -/
#guard_msgs in
#synth ArbitraryFueled Foo

/-- info: instArbitraryOfArbitraryFueled -/
#guard_msgs in
#synth Arbitrary Foo

/-- `Shrinkable` instance for `Foo`, which shrinks each of its constituent fields -/
instance : Shrinkable Foo where
  shrink (foo : Foo) :=
    let strings := Shrinkable.shrink foo.stringField
    let bools := Shrinkable.shrink foo.boolField
    let nats := Shrinkable.shrink foo.natField
    let zippedFields := List.zip (List.zip strings bools) nats
    (fun ((s, b), n) => Foo.mk s b n) <$> zippedFields

/-- `SampleableExt` instance for `Tree` -/
instance : SampleableExt Foo :=
  SampleableExt.mkSelfContained Arbitrary.arbitrary

/-- error: Found a counter-example! -/
#guard_msgs in
#eval Testable.check (∀ foo : Foo, foo.stringField.isEmpty || !foo.boolField || foo.natField == 0)
  (cfg := {numInst := 100, maxSize := 5, quiet := true})
