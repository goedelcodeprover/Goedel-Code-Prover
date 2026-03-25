import Quickcheck.Arbitrary
import Quickcheck.DeriveArbitrary
import Quickcheck.Attr
import Quickcheck.Testable

open Quickcheck

/-- A dummy `inductive` type isomorphic to the polymorphic `List` type,
    used as an example of a parameterized inductive type -/
inductive MyList (α : Type) where
  | MyNil : MyList α
  | MyCons : α → MyList α → MyList α
  deriving Repr, BEq

set_option trace.quickcheck.deriving.arbitrary true in
/--
trace: [quickcheck.deriving.arbitrary] ⏎
    [mutual
       def arbitraryMyList✝ {α✝} [Quickcheck.Arbitrary✝ α✝] : Nat → Quickcheck.Gen (@MyList✝ α✝) :=
         let rec aux_arb (fuel✝ : Nat) : Quickcheck.Gen (@MyList✝ α✝) :=
           match fuel✝ with
           | Nat.zero => Quickcheck.Gen.oneOfWithDefault (pure MyList.MyNil) [(pure MyList.MyNil)]
           | fuel'✝ + 1 =>
             Quickcheck.Gen.frequency (pure MyList.MyNil)
               [(1, (pure MyList.MyNil)),
                 (fuel'✝ + 1,
                   (do
                     let a✝ ← Quickcheck.Arbitrary.arbitrary
                     let a✝¹ ← aux_arb fuel'✝
                     return MyList.MyCons a✝ a✝¹))]
         fun fuel✝ => aux_arb fuel✝
     end,
     instance {α✝} [Quickcheck.Arbitrary✝ α✝] : Quickcheck.ArbitraryFueled✝ (@MyList✝ α✝) :=
       ⟨arbitraryMyList✝⟩]
-/
#guard_msgs in
deriving instance Arbitrary for MyList

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitraryFueled`
-- when `α` is specialized to `Nat`

/-- info: instArbitraryFueledMyListOfArbitrary -/
#guard_msgs in
#synth ArbitraryFueled (MyList Nat)

/-- info: instArbitraryOfArbitraryFueled -/
#guard_msgs in
#synth Arbitrary (MyList Nat)

-- Infrastructure for testing the derived generator

/-- Converts a `MyList` to an ordinary `List` -/
def listOfMyList (l : MyList α) : List α :=
  match l with
  | .MyNil => []
  | .MyCons x xs => x :: listOfMyList xs

/-- Converts an ordinary `List` to a `MyList` -/
def myListOfList (l : List α) : MyList α :=
  match l with
  | [] => .MyNil
  | x :: xs => .MyCons x (myListOfList xs)

/-- Trivial shrinker for `MyList α`.
    (Under the hood, this converts the `MyList` to an ordinary `List`,
    uses the default `Shrinkable` instance for `List α`, then converts it back to `MyList α`.) -/
def shrinkMyList [Shrinkable α] (myList : MyList α) : List (MyList α) :=
  let l := listOfMyList myList
  myListOfList <$> Shrinkable.shrink l

/-- `Shrinkable` instance for `MyList α` -/
instance [Shrinkable α] : Shrinkable (MyList α) where
  shrink := shrinkMyList

/- `SampleableExt` instance for `MyList α`.

   (Note that the proxy type is still `MyList α` in this instance, and not `List α`,
   since we are creating the `SampleableExt` instance using `SampleableExt.mkSelfContained`.) -/
instance [Repr α] [Shrinkable α] [Arbitrary α] : SampleableExt (MyList α) :=
  SampleableExt.mkSelfContained Arbitrary.arbitrary

/-!
To test whether the derived generator can generate counterexamples,
we create an erroneous property `∀ l : MyList Nat, reverse (reverse l) != l`,
and ask Quickcheck to falsify it.

(This property is false, since `reverse` is an involution on `List α`, and
`MyList α` is isomorphic to `List α`.)
-/

/-- Returns the elements of a `MyList α` in reverse order.

    Implementation adapted from the Haskell `List.reverse` function.
    https://hackage.haskell.org/package/base-4.17.1.0/docs/Prelude.html#v:reverse -/
def reverse (l : MyList α) : MyList α :=
  rev l .MyNil
    where
      rev (l : MyList α) (acc : MyList α) :=
        match l with
        | .MyNil => acc
        | .MyCons x xs => rev xs (.MyCons x acc)

/-- error: Found a counter-example! -/
#guard_msgs in
#eval Testable.check (∀ l : MyList Nat, reverse (reverse l) != l)
  (cfg := {numInst := 10, maxSize := 5, quiet := true})
