import Quickcheck.Attr
import Quickcheck.Arbitrary
import Quickcheck.DeriveArbitrary
import Quickcheck.Testable

open Quickcheck Gen

set_option guard_msgs.diff true

/-- Binary operators for the NKI language,
    adapted from https://github.com/leanprover/KLR/blob/main/KLR/NKI/Basic.lean -/
inductive BinOp where
  -- logical
  | land | lor
  -- comparison
  | eq | ne | lt | le | gt | ge
  -- arithmetic
  | add | sub | mul | div | mod | pow | floor
  -- bitwise
  | lshift | rshift | or | xor | and
  deriving Repr

set_option trace.quickcheck.deriving.arbitrary true in
/--
trace: [quickcheck.deriving.arbitrary] ⏎
    [mutual
       def arbitraryBinOp✝ : Nat → Quickcheck.Gen (@BinOp✝) :=
         let rec aux_arb (fuel✝ : Nat) : Quickcheck.Gen (@BinOp✝) :=
           match fuel✝ with
           | Nat.zero =>
             Quickcheck.Gen.oneOfWithDefault (pure BinOp.land)
               [(pure BinOp.land), (pure BinOp.lor), (pure BinOp.eq), (pure BinOp.ne), (pure BinOp.lt), (pure BinOp.le),
                 (pure BinOp.gt), (pure BinOp.ge), (pure BinOp.add), (pure BinOp.sub), (pure BinOp.mul),
                 (pure BinOp.div), (pure BinOp.mod), (pure BinOp.pow), (pure BinOp.floor), (pure BinOp.lshift),
                 (pure BinOp.rshift), (pure BinOp.or), (pure BinOp.xor), (pure BinOp.and)]
           | fuel'✝ + 1 =>
             Quickcheck.Gen.frequency (pure BinOp.land)
               [(1, (pure BinOp.land)), (1, (pure BinOp.lor)), (1, (pure BinOp.eq)), (1, (pure BinOp.ne)),
                 (1, (pure BinOp.lt)), (1, (pure BinOp.le)), (1, (pure BinOp.gt)), (1, (pure BinOp.ge)),
                 (1, (pure BinOp.add)), (1, (pure BinOp.sub)), (1, (pure BinOp.mul)), (1, (pure BinOp.div)),
                 (1, (pure BinOp.mod)), (1, (pure BinOp.pow)), (1, (pure BinOp.floor)), (1, (pure BinOp.lshift)),
                 (1, (pure BinOp.rshift)), (1, (pure BinOp.or)), (1, (pure BinOp.xor)), (1, (pure BinOp.and)), ]
         fun fuel✝ => aux_arb fuel✝
     end,
     instance : Quickcheck.ArbitraryFueled✝ (@BinOp✝) :=
       ⟨arbitraryBinOp✝⟩]
-/
#guard_msgs in
deriving instance Arbitrary for BinOp

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitraryFueled`

/-- info: instArbitraryFueledBinOp -/
#guard_msgs in
#synth ArbitraryFueled BinOp

/-- info: instArbitraryOfArbitraryFueled -/
#guard_msgs in
#synth Arbitrary BinOp

/-- Trivial `Shrinkable` instance for `BinOp`s -/
instance : Shrinkable BinOp where
  shrink := fun _ => []

/-- `SampleableExt` instance for `BinOp` -/
instance : SampleableExt BinOp :=
  SampleableExt.mkSelfContained Arbitrary.arbitrary

-- To test whether the derived generator can generate counterexamples,
-- we state an (erroneous) property that states that all binary operators
-- are logical operators, and see if the generator can refute this property.

/-- Determines whether a `BinOp` is a logical operation -/
def isLogicalOp (op : BinOp) : Bool :=
  match op with
  | .land | .lor => true
  | _ => false

/-- error: Found a counter-example! -/
#guard_msgs in
#eval Testable.check (∀ op : BinOp, isLogicalOp op)
  (cfg := {numInst := 10, maxSize := 5, quiet := true})
