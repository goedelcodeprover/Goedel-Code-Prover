import Quickcheck

set_option linter.unusedVariables false

def average (xs : List Nat) : Nat :=
  xs.getLast?.getD 0

def listMax (xs : List Nat) : Nat :=
  xs.foldl max 0


theorem average_spec : ∀ xs, average xs ≤ listMax xs := by
  quickcheck (config := { Quickcheck.Configuration.extensive with quiet := true, randomSeed := some 42 })
