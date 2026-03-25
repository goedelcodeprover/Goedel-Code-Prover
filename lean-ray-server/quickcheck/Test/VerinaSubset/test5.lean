import Quickcheck

set_option linter.unusedVariables false

def average (xs : List Nat) : Nat :=
  xs.getLast!

def listMax (xs : List Nat) : Nat :=
  xs.foldl max 0

/--
error: [Quickcheck Safety Error]
Partial function `List.getLast!` can panic.
Safe alternative: List.getLast?

To fix: wrap partial functions with guards like `if l.length > 0 then ... else True`
Or disable SafeGuard: quickcheck (config := { enableSafeGuard := false })
-/
#guard_msgs in
theorem average_spec : ∀ xs, average xs ≤ listMax xs := by
  quickcheck (config := { Quickcheck.Configuration.extensive with quiet := true, randomSeed := some 42 })
