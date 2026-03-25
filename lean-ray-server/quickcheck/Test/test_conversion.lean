import Quickcheck

set_option maxHeartbeats 0
set_option trace.quickcheck.decoration true

-- Simple test: check that conversion works
example : ∀ (l : List Nat), (∀ d ∈ l, d < 10) → True := by
  quickcheck (config := {numInst := 10})
