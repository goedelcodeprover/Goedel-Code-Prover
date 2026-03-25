import Quickcheck

set_option maxHeartbeats 0



@[reducible, simp]
def findSmallest_precond (s : Array Nat) : Prop :=
  True

def findSmallest (s : Array Nat) (h_precond : findSmallest_precond (s)) : Option Nat :=
  s.toList.min?

@[reducible, simp]
def findSmallest_postcond (s : Array Nat) (result: Option Nat) (h_precond : findSmallest_precond (s)) :=
  let xs := s.toList
  match result with
  | none => xs = []
  | some r => r ∈ xs ∧ (∀ x, x ∈ xs → r ≤ x)

theorem findSmallest_spec_satisfied (s: Array Nat) (h_precond : findSmallest_precond (s)) :
    findSmallest_postcond (s) (findSmallest (s) h_precond) h_precond := by
  unfold findSmallest_postcond
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })
