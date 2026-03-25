import Quickcheck

namespace debug_test

-- Enable all relevant traces
set_option trace.quickcheck.split true
set_option trace.quickcheck.decoration true

@[reducible]
def test_postcond (result : Option (Nat × Nat)) : Prop :=
  match result with
  | none => True
  | some (i, j) => i < j ∧ (List.all [1,2,3] (fun x => x > 0))

-- Test: after `unfold`, does `quickcheck` automatically call `preprocess` and split?
theorem test_auto_split (result : Option (Nat × Nat)) : test_postcond result := by
  unfold test_postcond
  -- `quickcheck` should call `preprocess` internally
  quickcheck (config := { Quickcheck.Configuration.fast with quiet := false })

end debug_test
