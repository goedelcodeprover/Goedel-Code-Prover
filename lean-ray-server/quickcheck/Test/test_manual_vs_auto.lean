import Quickcheck

set_option trace.quickcheck.split true

namespace test_manual_vs_auto

@[reducible]
def test_postcond (result : Option (Nat × Nat)) : Prop :=
  match result with
  | none => True
  | some (i, j) => i < j ∧ (List.all [1,2,3] (fun x => x > 0))

-- Test 1: manual `preprocess` + `all_goals quickcheck`
theorem test_manual (result : Option (Nat × Nat)) : test_postcond result := by
  unfold test_postcond
  preprocess  -- explicit call
  all_goals quickcheck  -- explicit call

-- Test 2: `quickcheck` only (`preprocess` runs inside)
theorem test_auto (result : Option (Nat × Nat)) : test_postcond result := by
  unfold test_postcond
  quickcheck  -- calls `preprocess` internally

end test_manual_vs_auto
