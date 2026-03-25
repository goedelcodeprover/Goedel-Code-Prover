import Quickcheck

set_option trace.quickcheck.split true
set_option trace.quickcheck.decoration true

namespace test_revert

@[reducible]
def test_postcond (result : Option (Nat × Nat)) : Prop :=
  match result with
  | none => True
  | some (i, j) => i < j ∧ (List.all [1,2,3] (fun x => x > 0))

-- Test: after manual `preprocess`, does `quickcheck` revert local variables?
theorem test_manual_preprocess (result : Option (Nat × Nat)) : test_postcond result := by
  unfold test_postcond
  preprocess
  -- There should now be 3 goals:
  -- 1. case h_1: ⊢ True
  -- 2. case h_2.left: i j : Nat ⊢ i < j
  -- 3. case h_2.right: i j : Nat ⊢ List.all ...

  -- Run `quickcheck` on each goal
  all_goals quickcheck

end test_revert
