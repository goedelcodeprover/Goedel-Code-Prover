import Quickcheck

def testFunc (x : Nat) : Option Nat :=
  if x > 0 then some x else none

-- casesOn form works with quickcheck:
example : forall x, (testFunc x).casesOn True (fun y => y > 0) := by
  quickcheck

-- match form fails:
-- example : forall x, match testFunc x with | none => True | some y => y > 0 := by
--   quickcheck  -- This fails
