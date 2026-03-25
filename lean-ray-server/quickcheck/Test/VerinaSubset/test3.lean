import Quickcheck

set_option linter.unusedVariables false

-- C Quickcheck can now test arbitrary Prop expressions directly!
-- This example has a flaw in the proposition: l1 = [1, 0] has getLast! = 0 but l1 ≠ [0]
-- C Quickcheck correctly finds this counter-example: l1 = [1, 0], l2 = [8]

-- Using sorry since this proposition is intentionally flawed and C Quickcheck finds counter-example
def test (l1 l2 : List Nat) : Bool := l1.length > 0 ∧ l2.length > 0
  ∧ (l1.all (fun x => decide (x < 10)) = true) ∧ (l2.all (fun x => decide (x < 10)) = true)
  ∧ (l1.getLast! ≠ 0 ∨ l1 = [0])
  ∧ (l2.getLast! ≠ 0 ∨ l2 = [0])


/-- error: Found a counter-example! -/
#guard_msgs in
example (l1 l2 : List Nat) : test l1 l2 := by
  quickcheck (config := { Quickcheck.Configuration.extensive with quiet := true })


def test1 (l1 l2 : List Nat) : Bool := l1.length > 0 ∧ l2.length > 0
  ∧ (l1.all (fun x => decide (x > 10)) = true) ∧ (l2.all (fun x => decide (x = 10)) = true)
  → (l1 ≠ [0]) ∧ (l2 ≠ [0])

example (l1 l2 : List Nat) : test1 l1 l2 := by
  -- quickcheck
  quickcheck (config := { Quickcheck.Configuration.extensive with quiet := true })

def test2 (l1 l2 : List Nat) : Bool := l1.length > 0 ∧ l2.length > 0
  ∧ (l1.all (fun x => decide (x < 10)) = true) ∧ (l2.all (fun x => decide (x > 10)) = true)
  → (l1 = []) ∧ (l2 = [])

example (l1 l2 : List Nat) : test2 l1 l2 := by
  -- quickcheck
  quickcheck (config := { Quickcheck.Configuration.extensive with quiet := true, randomSeed := some 42 })

-- #eval test2 [5395] [6494, 1004]
-- #eval test [] []
