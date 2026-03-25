import Quickcheck

-- Simulate the verina_advanced_79 structure

@[reducible]
def twoSum_precond (nums : List Int) (target : Int) : Prop := True

def twoSum (nums : List Int) (target : Int) (h_precond : twoSum_precond nums target) : Option (Nat × Nat) :=
  none  -- simplified

@[reducible]
def twoSum_postcond (nums : List Int) (target : Int) (result: Option (Nat × Nat))
    (h_precond : twoSum_precond nums target) : Prop :=
  match result with
  | none => List.Pairwise (· + · ≠ target) nums
  | some (i, j) => i < j ∧ j < nums.length

-- Test 1: Can we get Decidable for the postcond?
example (nums : List Int) (target : Int) (h_precond : twoSum_precond nums target) :
    Decidable (twoSum_postcond nums target (twoSum nums target h_precond) h_precond) :=
  inferInstance

-- Test 2: Can we get Testable directly?
-- This is the key test
-- #check (inferInstance : Quickcheck.Testable
--   (∀ nums : List Int, ∀ target : Int, ∀ h_precond : twoSum_precond nums target,
--    twoSum_postcond nums target (twoSum nums target h_precond) h_precond))

-- Test 3: Without the h_precond dependency
def twoSum2 (nums : List Int) (target : Int) : Option (Nat × Nat) := none

def twoSum_postcond2 (nums : List Int) (target : Int) (result: Option (Nat × Nat)) : Prop :=
  match result with
  | none => List.Pairwise (· + · ≠ target) nums
  | some (i, j) => i < j ∧ j < nums.length

#check (inferInstance : Quickcheck.Testable
  (∀ nums : List Int, ∀ target : Int,
   twoSum_postcond2 nums target (twoSum2 nums target)))

-- Test 4: With True precondition but simpler
theorem test4 (nums: List Int) (target: Int) (h_precond : True) :
    twoSum_postcond2 nums target (twoSum2 nums target) := by
  unfold twoSum_postcond2 twoSum2
  quickcheck (config := { Quickcheck.Configuration.normal with onlyDecidable := true, enableSafeNorm := true, quiet := true })
