import Quickcheck

-- Test: Can we decide List.Pairwise with a captured variable?

-- Test 1: Simple case - should work
#check (inferInstance : Decidable (List.Pairwise (· < ·) [1, 2, 3]))

-- Test 2: With captured variable - does this work?
def testPairwiseWithCapture (target : Int) (nums : List Int) : Bool :=
  decide (List.Pairwise (fun a b => a + b ≠ target) nums)

-- Test 3: Check if DecidableRel is inferred
example (target : Int) : DecidableRel (fun (a b : Int) => a + b ≠ target) := inferInstance

-- Test 4: Check Decidable for specific Pairwise
example (target : Int) (nums : List Int) : Decidable (List.Pairwise (fun a b => a + b ≠ target) nums) :=
  inferInstance

-- Test 5: The actual pattern from verina_advanced_79
-- This is the problematic case
example (nums : List Int) (target : Int) :
    Decidable (List.Pairwise (· + · ≠ target) nums) :=
  inferInstance

-- Test 6: With Testable
#check (inferInstance : Quickcheck.Testable (∀ nums : List Int, ∀ target : Int, List.Pairwise (· + · ≠ target) nums → True))

-- Test 7: Simpler Testable check
example : True := by
  have h : ∀ nums : List Int, ∀ target : Int, Decidable (List.Pairwise (fun a b => a + b ≠ target) nums) :=
    fun _ _ => inferInstance
  trivial
