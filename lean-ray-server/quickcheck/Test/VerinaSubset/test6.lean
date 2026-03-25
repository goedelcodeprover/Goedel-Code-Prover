import Quickcheck

set_option linter.unusedVariables false

section Test

@[reducible]
def twoSum_precond (nums : List Int) (target : Int) : Prop :=
  True

def twoSum (nums : List Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) : Option (Nat × Nat) :=
  let rec outer (lst : List Int) (i : Nat)
            : Option (Nat × Nat) :=
        match lst with
        | [] =>
            none
        | x :: xs =>
            let rec inner (lst' : List Int) (j : Nat)
                    : Option Nat :=
                match lst' with
                | [] =>
                    none
                | y :: ys =>
                    if x + y = target then
                        some j
                    else
                        inner ys (j + 1)
            match inner xs (i + 1) with
            | some j =>
                some (i, j)
            | none =>
                outer xs (i + 1)
        outer nums 0

@[reducible]
def twoSum_postcond (nums : List Int) (target : Int) (result: Option (Nat × Nat)) (h_precond : twoSum_precond (nums) (target)) : Prop :=
    match result with
    | none => List.Pairwise (fun x y => x + y ≠ target) nums
    | some (i, j) =>
        i < j ∧
        j < nums.length ∧
        nums[i]! + nums[j]! = target ∧
        List.Pairwise (fun a b => a + b ≠ target) (nums.take i) ∧
        ((nums.take i).all fun a => (nums.drop i).all fun b => decide (a + b ≠ target)) = true ∧
        ((nums.drop (j + 1)).all fun a => decide (a + nums[j]! ≠ target)) = true

/--
error: Found a counter-example!
-/
#guard_msgs in
theorem twoSum_spec_satisfied (nums: List Int) (target: Int) (h_precond : twoSum_precond (nums) (target)) :
    twoSum_postcond (nums) (target) (twoSum (nums) (target) h_precond) h_precond := by
    unfold twoSum_precond at h_precond
    unfold twoSum_postcond
    quickcheck (config := { Quickcheck.Configuration.extensive with quiet := true, randomSeed := some 42 })

end Test
