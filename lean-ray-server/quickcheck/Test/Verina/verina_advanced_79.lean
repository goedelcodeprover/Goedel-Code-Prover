import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_79


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def twoSum_precond (nums : List Int) (target : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def twoSum (nums : List Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) : Option (Nat × Nat) :=
  -- !benchmark @start code
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
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def twoSum_postcond (nums : List Int) (target : Int) (result: Option (Nat × Nat)) (h_precond : twoSum_precond (nums) (target)) : Prop :=
  -- !benchmark @start postcond
    match result with
    | none => List.Pairwise (· + · ≠ target) nums
    | some (i, j) =>
        i < j ∧
        j < nums.length ∧
        nums[i]! + nums[j]! = target ∧
        -- i must be the first i
        List.Pairwise (fun a b => a + b ≠ target) (nums.take i) ∧
        List.all (nums.take i) (fun a => List.all (nums.drop i) (fun b => a + b ≠ target) ) ∧
        -- j must be the first j
        List.all (nums.drop (j + 1)) (fun a => a + nums[j]! ≠ target)

  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux

-- set_option trace.quickcheck.safenorm true in
-- set_option trace.quickcheck.decoration true in
set_option maxHeartbeats 0
set_option synthInstance.maxSize 5120
theorem twoSum_spec_satisfied (nums: List Int) (target: Int) (h_precond : twoSum_precond (nums) (target)) :
    twoSum_postcond (nums) (target) (twoSum (nums) (target) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold twoSum_postcond
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })
  -- quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_79
