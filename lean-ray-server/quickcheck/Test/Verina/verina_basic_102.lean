import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_102


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def twoSum_precond (nums : Array Int) (target : Int) : Prop :=
  -- !benchmark @start precond
  nums.size > 1 ∧ ¬ List.Pairwise (fun a b => a + b ≠ target) nums.toList
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def twoSum (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) : (Nat × Nat) :=
  -- !benchmark @start code
  let n := nums.size
  let rec outer (i : Nat) : Option (Nat × Nat) :=
    if i < n - 1 then
      let rec inner (j : Nat) : Option (Nat × Nat) :=
        if j < n then
          if nums[i]! + nums[j]! = target then
            some (i, j)
          else
            inner (j + 1)
        else
          none
      match inner (i + 1) with
      | some pair => some pair
      | none      => outer (i + 1)
    else
      none
  match outer 0 with
  | some pair => pair
  | none      => panic "twoSum: no solution found"
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def twoSum_postcond (nums : Array Int) (target : Int) (result: (Nat × Nat)) (h_precond : twoSum_precond (nums) (target)) :=
  -- !benchmark @start postcond
  let (i, j) := result
  -- two sum holds
  i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target ∧
  -- i must be the first i
  List.Pairwise (fun a b => a + b ≠ target) (nums.toList.take i) ∧
  List.all (nums.toList.take i) (fun a => List.all (nums.toList.drop i) (fun b => a + b ≠ target) ) ∧
  -- j must be the first j
  List.all (nums.toList.drop (j + 1)) (fun a => a + nums[j]! ≠ target)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux

-- set_option trace.quickcheck.split true
-- set_option trace.quickcheck.safenorm true
set_option maxHeartbeats 0 in
theorem twoSum_spec_satisfied (nums: Array Int) (target: Int) (h_precond : twoSum_precond (nums) (target)) :
    twoSum_postcond (nums) (target) (twoSum (nums) (target) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold twoSum_postcond
  quickcheck (config := { Quickcheck.Configuration.adaptive with enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_102
