import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_52


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def minOperations_precond (nums : List Nat) (k : Nat) : Prop :=
  -- !benchmark @start precond
  let target_nums := (List.range k).map (· + 1)
  target_nums.all (fun n => List.elem n nums)
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def minOperations (nums : List Nat) (k : Nat) (h_precond : minOperations_precond (nums) (k)) : Nat :=
  -- !benchmark @start code
  -- edge case k=0, requires 0 operations
  if k == 0 then 0 else
  -- recursive helper function
  let rec loop (remaining : List Nat) (collected : List Nat) (collected_count : Nat) (ops : Nat) : Nat :=
    match remaining with
    | [] => ops -- base case
    | head :: tail =>
      let ops' := ops + 1
      -- check if the element is relevant (1 <= head <= k) and not already collected
      -- use a list `collected` to keep track of unique numbers found so far
      if head > 0 && head <= k && !(List.elem head collected) then
          let collected' := head :: collected -- add new unique element to our tracking list
          let collected_count' := collected_count + 1
          if collected_count' == k then
            ops' -- found all k distinct required numbers
          else
            loop tail collected' collected_count' ops' -- continue searching, count increased
      else
        -- element is irrelevant (> k), zero/negative, or a duplicate (already in `collected`)
        loop tail collected collected_count ops' -- continue searching, count not increased
  -- start the loop, initially empty collection, 0 count, 0 operations
  loop nums.reverse [] 0 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def minOperations_postcond (nums : List Nat) (k : Nat) (result: Nat) (h_precond : minOperations_precond (nums) (k)) : Prop :=
  -- !benchmark @start postcond
  -- define the list of elements processed after `result` operations
  let processed := (nums.reverse).take result
  -- define the target numbers to collect (1 to k)
  let target_nums := (List.range k).map (· + 1)

  -- condition 1: All target numbers must be present in the processed elements
  let collected_all := target_nums.all (fun n => List.elem n processed)

  -- condition 2: `result` must be the minimum number of operations.
  -- This means either result is 0 (which implies k must be 0 as target_nums would be empty)
  -- or result > 0, and taking one less operation (result - 1) is not sufficient
  let is_minimal :=
    if result > 0 then
      -- if one fewer element is taken, not all target numbers should be present
      let processed_minus_one := (nums.reverse).take (result - 1)
      ¬ (target_nums.all (fun n => List.elem n processed_minus_one))
    else
      -- if result is 0, it can only be minimal if k is 0 (no targets required)
      -- So if k=0, `collected_all` is true. If result=0, this condition `k==0` ensures minimality.
      k == 0

  -- overall specification:
  collected_all ∧ is_minimal
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem minOperations_spec_satisfied (nums: List Nat) (k: Nat) (h_precond : minOperations_precond (nums) (k)) :
    minOperations_postcond (nums) (k) (minOperations (nums) (k) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_52
