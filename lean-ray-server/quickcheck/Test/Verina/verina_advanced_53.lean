import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_53


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def minimumRightShifts_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  List.Nodup nums
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def minimumRightShifts (nums : List Int) (h_precond : minimumRightShifts_precond (nums)) : Int :=
  -- !benchmark @start code
  let n := nums.length
  -- base cases: empty or single element list is already sorted
  if n <= 1 then 0 else

  -- local helper function to check if a list is sorted in ascending order
  let rec isSortedAux (l : List Int) : Bool :=
    match l with
    | [] => true       -- empty list is sorted
    | [_] => true      -- single element list is sorted
    | x :: y :: xs => if x <= y then isSortedAux (y :: xs) else false -- check pairwise

  -- check if the input list is already sorted
  if isSortedAux nums then 0 else

  -- local helper function to perform a single right shift
  -- assume the list `l` is non-empty based on the initial n > 1 check
  let rightShiftOnce (l : List Int) : List Int :=
     match l.reverse with
     | [] => [] -- should not happen for n > 1
     | last :: revInit => last :: revInit.reverse -- `last` is the original last element

  -- recursive function to check subsequent shifts
  -- `shifts_count` is the number of shifts already performed to get `current_list`
  -- we are checking if `current_list` is sorted
  let rec checkShifts (shifts_count : Nat) (current_list : List Int) : Int :=
    -- base case: stop recursion if we've checked n-1 shifts (count goes from 1 to n)
    -- the original list (0 shifts) has already been checked
    if shifts_count >= n then -1
    else
      -- check if the current state is sorted
      if isSortedAux current_list then
        (shifts_count : Int) -- found it after 'shifts_count' shifts
      else
        -- recursion: increment shift count, apply next shift
        checkShifts (shifts_count + 1) (rightShiftOnce current_list)
  -- specify the decreasing measure for the termination checker: n - shifts_count
  termination_by n - shifts_count

  -- start the checking process by performing the first shift and checking subsequent states
  -- the initial list (0 shifts) hass already been checked and is not sorted
  checkShifts 1 (rightShiftOnce nums) -- start checking from the state after 1 shift
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def minimumRightShifts_postcond (nums : List Int) (result: Int) (h_precond : minimumRightShifts_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  let n := nums.length

  let isSorted (l : List Int) := List.Pairwise (· ≤ ·) l
  let rightShift (k : Nat) (l : List Int) := l.rotateRight k

  -- specification logic based on the result value
  if n <= 1 then result = 0 else -- specification for base cases

  -- case 1: a non-negative result means a solution was found
  (result ≥ 0 ∧
   -- result corresponds to a valid shift count result < n
   result < n ∧
   -- applying result shifts results in a sorted list
   isSorted (rightShift result.toNat nums) ∧
   -- result is the minimum such non-negative shift count
   (List.range result.toNat |>.all (fun j => ¬ isSorted (rightShift j nums)))
  ) ∨

  -- case 2: result is -1 means no solution exists within n shifts
  (result = -1 ∧
   -- for all possible shift counts k from 0 to n-1, the resulting list is not sorted
   (List.range n |>.all (fun k => ¬ isSorted (rightShift k nums)))
  )
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem minimumRightShifts_spec_satisfied (nums: List Int) (h_precond : minimumRightShifts_precond (nums)) :
    minimumRightShifts_postcond (nums) (minimumRightShifts (nums) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_53
