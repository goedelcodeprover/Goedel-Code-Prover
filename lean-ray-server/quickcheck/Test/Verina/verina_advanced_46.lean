import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_46


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def maxSubarraySum_precond (numbers : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def maxSubarraySum (numbers : List Int) (h_precond : maxSubarraySum_precond (numbers)) : Int :=
  -- !benchmark @start code
  let rec isAllNegative : List Int → Bool
    | [] => true
    | x :: xs => if x >= 0 then false else isAllNegative xs

  let rec findMaxProduct : List Int → Int → Int → Int
    | [], currMax, _ => currMax
    | [x], currMax, _ => max currMax x
    | x :: y :: rest, currMax, currSum =>
        let newSum := max y (currSum + y)
        let newMax := max currMax newSum
        findMaxProduct (y :: rest) newMax newSum

  let handleList : List Int → Nat
    | [] => 0
    | xs =>
        if isAllNegative xs then
          0
        else
          match xs with
          | [] => 0
          | x :: rest =>
              let initialMax := max 0 x
              let startSum := max 0 x
              let result := findMaxProduct (x :: rest) initialMax startSum
              result.toNat

  handleList numbers
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def maxSubarraySum_postcond (numbers : List Int) (result: Int) (h_precond : maxSubarraySum_precond (numbers)) : Prop :=
  -- !benchmark @start postcond
  let subArraySums :=
    List.range (numbers.length + 1) |>.flatMap (fun start =>
      List.range (numbers.length - start + 1) |>.map (fun len =>
        numbers.drop start |>.take len |>.sum))
  subArraySums.contains result ∧ subArraySums.all (· ≤ result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem maxSubarraySum_spec_satisfied (numbers: List Int) (h_precond : maxSubarraySum_precond (numbers)) :
    maxSubarraySum_postcond (numbers) (maxSubarraySum (numbers) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_46
