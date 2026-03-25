import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_22


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def isPeakValley_precond (lst : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isPeakValley (lst : List Int) (h_precond : isPeakValley_precond (lst)) : Bool :=
  -- !benchmark @start code
  let rec aux (l : List Int) (increasing : Bool) (startedDecreasing : Bool) : Bool :=
    match l with
    | x :: y :: rest =>
      if x < y then
        if startedDecreasing then false
        else aux (y :: rest) true startedDecreasing
      else if x > y then
        if increasing then aux (y :: rest) increasing true
        else false
      else false
    | _ => increasing && startedDecreasing
  aux lst false false
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isPeakValley_postcond (lst : List Int) (result: Bool) (h_precond : isPeakValley_precond (lst)) : Prop :=
  -- !benchmark @start postcond
  let len := lst.length
  let validPeaks :=
    List.range len |>.filter (fun p =>
      1 ≤ p ∧ p < len - 1 ∧

      -- check strictly increasing before peak
      (List.range p).all (fun i =>
        lst[i]! < lst[i + 1]!
      ) ∧

      -- check strictly decreasing after peak
      (List.range (len - 1 - p)).all (fun i =>
        lst[p + i]! > lst[p + i + 1]!
      )
    )
  (validPeaks != [] → result) ∧
  (validPeaks.length = 0 → ¬ result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isPeakValley_spec_satisfied (lst: List Int) (h_precond : isPeakValley_precond (lst)) :
    isPeakValley_postcond (lst) (isPeakValley (lst) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_22
