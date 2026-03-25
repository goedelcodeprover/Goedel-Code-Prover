import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_36


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def majorityElement_precond (xs : List Nat) : Prop :=
  -- !benchmark @start precond
  xs.length > 0 ∧ xs.any (fun x => xs.count x > xs.length / 2)
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def majorityElement (xs : List Nat) (h_precond : majorityElement_precond (xs)) : Nat :=
  -- !benchmark @start code
  let rec countOccurrences (target : Nat) (lst : List Nat) : Nat :=
    match lst with
    | [] => 0
    | y :: ys =>
      if y = target then 1 + countOccurrences target ys
      else countOccurrences target ys

  let rec findCandidate (lst : List Nat) (candidate : Option Nat) (count : Nat) : Nat :=
    match lst with
    | [] =>
      match candidate with
      | some c => c
      | none => 0 -- unreachable since we assume majority element exists
    | x :: xs =>
      match candidate with
      | some c =>
        if x = c then
          findCandidate xs (some c) (count + 1)
        else if count = 0 then
          findCandidate xs (some x) 1
        else
          findCandidate xs (some c) (count - 1)
      | none =>
        findCandidate xs (some x) 1

  let cand := findCandidate xs none 0
  cand
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def majorityElement_postcond (xs : List Nat) (result: Nat) (h_precond : majorityElement_precond (xs)) : Prop :=
  -- !benchmark @start postcond
  let count := xs.count result
  count > xs.length / 2
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem majorityElement_spec_satisfied (xs: List Nat) (h_precond : majorityElement_precond (xs)) :
    majorityElement_postcond (xs) (majorityElement (xs) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_36
