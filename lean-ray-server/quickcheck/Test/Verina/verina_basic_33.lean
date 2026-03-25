import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_33


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def smallestMissingNumber_precond (s : List Nat) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) s
  -- !benchmark @end precond

-- !benchmark @start code_aux

-- !benchmark @end code_aux


def smallestMissingNumber (s : List Nat) (h_precond : smallestMissingNumber_precond (s)) : Nat :=
  -- !benchmark @start code
  let rec findMissing (v : Nat) (l : List Nat) : Nat :=
    match l with
    | [] => v
    | x :: xs =>
      if x > v then v
      else if x = v then findMissing (v + 1) xs
      else findMissing v xs
  findMissing 0 s
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def smallestMissingNumber_postcond (s : List Nat) (result: Nat) (h_precond : smallestMissingNumber_precond (s)) :=
  -- !benchmark @start postcond
  ¬ List.elem result s ∧ (∀ k : Nat, k < result → List.elem k s)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux

set_option maxHeartbeats 0
theorem smallestMissingNumber_spec_satisfied (s: List Nat) (h_precond : smallestMissingNumber_precond (s)) :
    smallestMissingNumber_postcond (s) (smallestMissingNumber (s) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_33
