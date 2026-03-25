import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_54


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def missingNumber_precond (nums : List Nat) : Prop :=
  -- !benchmark @start precond
  nums.all (fun x => x ≤ nums.length) ∧ List.Nodup nums
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def missingNumber (nums : List Nat) (h_precond : missingNumber_precond (nums)) : Nat :=
  -- !benchmark @start code
  let n := nums.length
  let expectedSum := (n * (n + 1)) / 2
  let actualSum := nums.foldl (· + ·) 0
  expectedSum - actualSum
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def missingNumber_postcond (nums : List Nat) (result: Nat) (h_precond : missingNumber_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  let n := nums.length
  (result ∈ List.range (n + 1)) ∧
  ¬(result ∈ nums) ∧
  ∀ x, (x ∈ List.range (n + 1)) → x ≠ result → x ∈ nums
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem missingNumber_spec_satisfied (nums: List Nat) (h_precond : missingNumber_precond (nums)) :
    missingNumber_postcond (nums) (missingNumber (nums) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_54
