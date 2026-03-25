import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_4


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def kthElement_precond (arr : Array Int) (k : Nat) : Prop :=
  -- !benchmark @start precond
  k ≥ 1 ∧ k ≤ arr.size
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def kthElement (arr : Array Int) (k : Nat) (h_precond : kthElement_precond (arr) (k)) : Int :=
  -- !benchmark @start code
  arr[k - 1]!
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def kthElement_postcond (arr : Array Int) (k : Nat) (result: Int) (h_precond : kthElement_precond (arr) (k)) :=
  -- !benchmark @start postcond
  arr.any (fun x => x = result ∧ x = arr[k - 1]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem kthElement_spec_satisfied (arr: Array Int) (k: Nat) (h_precond : kthElement_precond (arr) (k)) :
    kthElement_postcond (arr) (k) (kthElement (arr) (k) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_4
