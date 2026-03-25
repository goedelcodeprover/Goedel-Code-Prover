import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_29


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def removeElement_precond (s : Array Int) (k : Nat) : Prop :=
  -- !benchmark @start precond
  k < s.size
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def removeElement (s : Array Int) (k : Nat) (h_precond : removeElement_precond (s) (k)) : Array Int :=
  -- !benchmark @start code
  s.eraseIdx! k
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def removeElement_postcond (s : Array Int) (k : Nat) (result: Array Int) (h_precond : removeElement_precond (s) (k)) :=
  -- !benchmark @start postcond
  result.size = s.size - 1 ∧
  (∀ i, i < k → result[i]! = s[i]!) ∧
  (∀ i, i < result.size → i ≥ k → result[i]! = s[i + 1]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem removeElement_spec_satisfied (s: Array Int) (k: Nat) (h_precond : removeElement_precond (s) (k)) :
    removeElement_postcond (s) (k) (removeElement (s) (k) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_29
