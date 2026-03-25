import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_97


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def TestArrayElements_precond (a : Array Int) (j : Nat) : Prop :=
  -- !benchmark @start precond
  j < a.size
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def TestArrayElements (a : Array Int) (j : Nat) (h_precond : TestArrayElements_precond (a) (j)) : Array Int :=
  -- !benchmark @start code
  a.set! j 60
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def TestArrayElements_postcond (a : Array Int) (j : Nat) (result: Array Int) (h_precond : TestArrayElements_precond (a) (j)) :=
  -- !benchmark @start postcond
  (result[j]! = 60) ∧ (∀ k, k < a.size → k ≠ j → result[k]! = a[k]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem TestArrayElements_spec_satisfied (a: Array Int) (j: Nat) (h_precond : TestArrayElements_precond (a) (j)) :
    TestArrayElements_postcond (a) (j) (TestArrayElements (a) (j) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_97
