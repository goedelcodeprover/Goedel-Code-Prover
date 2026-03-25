import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_103


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def UpdateElements_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size ≥ 8
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def UpdateElements (a : Array Int) (h_precond : UpdateElements_precond (a)) : Array Int :=
  -- !benchmark @start code
  let a1 := a.set! 4 ((a[4]!) + 3)
  let a2 := a1.set! 7 516
  a2
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def UpdateElements_postcond (a : Array Int) (result: Array Int) (h_precond : UpdateElements_precond (a)) :=
  -- !benchmark @start postcond
  result[4]! = (a[4]!) + 3 ∧
  result[7]! = 516 ∧
  (∀ i, i < a.size → i ≠ 4 → i ≠ 7 → result[i]! = a[i]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem UpdateElements_spec_satisfied (a: Array Int) (h_precond : UpdateElements_precond (a)) :
    UpdateElements_postcond (a) (UpdateElements (a) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_103
