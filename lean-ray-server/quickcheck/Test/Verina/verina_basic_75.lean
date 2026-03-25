import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_75


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def minArray_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux
def loop (a : Array Int) (i : Nat) (currentMin : Int) : Int :=
  if i < a.size then
    let newMin := if currentMin > a[i]! then a[i]! else currentMin
    loop a (i + 1) newMin
  else
    currentMin
-- !benchmark @end code_aux


def minArray (a : Array Int) (h_precond : minArray_precond (a)) : Int :=
  -- !benchmark @start code
  loop a 1 (a[0]!)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def minArray_postcond (a : Array Int) (result: Int) (h_precond : minArray_precond (a)) :=
  -- !benchmark @start postcond
  (∀ i : Nat, i < a.size → result <= a[i]!) ∧ (∃ i : Nat, i < a.size ∧ result = a[i]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem minArray_spec_satisfied (a: Array Int) (h_precond : minArray_precond (a)) :
    minArray_postcond (a) (minArray (a) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_75
