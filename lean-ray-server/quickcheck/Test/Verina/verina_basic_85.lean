import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_85


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def reverse_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def reverse_core (arr : Array Int) (i : Nat) : Array Int :=
  if i < arr.size / 2 then
    let j := arr.size - 1 - i
    let temp := arr[i]!
    let arr' := arr.set! i (arr[j]!)
    let arr'' := arr'.set! j temp
    reverse_core arr'' (i + 1)
  else
    arr
-- !benchmark @end code_aux


def reverse (a : Array Int) (h_precond : reverse_precond (a)) : Array Int :=
  -- !benchmark @start code
  reverse_core a 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def reverse_postcond (a : Array Int) (result: Array Int) (h_precond : reverse_precond (a)) :=
  -- !benchmark @start postcond
  (result.size = a.size) ∧ (∀ i : Nat, i < a.size → result[i]! = a[a.size - 1 - i]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem reverse_spec_satisfied (a: Array Int) (h_precond : reverse_precond (a)) :
    reverse_postcond (a) (reverse (a) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_85
