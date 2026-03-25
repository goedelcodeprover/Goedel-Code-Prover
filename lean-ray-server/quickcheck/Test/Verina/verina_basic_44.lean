import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_44


-- !benchmark @start solution_aux
def isOdd (n : Int) : Bool :=
  n % 2 == 1
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isOddAtIndexOdd_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isOddAtIndexOdd (a : Array Int) (h_precond : isOddAtIndexOdd_precond (a)) : Bool :=
  -- !benchmark @start code
  -- First create pairs of (index, value) for all elements in the array
  let indexedArray := a.mapIdx fun i x => (i, x)

  -- Check if all elements at odd indices are odd numbers
  indexedArray.all fun (i, x) => !(isOdd i) || isOdd x
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isOddAtIndexOdd_postcond (a : Array Int) (result: Bool) (h_precond : isOddAtIndexOdd_precond (a)) :=
  -- !benchmark @start postcond
  result ↔ (∀ i, (hi : i < a.size) → isOdd i → isOdd (a[i]))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isOddAtIndexOdd_spec_satisfied (a: Array Int) (h_precond : isOddAtIndexOdd_precond (a)) :
    isOddAtIndexOdd_postcond (a) (isOddAtIndexOdd (a) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_44
