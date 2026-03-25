import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_10


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isGreater_precond (n : Int) (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isGreater (n : Int) (a : Array Int) (h_precond : isGreater_precond (n) (a)) : Bool :=
  -- !benchmark @start code
  a.all fun x => n > x
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isGreater_postcond (n : Int) (a : Array Int) (result: Bool) (h_precond : isGreater_precond (n) (a)) :=
  -- !benchmark @start postcond
  (∀ i, (hi : i < a.size) → n > a[i]) ↔ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isGreater_spec_satisfied (n: Int) (a: Array Int) (h_precond : isGreater_precond (n) (a)) :
    isGreater_postcond (n) (a) (isGreater (n) (a) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_10
