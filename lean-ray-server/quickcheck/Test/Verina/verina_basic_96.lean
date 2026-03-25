import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_96


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def SwapSimultaneous_precond (X : Int) (Y : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def SwapSimultaneous (X : Int) (Y : Int) (h_precond : SwapSimultaneous_precond (X) (Y)) : Int × Int :=
  -- !benchmark @start code
  (Y, X)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def SwapSimultaneous_postcond (X : Int) (Y : Int) (result: Int × Int) (h_precond : SwapSimultaneous_precond (X) (Y)) :=
  -- !benchmark @start postcond
  result.1 = Y ∧ result.2 = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem SwapSimultaneous_spec_satisfied (X: Int) (Y: Int) (h_precond : SwapSimultaneous_precond (X) (Y)) :
    SwapSimultaneous_postcond (X) (Y) (SwapSimultaneous (X) (Y) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_96
