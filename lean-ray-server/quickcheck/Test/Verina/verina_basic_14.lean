import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_14


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def containsZ_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def containsZ (s : String) (h_precond : containsZ_precond (s)) : Bool :=
  -- !benchmark @start code
  s.toList.any fun c => c = 'z' || c = 'Z'
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def containsZ_postcond (s : String) (result: Bool) (h_precond : containsZ_precond (s)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  (∃ x, x ∈ cs ∧ (x = 'z' ∨ x = 'Z')) ↔ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem containsZ_spec_satisfied (s: String) (h_precond : containsZ_precond (s)) :
    containsZ_postcond (s) (containsZ (s) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_14
