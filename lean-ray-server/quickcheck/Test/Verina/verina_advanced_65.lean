import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_65


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def reverseString_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def reverseString (s : String) (h_precond : reverseString_precond (s)) : String :=
  -- !benchmark @start code
  let rec reverseAux (chars : List Char) (acc : List Char) : List Char :=
    match chars with
    | [] => acc
    | h::t => reverseAux t (h::acc)
  String.mk (reverseAux (s.toList) [])
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def reverseString_postcond (s : String) (result: String) (h_precond : reverseString_precond (s)) : Prop :=
  -- !benchmark @start postcond
  result.length = s.length ∧ result.toList = s.toList.reverse
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem reverseString_spec_satisfied (s: String) (h_precond : reverseString_precond (s)) :
    reverseString_postcond (s) (reverseString (s) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_65
