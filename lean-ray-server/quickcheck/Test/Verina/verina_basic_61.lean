import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_61


-- !benchmark @start solution_aux
def isDigit (c : Char) : Bool :=
  (c ≥ '0') && (c ≤ '9')
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def allDigits_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def allDigits (s : String) (h_precond : allDigits_precond (s)) : Bool :=
  -- !benchmark @start code
  let rec loop (it : String.Iterator) : Bool :=
    if it.atEnd then
      true
    else
      if !isDigit it.curr then
        false
      else
        loop it.next
  loop s.iter
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def allDigits_postcond (s : String) (result: Bool) (h_precond : allDigits_precond (s)) :=
  -- !benchmark @start postcond
  (result = true ↔ ∀ c ∈ s.toList, isDigit c)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem allDigits_spec_satisfied (s: String) (h_precond : allDigits_precond (s)) :
    allDigits_postcond (s) (allDigits (s) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_61
