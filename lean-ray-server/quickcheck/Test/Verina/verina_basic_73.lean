import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_73


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Match_precond (s : String) (p : String) : Prop :=
  -- !benchmark @start precond
  s.toList.length = p.toList.length
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def Match (s : String) (p : String) (h_precond : Match_precond (s) (p)) : Bool :=
  -- !benchmark @start code
  let sList := s.toList
  let pList := p.toList
  let rec loop (i : Nat) : Bool :=
    if i < sList.length then
      if (sList[i]! ≠ pList[i]!) ∧ (pList[i]! ≠ '?') then false
      else loop (i + 1)
    else true
  loop 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def Match_postcond (s : String) (p : String) (result: Bool) (h_precond : Match_precond (s) (p)) :=
  -- !benchmark @start postcond
  (result = true ↔ ∀ n : Nat, n < s.toList.length → ((s.toList[n]! = p.toList[n]!) ∨ (p.toList[n]! = '?')))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem Match_spec_satisfied (s: String) (p: String) (h_precond : Match_precond (s) (p)) :
    Match_postcond (s) (p) (Match (s) (p) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_73
