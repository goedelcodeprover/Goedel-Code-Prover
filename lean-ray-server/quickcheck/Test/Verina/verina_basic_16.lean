import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_16


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def replaceChars_precond (s : String) (oldChar : Char) (newChar : Char) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def replaceChars (s : String) (oldChar : Char) (newChar : Char) (h_precond : replaceChars_precond (s) (oldChar) (newChar)) : String :=
  -- !benchmark @start code
  let cs := s.toList
  let cs' := cs.map (fun c => if c = oldChar then newChar else c)
  String.mk cs'
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def replaceChars_postcond (s : String) (oldChar : Char) (newChar : Char) (result: String) (h_precond : replaceChars_precond (s) (oldChar) (newChar)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  let cs' := result.toList
  result.length = s.length ∧
  (∀ i, i < cs.length →
    (cs[i]! = oldChar → cs'[i]! = newChar) ∧
    (cs[i]! ≠ oldChar → cs'[i]! = cs[i]!))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem replaceChars_spec_satisfied (s: String) (oldChar: Char) (newChar: Char) (h_precond : replaceChars_precond (s) (oldChar) (newChar)) :
    replaceChars_postcond (s) (oldChar) (newChar) (replaceChars (s) (oldChar) (newChar) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_16
