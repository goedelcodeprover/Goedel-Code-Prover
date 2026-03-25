import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_31


-- !benchmark @start solution_aux
def isLowerCase (c : Char) : Bool :=
  'a' ≤ c ∧ c ≤ 'z'

def shiftMinus32 (c : Char) : Char :=
  Char.ofNat ((c.toNat - 32) % 128)
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def toUppercase_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def toUppercase (s : String) (h_precond : toUppercase_precond (s)) : String :=
  -- !benchmark @start code
  let cs := s.toList
  let cs' := cs.map (fun c => if isLowerCase c then shiftMinus32 c else c)
  String.mk cs'
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def toUppercase_postcond (s : String) (result: String) (h_precond : toUppercase_precond (s)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  let cs' := result.toList
  (result.length = s.length) ∧
  (∀ i, i < s.length →
    (isLowerCase cs[i]! → cs'[i]! = shiftMinus32 cs[i]!) ∧
    (¬isLowerCase cs[i]! → cs'[i]! = cs[i]!))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem toUppercase_spec_satisfied (s: String) (h_precond : toUppercase_precond (s)) :
    toUppercase_postcond (s) (toUppercase (s) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_31
