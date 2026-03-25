import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_17


-- !benchmark @start solution_aux
def isUpperCase (c : Char) : Bool :=
  'A' ≤ c ∧ c ≤ 'Z'

def shift32 (c : Char) : Char :=
  Char.ofNat (c.toNat + 32)
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def toLowercase_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def toLowercase (s : String) (h_precond : toLowercase_precond (s)) : String :=
  -- !benchmark @start code
  let cs := s.toList
  let cs' := cs.map (fun c => if isUpperCase c then shift32 c else c)
  String.mk cs'
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def toLowercase_postcond (s : String) (result: String) (h_precond : toLowercase_precond (s)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  let cs' := result.toList
  (result.length = s.length) ∧
  (∀ i : Nat, i < s.length →
    (isUpperCase cs[i]! → cs'[i]! = shift32 cs[i]!) ∧
    (¬isUpperCase cs[i]! → cs'[i]! = cs[i]!))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem toLowercase_spec_satisfied (s: String) (h_precond : toLowercase_precond (s)) :
    toLowercase_postcond (s) (toLowercase (s) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_17
