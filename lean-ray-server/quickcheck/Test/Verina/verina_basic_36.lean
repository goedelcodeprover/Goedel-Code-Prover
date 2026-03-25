import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_36


-- !benchmark @start solution_aux
def isSpaceCommaDot (c : Char) : Bool :=
  if c = ' ' then true
  else if c = ',' then true
  else if c = '.' then true
  else false
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def replaceWithColon_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def replaceWithColon (s : String) (h_precond : replaceWithColon_precond (s)) : String :=
  -- !benchmark @start code
  let cs := s.toList
  let cs' := cs.map (fun c => if isSpaceCommaDot c then ':' else c)
  String.mk cs'
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def replaceWithColon_postcond (s : String) (result: String) (h_precond : replaceWithColon_precond (s)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  let cs' := result.toList
  result.length = s.length ∧
  (∀ i, i < s.length →
    (isSpaceCommaDot cs[i]! → cs'[i]! = ':') ∧
    (¬isSpaceCommaDot cs[i]! → cs'[i]! = cs[i]!))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem replaceWithColon_spec_satisfied (s: String) (h_precond : replaceWithColon_precond (s)) :
    replaceWithColon_postcond (s) (replaceWithColon (s) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_36
