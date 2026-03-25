import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_6


-- !benchmark @start solution_aux
def toLower (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'Z' then
    Char.ofNat (Char.toNat c + 32)
  else
    c

def normalize_str (s : String) : List Char :=
  s.data.map toLower
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def allVowels_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def allVowels (s : String) (h_precond : allVowels_precond (s)) : Bool :=
  -- !benchmark @start code
  let chars := normalize_str s
  let vowelSet := ['a', 'e', 'i', 'o', 'u']
  vowelSet.all (fun v => chars.contains v)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def allVowels_postcond (s : String) (result: Bool) (h_precond : allVowels_precond (s)) : Prop :=
  -- !benchmark @start postcond
  let chars := normalize_str s
  (result ↔ List.all ['a', 'e', 'i', 'o', 'u'] (fun v => chars.contains v))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem allVowels_spec_satisfied (s: String) (h_precond : allVowels_precond (s)) :
    allVowels_postcond (s) (allVowels (s) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_6
