import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_71


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def LongestCommonPrefix_precond (str1 : List Char) (str2 : List Char) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def LongestCommonPrefix (str1 : List Char) (str2 : List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) : List Char :=
  -- !benchmark @start code
  let minLength := Nat.min str1.length str2.length
  let rec aux (idx : Nat) (acc : List Char) : List Char :=
    if idx < minLength then
      match str1[idx]?, str2[idx]? with
      | some c1, some c2 =>
          if c1 ≠ c2 then acc
          else aux (idx + 1) (acc ++ [c1])
      | _, _ => acc
    else acc
  aux 0 []
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def LongestCommonPrefix_postcond (str1 : List Char) (str2 : List Char) (result: List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) :=
  -- !benchmark @start postcond
  (result.length ≤ str1.length) ∧ (result = str1.take result.length) ∧
  (result.length ≤ str2.length) ∧ (result = str2.take result.length) ∧
  (result.length = str1.length ∨ result.length = str2.length ∨
    (str1[result.length]? ≠ str2[result.length]?))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem LongestCommonPrefix_spec_satisfied (str1: List Char) (str2: List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) :
    LongestCommonPrefix_postcond (str1) (str2) (LongestCommonPrefix (str1) (str2) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_71
