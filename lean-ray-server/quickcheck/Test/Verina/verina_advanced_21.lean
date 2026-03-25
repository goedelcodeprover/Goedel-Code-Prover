import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_21


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def isPalindrome_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isPalindrome (s : String) (h_precond : isPalindrome_precond (s)) : Bool :=
  -- !benchmark @start code
  let length := s.length

if length <= 1 then
  true
else
  let arr := s.toList

  let rec checkIndices (left : Nat) (right : Nat) (chars : List Char) : Bool :=
    if left >= right then
      true
    else
      match chars[left]?, chars[right]? with
      | some cLeft, some cRight =>
        if cLeft == cRight then
          checkIndices (left + 1) (right - 1) chars
        else
          false
      | _, _ => false
  let approach1 := checkIndices 0 (length - 1) arr

  let rec reverseList (acc : List Char) (xs : List Char) : List Char :=
    match xs with
    | []      => acc
    | h :: t  => reverseList (h :: acc) t
  let reversed := reverseList [] arr
  let approach2 := (arr == reversed)

  approach1 && approach2
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isPalindrome_postcond (s : String) (result: Bool) (h_precond : isPalindrome_precond (s)) : Prop :=
  -- !benchmark @start postcond
  (result → (s.toList == s.toList.reverse)) ∧
  (¬ result → (s.toList ≠ [] ∧ s.toList != s.toList.reverse))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isPalindrome_spec_satisfied (s: String) (h_precond : isPalindrome_precond (s)) :
    isPalindrome_postcond (s) (isPalindrome (s) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_21
