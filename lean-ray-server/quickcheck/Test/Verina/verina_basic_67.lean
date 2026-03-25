import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_67


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def IsPalindrome_precond (x : List Char) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def isPalindromeHelper (x : List Char) (i j : Nat) : Bool :=
  if i < j then
    match x[i]?, x[j]? with
    | some ci, some cj =>
      if ci ≠ cj then false else isPalindromeHelper x (i + 1) (j - 1)
    | _, _ => false  -- This case should not occur due to valid indices
  else true
-- !benchmark @end code_aux


def IsPalindrome (x : List Char) (h_precond : IsPalindrome_precond (x)) : Bool :=
  -- !benchmark @start code
  if x.length = 0 then true else isPalindromeHelper x 0 (x.length - 1)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def IsPalindrome_postcond (x : List Char) (result: Bool) (h_precond : IsPalindrome_precond (x)) :=
  -- !benchmark @start postcond
  result ↔ ∀ i : Nat, i < x.length → (x[i]! = x[x.length - i - 1]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem IsPalindrome_spec_satisfied (x: List Char) (h_precond : IsPalindrome_precond (x)) :
    IsPalindrome_postcond (x) (IsPalindrome (x) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_67
