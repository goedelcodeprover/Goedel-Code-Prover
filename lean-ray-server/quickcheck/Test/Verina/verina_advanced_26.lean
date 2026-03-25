import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_26


-- !benchmark @start solution_aux
def digitToLetters (c : Char) : List Char :=
  match c with
  | '2' => ['a', 'b', 'c']
  | '3' => ['d', 'e', 'f']
  | '4' => ['g', 'h', 'i']
  | '5' => ['j', 'k', 'l']
  | '6' => ['m', 'n', 'o']
  | '7' => ['p', 'q', 'r', 's']
  | '8' => ['t', 'u', 'v']
  | '9' => ['w', 'x', 'y', 'z']
  | _ => []
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def letterCombinations_precond (digits : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
-- !benchmark @end code_aux


def letterCombinations (digits : String) (h_precond : letterCombinations_precond (digits)) : List String :=
  -- !benchmark @start code
  let chars := digits.toList
  go chars
  where
    go : List Char → List String
    | [] => []
    | (d :: ds) =>
      let restCombinations := go ds
      let currentLetters := digitToLetters d
      match restCombinations with
      | [] => currentLetters.map (λ c => String.singleton c)
      | _ => currentLetters.flatMap (λ c => restCombinations.map (λ s => String.singleton c ++ s))
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def letterCombinations_postcond (digits : String) (result: List String) (h_precond : letterCombinations_precond (digits)) : Prop :=
  -- !benchmark @start postcond
  if digits.isEmpty then
    result = []
  else if digits.toList.any (λ c => ¬(c ∈ ['2','3','4','5','6','7','8','9'])) then
    result = []
  else
    let expected := digits.toList.map digitToLetters |>.foldl (λ acc ls => acc.flatMap (λ s => ls.map (λ c => s ++ String.singleton c)) ) [""]
    result.length = expected.length ∧ result.all (λ s => s ∈ expected) ∧ expected.all (λ s => s ∈ result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem letterCombinations_spec_satisfied (digits: String) (h_precond : letterCombinations_precond (digits)) :
    letterCombinations_postcond (digits) (letterCombinations (digits) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_26
