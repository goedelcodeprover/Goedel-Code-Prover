import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_66


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def reverseWords_precond (words_str : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def reverseWords (words_str : String) (h_precond : reverseWords_precond (words_str)) : String :=
  -- !benchmark @start code
  let rawWords : List String := words_str.splitOn " "
  let rec filterNonEmpty (words : List String) : List String :=
    match words with
    | [] => []
    | h :: t =>
      if h = "" then
        filterNonEmpty t
      else
        h :: filterNonEmpty t
  let filteredWords : List String := filterNonEmpty rawWords
  let revWords : List String := filteredWords.reverse
  let rec joinWithSpace (words : List String) : String :=
    match words with
    | [] => ""
    | [w] => w
    | h :: t =>
      -- Append the current word with a space and continue joining the rest.
      h ++ " " ++ joinWithSpace t
  let result : String := joinWithSpace revWords
  result
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def reverseWords_postcond (words_str : String) (result: String) (h_precond : reverseWords_precond (words_str)) : Prop :=
  -- !benchmark @start postcond
  ∃ words : List String,
    (words = (words_str.splitOn " ").filter (fun w => w ≠ "")) ∧
    result = String.intercalate " " (words.reverse)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem reverseWords_spec_satisfied (words_str: String) (h_precond : reverseWords_precond (words_str)) :
    reverseWords_postcond (words_str) (reverseWords (words_str) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold reverseWords_postcond
  quickcheck (config := { Quickcheck.Configuration.normal with decidableBound := some 100, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_66
