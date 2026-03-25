import Quickcheck


set_option maxHeartbeats 0



namespace verina_advanced_66

@[reducible]
def reverseWords_precond (words_str : String) : Prop :=
  True

def reverseWords (words_str : String) (h_precond : reverseWords_precond (words_str)) : String :=
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
      h ++ " " ++ joinWithSpace t
  let result : String := joinWithSpace revWords
  result

@[reducible]
def reverseWords_postcond (words_str : String) (result: String) (h_precond : reverseWords_precond (words_str)) : Prop :=
  ∃ words : List String,
    (words = (words_str.splitOn " ").filter (fun w => w ≠ "")) ∧
    result = String.intercalate " " (words.reverse)

theorem reverseWords_spec_satisfied (words_str: String) (h_precond : reverseWords_precond (words_str)) :
    reverseWords_postcond (words_str) (reverseWords (words_str) h_precond) h_precond := by
    quickcheck (config := { Quickcheck.Configuration.normal with quiet := true, randomSeed := some 42 })

end verina_advanced_66
