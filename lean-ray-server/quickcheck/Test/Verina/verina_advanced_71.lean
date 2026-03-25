import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_71


-- !benchmark @start solution_aux
def countOnes (lst : List Char) : Nat :=
  lst.foldl (fun acc c => if c = '1' then acc + 1 else acc) 0
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def shortestBeautifulSubstring_precond (s : String) (k : Nat) : Prop :=
  -- !benchmark @start precond
  s.toList.all (fun c => c = '0' ∨ c = '1')
  -- !benchmark @end precond


-- !benchmark @start code_aux
def listToString (lst : List Char) : String :=
  String.mk lst
def isLexSmaller (a b : List Char) : Bool :=
  listToString a < listToString b
def allSubstrings (s : List Char) : List (List Char) :=
  let n := s.length
  (List.range n).flatMap (fun i =>
    (List.range (n - i)).map (fun j =>
      s.drop i |>.take (j + 1)))
-- !benchmark @end code_aux


def shortestBeautifulSubstring (s : String) (k : Nat) (h_precond : shortestBeautifulSubstring_precond (s) (k)) : String :=
  -- !benchmark @start code
  let chars := s.data
  let candidates := allSubstrings chars |>.filter (fun sub => countOnes sub = k)

  let compare (a b : List Char) : Bool :=
    a.length < b.length ∨ (a.length = b.length ∧ isLexSmaller a b)

  let best := candidates.foldl (fun acc cur =>
    match acc with
    | none => some cur
    | some best => if compare cur best then some cur else some best) none
  match best with
  | some b => listToString b
  | none => ""
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def shortestBeautifulSubstring_postcond (s : String) (k : Nat) (result: String) (h_precond : shortestBeautifulSubstring_precond (s) (k)) : Prop :=
  -- !benchmark @start postcond
  let chars := s.data
  let substrings := (List.range chars.length).flatMap (fun i =>
    (List.range (chars.length - i + 1)).map (fun len =>
      chars.drop i |>.take len))
  let isBeautiful := fun sub => countOnes sub = k
  let beautiful := substrings.filter (fun sub => isBeautiful sub)
  let targets := beautiful.map (·.asString) |>.filter (fun s => s ≠ "")
  (result = "" ∧ targets = []) ∨
  (result ∈ targets ∧
   ∀ r ∈ targets, r.length ≥ result.length ∨ (r.length = result.length ∧ result ≤ r))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem shortestBeautifulSubstring_spec_satisfied (s: String) (k: Nat) (h_precond : shortestBeautifulSubstring_precond (s) (k)) :
    shortestBeautifulSubstring_postcond (s) (k) (shortestBeautifulSubstring (s) (k) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_71
