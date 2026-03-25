import Quickcheck

set_option maxHeartbeats 0



def isUpperAlpha (c : Char) : Bool :=
  'A' ≤ c ∧ c ≤ 'Z'

def isLowerAlpha (c : Char) : Bool :=
  'a' ≤ c ∧ c ≤ 'z'

def isAlpha (c : Char) : Bool :=
  isUpperAlpha c ∨ isLowerAlpha c

def toLower (c : Char) : Char :=
  if isUpperAlpha c then Char.ofNat (c.toNat + 32) else c

def normalizeChar (c : Char) : Option Char :=
  if isAlpha c then some (toLower c) else none

def normalizeString (s : String) : List Char :=
  s.toList.foldr (fun c acc =>
    match normalizeChar c with
    | some c' => c' :: acc
    | none    => acc
  ) []

@[reducible]
def isCleanPalindrome_precond (s : String) : Prop :=
  True

def reverseList (xs : List Char) : List Char :=
  xs.reverse

def isCleanPalindrome (s : String) (h_precond : isCleanPalindrome_precond (s)) : Bool :=
  let norm := normalizeString s
  decide (norm = reverseList norm)

@[reducible]
def isCleanPalindrome_postcond (s : String) (result: Bool) (h_precond : isCleanPalindrome_precond (s)) : Prop :=
  let norm := normalizeString s
  (result = true → norm = norm.reverse) ∧
  (result = false → norm ≠ norm.reverse)


theorem isCleanPalindrome_spec_satisfied (s: String) (h_precond : isCleanPalindrome_precond (s)) :
    isCleanPalindrome_postcond (s) (isCleanPalindrome (s) h_precond) h_precond := by
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })
