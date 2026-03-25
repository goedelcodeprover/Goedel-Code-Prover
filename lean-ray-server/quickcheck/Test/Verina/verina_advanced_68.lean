import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_68


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def runLengthEncoder_precond (input : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def runLengthEncoder (input : String) (h_precond : runLengthEncoder_precond (input)) : String :=
  -- !benchmark @start code
  -- Convert string to character list
  let chars : String → List Char := fun s => s.data

  -- Check character equality
  let charEq : Char → Char → Bool := fun c1 c2 => c1 == c2

  -- Convert number to string
  let numToString : Nat → String := fun n =>
    let rec digits : Nat → List Char := fun n =>
      if n < 10 then
        [Char.ofNat (n + 48)]  -- ASCII '0' is 48
      else
        digits (n / 10) ++ [Char.ofNat (n % 10 + 48)]
    String.mk (digits n)

  -- Main encoding logic (fixed version)
  let rec encode : List Char → Option Char → Nat → String :=
    fun input currentChar count =>
      match input with
      | [] =>
        -- Process remaining characters
        match currentChar with
        | none => ""
        | some c => String.mk [c] ++ numToString count
      | c::rest =>
        match currentChar with
        | none => encode rest c 1
        | some c' =>
          if charEq c c' then
            encode rest c' (count + 1)
          else
            let currentPart := String.mk [c'] ++ numToString count
            currentPart ++ encode rest c 1

  -- Handle empty input
  if input.isEmpty then
    ""
  else
    let firstChar := (chars input).head?
    encode (chars input).tail firstChar 1
  -- !benchmark @end code

-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def runLengthEncoder_postcond (input : String) (result: String) (h_precond : runLengthEncoder_precond (input)) : Prop :=
  -- !benchmark @start postcond
  -- Helper functions
  let chars : String → List Char := fun s => s.data

  -- Parse encoded string into (char, count) pairs
  let parseEncodedString : String → List (Char × Nat) :=
    let rec parseState : List Char → Option Char → Option Nat → List (Char × Nat) → List (Char × Nat) :=
      fun remaining currentChar currentCount acc =>
        match remaining with
        | [] =>
          -- Add final pair if we have both char and count
          match currentChar, currentCount with
          | some c, some n => (c, n) :: acc
          | _, _ => acc
        | c :: cs =>
          if c.isDigit then
            match currentChar with
            | none => [] -- Invalid format: digit without preceding character
            | some ch =>
              -- Update current count
              let digit := c.toNat - 48
              let newCount :=
                match currentCount with
                | none => digit
                | some n => n * 10 + digit
              parseState cs currentChar (some newCount) acc
          else
            -- We found a new character, save previous pair if exists
            let newAcc :=
              match currentChar, currentCount with
              | some ch, some n => (ch, n) :: acc
              | _, _ => acc
            parseState cs (some c) none newAcc

    fun s =>
      let result := parseState (chars s) none none []
      result.reverse

  -- Format check: characters followed by at least one digit
  let formatValid : Bool :=
    let rec checkPairs (chars : List Char) (nowDigit : Bool) : Bool :=
      match chars with
      | [] => true
      | c :: cs =>
        if nowDigit && c.isDigit then
          checkPairs cs true
        else
        -- Need at least one digit after character
          match cs with
          | [] => false -- Ending with character, no digits
          | d :: ds =>
            if d.isDigit then
              checkPairs ds true
            else
              false -- No digit after character

    checkPairs (chars result) false

  -- Content validation
  let contentValid : Bool :=
    let pairs := parseEncodedString result
    let expanded := pairs.flatMap (fun (c, n) => List.replicate n c)
    expanded == chars input

  -- Empty check
  let nonEmptyValid : Bool :=
    input.isEmpty = result.isEmpty

  formatValid && contentValid && nonEmptyValid
  -- !benchmark @end postcond

-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem runLengthEncoder_spec_satisfied (input: String) (h_precond : runLengthEncoder_precond (input)) :
    runLengthEncoder_postcond (input) (runLengthEncoder (input) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_68
