import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_64


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def insert_precond (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) : Prop :=
  -- !benchmark @start precond
  l ≤ oline.size ∧
  p ≤ nl.size ∧
  atPos ≤ l
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def insert (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (h_precond : insert_precond (oline) (l) (nl) (p) (atPos)) : Array Char :=
  -- !benchmark @start code
  let result := Array.mkArray (l + p) ' '

  let result := Array.foldl
    (fun acc i =>
      if i < atPos then acc.set! i (oline[i]!) else acc)
    result
    (Array.range l)

  let result := Array.foldl
    (fun acc i =>
      acc.set! (atPos + i) (nl[i]!))
    result
    (Array.range p)

  let result := Array.foldl
    (fun acc i =>
      if i >= atPos then acc.set! (i + p) (oline[i]!) else acc)
    result
    (Array.range l)

  result
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def insert_postcond (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (result: Array Char) (h_precond : insert_precond (oline) (l) (nl) (p) (atPos)) :=
  -- !benchmark @start postcond
  result.size = l + p ∧
  (List.range p).all (fun i => result[atPos + i]! = nl[i]!) ∧
  (List.range atPos).all (fun i => result[i]! = oline[i]!) ∧
  (List.range (l - atPos)).all (fun i => result[atPos + p + i]! = oline[atPos + i]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem insert_spec_satisfied (oline: Array Char) (l: Nat) (nl: Array Char) (p: Nat) (atPos: Nat) (h_precond : insert_precond (oline) (l) (nl) (p) (atPos)) :
    insert_postcond (oline) (l) (nl) (p) (atPos) (insert (oline) (l) (nl) (p) (atPos) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_64
