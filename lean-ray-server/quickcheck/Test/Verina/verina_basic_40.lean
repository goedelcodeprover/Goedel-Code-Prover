import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_40


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def secondSmallest_precond (s : Array Int) : Prop :=
  -- !benchmark @start precond
  s.size > 1
  -- !benchmark @end precond


-- !benchmark @start code_aux
def minListHelper : List Int → Int
| [] => panic! "minListHelper: empty list"
| [_] => panic! "minListHelper: singleton list"
| a :: b :: [] => if a ≤ b then a else b
| a :: b :: c :: xs =>
    let m := minListHelper (b :: c :: xs)
    if a ≤ m then a else m

def minList (l : List Int) : Int :=
  minListHelper l

def secondSmallestAux (s : Array Int) (i minIdx secondIdx : Nat) : Int :=
  if i ≥ s.size then
    s[secondIdx]!
  else
    let x    := s[i]!
    let m    := s[minIdx]!
    let smin := s[secondIdx]!
    if x < m then
      secondSmallestAux s (i + 1) i minIdx
    else if x < smin then
      secondSmallestAux s (i + 1) minIdx i
    else
      secondSmallestAux s (i + 1) minIdx secondIdx
termination_by s.size - i
-- !benchmark @end code_aux


def secondSmallest (s : Array Int) (h_precond : secondSmallest_precond (s)) : Int :=
  -- !benchmark @start code
  let (minIdx, secondIdx) :=
    if s[1]! < s[0]! then (1, 0) else (0, 1)
  secondSmallestAux s 2 minIdx secondIdx
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def secondSmallest_postcond (s : Array Int) (result: Int) (h_precond : secondSmallest_precond (s)) :=
  -- !benchmark @start postcond
  (∃ i, i < s.size ∧ s[i]! = result) ∧
  (∃ j, j < s.size ∧ s[j]! < result ∧
    ∀ k, k < s.size → s[k]! ≠ s[j]! → s[k]! ≥ result)
  -- !benchmark @end postcond



theorem secondSmallest_spec_satisfied (s: Array Int) (h_precond : secondSmallest_precond (s)) :
    secondSmallest_postcond (s) (secondSmallest (s) h_precond) h_precond := by
  unfold secondSmallest_postcond
  quickcheck (config := { Quickcheck.Configuration.adaptive with enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_40
