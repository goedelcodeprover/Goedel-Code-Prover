import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_58


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def nthUglyNumber_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  n > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux
def nextUgly (seq : List Nat) (c2 c3 c5 : Nat) : (Nat × Nat × Nat × Nat) :=
  let i2 := seq[c2]! * 2
  let i3 := seq[c3]! * 3
  let i5 := seq[c5]! * 5
  let next := min i2 (min i3 i5)
  let c2' := if next = i2 then c2 + 1 else c2
  let c3' := if next = i3 then c3 + 1 else c3
  let c5' := if next = i5 then c5 + 1 else c5
  (next, c2', c3', c5')

-- !benchmark @end code_aux


def nthUglyNumber (n : Nat) (h_precond : nthUglyNumber_precond (n)) : Nat :=
  -- !benchmark @start code
  let rec loop (i : Nat) (seq : List Nat) (c2 c3 c5 : Nat) : List Nat :=
    match i with
    | 0 => seq
    | Nat.succ i' =>
      let (next, c2', c3', c5') := nextUgly seq c2 c3 c5
      loop i' (seq ++ [next]) c2' c3' c5'
  (loop (n - 1) [1] 0 0 0)[(n - 1)]!
  -- !benchmark @end code


-- !benchmark @start postcond_aux
def divideOut : Nat → Nat → Nat
  | n, p =>
    if h : p > 1 ∧ n > 0 ∧ n % p = 0 then
      have : n / p < n := by
        apply Nat.div_lt_self
        · exact h.2.1  -- n > 0
        · exact Nat.lt_of_succ_le (Nat.succ_le_of_lt h.1)  -- 1 < p, so 2 ≤ p
      divideOut (n / p) p
    else n
termination_by n p => n

def isUgly (x : Nat) : Bool :=
  if x = 0 then
    false
  else
    let n1 := divideOut x 2
    let n2 := divideOut n1 3
    let n3 := divideOut n2 5
    n3 = 1
-- !benchmark @end postcond_aux


@[reducible, simp]
def nthUglyNumber_postcond (n : Nat) (result: Nat) (h_precond : nthUglyNumber_precond (n)) : Prop :=
  -- !benchmark @start postcond
  isUgly result = true ∧
  ((List.range (result)).filter (fun i => isUgly i)).length = n - 1
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem nthUglyNumber_spec_satisfied (n: Nat) (h_precond : nthUglyNumber_precond (n)) :
    nthUglyNumber_postcond (n) (nthUglyNumber (n) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_58
