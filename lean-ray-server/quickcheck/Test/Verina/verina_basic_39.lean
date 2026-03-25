import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_39


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def rotateRight_precond (l : List Int) (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def rotateRight (l : List Int) (n : Nat) (h_precond : rotateRight_precond (l) (n)) : List Int :=
  -- !benchmark @start code
  let len := l.length
  if len = 0 then l
  else
    (List.range len).map (fun i : Nat =>
      let idx_int : Int := ((Int.ofNat i - Int.ofNat n + Int.ofNat len) % Int.ofNat len)
      let idx_nat : Nat := Int.toNat idx_int
      l.getD idx_nat (l.headD 0)
    )
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def rotateRight_postcond (l : List Int) (n : Nat) (result: List Int) (h_precond : rotateRight_precond (l) (n)) :=
  -- !benchmark @start postcond
  result.length = l.length ∧
  (∀ i : Nat, i < l.length →
    let len := l.length
    let rotated_index := Int.toNat ((Int.ofNat i - Int.ofNat n + Int.ofNat len) % Int.ofNat len)
    result[i]? = l[rotated_index]?)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem rotateRight_spec_satisfied (l: List Int) (n: Nat) (h_precond : rotateRight_precond (l) (n)) :
    rotateRight_postcond (l) (n) (rotateRight (l) (n) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_39
