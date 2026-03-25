import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_46


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def lastPosition_precond (arr : Array Int) (elem : Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) arr.toList
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def lastPosition (arr : Array Int) (elem : Int) (h_precond : lastPosition_precond (arr) (elem)) : Int :=
  -- !benchmark @start code
  let rec loop (i : Nat) (pos : Int) : Int :=
    if i < arr.size then
      let a := arr[i]!
      if a = elem then loop (i + 1) i
      else loop (i + 1) pos
    else pos
  loop 0 (-1)
  -- !benchmark @end code

-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def lastPosition_postcond (arr : Array Int) (elem : Int) (result: Int) (h_precond : lastPosition_precond (arr) (elem)) :=
  -- !benchmark @start postcond
  (result ≥ 0 →
    arr[result.toNat]! = elem ∧ (arr.toList.drop (result.toNat + 1)).all (· ≠ elem)) ∧
  (result = -1 → arr.toList.all (· ≠ elem))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem lastPosition_spec_satisfied (arr: Array Int) (elem: Int) (h_precond : lastPosition_precond (arr) (elem)) :
    lastPosition_postcond (arr) (elem) (lastPosition (arr) (elem) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_46
