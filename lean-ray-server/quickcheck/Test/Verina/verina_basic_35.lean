import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_35


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def MoveZeroesToEnd_precond (arr : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def MoveZeroesToEnd (arr : Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) : Array Int :=
  -- !benchmark @start code
  let nonZeros := arr.toList.filter (· ≠ 0)
  let zeros := arr.toList.filter (· = 0)
  Array.mk (nonZeros ++ zeros)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def MoveZeroesToEnd_postcond (arr : Array Int) (result: Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) :=
  -- !benchmark @start postcond
  let firstResZeroIdx := result.toList.idxOf 0
  List.isPerm result.toList arr.toList ∧
  result.toList.take firstResZeroIdx = arr.toList.filter (· ≠ 0) ∧
  result.toList.drop firstResZeroIdx = arr.toList.filter (· = 0)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem MoveZeroesToEnd_spec_satisfied (arr: Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) :
    MoveZeroesToEnd_postcond (arr) (MoveZeroesToEnd (arr) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_35
