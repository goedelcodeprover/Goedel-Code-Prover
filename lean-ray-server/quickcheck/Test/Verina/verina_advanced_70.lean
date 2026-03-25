import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_70


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def semiOrderedPermutation_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def semiOrderedPermutation (nums : List Int) (h_precond : semiOrderedPermutation_precond (nums)) : Int :=
  -- !benchmark @start code
  let lengthList := nums.length
  let numOne : Int := 1
  let largestNum : Int := Int.ofNat lengthList

  let firstIndex := nums.idxOf numOne
  let lastIndex := nums.idxOf largestNum

  let startPosition := 0
  let endPosition := lengthList - 1

  let shouldMoveOne := firstIndex != startPosition
  let shouldMoveLast := lastIndex != endPosition

  let distanceOne := if shouldMoveOne then firstIndex else 0
  let distanceLast := if shouldMoveLast then endPosition - lastIndex else 0

  let totalMoves := distanceOne + distanceLast
  let needAdjustment := firstIndex > lastIndex
  let adjustedMoves := if needAdjustment then totalMoves - 1 else totalMoves

  adjustedMoves
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def semiOrderedPermutation_postcond (nums : List Int) (result: Int) (h_precond : semiOrderedPermutation_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  let n := nums.length
  let pos1 := nums.idxOf 1
  let posn := nums.idxOf (Int.ofNat n)
  if pos1 > posn then
    pos1 + n = result + 2 + posn
  else
    pos1 + n = result + 1 + posn
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem semiOrderedPermutation_spec_satisfied (nums: List Int) (h_precond : semiOrderedPermutation_precond (nums)) :
    semiOrderedPermutation_postcond (nums) (semiOrderedPermutation (nums) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_70
