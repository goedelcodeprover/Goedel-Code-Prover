import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_93


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def SwapBitvectors_precond (X : UInt8) (Y : UInt8) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def SwapBitvectors (X : UInt8) (Y : UInt8) (h_precond : SwapBitvectors_precond (X) (Y)) : UInt8 × UInt8 :=
  -- !benchmark @start code
  let temp := X.xor Y
  let newY := temp.xor Y
  let newX := temp.xor newY
  (newX, newY)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def SwapBitvectors_postcond (X : UInt8) (Y : UInt8) (result: UInt8 × UInt8) (h_precond : SwapBitvectors_precond (X) (Y)) :=
  -- !benchmark @start postcond
  result.fst = Y ∧ result.snd = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem SwapBitvectors_spec_satisfied (X: UInt8) (Y: UInt8) (h_precond : SwapBitvectors_precond (X) (Y)) :
    SwapBitvectors_postcond (X) (Y) (SwapBitvectors (X) (Y) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_93
