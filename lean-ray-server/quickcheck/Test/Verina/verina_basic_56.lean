import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_56


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def copy_precond (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) : Prop :=
  -- !benchmark @start precond
  src.size ≥ sStart + len ∧
  dest.size ≥ dStart + len
  -- !benchmark @end precond


-- !benchmark @start code_aux
def updateSegment : Array Int → Array Int → Nat → Nat → Nat → Array Int
  | r, src, sStart, dStart, 0 => r
  | r, src, sStart, dStart, n+1 =>
      let rNew := r.set! (dStart + n) (src[sStart + n]!)
      updateSegment rNew src sStart dStart n
-- !benchmark @end code_aux


def copy (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (h_precond : copy_precond (src) (sStart) (dest) (dStart) (len)) : Array Int :=
  -- !benchmark @start code
  if len = 0 then dest
  else
    let r := dest
    updateSegment r src sStart dStart len
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def copy_postcond (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (result: Array Int) (h_precond : copy_precond (src) (sStart) (dest) (dStart) (len)) :=
  -- !benchmark @start postcond
  result.size = dest.size ∧
  (∀ i, i < dStart → result[i]! = dest[i]!) ∧
  (∀ i, dStart + len ≤ i → i < result.size → result[i]! = dest[i]!) ∧
  (∀ i, i < len → result[dStart + i]! = src[sStart + i]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem copy_spec_satisfied (src: Array Int) (sStart: Nat) (dest: Array Int) (dStart: Nat) (len: Nat) (h_precond : copy_precond (src) (sStart) (dest) (dStart) (len)) :
    copy_postcond (src) (sStart) (dest) (dStart) (len) (copy (src) (sStart) (dest) (dStart) (len) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.normal with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_56
