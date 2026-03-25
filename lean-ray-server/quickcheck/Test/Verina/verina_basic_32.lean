import Quickcheck

namespace verina_basic_32


-- !benchmark @start import type=llm
-- !benchmark @end import

-- !benchmark @start import type=test
-- !benchmark @end import

-- !benchmark @start solution_aux
-- !benchmark @end solution_aux
-- !benchmark @start precond_aux
-- !benchmark @end precond_aux

@[reducible, simp]
def swapFirstAndLast_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond

-- !benchmark @start code_aux
-- !benchmark @end code_aux


def swapFirstAndLast (a : Array Int) (h_precond: swapFirstAndLast_precond a) : Array Int :=
  -- !benchmark @start code
  let first := a[0]!
  let last := a[a.size - 1]!
  a.set! 0 last |>.set! (a.size - 1) first
  -- !benchmark @end code

-- !benchmark @start postcond_aux
-- !benchmark @end postcond_aux

-- Theorem: The last element of the input array should be the first element of the modified array; The first element of the input array should be the last element of the modified array; All other elements remain unchanged
@[reducible, simp]
def swapFirstAndLast_postcond (a : Array Int) (result : Array Int) (h_precond: swapFirstAndLast_precond a) : Prop :=
  -- !benchmark @start postcond
  result.size = a.size ∧
  result[0]! = a[a.size - 1]! ∧
  result[result.size - 1]! = a[0]! ∧
  (List.range (result.size - 2)).all (fun i => result[i + 1]! = a[i + 1]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux
-- !benchmark @end proof_aux

theorem swapFirstAndLast_spec_satisfied (a : Array Int) (h_precond: swapFirstAndLast_precond a) :
    swapFirstAndLast_postcond a (swapFirstAndLast a h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with decidableBound := some 1000, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_32
