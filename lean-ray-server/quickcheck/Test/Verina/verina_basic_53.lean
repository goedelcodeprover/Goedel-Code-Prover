import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_53


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def CalSum_precond (N : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def CalSum (N : Nat) (h_precond : CalSum_precond (N)) : Nat :=
  -- !benchmark @start code
  let rec loop (n : Nat) : Nat :=
    if n = 0 then 0
    else n + loop (n - 1)
  loop N
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def CalSum_postcond (N : Nat) (result: Nat) (h_precond : CalSum_precond (N)) :=
  -- !benchmark @start postcond
  2 * result = N * (N + 1)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem CalSum_spec_satisfied (N: Nat) (h_precond : CalSum_precond (N)) :
    CalSum_postcond (N) (CalSum (N) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_53
