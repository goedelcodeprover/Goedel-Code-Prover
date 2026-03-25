import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_7


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def binaryToDecimal_precond (digits : List Nat) : Prop :=
  -- !benchmark @start precond
  digits.all (fun d => d = 0 ∨ d = 1)
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def binaryToDecimal (digits : List Nat) (h_precond : binaryToDecimal_precond (digits)) : Nat :=
  -- !benchmark @start code
  let rec helper (digits : List Nat) : Nat :=
    match digits with
    | [] => 0
    | first :: rest => first * Nat.pow 2 rest.length + helper rest
  helper digits
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def binaryToDecimal_postcond (digits : List Nat) (result: Nat) (h_precond : binaryToDecimal_precond (digits)) : Prop :=
  -- !benchmark @start postcond
  result - List.foldl (λ acc bit => acc * 2 + bit) 0 digits = 0 ∧
  List.foldl (λ acc bit => acc * 2 + bit) 0 digits - result = 0
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem binaryToDecimal_spec_satisfied (digits: List Nat) (h_precond : binaryToDecimal_precond (digits)) :
    binaryToDecimal_postcond (digits) (binaryToDecimal (digits) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_7
