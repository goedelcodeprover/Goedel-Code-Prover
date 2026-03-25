import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_108


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def below_zero_precond (operations : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def buildS (operations : List Int) : Array Int :=
  let sList := operations.foldl
    (fun (acc : List Int) (op : Int) =>
      let last := acc.getLast? |>.getD 0
      acc.append [last + op])
    [0]
  Array.mk sList
-- !benchmark @end code_aux


def below_zero (operations : List Int) (h_precond : below_zero_precond (operations)) : (Array Int × Bool) :=
  -- !benchmark @start code
  let s := buildS operations
  let rec check_negative (lst : List Int) : Bool :=
    match lst with
    | []      => false
    | x :: xs => if x < 0 then true else check_negative xs
  let result := check_negative (s.toList)
  (s, result)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def below_zero_postcond (operations : List Int) (result: (Array Int × Bool)) (h_precond : below_zero_precond (operations)) :=
  -- !benchmark @start postcond
  let s := result.1
  let result := result.2
  s.size = operations.length + 1 ∧
  s[0]? = some 0 ∧
  (List.range (s.size - 1)).all (fun i => s[i + 1]? = some (s[i]! + operations[i]!)) ∧
  ((result = true) → ((List.range (operations.length)).any (fun i => s[i + 1]! < 0))) ∧
  ((result = false) → s.all (· ≥ 0))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem below_zero_spec_satisfied (operations: List Int) (h_precond : below_zero_precond (operations)) :
    below_zero_postcond (operations) (below_zero (operations) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_108
