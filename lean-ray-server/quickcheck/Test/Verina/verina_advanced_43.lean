import Quickcheck

namespace verina_advanced_43


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def maxStrength_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  nums ≠ []
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def maxStrength (nums : List Int) (h_precond : maxStrength_precond (nums)) : Int :=
  -- !benchmark @start code
  let powerSet := fun (l : List Int) =>
    let n := l.length
    let masks := List.range (2^n)
    masks.map fun mask =>
      (List.range n).foldr (fun i acc =>
        if (mask.shiftRight i).land 1 == 1 then l[i]! :: acc else acc
      ) []

  let subsets := powerSet nums
  let nonEmpty := subsets.filter (· ≠ [])
  let products := List.map (fun subset =>
    List.foldl (fun acc x =>
      acc * x) (1 : Int) subset)
    nonEmpty
  (List.max? products).getD (-1000000)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def maxStrength_postcond (nums : List Int) (result: Int) (h_precond : maxStrength_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  let powerSet := fun (l : List Int) =>
    let n := l.length
    let masks := List.range (2 ^ n)
    masks.map fun mask =>
      (List.range n).foldr (fun i acc =>
        if (mask.shiftRight i).land 1 == 1 then l[i]! :: acc else acc
      ) []
  let sublists := (powerSet nums).filter (· ≠ [])
  let products := sublists.map (List.foldl (· * ·) 1)
  products.contains result ∧ products.all (· ≤ result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux


theorem maxStrength_spec_satisfied (nums: List Int) (h_precond : maxStrength_precond (nums)) :
    maxStrength_postcond (nums) (maxStrength (nums) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold maxStrength_postcond
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_43
