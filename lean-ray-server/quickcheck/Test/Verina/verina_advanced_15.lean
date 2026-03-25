import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_15


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def increasingTriplet_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def increasingTriplet (nums : List Int) (h_precond : increasingTriplet_precond (nums)) : Bool :=
  -- !benchmark @start code
  -- must have at least 3 elements to form a triplet
  let rec lengthCheck : List Int → Nat → Nat
    | [], acc => acc
    | _ :: rest, acc => lengthCheck rest (acc + 1)

  let len := lengthCheck nums 0

  if len < 3 then
    false
  else
    -- scan for increasing triplet
    let rec loop (xs : List Int) (first : Int) (second : Int) : Bool :=
      match xs with
      | [] => false
      | x :: rest =>
        let nextFirst := if x ≤ first then x else first
        let nextSecond := if x > first ∧ x ≤ second then x else second
        if x ≤ first then
          loop rest nextFirst second
        else if x ≤ second then
          loop rest first nextSecond
        else
          true  -- found triplet
    match nums with
    | [] => false
    | _ :: rest1 =>
      match rest1 with
      | [] => false
      | _ :: rest2 =>
        match rest2 with
        | [] => false
        | _ =>
          loop nums 2147483647 2147483647
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def increasingTriplet_postcond (nums : List Int) (result: Bool) (h_precond : increasingTriplet_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  let nums' := nums.zipIdx
  (result →
    nums'.any (fun (x, i) =>
      nums'.any (fun (y, j) =>
        nums'.any (fun (z, k) =>
          i < j ∧ j < k ∧ x < y ∧ y < z
        )
      )
    ))
  ∧
  (¬ result → nums'.all (fun (x, i) =>
    nums'.all (fun (y, j) =>
      nums'.all (fun (z, k) =>
        i ≥ j ∨ j ≥ k ∨ x ≥ y ∨ y ≥ z
      )
    )
  ))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem increasingTriplet_spec_satisfied (nums: List Int) (h_precond : increasingTriplet_precond (nums)) :
    increasingTriplet_postcond (nums) (increasingTriplet (nums) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_15
