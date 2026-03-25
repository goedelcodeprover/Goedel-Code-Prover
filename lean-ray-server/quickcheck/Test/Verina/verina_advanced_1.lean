import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def filterlist (x : Int) (nums : List Int) : List Int :=
  let rec aux (lst : List Int) : List Int :=
    match lst with
    | []      => []
    | y :: ys => if y = x then y :: aux ys else aux ys
  aux nums
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def FindSingleNumber_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  let numsCount := nums.map (fun x => nums.count x)
  numsCount.all (fun count => count = 1 ∨ count = 2) ∧ numsCount.count 1 = 1
  -- !benchmark @end precond


-- !benchmark @start code_aux
-- !benchmark @end code_aux

def FindSingleNumber (nums : List Int) (h_precond : FindSingleNumber_precond (nums)) : Int :=
  -- !benchmark @start code
  let rec findUnique (remaining : List Int) : Int :=
    match remaining with
    | [] =>
      0
    | x :: xs =>
      let filtered : List Int :=
        filterlist x nums
      let count : Nat :=
        filtered.length
      if count = 1 then
        x
      else
        findUnique xs
  findUnique nums
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux

@[reducible]
def FindSingleNumber_postcond (nums : List Int) (result: Int) (h_precond : FindSingleNumber_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  (nums.length > 0)
  ∧
  ((filterlist result nums).length = 1)
  ∧
  (∀ (x : Int),
    x ∈ nums →
    (x = result) ∨ ((filterlist x nums).length = 2))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem FindSingleNumber_spec_satisfied (nums: List Int) (h_precond : FindSingleNumber_precond (nums)) :
    FindSingleNumber_postcond (nums) (FindSingleNumber (nums) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })
  -- !benchmark @end proof
