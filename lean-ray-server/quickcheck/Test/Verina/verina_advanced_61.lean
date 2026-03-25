import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def productExceptSelf_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
-- Helper: Compute prefix products.
-- prefix[i] is the product of all elements in nums before index i.
def computepref (nums : List Int) : List Int :=
  nums.foldl (fun acc x => acc ++ [acc.getLast! * x]) [1]

-- Helper: Compute suffix products.
-- suffix[i] is the product of all elements in nums from index i (inclusive) to the end.
-- We reverse the list and fold, then reverse back.
def computeSuffix (nums : List Int) : List Int :=
  let revSuffix := nums.reverse.foldl (fun acc x => acc ++ [acc.getLast! * x]) [1]
  revSuffix.reverse
-- !benchmark @end code_aux


def productExceptSelf (nums : List Int) (h_precond : productExceptSelf_precond (nums)) : List Int :=
  -- !benchmark @start code
  let n := nums.length
  if n = 0 then []
  else
    let pref := computepref nums  -- length = n + 1, where prefix[i] = product of nums[0 ... i-1]
    let suffix := computeSuffix nums  -- length = n + 1, where suffix[i] = product of nums[i ... n-1]
    -- For each index i (0 ≤ i < n): result[i] = prefix[i] * suffix[i+1]
    -- Use array-style indexing as get! is deprecated
    List.range n |>.map (fun i => pref[i]! * suffix[i+1]!)
  -- !benchmark @end code


-- !benchmark @start postcond_aux
-- Specification Helper: Product of a list of Ints
-- Defined locally if not available/imported
def List.myprod : List Int → Int
  | [] => 1
  | x :: xs => x * xs.myprod
-- !benchmark @end postcond_aux


@[reducible]
def productExceptSelf_postcond (nums : List Int) (result: List Int) (h_precond : productExceptSelf_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  nums.length = result.length ∧
  (List.range nums.length |>.all (fun i =>
    result[i]! = some (((List.take i nums).myprod) * ((List.drop (i+1) nums).myprod))))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem productExceptSelf_spec_satisfied (nums: List Int) (h_precond : productExceptSelf_precond (nums)) :
    productExceptSelf_postcond (nums) (productExceptSelf (nums) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
