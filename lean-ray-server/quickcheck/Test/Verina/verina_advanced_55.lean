import Quickcheck
-- !benchmark @start import type=solution
import Std.Data.HashMap
open Std
-- !benchmark @end import

namespace verina_advanced_55


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def mostFrequent_precond (xs : List Int) : Prop :=
  -- !benchmark @start precond
  xs ≠ []
  -- !benchmark @end precond


-- !benchmark @start code_aux
-- Build a frequency map from the list
def countMap (xs : List Int) : HashMap Int Nat :=
  let step := fun m x =>
    let current := m.getD x 0
    m.insert x (current + 1)
  let init := (HashMap.empty : HashMap Int Nat)
  xs.foldl step init

-- Compute the maximum frequency in the map
def getMaxFrequency (m : HashMap Int Nat) : Nat :=
  let step := fun acc (_k, v) =>
    if v > acc then v else acc
  let init := 0
  m.toList.foldl step init

-- Extract all keys whose frequency == maxFreq
def getCandidates (m : HashMap Int Nat) (maxFreq : Nat) : List Int :=
  let isTarget := fun (_k, v) => v = maxFreq
  let extract := fun (k, _) => k
  m.toList.filter isTarget |>.map extract

-- Return the first candidate element from original list
def getFirstWithFreq (xs : List Int) (candidates : List Int) : Int :=
  match xs.find? (fun x => candidates.contains x) with
  | some x => x
  | none => 0
-- !benchmark @end code_aux


def mostFrequent (xs : List Int) (h_precond : mostFrequent_precond (xs)) : Int :=
  -- !benchmark @start code
  let freqMap := countMap xs
  let maxF := getMaxFrequency freqMap
  let candidates := getCandidates freqMap maxF
  getFirstWithFreq xs candidates
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def mostFrequent_postcond (xs : List Int) (result: Int) (h_precond : mostFrequent_precond (xs)) : Prop :=
  -- !benchmark @start postcond
  let count := fun x => xs.countP (fun y => y = x)
  result ∈ xs ∧
  xs.all (fun x => count x ≤ count result) ∧
  ((xs.filter (fun x => count x = count result)).head? = some result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem mostFrequent_spec_satisfied (xs: List Int) (h_precond : mostFrequent_precond (xs)) :
    mostFrequent_postcond (xs) (mostFrequent (xs) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_55
