import Quickcheck
import Std.Data.HashMap
open Std

set_option maxHeartbeats 0



namespace verina_advanced_35

@[reducible]
def majorityElement_precond (nums : List Int) : Prop :=
  nums.length > 0 ∧ nums.any (fun x => nums.count x > nums.length / 2)

def majorityElement (nums : List Int) (h_precond : majorityElement_precond (nums)) : Int :=
  Id.run do
    let mut counts : HashMap Int Nat := {}
    let n := nums.length
    for x in nums do
      let count := counts.getD x 0
      counts := counts.insert x (count + 1)
    match counts.toList.find? (fun (_, c) => c > n / 2) with
    | some (k, _) => k
    | none      => 0

@[reducible]
def majorityElement_postcond (nums : List Int) (result: Int) (h_precond : majorityElement_precond (nums)) : Prop :=
  let n := nums.length
  (nums.count result) > n / 2
  ∧ ∀ x, x ≠ result → nums.count x ≤ n / 2

theorem majorityElement_spec_satisfied (nums: List Int) (h_precond : majorityElement_precond (nums)) :
    majorityElement_postcond (nums) (majorityElement (nums) h_precond) h_precond := by
    quickcheck (config := { Quickcheck.Configuration.extensive with quiet := true, randomSeed := some 42 })


end verina_advanced_35
