import Quickcheck
-- !benchmark @start import type=solution
import Std.Data.HashSet
open Std
-- !benchmark @end import

namespace verina_advanced_74


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def solution_precond (nums : List Nat) : Prop :=
  -- !benchmark @start precond
  1 ≤ nums.length ∧ nums.length ≤ 100 ∧ nums.all (fun x => 1 ≤ x ∧ x ≤ 100)
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def solution (nums : List Nat) : Nat :=
  -- !benchmark @start code
  let n := nums.length
  let subarray := fun (i j : Nat) => (nums.drop i).take (j - i + 1)
  let distinctCount := fun (l : List Nat) =>
    let hashSet := l.foldl (fun (s : HashSet Nat) a => s.insert a) HashSet.empty
    hashSet.size
  List.range n |>.foldl (fun acc i =>
    acc +
      (List.range (n - i) |>.foldl (fun acc' d =>
        let subarr := subarray i (i + d)
        let cnt := distinctCount subarr
        acc' + cnt * cnt
      ) 0)
  ) 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def solution_postcond (nums : List Nat) (result: Nat) : Prop :=
  -- !benchmark @start postcond
  let n := nums.length;

  let getSubarray_local := fun (i j : Nat) =>
    (nums.drop i).take (j - i + 1);

  let distinctCount_local := fun (l : List Nat) =>
    let foldFn := fun (seen : List Nat) (x : Nat) =>
      if seen.elem x then seen else x :: seen;
    let distinctElems := l.foldl foldFn [];
    distinctElems.length;

  let square_local := fun (n : Nat) => n * n;

  (1 <= n ∧ n <= 100 ∧ nums.all (fun x => 1 <= x ∧ x <= 100)) ->
  (
    result >= 0
    ∧
    let expectedSum : Nat :=
      List.range n |>.foldl (fun (outerSum : Nat) (i : Nat) =>
        let innerSum : Nat :=
          List.range (n - i) |>.foldl (fun (currentInnerSum : Nat) (d : Nat) =>
            let j := i + d;
            let subarr := getSubarray_local i j;
            let count := distinctCount_local subarr;
            currentInnerSum + square_local count
          ) 0
        outerSum + innerSum
      ) 0;

    result = expectedSum
  )
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem solution_spec_satisfied (nums: List Nat) :
    solution_postcond (nums) (solution (nums)) := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_74
