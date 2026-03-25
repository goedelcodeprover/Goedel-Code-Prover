import Quickcheck

set_option synthInstance.maxSize 512
set_option maxHeartbeats 0



namespace verina_basic_34

def isEven (n : Int) : Bool :=
  n % 2 = 0

@[reducible, simp]
def findEvenNumbers_precond (arr : Array Int) : Prop :=
  True

def findEvenNumbers (arr : Array Int) (h_precond : findEvenNumbers_precond (arr)) : Array Int :=
  arr.foldl (fun acc x => if isEven x then acc.push x else acc) #[]

@[reducible, simp]
def findEvenNumbers_postcond (arr : Array Int) (result: Array Int) (h_precond : findEvenNumbers_precond (arr)) :=
  -- (∀ x, x ∈ result → isEven x ∧ x ∈ arr.toList) ∧
  -- (∀ x, x ∈ arr.toList → isEven x → x ∈ result)
  -- ∧
  (∀ x y, x ∈ arr.toList → y ∈ arr.toList →
    isEven x → isEven y →
    arr.toList.idxOf x ≤ arr.toList.idxOf y →
    result.toList.idxOf x ≤ result.toList.idxOf y)


theorem findEvenNumbers_spec_satisfied (arr: Array Int) (h_precond : findEvenNumbers_precond (arr)) :
    findEvenNumbers_postcond (arr) (findEvenNumbers (arr) h_precond) h_precond := by
    quickcheck (config := { Quickcheck.Configuration.extensive with decidableBound := some 100 })



end verina_basic_34
