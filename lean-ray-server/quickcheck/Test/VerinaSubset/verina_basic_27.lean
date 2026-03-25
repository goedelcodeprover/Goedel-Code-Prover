import Quickcheck
import Std.Data.HashSet

set_option maxHeartbeats 0

namespace verina_basic_27

@[reducible, simp]
def pre_findFirstRepeatedChar (s : String) : Prop :=
  True

def findFirstRepeatedChar (s : String) (h_precond : pre_findFirstRepeatedChar (s)) : Option Char :=
  let cs := s.toList
  let rec loop (i : Nat) (seen : Std.HashSet Char) : Option Char :=
    if i < cs.length then
      let c := cs[i]!
      if seen.contains c then
        some c
      else
        loop (i + 1) (seen.insert c)
    else
      none
  loop 0 Std.HashSet.empty

@[reducible, simp]
def post_findFirstRepeatedChar (s : String) (result: Option Char) (h_precond : pre_findFirstRepeatedChar (s)) :=
  let cs := s.toList
  match result with
  | some c =>
    let secondIdx := cs.zipIdx.findIdx (fun (x, i) => x = c && i ≠ cs.idxOf c)
    cs.count c ≥ 2 ∧
    List.Pairwise (· ≠ ·) (cs.take secondIdx)
  | none =>
    List.Pairwise (· ≠ ·) cs

theorem findFirstRepeatedChar_spec_satisfied (s: String) (h_precond : pre_findFirstRepeatedChar (s)) :
    post_findFirstRepeatedChar (s) (findFirstRepeatedChar (s) h_precond) h_precond := by
    unfold post_findFirstRepeatedChar
    quickcheck (config := { Quickcheck.Configuration.extensive with decidableBound := some 100 })

end verina_basic_27
