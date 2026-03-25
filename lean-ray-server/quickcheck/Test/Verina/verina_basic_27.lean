import Quickcheck
-- !benchmark @start import type=solution
import Std.Data.HashSet
-- !benchmark @end import

namespace verina_basic_27


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def findFirstRepeatedChar_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def findFirstRepeatedChar (s : String) (h_precond : findFirstRepeatedChar_precond (s)) : Option Char :=
  -- !benchmark @start code
  let cs := s.toList
  let rec loop (i : Nat) (seen : Std.HashSet Char) : Option Char :=
    if i < cs.length then
      let c := cs[i]!
      if seen.contains c then
        some c
      else
        loop (i + 1) (seen.insert c)
    else
      -- When no repeated char is found, return (false, arbitrary char)
      none
  loop 0 Std.HashSet.empty
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux



@[reducible, simp]
def findFirstRepeatedChar_postcond (s : String) (result: Option Char) (h_precond : findFirstRepeatedChar_precond (s)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  match result with
  | some c =>
    let secondIdx := cs.zipIdx.findIdx (fun (x, i) => x = c && i ≠ cs.idxOf c)
    -- Exists repeated char
    cs.count c ≥ 2 ∧
    -- There is no other repeated char before the found one
    List.Pairwise (· ≠ ·) (cs.take secondIdx)
  | none =>
    -- There is no repeated char
    List.Pairwise (· ≠ ·) cs
  -- !benchmark @end postcond

-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem findFirstRepeatedChar_spec_satisfied (s: String) (h_precond : findFirstRepeatedChar_precond (s)) :
    findFirstRepeatedChar_postcond (s) (findFirstRepeatedChar (s) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold findFirstRepeatedChar_postcond
  -- split
  quickcheck (config := { Quickcheck.Configuration.adaptive with decidableBound := some 100, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_27
