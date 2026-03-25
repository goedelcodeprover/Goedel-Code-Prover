import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_67


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def runLengthEncode_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def runLengthEncode (s : String) (h_precond : runLengthEncode_precond (s)) : List (Char × Nat) :=
  -- !benchmark @start code
  let chars := s.data

  let rec encodeAux (acc : List (Char × Nat)) (rest : List Char) : List (Char × Nat) :=
    match rest with
    | [] => acc.reverse
    | h :: t =>
      match acc with
      | (ch, count) :: accTail =>
        if ch = h then
          encodeAux ((ch, count + 1) :: accTail) t
        else
          encodeAux ((h, 1) :: (ch, count) :: accTail) t
      | [] =>
        encodeAux ([(h, 1)]) t

  let encoded := encodeAux [] chars
  encoded
  -- !benchmark @end code


-- !benchmark @start postcond_aux
def decodeRLE (lst : List (Char × Nat)) : String :=
  match lst with
  | [] => ""
  | (ch, cnt) :: tail =>
    let repeated := String.mk (List.replicate cnt ch)
    repeated ++ decodeRLE tail
-- !benchmark @end postcond_aux


@[reducible, simp]
def runLengthEncode_postcond (s : String) (result: List (Char × Nat)) (h_precond : runLengthEncode_precond (s)) : Prop :=
  -- !benchmark @start postcond
  (∀ pair ∈ result, pair.snd > 0) ∧
  (∀ i : Nat, i < result.length - 1 → (result[i]!).fst ≠ (result[i+1]!).fst) ∧
  decodeRLE result = s
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem runLengthEncode_spec_satisfied (s: String) (h_precond : runLengthEncode_precond (s)) :
    runLengthEncode_postcond (s) (runLengthEncode (s) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_67
