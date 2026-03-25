import Quickcheck


def a : List Int := []

def List.range_safe (n : Nat) : List Nat :=
  if n > 10 then
    panic! "n is too large"
  else
    List.range n

#eval List.range_safe 11

theorem List.range_safe_spec (n : Nat) : List.range_safe n = List.range n := by
  quickcheck
