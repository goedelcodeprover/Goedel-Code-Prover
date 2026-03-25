import Quickcheck

-- ============================================================
-- Example: use the `complexity_analysis` tactic directly
-- ============================================================

-- Simple case: linear complexity
theorem test_complexity_tactic (xs : List Nat) (ys : List Nat) : xs.length ≥ 0 := by
  complexity_analysis  -- show complexity analysis and suggested maxSize
  sorry

-- Exponential complexity example
def allSubseq (arr : Array Int) :=
  (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]]
  |>.map List.reverse

theorem test_complexity_exponential (a : Array Int) :
    let subseqA := allSubseq a
    subseqA.length > 0 := by
  complexity_analysis  -- detects O(2^n) and suggests maxSize = 12
  sorry

theorem test_complexity_exponential_2 (n : Nat) :
    (List.range (2 ^ n)).length = 2 ^ n := by
  complexity_analysis  -- detects O(2^n) and suggests maxSize = 12
  sorry

-- Polynomial complexity examples
theorem test_complexity_polynomial (n : Nat) :
    (List.range (n ^ 3)).length = n ^ 3 := by
  complexity_analysis  -- detects O(n^3) and suggests maxSize = 20
  sorry

theorem test_complexity_polynomial_2 (n : Nat) :
    (List.range (n ^ 4)).length = n ^ 4 := by
  complexity_analysis  -- detects O(n^4) and suggests maxSize = 20
  sorry

-- Quadratic complexity example
theorem test_complexity_quadratic (n : Nat) :
    (List.range (n * n)).length = n * n := by
  complexity_analysis  -- detects O(n^2) and suggests maxSize = 50
  sorry

-- Mixed complexity example
theorem test_complexity_mixed (xs : List Nat) (n : Nat) :
    let ys := List.range (2 ^ n)
    xs.length + ys.length > 0 := by
  complexity_analysis  -- xs: O(n), n: O(2^n)
  sorry
