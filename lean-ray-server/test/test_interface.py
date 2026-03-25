from lean_verifier import LeanVerifier

mock_proof_1 = """import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem lean_workbook_10009 (a b c: ℝ) (ha : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a + b + c = 1): a^3 + b^3 + c^3 + (15 * a * b * c)/4 ≥ 1/4 := by

nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
sq_nonneg (a + b + c)]"""

mock_proof_2 = """import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem test : 1 = 1 := by
  simp
"""

verifier = LeanVerifier()
verifier.initialize()
response = verifier.verify_batch([mock_proof_1, mock_proof_2], timeout=60)
print(response)
results = verifier.parse_results(response)
print(results)