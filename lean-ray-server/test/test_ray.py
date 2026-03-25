from lean_verifier import LeanVerifier

verifier = LeanVerifier()
verifier.initialize()

code = ["""import Mathlib\n\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\ntheorem test : 1 = 1 := by\n  simp
    """]*10

responses = verifier.verify_batch(code)
print(responses)