code = """
import Tacs
import Mathlib

set_option maxHeartbeats 0

namespace verina_advanced_18

def countDigits (n : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else go (n / 10) (acc + 1)
  go n (if n = 0 then 1 else 0)

@[reducible]
def isArmstrong_precond (n : Nat) : Prop :=
  True

def sumPowers (n : Nat) (k : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else
      let digit := n % 10
      go (n / 10) (acc + digit ^ k)
  go n 0

def isArmstrong (n : Nat) (h_precond : isArmstrong_precond (n)) : Bool :=
  let k := countDigits n
  sumPowers n k = n

@[reducible]
def isArmstrong_postcond (n : Nat) (result: Bool) (h_precond : isArmstrong_precond (n)) : Prop :=
  let n' := List.foldl (fun acc d => acc + d ^ countDigits n) 0 (List.map (fun c => c.toNat - '0'.toNat) (toString n).toList)
  (result → (n = n')) ∧
  (¬ result → (n ≠ n'))

theorem verina_advanced_18.isArmstrong_spec_satisfied.extracted_1 (n : ℕ) :
  (decide (verina_advanced_18.sumPowers.go (verina_advanced_18.countDigits.go n (if n = 0 then 1 else 0)) n 0 = n) = true →
      n =
        List.foldl (fun acc d => acc + d ^ verina_advanced_18.countDigits.go n (if n = 0 then 1 else 0)) 0
          (List.map (fun c => c.toNat - 48) (toString n).data)) ∧
    (¬decide (verina_advanced_18.sumPowers.go (verina_advanced_18.countDigits.go n (if n = 0 then 1 else 0)) n 0 = n) = true →
      ¬n =
          List.foldl (fun acc d => acc + d ^ verina_advanced_18.countDigits.go n (if n = 0 then 1 else 0)) 0
            (List.map (fun c => c.toNat - 48) (toString n).data)) := by
  classical
  let k := verina_advanced_18.countDigits.go n (if n = 0 then 1 else 0)
  let F : Nat :=
    List.foldl (fun acc d => acc + d ^ k) 0
      (List.map (fun c => c.toNat - 48) (toString n).data)
  let S : Nat := verina_advanced_18.sumPowers.go k n 0

  have hFS : F = S := by
    simpa [F, k] using (fold_eq_sumPowers_go n)

  constructor
  · -- First direction: if decide (S = n) = true then n = F
    intro hdec
    have hdec' : decide (S = n) = true := by
      simpa [S, k]
    have hSeqn : S = n := (decide_eq_true_iff (S = n)).1 hdec'
    have h1 : n = S := hSeqn.symm
    have h2 : S = F := hFS.symm
    have : n = F := h1.trans h2
    simpa [F, k] using this
  · -- Second direction: if not decide (S = n) then not (n = F)
    intro hnotdec
    have hnotdec' : ¬ decide (S = n) = true := by
      simpa [S, k] using hnotdec
    have hSneqn : ¬ S = n := by
      intro hEq
      have : decide (S = n) = true := (decide_eq_true_iff (S = n)).2 hEq
      exact hnotdec' this
    intro hne
    have hSF : S = F := hFS.symm
    have hFn : F = n := hne.symm
    exact hSneqn (hSF.trans hFn)

end verina_advanced_18
"""

import requests


server_url = "http://localhost:8000"

payload = {"codes": [code], "timeout": 10, "max_retries": 1}
resp = requests.post(f"{server_url.rstrip('/')}/verify/batch", json=payload, timeout=(len(code) * 10 + 10))
resp.raise_for_status()
result = resp.json().get("results", [])
print(result)
messages = result[0].get("response", {}).get("response", {}).get("messages", [])
error = result[0].get("error_message", [True])[0]
data_list = [msg.get("data", "") for msg in messages if "data" in msg and msg.get("severity", "") == "error"]
sorries = result[0].get("response", {}).get("response", {}).get("sorries", [])
print(data_list, (error, len(sorries)))