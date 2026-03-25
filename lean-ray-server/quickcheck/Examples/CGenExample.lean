/-
Example: C-accelerated Quickcheck RNG

Shows how to use the fast C-backed RNG for test case generation.
-/

import Quickcheck.CGen

namespace Examples

open Quickcheck

/-- Example: draw random values with the C RNG -/
def example1 : IO Unit := do
  let rng0 := CRng.init 42
  let (n1, rng1) := CRng.next rng0
  IO.println s!"Random UInt64: {n1}"
  let (n2, rng2) := CRng.genNat' rng1 100
  IO.println s!"Random Nat (0-100): {n2}"
  let (b, rng3) := CRng.genBool rng2
  IO.println s!"Random Bool: {b}"
  let (i, _) := CRng.genInt' rng3 (-100) 100
  IO.println s!"Random Int (-100 to 100): {i}"

/-- Example: random list lengths -/
def example2 : IO Unit := do
  let mut rng := CRng.init 12345
  for _ in [0:10] do
    let (len, rng') := CRng.genListLength' rng 50
    IO.println s!"List length: {len}"
    rng := rng'

/-- Example: random array lengths -/
def example3 : IO Unit := do
  let mut rng := CRng.init 67890
  for _ in [0:10] do
    let (len, rng') := CRng.genArrayLength' rng 100
    IO.println s!"Array length: {len}"
    rng := rng'

/-- Run all examples -/
def main : IO Unit := do
  IO.println "=== Example 1: basic RNG ==="
  example1
  IO.println "\n=== Example 2: list lengths ==="
  example2
  IO.println "\n=== Example 3: array lengths ==="
  example3

-- Run examples
#eval main

end Examples
