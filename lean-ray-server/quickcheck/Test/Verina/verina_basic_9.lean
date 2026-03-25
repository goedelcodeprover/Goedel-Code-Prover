import Quickcheck
import Quickcheck.Lemma.ArrayLogics
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_9


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def hasCommonElement_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0 ∧ b.size > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def hasCommonElement (a : Array Int) (b : Array Int) (h_precond : hasCommonElement_precond (a) (b)) : Bool :=
  -- !benchmark @start code
  a.any fun x => b.any fun y => x = y
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def hasCommonElement_postcond (a : Array Int) (b : Array Int) (result: Bool) (h_precond : hasCommonElement_precond (a) (b)) :=
  -- !benchmark @start postcond
  (∃ i j, i < a.size ∧ j < b.size ∧ a[i]! = b[j]!) ↔ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux

theorem hasCommonElement_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : hasCommonElement_precond (a) (b)) :
    hasCommonElement_postcond (a) (b) (hasCommonElement (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold hasCommonElement_postcond
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, safeNormUnrollBound := 10, quiet := true })

  -- !benchmark @end proof
end verina_basic_9
