/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zenali
-/

import Lean
import Lean.Meta.Tactic.Simp

/-!
# Quickcheck Lemma Attribute

This module defines the `@[quickcheck]` attribute for marking lemmas that should
be used by SafeNorm for normalizing expressions before quickcheck testing.

Following Aesop's design philosophy, we use a theorem library with tagged lemmas
rather than direct expression manipulation.
-/

namespace Quickcheck

open Lean Meta

/-- Attribute for marking lemmas to be used by SafeNorm -/
initialize quickcheckExt : SimpExtension ←
  registerSimpAttr `quickcheck "Lemmas for Quickcheck SafeNorm normalization"

end Quickcheck
