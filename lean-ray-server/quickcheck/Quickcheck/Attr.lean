/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Kim Morrison
-/

import Lean.Util.Trace

open Lean

initialize registerTraceClass `quickcheck
initialize registerTraceClass `quickcheck.instance
initialize registerTraceClass `quickcheck.decoration
initialize registerTraceClass `quickcheck.discarded
initialize registerTraceClass `quickcheck.success
initialize registerTraceClass `quickcheck.shrink.steps
initialize registerTraceClass `quickcheck.shrink.candidates
initialize registerTraceClass `quickcheck.deriving.arbitrary
initialize registerTraceClass `quickcheck.preprocess
initialize registerTraceClass `quickcheck.safenorm
initialize registerTraceClass `quickcheck.adaptive
