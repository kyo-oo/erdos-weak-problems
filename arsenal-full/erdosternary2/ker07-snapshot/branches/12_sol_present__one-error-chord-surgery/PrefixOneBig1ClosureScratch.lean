/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1059 / 1132
/-    Path         : branches/sol_one-error-chord-surgery/PrefixOneBig1ClosureScratch.lean
/-    Ref          : origin/sol/one-error-chord-surgery
/-    First-commit : 2026-08-17 21:05:12 +0530  (b961a36)
/-    Last-commit  : 2026-08-17 21:05:12 +0530  (b961a36)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 21:05:12 +0530  b961a36  (ker07-dev)
/-        test: pin prefix-one child-gate survive closure
/- ====================================================================== -/

import ErdosTernary2

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Prefix-one BIG1 chord closure — RED integration target

This file is intentionally the first compile target of the surgery.
It pins the exact theorem that must replace the residual-omega dependency in
the historical 401,200-byte monolith.

Important scope rule from Boss's handwritten operator:
`I ≠ BIG1` is NOT a global/public hypothesis.  It may only be invoked when a
concrete two-digit information cell is being resolved.  The public closure
below therefore carries no `I ≠ 1` parameter.
-/

/-- RED test: the surgery is complete only when this theorem is provided by the
new canonical two-digit chord closure. -/
example
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (data : GSTPrefixOneOmegaData s n) :
    ∃ j, gstOmegaEvent s 1 n j = .survive := by
  exact gst_prefix_one_child_gate_forces_parent_survive_inline
    s n hs hn data
