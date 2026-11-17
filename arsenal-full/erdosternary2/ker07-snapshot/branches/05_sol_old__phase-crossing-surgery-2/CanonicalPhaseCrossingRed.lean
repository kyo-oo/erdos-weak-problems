/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0692 / 1132
/-    Path         : branches/sol_phase-crossing-surgery-2/CanonicalPhaseCrossingRed.lean
/-    Ref          : origin/sol/phase-crossing-surgery-2
/-    First-commit : 2026-08-17 00:18:14 +0530  (9b0efcf)
/-    Last-commit  : 2026-08-17 00:18:14 +0530  (9b0efcf)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 00:18:14 +0530  9b0efcf  (ker07-dev)
/-        Add RED test for canonical physical phase crossing
/- ====================================================================== -/

import GSTPhaseCrossingScratch
import PurePowerBadAxisScratch
import PurePowerResidueGraphScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
RED test for the comparator surgery.

This file deliberately states only the canonical prefix-one physical crossing
needed to replace the quarantined residual-Omega dependency.  No legacy
`GSTResidualNavigationLift`, no Omega termination theorem, and no universal
Erdos theorem are imported as proof shortcuts.
-/

/-- Canonical prefix-one phase crossing: the child and parent energies are the
same exact pure-power rectangle, with the child carrying seed 0 and the parent
forced prefix carrying seed 1. -/
theorem gst_canonical_prefix_one_physical_crossing_red
    (s n T H E0 E1 : Nat)
    (hs : 1 ≤ s)
    (hT : T = gstNavigationConstantS (s+1) n)
    (hH : H = cS s / 3 + 4^(3^s) * T)
    (hE0 : E0 = 1 + 3 * 3^(s+1) * T)
    (hE1 : E1 = 4^(3^s) * E0) :
    GSTPhysicalPhaseCrossingS (3^(s+1)) T H E0 E1 := by
  -- Expected RED frontier: prove transport of one literal double jump across
  -- the exact canonical power rectangle.
  intro h0
  exact gst_canonical_prefix_one_physical_crossing_transport
    s n T H E0 E1 hs hT hH hE0 hE1 h0
