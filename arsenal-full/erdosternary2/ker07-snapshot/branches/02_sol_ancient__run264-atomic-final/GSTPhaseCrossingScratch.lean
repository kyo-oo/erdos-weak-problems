/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0606 / 1132
/-    Path         : branches/sol_run264-atomic-final/GSTPhaseCrossingScratch.lean
/-    Ref          : origin/sol/run264-atomic-final
/-    First-commit : 2026-08-16 13:11:10 +0530  (98c1fdd)
/-    Last-commit  : 2026-08-16 15:45:06 +0530  (97ab42d)
/-    Total commits: 4
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/4] 2026-08-16 13:11:10 +0530  98c1fdd  (ker07-dev)
/-        Add physical phase-crossing reduction scratch
/- [02/4] 2026-08-16 14:52:14 +0530  141d403  (ker07-dev)
/-        Test atomic prefix-one bad-trace contradiction
/- [03/4] 2026-08-16 15:08:48 +0530  24f7752  (ker07-dev)
/-        Restore phase-crossing scratch to independent green reduction
/- [04/4] 2026-08-16 15:45:06 +0530  97ab42d  (ker07-dev)
/-        Kernel-check atomic reduction helpers through phase scratch
/- ====================================================================== -/

import GSTResidueSpacetimeScratch
import AtomicPrefixOneReductionScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Physical phase-crossing reduction

This file does not assume the missing prefix-one crossing theorem.  It removes
all remaining event/Omega vocabulary from that seam and identifies both sides
with literal simultaneous +2 jumps in the exact power residue tower.
-/

/-- A seed-zero child Happy Gate is exactly a physical phase-zero double jump. -/
theorem gst_phase0_seeded_happy_iff_double_jumpS
    (D T E q : Nat) (hD : 3 ≤ D)
    (hE : E = 1 + 3*D*T) :
    (gstDigitS T q = 2 ∧
      (gstAffineMulCarryS 4 0 T q = 0 ∨
       gstAffineMulCarryS 4 0 T q = 3)) ↔
      GSTDoubleJumpS (3*D) E q := by
  rw [gst_seeded_happy_iff_common_twoS 0 T q (by decide)]
  simpa using gst_phase0_common_two_iff_double_jumpS D T E q hD hE

/-- A seed-one parent Happy Gate is exactly a physical phase-one double jump. -/
theorem gst_phase1_seeded_happy_iff_double_jumpS
    (D H E q : Nat) (hD : 3 ≤ D)
    (hE : E = 1 + D + 3*D*H) :
    (gstDigitS H q = 2 ∧
      (gstAffineMulCarryS 4 1 H q = 0 ∨
       gstAffineMulCarryS 4 1 H q = 3)) ↔
      GSTDoubleJumpS (3*D) E q := by
  rw [gst_seeded_happy_iff_common_twoS 1 H q (by decide)]
  simpa using gst_phase1_common_two_iff_double_jumpS D H E q hD hE

/-- Complete seed-one parent badness is precisely absence of every physical
phase-one double jump. -/
theorem gst_phase1_seeded_bad_iff_no_double_jumpS
    (D H E : Nat) (hD : 3 ≤ D)
    (hE : E = 1 + D + 3*D*H) :
    GSTSeededBadTraceS 1 H ↔
      ∀ q, ¬ GSTDoubleJumpS (3*D) E q := by
  constructor
  · intro hbad q hjump
    have hnoCommon :=
      (gst_seeded_bad_iff_no_common_twoS 1 H (by decide)).1 hbad q
    apply hnoCommon
    exact (gst_phase1_common_two_iff_double_jumpS D H E q hD hE).2 hjump
  · intro hno
    apply (gst_seeded_bad_iff_no_common_twoS 1 H (by decide)).2
    intro q hcommon
    apply hno q
    exact (gst_phase1_common_two_iff_double_jumpS D H E q hD hE).1 hcommon

/-- The exact remaining mathematical seam after the first forty green commits:
a phase-zero double jump must cross the phase-one wall.  This is deliberately a
property, not an axiom or theorem claim. -/
def GSTPhysicalPhaseCrossingS (D T H E0 E1 : Nat) : Prop :=
  (∃ q, GSTDoubleJumpS (3*D) E0 q) →
    ∃ q, GSTDoubleJumpS (3*D) E1 q

/-- Once the physical crossing property is supplied, a certified child gate
contradicts a completely bad phase-one parent immediately.  Thus future work
has exactly one target: prove `GSTPhysicalPhaseCrossingS` from the canonical
pure-power rectangle, rather than proving an artificial pointwise reflection. -/
theorem gst_physical_crossing_contradicts_parent_badS
    (D T H E0 E1 q0 : Nat)
    (hD : 3 ≤ D)
    (hE0 : E0 = 1 + 3*D*T)
    (hE1 : E1 = 1 + D + 3*D*H)
    (hcross : GSTPhysicalPhaseCrossingS D T H E0 E1)
    (hchild : gstDigitS T q0 = 2 ∧
      (gstAffineMulCarryS 4 0 T q0 = 0 ∨
       gstAffineMulCarryS 4 0 T q0 = 3))
    (hparentBad : GSTSeededBadTraceS 1 H) : False := by
  have h0 : GSTDoubleJumpS (3*D) E0 q0 :=
    (gst_phase0_seeded_happy_iff_double_jumpS D T E0 q0 hD hE0).1 hchild
  obtain ⟨q1, h1⟩ := hcross ⟨q0, h0⟩
  have hno :=
    (gst_phase1_seeded_bad_iff_no_double_jumpS D H E1 hD hE1).1 hparentBad
  exact hno q1 h1
