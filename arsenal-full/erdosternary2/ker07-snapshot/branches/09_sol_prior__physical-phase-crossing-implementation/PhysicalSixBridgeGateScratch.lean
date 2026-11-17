/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1027 / 1132
/-    Path         : branches/sol_physical-phase-crossing-implementation/PhysicalSixBridgeGateScratch.lean
/-    Ref          : origin/sol/physical-phase-crossing-implementation
/-    First-commit : 2026-08-17 11:18:13 +0530  (6c6d261)
/-    Last-commit  : 2026-08-17 11:18:40 +0530  (7745ad1)
/-    Total commits: 2
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/2] 2026-08-17 11:18:13 +0530  6c6d261  (ker07-dev)
/-        Add exact physical six-state gate dictionary
/- [02/2] 2026-08-17 11:18:40 +0530  7745ad1  (ker07-dev)
/-        Harden physical six-state gate dictionary
/- ====================================================================== -/

import CanonicalOriginCutIntersectionScratch
import HandwrittenKernelV2Scratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Exact physical six-state bridge form of a GST Happy Gate

One ordinary x4 GST cell is two consecutive x2/base-3 bridge cells.  This file
packages the exact gate condition in those two microscopic six-state masses.
No phase-order or horizontal-transport claim is made here.
-/

/-- The ordered pair of microscopic x2 masses of one physical GST cell. -/
def gstPhysicalMicroPairS (R p : Nat) : Nat × Nat :=
  let C := gstCarryS R p
  let d := gstDigitS R p
  (gstFirstMicroMassS C d, gstSecondMicroMassS C d)

/-- Scratch GST carries are legal four-state carries at every cut. -/
theorem gst_carryS_lt_four_allS (R p : Nat) :
    gstCarryS R p < 4 := by
  have h := gst_affine_carry_lt_multiplierS 4 0 R p
    (by decide : 0 < 4) (by decide : 0 < 4)
  simpa [gstCarryS, gstAffineMulCarryS] using h

/-- Scratch ternary digits are always legal three-state digits. -/
theorem gst_digitS_lt_three_allS (R p : Nat) :
    gstDigitS R p < 3 := by
  unfold gstDigitS
  exact Nat.mod_lt _ (by decide)

/-- Finite twelve-cell classification: a GST Happy state is exactly one of the
two microscopic six-state patterns

  (4,2) = DESTROY -> CREATE  (NULL realization),
  (5,5) = SURVIVE -> SURVIVE (GST+ realization).
-/
theorem gst_micro_pair_happy_iffS
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    (d = 2 ∧ (C = 0 ∨ C = 3)) ↔
      ((gstFirstMicroMassS C d = 4 ∧ gstSecondMicroMassS C d = 2) ∨
       (gstFirstMicroMassS C d = 5 ∧ gstSecondMicroMassS C d = 5)) := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    norm_num [gstFirstMicroMassS, gstSecondMicroMassS,
      gstMicroHighBitS, gstMicroLowBitS, gstFirstMicroOutputS]

/-- Exact physical gate dictionary for an arbitrary natural R at row p. -/
theorem gst_physical_micro_pair_happy_iffS
    (R p : Nat) :
    (gstDigitS R p = 2 ∧
      (gstCarryS R p = 0 ∨ gstCarryS R p = 3)) ↔
      (gstPhysicalMicroPairS R p = (4,2) ∨
       gstPhysicalMicroPairS R p = (5,5)) := by
  have hC := gst_carryS_lt_four_allS R p
  have hd := gst_digitS_lt_three_allS R p
  have hiff := gst_micro_pair_happy_iffS
    (gstCarryS R p) (gstDigitS R p) hC hd
  simpa [gstPhysicalMicroPairS] using hiff

/-- Under a physical bad-pair hypothesis, both microscopic Happy patterns are
forbidden at the same cell. -/
theorem gst_physical_bad_forbids_happy_micro_pairsS
    (R p : Nat)
    (hbad : GSTBadPairS (gstCarryS R p) (gstDigitS R p)) :
    gstPhysicalMicroPairS R p ≠ (4,2) ∧
      gstPhysicalMicroPairS R p ≠ (5,5) := by
  constructor
  · intro h42
    apply hbad
    exact (gst_physical_micro_pair_happy_iffS R p).2 (Or.inl h42)
  · intro h55
    apply hbad
    exact (gst_physical_micro_pair_happy_iffS R p).2 (Or.inr h55)
