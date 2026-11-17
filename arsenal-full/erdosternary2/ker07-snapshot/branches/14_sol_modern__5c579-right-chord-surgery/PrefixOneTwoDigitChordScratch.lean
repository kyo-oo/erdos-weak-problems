/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1052 / 1132
/-    Path         : branches/sol_5c579-right-chord-surgery/PrefixOneTwoDigitChordScratch.lean
/-    Ref          : origin/sol/5c579-right-chord-surgery
/-    First-commit : 2026-08-17 20:36:00 +0530  (a606e29)
/-    Last-commit  : 2026-08-17 20:44:04 +0530  (bf56a77)
/-    Total commits: 2
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/2] 2026-08-17 20:36:00 +0530  a606e29  (ker07-dev)
/-        surgery: isolate local two-digit BIG1 chord on physical x4 cells
/- [02/2] 2026-08-17 20:44:04 +0530  bf56a77  (ker07-dev)
/-        surgery: classify local two-digit chord into GST+ and NULL
/- ====================================================================== -/

import HandwrittenBig1PathProjectorScratch
import InformationForcingScratch
import HandwrittenUniversalParadoxPotentialScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Prefix-one two-digit right chord

Production scope correction.

Boss's handwritten condition `I ≠ 1` is used here ONLY while resolving one
actual physical x4 GST cell, i.e. exactly the two consecutive x2/base-3
microscopic bridge layers inside that cell.  It is not promoted to an
arbitrary-depth path hypothesis and it is not a horizontal-transport axiom.

The local chord is:

  actual nonzero BIG2 input
  + BIG1 excluded on the two microscopic outputs of this one x4 cell
  -> unique microscopic word 55_6
  -> mass code 35 = 6^2 - 1
  -> physical GST+ SURVIVE/SURVIVE.

If the local `I ≠ 1` blade is not available, we do not discard the cell.  At
an already-Happy BIG2 cell the complementary branch is exactly the physical
NULL word 42_6, which passes through BIG1 and is handed to the old
origin/regeneration/U machinery.  Thus `I ≠ 1` is a local classifier, never a
global premise.

Repeated use is legitimate only when each invocation has separately been
identified with an actual physical x4 cell by the canonical information/carry
machinery.
-/

/-- BIG1 exclusion restricted to one genuine two-micro-layer physical cell. -/
def GSTPhysicalTwoDigitBig1ClearS (R p : Nat) : Prop :=
  gstDigitS R p ≠ 1 ∧
  gstFirstMicroOutputS (gstCarryS R p) (gstDigitS R p) ≠ 1 ∧
  gstSecondMicroOutputS (gstCarryS R p) (gstDigitS R p) ≠ 1

/-- The two microscopic x2 layers really do reconstruct the ordinary x4 GST
output digit.  This is a finite twelve-cell identity, not a re-coordinate or
phase-transport assumption. -/
theorem gst_second_micro_output_eq_x4_outputS
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    gstSecondMicroOutputS C d = gstOutputDigitS C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    norm_num [gstSecondMicroOutputS, gstSecondMicroMassS,
      gstFirstMicroOutputS, gstFirstMicroMassS,
      gstMicroHighBitS, gstMicroLowBitS, gstOutputDigitS]

/-- RIGHT CHORD, local form.

At an actual physical cell whose input information is BIG2, applying Boss's
`I ≠ 1` only to this two-digit/two-micro-layer case kills the NULL
DESTROY->CREATE orientation and leaves exactly GST+ SURVIVE->SURVIVE.
The same state is the 55_6 / 35 boundary state of the aligned 36-state V2
cell. -/
theorem gst_physical_two_digit_chord_forces_gst_plusS
    (R p : Nat)
    (hd2 : gstDigitS R p = 2)
    (hI : GSTPhysicalTwoDigitBig1ClearS R p) :
    gstCarryS R p = 3 ∧
      gstPhysicalMicroPairS R p = (5, 5) ∧
      gstOutputDigitS (gstCarryS R p) (gstDigitS R p) = 2 ∧
      gstFirstMicroMassS (gstCarryS R p) (gstDigitS R p) +
        6 * gstSecondMicroMassS (gstCarryS R p) (gstDigitS R p) = 35 := by
  have hC : gstCarryS R p < 4 := gst_carryS_lt_four_allS R p
  have hd : gstDigitS R p < 3 := gst_digitS_lt_three_allS R p
  have hd0 : gstDigitS R p ≠ 0 := by omega
  obtain ⟨hC3, _hd2, _hmid2, hout2, hM1, hM2⟩ :=
    gst_big1_projector_two_layer_forces_plus_surviveS
      (gstCarryS R p) (gstDigitS R p) hC hd hd0 hI.1 hI.2.1 hI.2.2
  refine ⟨hC3, ?_, ?_, ?_⟩
  · unfold gstPhysicalMicroPairS
    rw [hM1, hM2]
  · rw [← gst_second_micro_output_eq_x4_outputS
      (gstCarryS R p) (gstDigitS R p) hC hd]
    exact hout2
  · rw [hM1, hM2]

/-- Event-word face of the same chord: after the local two-digit projector the
only nonzero physical realization has the ordered microscopic event pair
(8,8).  This is the EQ2 event-word SURVIVE symbol on both x2 layers. -/
theorem gst_physical_two_digit_chord_event_88S
    (R p : Nat)
    (hd2 : gstDigitS R p = 2)
    (hI : GSTPhysicalTwoDigitBig1ClearS R p) :
    gstBinaryBridgeEventS
        (gstMicroHighBitS (gstCarryS R p)) (gstDigitS R p) = 8 ∧
      gstBinaryBridgeEventS
        (gstMicroLowBitS (gstCarryS R p))
        (gstFirstMicroOutputS (gstCarryS R p) (gstDigitS R p)) = 8 := by
  have h := gst_physical_two_digit_chord_forces_gst_plusS R p hd2 hI
  rw [h.1, hd2]
  decide

/-- The numerical chord shared by the two-digit projector, the six-state
bridge universe, and the 36-state V2 boundary. -/
theorem gst_physical_two_digit_chord_35S
    (R p : Nat)
    (hd2 : gstDigitS R p = 2)
    (hI : GSTPhysicalTwoDigitBig1ClearS R p) :
    gstFirstMicroMassS (gstCarryS R p) (gstDigitS R p) +
        6 * gstSecondMicroMassS (gstCarryS R p) (gstDigitS R p) =
      6^2 - 1 := by
  rw [(gst_physical_two_digit_chord_forces_gst_plusS R p hd2 hI).2.2.2]
  decide

/-! ## Exhaustive local classification at an actual Happy BIG2 cell -/

/-- At a physical Happy digit-two cell, Boss's local `I ≠ 1` condition is
*equivalent* to being the GST+ carry-three orientation.  The NULL carry-zero
orientation is exactly the complementary cell because its first x2 layer
emits BIG1.  This theorem is the scope firewall preventing accidental global
use of `I ≠ 1`. -/
theorem gst_happy_big2_two_digit_clear_iff_plusS
    (R p : Nat)
    (hd2 : gstDigitS R p = 2)
    (hhappy : gstCarryS R p = 0 ∨ gstCarryS R p = 3) :
    GSTPhysicalTwoDigitBig1ClearS R p ↔ gstCarryS R p = 3 := by
  unfold GSTPhysicalTwoDigitBig1ClearS
  rcases hhappy with h0 | h3
  · rw [h0, hd2]
    decide
  · rw [h3, hd2]
    decide

/-- The complementary local branch is exactly NULL.  No information is lost:
when `I ≠ 1` fails at an already-Happy BIG2 cell, the physical word is 42_6,
its first micro-output is BIG1, its event word is DESTROY->CREATE = (5,7), and
its handwritten U jump is the exact NULL value -8. -/
theorem gst_happy_big2_two_digit_not_clear_is_nullS
    (R p : Nat)
    (hd2 : gstDigitS R p = 2)
    (hhappy : gstCarryS R p = 0 ∨ gstCarryS R p = 3)
    (hnot : ¬ GSTPhysicalTwoDigitBig1ClearS R p) :
    gstCarryS R p = 0 ∧
      gstPhysicalMicroPairS R p = (4, 2) ∧
      gstFirstMicroOutputS (gstCarryS R p) (gstDigitS R p) = 1 ∧
      gstBinaryBridgeEventS
          (gstMicroHighBitS (gstCarryS R p)) (gstDigitS R p) = 5 ∧
      gstBinaryBridgeEventS
          (gstMicroLowBitS (gstCarryS R p))
          (gstFirstMicroOutputS (gstCarryS R p) (gstDigitS R p)) = 7 ∧
      gstHandwrittenUJumpS (gstCarryS R p) (gstDigitS R p) = -8 := by
  have hiff := gst_happy_big2_two_digit_clear_iff_plusS R p hd2 hhappy
  have h0 : gstCarryS R p = 0 := by
    rcases hhappy with hzero | hthree
    · exact hzero
    · exfalso
      apply hnot
      exact hiff.mpr hthree
  rw [h0, hd2]
  decide

/-- Complete right-chord dichotomy.  There is no third physical Happy BIG2
orientation.  The clear branch is GST+ 55_6 / (8,8) / code 35 / U=-6; the
non-clear branch is NULL 42_6 / (5,7) / BIG1 crossing / U=-8.  Global proof
logic must dispatch the second branch through canonical origin regeneration,
not by strengthening the `I ≠ 1` premise. -/
theorem gst_happy_big2_right_chord_dichotomyS
    (R p : Nat)
    (hd2 : gstDigitS R p = 2)
    (hhappy : gstCarryS R p = 0 ∨ gstCarryS R p = 3) :
    (GSTPhysicalTwoDigitBig1ClearS R p ∧
      gstCarryS R p = 3 ∧
      gstPhysicalMicroPairS R p = (5, 5) ∧
      gstBinaryBridgeEventS
          (gstMicroHighBitS (gstCarryS R p)) (gstDigitS R p) = 8 ∧
      gstBinaryBridgeEventS
          (gstMicroLowBitS (gstCarryS R p))
          (gstFirstMicroOutputS (gstCarryS R p) (gstDigitS R p)) = 8 ∧
      gstFirstMicroMassS (gstCarryS R p) (gstDigitS R p) +
          6 * gstSecondMicroMassS (gstCarryS R p) (gstDigitS R p) = 35 ∧
      gstHandwrittenUJumpS (gstCarryS R p) (gstDigitS R p) = -6) ∨
    (¬ GSTPhysicalTwoDigitBig1ClearS R p ∧
      gstCarryS R p = 0 ∧
      gstPhysicalMicroPairS R p = (4, 2) ∧
      gstFirstMicroOutputS (gstCarryS R p) (gstDigitS R p) = 1 ∧
      gstBinaryBridgeEventS
          (gstMicroHighBitS (gstCarryS R p)) (gstDigitS R p) = 5 ∧
      gstBinaryBridgeEventS
          (gstMicroLowBitS (gstCarryS R p))
          (gstFirstMicroOutputS (gstCarryS R p) (gstDigitS R p)) = 7 ∧
      gstHandwrittenUJumpS (gstCarryS R p) (gstDigitS R p) = -8) := by
  by_cases hI : GSTPhysicalTwoDigitBig1ClearS R p
  · left
    have hplus := gst_physical_two_digit_chord_forces_gst_plusS R p hd2 hI
    have hevents := gst_physical_two_digit_chord_event_88S R p hd2 hI
    refine ⟨hI, hplus.1, hplus.2.1, hevents.1, hevents.2,
      hplus.2.2.2, ?_⟩
    rw [hplus.1, hd2]
    decide
  · right
    have hnull := gst_happy_big2_two_digit_not_clear_is_nullS
      R p hd2 hhappy hI
    exact ⟨hI, hnull⟩
