/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0691 / 1132
/-    Path         : branches/sol_phase-crossing-surgery/GSTPhaseCrossingTransferScratch.lean
/-    Ref          : origin/sol/phase-crossing-surgery
/-    First-commit : 2026-08-16 23:23:30 +0530  (5b7808e)
/-    Last-commit  : 2026-08-16 23:23:30 +0530  (5b7808e)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-16 23:23:30 +0530  5b7808e  (ker07-dev)
/-        Add exact vertical correction handoff for phase crossing
/- ====================================================================== -/

import GSTPhaseCrossingCarrierScratch
import PhaseCycleInformationScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Exact vertical handoff for the phase-crossing surgery

The horizontal phase multiplier is a power of four.  At one ternary row the
two wide carries

  Z = carry of A*R,
  W = carry of A*(4R)

are the correction coordinates transporting the adjacent child pair R,4R to
the adjacent phase pair A*R,A*(4R).  No global mirror or terminal state is
assumed.
-/

/-- Exact commuting square for the two adjacent multiplication axes. -/
theorem gst_power_wide_carry_commuting_squareS
    (N R p : Nat) :
    gstWideCarryS (4^N) (4*R) p +
        4^N * gstWideCarryS 4 R p =
      gstWideCarryS 4 (4^N*R) p +
        4 * gstWideCarryS (4^N) R p := by
  have hcommute :
      0 + 4^N * (0 + 4*R) =
        0 + 4 * (0 + 4^N*R) := by ring
  have h := gst_seeded_shared_information_equationS
    (4^N) 0 0 0 0 R p hcommute
  simpa [gstWideCarryS, gstAffineMulCarryS] using h

/-- If the child adjacent powers share digit two at row p, then the phase-one
adjacent powers share digit two at that same row exactly when both vertical
correction carries vanish modulo three. -/
theorem gst_power_common_two_crosses_same_row_iffS
    (N R p : Nat)
    (hchild :
      gstWideDigitS R p = 2 ∧
      gstWideDigitS (4*R) p = 2) :
    (gstWideDigitS (4^N*R) p = 2 ∧
      gstWideDigitS (4^N*(4*R)) p = 2) ↔
    (gstWideCarryS (4^N) R p % 3 = 0 ∧
      gstWideCarryS (4^N) (4*R) p % 3 = 0) := by
  rw [gst_power_strip_digit_two_iff_quotient_mod_three_zeroS
        R p N hchild.1,
      gst_power_strip_digit_two_iff_quotient_mod_three_zeroS
        (4*R) p N hchild.2]
  rw [← gst_power_wide_carry_is_strip_quotientS R p N,
      ← gst_power_wide_carry_is_strip_quotientS (4*R) p N]

/-- Therefore failure to cross a child common-two at the same row is not loss
of information: at least one exact correction coordinate is still nonzero
modulo three. -/
theorem gst_power_common_two_failed_same_row_has_live_correctionS
    (N R p : Nat)
    (hchild :
      gstWideDigitS R p = 2 ∧
      gstWideDigitS (4*R) p = 2)
    (hfail :
      ¬ (gstWideDigitS (4^N*R) p = 2 ∧
         gstWideDigitS (4^N*(4*R)) p = 2)) :
    gstWideCarryS (4^N) R p % 3 ≠ 0 ∨
      gstWideCarryS (4^N) (4*R) p % 3 ≠ 0 := by
  have hiff := gst_power_common_two_crosses_same_row_iffS N R p hchild
  by_contra hno
  push_neg at hno
  exact hfail (hiff.mpr hno)

/-- The correction coordinate itself obeys the ordinary vertical carry law. -/
theorem gst_power_wide_correction_forwardS
    (N R p : Nat) :
    gstWideCarryS (4^N) R (p+1) =
      (gstWideCarryS (4^N) R p +
        4^N * gstWideDigitS R p) / 3 := by
  exact gst_wide_carry_forward_exactS (4^N) R p

/-- At a child common-two row both correction coordinates receive the same
explicit +2A packet before the next ternary cut. -/
theorem gst_power_common_two_corrections_forwardS
    (N R p : Nat)
    (hchild :
      gstWideDigitS R p = 2 ∧
      gstWideDigitS (4*R) p = 2) :
    gstWideCarryS (4^N) R (p+1) =
        (gstWideCarryS (4^N) R p + 2*4^N) / 3 ∧
      gstWideCarryS (4^N) (4*R) (p+1) =
        (gstWideCarryS (4^N) (4*R) p + 2*4^N) / 3 := by
  constructor
  · rw [gst_power_wide_correction_forwardS, hchild.1]
    ring_nf
  · rw [gst_power_wide_correction_forwardS, hchild.2]
    ring_nf
