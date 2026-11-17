/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1048 / 1132
/-    Path         : branches/sol_global-flux-surgery/GlobalPrefixOneFluxSurgeryScratch.lean
/-    Ref          : origin/sol/global-flux-surgery
/-    First-commit : 2026-08-17 14:09:02 +0530  (4c5b11f)
/-    Last-commit  : 2026-08-17 14:09:02 +0530  (4c5b11f)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 14:09:02 +0530  4c5b11f  (ker07-dev)
/-        Add exact x2 physical flux bridge for prefix-one surgery
/- ====================================================================== -/

import HandwrittenSignedKernelFluxScratch
import StripConservationScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Global prefix-one flux surgery

This file connects the handwritten signed x2 kernel to the *physical* power
columns.  It introduces no forcing principle and no residual termination
assumption.

For a fixed ternary row `p`, column `i` is the actual power column
`2^i * R`.  The incoming binary carry for the microscopic x2 bridge is the
ordinary wide carry for multiplication by two at that row.  Consequently the
microscopic bridge output is definitionally the ternary digit of the next
physical power column.

This is the exact bridge needed before the BIG1 projector can be used in the
historical prefix-one surgery: CREATE/DESTROY cancellation and the SURVIVE
residual are now attached to real adjacent power columns rather than to an
abstract bridge path.
-/

/-- Binary carry entering the physical x2 bridge at power-column `i`. -/
def gstPhysicalBinaryCarryS (R i p : Nat) : Nat :=
  gstWideCarryS 2 (2^i * R) p

/-- Ternary information digit at power-column `i`. -/
def gstPhysicalBinaryDigitS (R i p : Nat) : Nat :=
  gstWideDigitS (2^i * R) p

/-- Every physical x2 carry is one binary bit. -/
theorem gst_physical_binary_carry_lt_twoS
    (R i p : Nat) : gstPhysicalBinaryCarryS R i p < 2 := by
  unfold gstPhysicalBinaryCarryS gstWideCarryS
  have hM : 0 < 3^p := Nat.pow_pos (by decide)
  have hr : (2^i * R) % 3^p < 3^p := Nat.mod_lt _ hM
  have hnum : 2 * ((2^i * R) % 3^p) < 3^p * 2 := by
    have h := Nat.mul_lt_mul_of_pos_left hr (by decide : 0 < 2)
    simpa [Nat.mul_comm] using h
  exact Nat.div_lt_of_lt_mul hnum

/-- Every physical column digit is a legal ternary digit. -/
theorem gst_physical_binary_digit_lt_threeS
    (R i p : Nat) : gstPhysicalBinaryDigitS R i p < 3 := by
  unfold gstPhysicalBinaryDigitS gstWideDigitS
  exact Nat.mod_lt _ (by decide)

/-- The abstract microscopic output is exactly the digit of the next physical
power column. -/
theorem gst_physical_binary_output_is_next_digitS
    (R i p : Nat) :
    gstMicroEventOutputS
        (gstPhysicalBinaryCarryS R i p)
        (gstPhysicalBinaryDigitS R i p) =
      gstPhysicalBinaryDigitS R (i+1) p := by
  have hout := gst_wide_output_digit_exactS 2 (2^i * R) p
  have hpow : 2 * (2^i * R) = 2^(i+1) * R := by
    rw [Nat.pow_succ]
    ring
  unfold gstPhysicalBinaryCarryS gstPhysicalBinaryDigitS
  unfold gstMicroEventOutputS
  rw [hpow] at hout
  exact hout.symm

/-- The signed BIG2 flux of one microscopic bridge is therefore the literal
difference of BIG2 indicators on two adjacent physical power columns. -/
theorem gst_physical_micro_big2_flux_exactS
    (R i p : Nat) :
    gstMicroBig2FluxS
        (gstPhysicalBinaryCarryS R i p)
        (gstPhysicalBinaryDigitS R i p) =
      7 *
        (gstMicroTwoIndicatorS (gstPhysicalBinaryDigitS R (i+1) p) -
         gstMicroTwoIndicatorS (gstPhysicalBinaryDigitS R i p)) := by
  rw [gst_micro_big2_flux_exactS]
  rw [gst_physical_binary_output_is_next_digitS]

/-- Physical form of Boss's signed-kernel decomposition.  The first term is a
true horizontal boundary flux; the second term is exactly the microscopic
SURVIVE residual between adjacent physical power columns. -/
theorem gst_physical_micro_kernel_decomposeS
    (R i p : Nat) :
    gstMicroKernelTwiceS
        (gstPhysicalBinaryCarryS R i p)
        (gstPhysicalBinaryDigitS R i p) =
      14 *
        (gstMicroTwoIndicatorS (gstPhysicalBinaryDigitS R (i+1) p) -
         gstMicroTwoIndicatorS (gstPhysicalBinaryDigitS R i p)) +
      7 *
        gstMicroTwoIndicatorS (gstPhysicalBinaryDigitS R i p) *
        gstMicroTwoIndicatorS (gstPhysicalBinaryDigitS R (i+1) p) := by
  rw [gst_micro_kernel_twice_decomposeS]
  rw [gst_physical_micro_big2_flux_exactS]
  rw [gst_physical_binary_output_is_next_digitS]
  ring

/-- Two microscopic columns are one physical x4 window.  If BIG2 occurs at
both x4 endpoints, the boundary-flux terms cancel exactly.  What remains is
only the two microscopic SURVIVE residuals.  Thus the BIG1 midpoint is the
only place where an x4 NULL rerouting can differ from the all-SURVIVE path. -/
theorem gst_physical_x4_endpoint_big2_kernel_chordS
    (R i p : Nat)
    (hleft : gstPhysicalBinaryDigitS R i p = 2)
    (hright : gstPhysicalBinaryDigitS R (i+2) p = 2) :
    gstMicroKernelTwiceS
        (gstPhysicalBinaryCarryS R i p)
        (gstPhysicalBinaryDigitS R i p) +
      gstMicroKernelTwiceS
        (gstPhysicalBinaryCarryS R (i+1) p)
        (gstPhysicalBinaryDigitS R (i+1) p) =
      14 * gstMicroTwoIndicatorS (gstPhysicalBinaryDigitS R (i+1) p) := by
  have h0 := gst_physical_micro_kernel_decomposeS R i p
  have h1 := gst_physical_micro_kernel_decomposeS R (i+1) p
  rw [hleft, hright] at h0 h1
  simp [gstMicroTwoIndicatorS] at h0 h1 ⊢
  linarith

/-- Pathwise BIG1-clear specialization of the physical x4 chord.  Once the
midpoint is also BIG2, the two-layer physical packet carries the nonzero
SURVIVE residual `14`; no CREATE/DESTROY cancellation remains. -/
theorem gst_physical_x4_big1_clear_kernel_chordS
    (R i p : Nat)
    (hleft : gstPhysicalBinaryDigitS R i p = 2)
    (hmiddle : gstPhysicalBinaryDigitS R (i+1) p = 2)
    (hright : gstPhysicalBinaryDigitS R (i+2) p = 2) :
    gstMicroKernelTwiceS
        (gstPhysicalBinaryCarryS R i p)
        (gstPhysicalBinaryDigitS R i p) +
      gstMicroKernelTwiceS
        (gstPhysicalBinaryCarryS R (i+1) p)
        (gstPhysicalBinaryDigitS R (i+1) p) = 14 := by
  rw [gst_physical_x4_endpoint_big2_kernel_chordS R i p hleft hright,
      hmiddle]
  decide
