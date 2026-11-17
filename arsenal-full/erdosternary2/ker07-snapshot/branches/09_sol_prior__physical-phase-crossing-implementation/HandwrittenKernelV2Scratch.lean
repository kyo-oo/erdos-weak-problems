/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0925 / 1132
/-    Path         : branches/sol_physical-phase-crossing-implementation/HandwrittenKernelV2Scratch.lean
/-    Ref          : origin/sol/physical-phase-crossing-implementation
/-    First-commit : 2026-08-17 08:28:38 +0530  (9fcd291)
/-    Last-commit  : 2026-08-17 08:28:38 +0530  (9fcd291)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 08:28:38 +0530  9fcd291  (ker07-dev)
/-        Formalize handwritten kernel six-state V2 orbit
/- ====================================================================== -/

import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Handwritten kernel on the fundamental six-state bridge

A single multiply-by-two/base-three bridge cell has mass

    m = a + 2*d,   a in {0,1}, d in {0,1,2},

hence `m < 6`.  Its alternate coordinate reading is

    R6(m) = floor(m/3) + 2*(m mod 3).

Boss's kernel magnitude `|7/(m-6)|` has denominator `6-m` on the physical
spectrum.  We keep the exact integer denominator here; all ratio statements
are expressed by cross multiplication, so no analytic structure is assumed.
-/

def gstMicroRotate6S (m : Nat) : Nat := m / 3 + 2*(m % 3)

def gstHandwrittenKernelDenomS (m : Nat) : Nat := 6 - m

/-- Exact six-state re-coordinate table. -/
theorem gst_micro_rotate6_tableS :
    gstMicroRotate6S 0 = 0 ∧
    gstMicroRotate6S 1 = 2 ∧
    gstMicroRotate6S 2 = 4 ∧
    gstMicroRotate6S 4 = 3 ∧
    gstMicroRotate6S 3 = 1 ∧
    gstMicroRotate6S 5 = 5 := by
  decide

/-- The only fixed bridge masses are the all-zero state and BIG2 SURVIVE. -/
theorem gst_micro_rotate6_fixed_iffS
    (m : Nat) (hm : m < 6) :
    gstMicroRotate6S m = m ↔ m = 0 ∨ m = 5 := by
  have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 <;>
    subst m <;> decide

/-- Thus the unique nonzero fixed state is mass five. -/
theorem gst_micro_rotate6_nonzero_fixedS
    (m : Nat) (hm : m < 6) (hm0 : m ≠ 0)
    (hfix : gstMicroRotate6S m = m) :
    m = 5 := by
  rcases (gst_micro_rotate6_fixed_iffS m hm).1 hfix with h0 | h5
  · exact False.elim (hm0 h0)
  · exact h5

/-- The proper alternate orbit has exact period four. -/
theorem gst_micro_rotate6_four_cycleS :
    gstMicroRotate6S (gstMicroRotate6S
      (gstMicroRotate6S (gstMicroRotate6S 1))) = 1 := by
  decide

/-- Kernel denominators on the active BIG2 masses. -/
theorem gst_handwritten_kernel_active_denomsS :
    gstHandwrittenKernelDenomS 2 = 4 ∧
    gstHandwrittenKernelDenomS 4 = 2 ∧
    gstHandwrittenKernelDenomS 5 = 1 := by
  decide

/-- CREATE -> DESTROY doubles the magnitude of 7/(6-m): denominator halves. -/
theorem gst_handwritten_kernel_create_destroy_doubleS :
    gstHandwrittenKernelDenomS 2 =
      2 * gstHandwrittenKernelDenomS 4 := by
  decide

/-- The reversed DESTROY -> CREATE orientation halves the kernel magnitude. -/
theorem gst_handwritten_kernel_destroy_create_halfS :
    2 * gstHandwrittenKernelDenomS 4 =
      gstHandwrittenKernelDenomS 2 := by
  decide

/-- SURVIVE is the nonzero fixed kernel state. -/
theorem gst_handwritten_kernel_survive_fixedS :
    gstMicroRotate6S 5 = 5 ∧ gstHandwrittenKernelDenomS 5 = 1 := by
  decide

/-- Integer cross-product form of telescoping around the complete nonfixed
four-cycle.  It is the denominator counterpart of

  K(2)/K(1) * K(4)/K(2) * K(3)/K(4) * K(1)/K(3) = 1.
-/
theorem gst_handwritten_kernel_cycle_telescopesS :
    gstHandwrittenKernelDenomS 1 *
      gstHandwrittenKernelDenomS 2 *
      gstHandwrittenKernelDenomS 4 *
      gstHandwrittenKernelDenomS 3 =
    gstHandwrittenKernelDenomS 2 *
      gstHandwrittenKernelDenomS 4 *
      gstHandwrittenKernelDenomS 3 *
      gstHandwrittenKernelDenomS 1 := by
  ring

/-- Decompose a legal x4 GST carry into its two binary bridge carries. -/
def gstMicroHighBitS (C : Nat) : Nat := C / 2
def gstMicroLowBitS (C : Nat) : Nat := C % 2

/-- First x2 bridge mass inside one x4 GST cell. -/
def gstFirstMicroMassS (C d : Nat) : Nat := gstMicroHighBitS C + 2*d

/-- Intermediate ternary digit emitted by the first x2 bridge. -/
def gstFirstMicroOutputS (C d : Nat) : Nat := gstFirstMicroMassS C d % 3

/-- Second x2 bridge mass inside one x4 GST cell. -/
def gstSecondMicroMassS (C d : Nat) : Nat :=
  gstMicroLowBitS C + 2*gstFirstMicroOutputS C d

/-- Exact microscopic patterns of the three canonical BIG2 orientations. -/
theorem gst_micro_big2_orientation_tableS :
    (gstFirstMicroMassS 0 1, gstSecondMicroMassS 0 1) = (2,4) ∧
    (gstFirstMicroMassS 0 2, gstSecondMicroMassS 0 2) = (4,2) ∧
    (gstFirstMicroMassS 3 2, gstSecondMicroMassS 3 2) = (5,5) := by
  decide

/-- The kernel orientation associated to phase-one hidden BIG2 is exactly a
binary factor two in cross-multiplied denominator form. -/
theorem gst_phase_one_micro_kernel_factor_twoS :
    gstHandwrittenKernelDenomS (gstFirstMicroMassS 0 1) =
      2 * gstHandwrittenKernelDenomS (gstSecondMicroMassS 0 1) := by
  decide

/-- Phase two reverses the same factor. -/
theorem gst_phase_two_micro_kernel_factor_halfS :
    2 * gstHandwrittenKernelDenomS (gstFirstMicroMassS 0 2) =
      gstHandwrittenKernelDenomS (gstSecondMicroMassS 0 2) := by
  decide

/-- GST+ SURVIVE is fixed in both microscopic layers. -/
theorem gst_plus_survive_micro_kernel_fixedS :
    gstFirstMicroMassS 3 2 = 5 ∧
      gstSecondMicroMassS 3 2 = 5 := by
  decide
