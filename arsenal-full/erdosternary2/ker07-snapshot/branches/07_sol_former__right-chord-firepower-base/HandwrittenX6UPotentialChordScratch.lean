/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0976 / 1132
/-    Path         : branches/sol_right-chord-firepower-base/HandwrittenX6UPotentialChordScratch.lean
/-    Ref          : origin/sol/right-chord-firepower-base
/-    First-commit : 2026-08-17 10:18:28 +0530  (fd8e920)
/-    Last-commit  : 2026-08-17 10:18:28 +0530  (fd8e920)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 10:18:28 +0530  fd8e920  (ker07-dev)
/-        Connect handwritten x-6 fibre to U-potential orientation
/- ====================================================================== -/

import HandwrittenKernelV2Scratch
import HandwrittenUniversalParadoxPotentialScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Exact x-6 / orientation / U-potential chord

For one physical x4 GST cell, split the carry into its two binary bridge bits
and form the two microscopic x2 masses m1,m2.  Boss's handwritten singular
coordinate x-6 is taken here literally as x=(m1+m2).

Across the twelve legal cells the singular fibre x=6 consists of exactly two
points:

  (m1,m2)=(2,4)  hidden CREATE->DESTROY
  (m1,m2)=(4,2)  exposed DESTROY->CREATE

The antisymmetric orientation z=m2-m1 separates them.  The independently
derived U-potential jump epsilon is affine in z on this fibre:

  epsilon = 4 + 6*z.

Thus the two sides of the handwritten pole are exactly BAD (+16) and NULL
SURVIVE (-8).  This is a local finite theorem only; no global transport across
the pole is asserted here.
-/

def gstHandwrittenXCoordS (C d : Nat) : Nat :=
  gstFirstMicroMassS C d + gstSecondMicroMassS C d

def gstHandwrittenZOrientS (C d : Nat) : Int :=
  (gstSecondMicroMassS C d : Int) - (gstFirstMicroMassS C d : Int)

/-- The singular x=6 fibre contains precisely the hidden/exposed BIG2 pair. -/
theorem gst_handwritten_x_eq_six_iff_big2_orientationS
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    gstHandwrittenXCoordS C d = 6 ↔
      (C = 0 ∧ d = 1) ∨ (C = 0 ∧ d = 2) := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    decide

/-- Exact two coordinates on the singular fibre. -/
theorem gst_handwritten_x6_orientation_tableS :
    gstHandwrittenXCoordS 0 1 = 6 ∧
    gstHandwrittenZOrientS 0 1 = 2 ∧
    gstHandwrittenXCoordS 0 2 = 6 ∧
    gstHandwrittenZOrientS 0 2 = -2 := by
  decide

/-- On x=6 the U-potential jump is exactly 4+6z. -/
theorem gst_handwritten_x6_u_jump_orientationS
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hx : gstHandwrittenXCoordS C d = 6) :
    gstHandwrittenUJumpS C d = 4 + 6 * gstHandwrittenZOrientS C d := by
  have hor := (gst_handwritten_x_eq_six_iff_big2_orientationS C d hC hd).1 hx
  rcases hor with ⟨hC0,hd1⟩ | ⟨hC0,hd2⟩ <;>
    subst C <;> subst d <;> decide

/-- Positive orientation is the hidden BAD point of the singular fibre. -/
theorem gst_handwritten_x6_hidden_u_jumpS :
    gstHandwrittenUJumpS 0 1 = 16 ∧
      gstHandwrittenZOrientS 0 1 = 2 := by
  decide

/-- Negative orientation is the exposed NULL SURVIVE point. -/
theorem gst_handwritten_x6_exposed_u_jumpS :
    gstHandwrittenUJumpS 0 2 = -8 ∧
      gstHandwrittenZOrientS 0 2 = -2 := by
  decide

/-- Therefore on the singular fibre negative U curvature is equivalent to the
exposed orientation. -/
theorem gst_handwritten_x6_negative_iff_exposedS
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hx : gstHandwrittenXCoordS C d = 6) :
    gstHandwrittenUJumpS C d < 0 ↔ (C = 0 ∧ d = 2) := by
  have hor := (gst_handwritten_x_eq_six_iff_big2_orientationS C d hC hd).1 hx
  rcases hor with ⟨hC0,hd1⟩ | ⟨hC0,hd2⟩ <;>
    subst C <;> subst d <;> decide
