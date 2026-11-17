/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1054 / 1132
/-    Path         : branches/sol_5c579-right-chord-surgery/PrefixOneRightChordLastGateScratch.lean
/-    Ref          : origin/sol/5c579-right-chord-surgery
/-    First-commit : 2026-08-17 20:44:53 +0530  (e737688)
/-    Last-commit  : 2026-08-17 20:44:53 +0530  (e737688)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 20:44:53 +0530  e737688  (ker07-dev)
/-        surgery: attach two-digit right chord to actual last child gate
/- ====================================================================== -/

import PrefixOneTwoDigitChordScratch
import CanonicalTrapScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Right chord at the actual last child Happy Gate

This file connects Boss's local two-digit `I ≠ 1` blade to the real child
wave used by the canonical last-gate trap.

Nothing global is assumed.  We first obtain an actual `GSTSeededHappyS 0 T q`,
then classify exactly that one physical x4 cell.  The next retained child seed
is therefore:

* `3` on the BIG1-clear GST+ branch;
* `2` on the BIG1-crossing NULL branch.

This is the precise hand-off point between younger-Sol's microscopic
six-state chord and Old Sol's information-regeneration descent.
-/

/-- Seed-zero seeded carry is definitionally the ordinary physical GST carry. -/
theorem gst_seed_zero_affine_carry_eq_physicalS
    (T p : Nat) :
    gstAffineMulCarryS 4 0 T p = gstCarryS T p := by
  rfl

/-- An actual seed-zero Happy Gate is an ordinary physical Happy BIG2 cell. -/
theorem gst_seed_zero_happy_is_physical_big2S
    (T p : Nat)
    (hgate : GSTSeededHappyS 0 T p) :
    gstDigitS T p = 2 ∧
      (gstCarryS T p = 0 ∨ gstCarryS T p = 3) := by
  simpa [GSTSeededHappyS, gst_seed_zero_affine_carry_eq_physicalS] using hgate

/-- Exact next physical carry after an actual Happy BIG2 cell. -/
theorem gst_happy_big2_next_carry_two_or_threeS
    (T p : Nat)
    (hgate : GSTSeededHappyS 0 T p) :
    gstCarryS T (p+1) = 2 ∨ gstCarryS T (p+1) = 3 := by
  have hp := gst_seed_zero_happy_is_physical_big2S T p hgate
  have hstep := gstCarryS_forward_exact_all T p
  rw [hp.1] at hstep
  rcases hp.2 with h0 | h3
  · left
    rw [h0] at hstep
    norm_num [gstStepCarryS] at hstep
    exact hstep
  · right
    rw [h3] at hstep
    norm_num [gstStepCarryS] at hstep
    exact hstep

/-- THE LOCAL HAND-OFF.

At the actual child gate there are exactly two physical possibilities.

* clear two-digit information: GST+ 55_6, event (8,8), code 35, and retained
  suffix seed 3;
* BIG1 crossing: NULL 42_6, event (5,7), and retained suffix seed 2.

There is no third branch and no pathwise BIG1 premise. -/
theorem gst_last_child_gate_right_chordS
    (T q : Nat)
    (hgate : GSTSeededHappyS 0 T q) :
    (GSTPhysicalTwoDigitBig1ClearS T q ∧
      gstCarryS T q = 3 ∧
      gstCarryS T (q+1) = 3 ∧
      gstPhysicalMicroPairS T q = (5, 5) ∧
      gstBinaryBridgeEventS
          (gstMicroHighBitS (gstCarryS T q)) (gstDigitS T q) = 8 ∧
      gstBinaryBridgeEventS
          (gstMicroLowBitS (gstCarryS T q))
          (gstFirstMicroOutputS (gstCarryS T q) (gstDigitS T q)) = 8 ∧
      gstFirstMicroMassS (gstCarryS T q) (gstDigitS T q) +
          6 * gstSecondMicroMassS (gstCarryS T q) (gstDigitS T q) = 35 ∧
      gstHandwrittenUJumpS (gstCarryS T q) (gstDigitS T q) = -6) ∨
    (¬ GSTPhysicalTwoDigitBig1ClearS T q ∧
      gstCarryS T q = 0 ∧
      gstCarryS T (q+1) = 2 ∧
      gstPhysicalMicroPairS T q = (4, 2) ∧
      gstFirstMicroOutputS (gstCarryS T q) (gstDigitS T q) = 1 ∧
      gstBinaryBridgeEventS
          (gstMicroHighBitS (gstCarryS T q)) (gstDigitS T q) = 5 ∧
      gstBinaryBridgeEventS
          (gstMicroLowBitS (gstCarryS T q))
          (gstFirstMicroOutputS (gstCarryS T q) (gstDigitS T q)) = 7 ∧
      gstHandwrittenUJumpS (gstCarryS T q) (gstDigitS T q) = -8) := by
  have hp := gst_seed_zero_happy_is_physical_big2S T q hgate
  have hlocal := gst_happy_big2_right_chord_dichotomyS T q hp.1 hp.2
  have hstep := gstCarryS_forward_exact_all T q
  rw [hp.1] at hstep
  rcases hlocal with hplus | hnull
  · left
    have hnext : gstCarryS T (q+1) = 3 := by
      rw [hplus.2.1] at hstep
      norm_num [gstStepCarryS] at hstep
      exact hstep
    exact ⟨hplus.1, hplus.2.1, hnext, hplus.2.2.1,
      hplus.2.2.2.1, hplus.2.2.2.2.1,
      hplus.2.2.2.2.2.1, hplus.2.2.2.2.2.2⟩
  · right
    have hnext : gstCarryS T (q+1) = 2 := by
      rw [hnull.2.1] at hstep
      norm_num [gstStepCarryS] at hstep
      exact hstep
    exact ⟨hnull.1, hnull.2.1, hnext, hnull.2.2.1,
      hnull.2.2.2.1, hnull.2.2.2.2.1,
      hnull.2.2.2.2.2.1, hnull.2.2.2.2.2.2⟩

/-- The retained seed after the globally last child gate is exactly the
formula-local selector: seed 3 iff the two-digit cell is BIG1-clear; seed 2
iff that cell crosses BIG1. -/
theorem gst_last_child_gate_next_seed_iff_clearS
    (T q : Nat)
    (hgate : GSTSeededHappyS 0 T q) :
    (gstCarryS T (q+1) = 3 ↔ GSTPhysicalTwoDigitBig1ClearS T q) ∧
      (gstCarryS T (q+1) = 2 ↔ ¬ GSTPhysicalTwoDigitBig1ClearS T q) := by
  have hchord := gst_last_child_gate_right_chordS T q hgate
  rcases hchord with hplus | hnull
  · constructor
    · constructor
      · intro _
        exact hplus.1
      · intro _
        exact hplus.2.2.1
    · constructor
      · intro h2
        rw [hplus.2.2.1] at h2
        omega
      · intro hnot
        exact False.elim (hnot hplus.1)
  · constructor
    · constructor
      · intro h3
        rw [hnull.2.2.1] at h3
        omega
      · intro hclear
        exact False.elim (hnull.1 hclear)
    · constructor
      · intro _
        exact hnull.1
      · intro _
        exact hnull.2.2.1
