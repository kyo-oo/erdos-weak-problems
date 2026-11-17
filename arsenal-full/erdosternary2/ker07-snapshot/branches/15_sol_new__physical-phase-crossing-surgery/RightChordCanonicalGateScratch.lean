/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1062 / 1132
/-    Path         : branches/sol_physical-phase-crossing-surgery/RightChordCanonicalGateScratch.lean
/-    Ref          : origin/sol/physical-phase-crossing-surgery
/-    First-commit : 2026-08-17 21:25:35 +0530  (6857400)
/-    Last-commit  : 2026-08-17 21:25:35 +0530  (6857400)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 21:25:35 +0530  6857400  (ker07-dev)
/-        Integrate scoped two-digit chord at canonical last gate
/- ====================================================================== -/

import CanonicalTrapScratch
import HandwrittenBig1PathProjectorScratch
import HandwrittenUniversalParadoxPotentialScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Right-chord canonical gate integration

This module enforces Boss's scope correction precisely:

* `I != 1` is NOT a global hypothesis on a GST/Omega trace;
* it is used only while resolving one concrete two-digit/x4 physical cell;
* once that cell is solved, the result is returned to the ordinary canonical
  GST coordinates and all subsequent reasoning uses the existing graph laws.

The local chord is

  2 -> 2 -> 2
  (m1,m2) = (5,5)
  55_6 = 35 = 6^2 - 1
  (C,w) = (3,22_3) = (3,8)

so the resolved cell is the GST+ SURVIVE/SURVIVE orientation.
-/

/-- The handwritten BIG1 projector, scoped to exactly one two-digit/x4 cell. -/
def GSTScopedTwoDigitBig1ClearS (C d : Nat) : Prop :=
  d ≠ 1 ∧
  gstFirstMicroOutputS C d ≠ 1 ∧
  gstSecondMicroOutputS C d ≠ 1

/-- One physical Happy Gate plus the scoped two-digit projector hits the unique
right chord.  No condition on any other information position is used. -/
theorem gst_scoped_two_digit_happy_gate_right_chordS
    (C d : Nat)
    (hC : C < 4) (hd : d < 3)
    (hhappy : d = 2 ∧ (C = 0 ∨ C = 3))
    (hclear : GSTScopedTwoDigitBig1ClearS C d) :
    C = 3 ∧ d = 2 ∧
      gstFirstMicroOutputS C d = 2 ∧
      gstSecondMicroOutputS C d = 2 ∧
      gstFirstMicroMassS C d = 5 ∧
      gstSecondMicroMassS C d = 5 ∧
      gstFirstMicroMassS C d + 6 * gstSecondMicroMassS C d = 35 ∧
      gstHandwrittenUJumpS C d = -6 := by
  have hd0 : d ≠ 0 := by rw [hhappy.1]; decide
  obtain ⟨hC3, hd2, hmid2, hout2, hM1, hM2⟩ :=
    gst_big1_projector_two_layer_forces_plus_surviveS
      C d hC hd hd0 hclear.1 hclear.2.1 hclear.2.2
  have h35 := gst_big1_projector_two_layer_chord_35S
    C d hC hd hd0 hclear.1 hclear.2.1 hclear.2.2
  have hU : gstHandwrittenUJumpS C d = -6 := by
    rw [hC3, hd2]
    decide
  exact ⟨hC3, hd2, hmid2, hout2, hM1, hM2, h35, hU⟩

/-- The mixed-radix state selected by the same chord is the maximal legal
36-state cell: carry 3 together with the ternary two-digit word 22. -/
theorem gst_scoped_right_chord_is_36_state_35S
    (C d : Nat)
    (hC : C < 4) (hd : d < 3)
    (hhappy : d = 2 ∧ (C = 0 ∨ C = 3))
    (hclear : GSTScopedTwoDigitBig1ClearS C d) :
    C + 4 * (2 + 3*2) = 35 ∧
      2 + 3*2 = 8 ∧
      35 = 6^2 - 1 := by
  have h := gst_scoped_two_digit_happy_gate_right_chordS
    C d hC hd hhappy hclear
  rw [h.1]
  decide

/-- Apply the scoped projector at an actual seed-zero child Happy Gate.
The current carry is forced from the old NULL/GST+ ambiguity to GST+ carry 3,
and the regenerated carry immediately after the gate remains 3. -/
theorem gst_scoped_child_gate_forces_plus_and_postseed_threeS
    (T q : Nat)
    (hgate : GSTSeededHappyS 0 T q)
    (hclear : GSTScopedTwoDigitBig1ClearS
      (gstAffineMulCarryS 4 0 T q) (gstDigitS T q)) :
    gstAffineMulCarryS 4 0 T q = 3 ∧
      gstAffineMulCarryS 4 0 T (q+1) = 3 ∧
      gstFirstMicroMassS
          (gstAffineMulCarryS 4 0 T q) (gstDigitS T q) +
        6 * gstSecondMicroMassS
          (gstAffineMulCarryS 4 0 T q) (gstDigitS T q) = 35 := by
  have hC : gstAffineMulCarryS 4 0 T q < 4 :=
    gst_affine_carry_lt_multiplierS 4 0 T q (by decide) (by decide)
  have hd : gstDigitS T q < 3 := gst_digitS_lt_three_allS T q
  have hright := gst_scoped_two_digit_happy_gate_right_chordS
    (gstAffineMulCarryS 4 0 T q) (gstDigitS T q)
    hC hd hgate hclear
  have hstep := gstAffineS_forward_exact_all 0 T q
  have hpost : gstAffineMulCarryS 4 0 T (q+1) = 3 := by
    rw [hstep, hgate.1, hright.1]
    decide
  exact ⟨hright.1, hpost, hright.2.2.2.2.2.2.1⟩

/-- The same last-gate chord lands the conserved shared-information carrier in
the GST+ high quarter at the gate itself.  This is the exact junction between
Boss's two-digit formula and Younger Sol's commuting-square information law. -/
theorem gst_scoped_child_gate_right_chord_high_quarterS
    (A z T q : Nat)
    (hA : 0 < A) (hz1 : 1 + 4*z < A)
    (hgate : GSTSeededHappyS 0 T q)
    (hclear : GSTScopedTwoDigitBig1ClearS
      (gstAffineMulCarryS 4 0 T q) (gstDigitS T q)) :
    let S :=
      gstAffineMulCarryS 4 1 (z + A*T) q +
        4 * gstAffineMulCarryS A z T q
    3*A ≤ S ∧ S < 4*A ∧
      gstAffineMulCarryS 4 0 T (q+1) = 3 ∧
      gstFirstMicroMassS
          (gstAffineMulCarryS 4 0 T q) (gstDigitS T q) +
        6 * gstSecondMicroMassS
          (gstAffineMulCarryS 4 0 T q) (gstDigitS T q) = 35 := by
  dsimp only
  obtain ⟨hplus, hpost, h35⟩ :=
    gst_scoped_child_gate_forces_plus_and_postseed_threeS T q hgate hclear
  have hcarry : gstCarryS T q = 3 := by
    simpa [gstCarryS, gstAffineMulCarryS] using hplus
  have hquarter := gst_shared_information_plus_high_quarterS
    A z T q hA hz1 hcarry
  exact ⟨hquarter.1, hquarter.2, hpost, h35⟩

/-- Strengthened two-boundary trap at a *specified* globally last child gate.
The old package retained only `C=2 or C=3`; the scoped right chord removes the
NULL branch and upgrades the post-gate child seed to the exact value `C=3`.

The only projector input is `hclear` for this one two-digit gate q. -/
theorem gst_scoped_last_gate_two_boundary_plus_trapS
    (A z T q : Nat)
    (hA : 0 < A)
    (hz1 : 1 + 4*z < A)
    (hparent : GSTSeededBadTraceS 1 (z + A*T))
    (hq : GSTSeededHappyS 0 T q)
    (hlast : ∀ r, q < r → ¬ GSTSeededHappyS 0 T r)
    (hclear : GSTScopedTwoDigitBig1ClearS
      (gstAffineMulCarryS 4 0 T q) (gstDigitS T q)) :
    let D := gstAffineMulCarryS 4 1 (z + A*T) (q+1)
    let Z := gstAffineMulCarryS A z T (q+1)
    let W := gstAffineMulCarryS A (1 + 4*z) (4*T) (q+1)
    let C := gstAffineMulCarryS 4 0 T (q+1)
    let Y := T / 3^(q+1)
    GSTSeededBadTraceS D (Z + A*Y) ∧
      GSTSeededBadTraceS C Y ∧
      C = 3 ∧
      D + 4*Z = W + A*C ∧
      W < A := by
  dsimp only
  have hparentSuffix :=
    gst_seeded_bad_trace_suffixS 1 (z + A*T) (q+1) hparent
  have hparentShape := gst_relative_affine_suffixS A z T (q+1)
  rw [hparentShape] at hparentSuffix

  have hchildSuffix := gst_suffix_after_last_gate_is_badS 0 T q hq hlast
  dsimp only at hchildSuffix
  have hstep := gstAffineS_forward_exact_all 0 T q
  have hCeq :
      gstAffineMulCarryS 4 0 T (q+1) =
        gstStepCarryS (gstAffineMulCarryS 4 0 T q) 2 := by
    rw [hstep, hq.1]
  rw [← hCeq] at hchildSuffix

  have hplus := gst_scoped_child_gate_forces_plus_and_postseed_threeS
    T q hq hclear
  have hC3 : gstAffineMulCarryS 4 0 T (q+1) = 3 := hplus.2.1

  have hEq := gst_shared_information_carry_equationS A z T (q+1)
  have hcarryEq :
      gstCarryS T (q+1) = gstAffineMulCarryS 4 0 T (q+1) := by
    simp [gstCarryS, gstAffineMulCarryS]
  rw [hcarryEq] at hEq
  have hshared :
      gstAffineMulCarryS 4 1 (z + A*T) (q+1) +
          4 * gstAffineMulCarryS A z T (q+1) =
        gstAffineMulCarryS A (1 + 4*z) (4*T) (q+1) +
          A * gstAffineMulCarryS 4 0 T (q+1) := hEq.symm

  have hW : gstAffineMulCarryS A (1 + 4*z) (4*T) (q+1) < A :=
    gst_affine_carry_lt_multiplierS A (1 + 4*z) (4*T) (q+1) hA hz1

  exact ⟨hparentSuffix, hchildSuffix, hC3, hshared, hW⟩
