/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1055 / 1132
/-    Path         : branches/sol_5c579-right-chord-surgery/CanonicalRightChordTrapScratch.lean
/-    Ref          : origin/sol/5c579-right-chord-surgery
/-    First-commit : 2026-08-17 20:50:54 +0530  (b3f97f0)
/-    Last-commit  : 2026-08-17 20:50:54 +0530  (b3f97f0)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 20:50:54 +0530  b3f97f0  (ker07-dev)
/-        surgery: retain local two-digit right chord in canonical last-gate trap
/- ====================================================================== -/

import PrefixOneRightChordLastGateScratch
import PurePowerResidueGraphScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Canonical right-chord trap

This is the first production-facing fusion of the old information-descent trap
with Boss's corrected two-digit handwritten chord.

The old canonical trap retained only

  C = 2 ∨ C = 3

for the child seed after the globally last child Happy Gate.  That statement
forgets the physical reason for the two values.  Here the exact same last gate
is retained together with its microscopic two-x2-layer certificate:

* `C = 3` iff this one physical x4 cell is BIG1-clear, hence GST+ `55_6`,
  event `(8,8)`, code `35`, U-jump `-6`;
* `C = 2` iff this one physical x4 cell crosses BIG1, hence NULL `42_6`,
  event `(5,7)`, U-jump `-8`.

Thus Boss's `I ≠ 1` condition is used only to classify this actual two-digit
cell.  The global suffix still moves exclusively through the old exact
regeneration/canonical-origin machinery.
-/

/-- Full local microscopic certificate at one actual seed-zero Happy Gate. -/
def GSTLocalTwoDigitRightChordS (T q : Nat) : Prop :=
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
      gstHandwrittenUJumpS (gstCarryS T q) (gstDigitS T q) = -8)

/-- The local certificate is not an assumption: it is forced by an actual
seed-zero child Happy Gate. -/
theorem gst_local_two_digit_right_chord_of_gateS
    (T q : Nat) (hgate : GSTSeededHappyS 0 T q) :
    GSTLocalTwoDigitRightChordS T q := by
  unfold GSTLocalTwoDigitRightChordS
  exact gst_last_child_gate_right_chordS T q hgate

/-- Strengthened canonical trap.  It is the old two-boundary trap with the
actual last child gate and its two-digit right chord retained rather than
forgotten. -/
def GSTCanonicalRightChordTrapS (A z T : Nat) : Prop :=
  ∃ q,
    let D := gstAffineMulCarryS 4 1 (z + A*T) (q+1)
    let Z := gstAffineMulCarryS A z T (q+1)
    let W := gstAffineMulCarryS A (1 + 4*z) (4*T) (q+1)
    let C := gstAffineMulCarryS 4 0 T (q+1)
    let Y := T / 3^(q+1)
    GSTSeededHappyS 0 T q ∧
      GSTSeededBadTraceS D (Z + A*Y) ∧
      GSTSeededBadTraceS C Y ∧
      (C = 2 ∨ C = 3) ∧
      GSTLocalTwoDigitRightChordS T q ∧
      (C = 3 ↔ GSTPhysicalTwoDigitBig1ClearS T q) ∧
      (C = 2 ↔ ¬ GSTPhysicalTwoDigitBig1ClearS T q) ∧
      D + 4*Z = W + A*C ∧
      W < A

/-- Construct the strengthened trap from exactly the same hypotheses as the
old canonical last-gate trap.  No new global projector, mirror, or forcing
axiom is inserted. -/
theorem gst_canonical_right_chord_trapS
    (A z T : Nat)
    (hA : 0 < A)
    (hz1 : 1 + 4*z < A)
    (hparent : GSTSeededBadTraceS 1 (z + A*T))
    (hchild : ∃ j, GSTSeededHappyS 0 T j) :
    GSTCanonicalRightChordTrapS A z T := by
  obtain ⟨q, hq, hlast⟩ :=
    gst_exists_global_last_seeded_gateS 0 T hchild
  refine ⟨q, ?_⟩
  dsimp only

  have hparentSuffix :=
    gst_seeded_bad_trace_suffixS 1 (z + A*T) (q+1) hparent
  have hparentShape := gst_relative_affine_suffixS A z T (q+1)
  rw [hparentShape] at hparentSuffix

  have hchildSuffix :=
    gst_suffix_after_last_gate_is_badS 0 T q hq hlast
  dsimp only at hchildSuffix
  have hchildStep := gstAffineS_forward_exact_all 0 T q
  have hCeq :
      gstAffineMulCarryS 4 0 T (q+1) =
        gstStepCarryS (gstAffineMulCarryS 4 0 T q) 2 := by
    rw [hchildStep, hq.1]
  rw [← hCeq] at hchildSuffix

  have hlatent0 := gst_happy_big2_next_carry_two_or_threeS T q hq
  have hseedEq :
      gstAffineMulCarryS 4 0 T (q+1) = gstCarryS T (q+1) :=
    gst_seed_zero_affine_carry_eq_physicalS T (q+1)
  have hlatent :
      gstAffineMulCarryS 4 0 T (q+1) = 2 ∨
        gstAffineMulCarryS 4 0 T (q+1) = 3 := by
    rw [hseedEq]
    exact hlatent0

  have hlocal : GSTLocalTwoDigitRightChordS T q :=
    gst_local_two_digit_right_chord_of_gateS T q hq
  have hclass := gst_last_child_gate_next_seed_iff_clearS T q hq
  have hclass3 :
      gstAffineMulCarryS 4 0 T (q+1) = 3 ↔
        GSTPhysicalTwoDigitBig1ClearS T q := by
    rw [hseedEq]
    exact hclass.1
  have hclass2 :
      gstAffineMulCarryS 4 0 T (q+1) = 2 ↔
        ¬ GSTPhysicalTwoDigitBig1ClearS T q := by
    rw [hseedEq]
    exact hclass.2

  have hEq := gst_shared_information_carry_equationS A z T (q+1)
  have hcarryEq :
      gstCarryS T (q+1) = gstAffineMulCarryS 4 0 T (q+1) := by
    symm
    exact hseedEq
  rw [hcarryEq] at hEq
  have hshared :
      gstAffineMulCarryS 4 1 (z + A*T) (q+1) +
          4 * gstAffineMulCarryS A z T (q+1) =
        gstAffineMulCarryS A (1 + 4*z) (4*T) (q+1) +
          A * gstAffineMulCarryS 4 0 T (q+1) := hEq.symm

  have hW : gstAffineMulCarryS A (1 + 4*z) (4*T) (q+1) < A :=
    gst_affine_carry_lt_multiplierS A (1 + 4*z) (4*T) (q+1) hA hz1

  exact ⟨hq, hparentSuffix, hchildSuffix, hlatent, hlocal,
    hclass3, hclass2, hshared, hW⟩

/-- Forgetting the new microscopic labels recovers the old canonical trap
exactly.  This proves the right-chord package is a strengthening, not a change
of the old arithmetic state. -/
theorem gst_canonical_right_chord_trap_forgetS
    (A z T : Nat)
    (htrap : GSTCanonicalRightChordTrapS A z T) :
    GSTCanonicalTwoBoundaryTrapS A z T := by
  obtain ⟨q, hgate, hparent, hchild, hC, _hlocal,
    _hclass3, _hclass2, hEq, hW⟩ := htrap
  exact ⟨q, hparent, hchild, hC, hEq, hW⟩

/-- Therefore the strengthened right-chord trap inherits the already-proved
canonical physical pure-power rectangle certificate without inventing any
horizontal transport. -/
theorem gst_canonical_right_chord_trap_is_physicalS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (s n c z : Nat)
    (hs : 1 ≤ s)
    (hA : 4^(3^s) = 1 + 3^(s+1)*c)
    (hc : c = 1 + 3*z)
    (htrap : GSTCanonicalRightChordTrapS
      (4^(3^s)) z (Q (s+1) n)) :
    GSTCanonicalPhysicalTrapS Q s n c z := by
  apply gst_canonical_trap_is_physical_surgeryS Q hQ s n c z hs hA hc
  exact gst_canonical_right_chord_trap_forgetS
    (4^(3^s)) z (Q (s+1) n) htrap

/-- The retained child seed is now semantically resolved: there is no anonymous
`2 ∨ 3` branch left in a right-chord trap. -/
theorem gst_canonical_right_chord_seed_classificationS
    (A z T : Nat)
    (htrap : GSTCanonicalRightChordTrapS A z T) :
    ∃ q,
      let C := gstAffineMulCarryS 4 0 T (q+1)
      GSTSeededHappyS 0 T q ∧
        ((C = 3 ∧ GSTPhysicalTwoDigitBig1ClearS T q) ∨
         (C = 2 ∧ ¬ GSTPhysicalTwoDigitBig1ClearS T q)) := by
  obtain ⟨q, hgate, _hparent, _hchild, hC, _hlocal,
    hclass3, hclass2, _hEq, _hW⟩ := htrap
  refine ⟨q, hgate, ?_⟩
  rcases hC with h2 | h3
  · exact Or.inr ⟨h2, hclass2.mp h2⟩
  · exact Or.inl ⟨h3, hclass3.mp h3⟩
