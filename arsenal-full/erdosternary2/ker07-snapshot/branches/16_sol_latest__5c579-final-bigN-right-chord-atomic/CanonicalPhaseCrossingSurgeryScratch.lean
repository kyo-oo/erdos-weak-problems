/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1070 / 1132
/-    Path         : branches/sol_5c579-final-bigN-right-chord-atomic/CanonicalPhaseCrossingSurgeryScratch.lean
/-    Ref          : origin/sol/5c579-final-bigN-right-chord-atomic
/-    First-commit : 2026-08-17 22:06:13 +0530  (deea9a0)
/-    Last-commit  : 2026-08-18 01:35:28 +0530  (99abb02)
/-    Total commits: 3
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/3] 2026-08-17 22:06:13 +0530  deea9a0  (ker07-dev)
/-        surgery: lock 5c579 with full BIG-N right-chord research monolith
/- [02/3] 2026-08-18 01:31:04 +0530  b518dd0  (ker07-dev)
/-        surgery: replace false bare-trap hole with provenance right-chord certificate
/- [03/3] 2026-08-18 01:35:28 +0530  99abb02  (ker07-dev)
/-        surgery: make crossing-failure certificate elaboration-stable
/- ====================================================================== -/

import GSTResidueSpacetimeScratch
import PurePowerResidueGraphScratch
import PurePowerBadAxisScratch
import PhaseCycleInformationScratch
import CanonicalTrapScratch
import PrefixOneRightChordLastGateScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Canonical prefix-one physical crossing surgery

This scratch never imports `ErdosTernary2`, the quarantined residual Ω chain,
or `gst_prefix_one_navigation_lift`.

The target is deliberately canonical. `Q` carries the exact perfect-power
origin certificate, `A` is literally `4^(3^s)`, and the two phase energies are
actual adjacent sections of the same power orbit.
-/

/-- Local form of the physical crossing interface. -/
def GSTCanonicalPhysicalCrossingS
    (D T H E0 E1 : Nat) : Prop :=
  (∃ q, GSTDoubleJumpS (3*D) E0 q) →
    ∃ q, GSTDoubleJumpS (3*D) E1 q

/-- The exact finite conserved-information trap produced when a seed-zero child
has at least one Happy Gate but the seed-one parent remains completely bad. -/
def GSTCanonicalTwoBoundaryTrapS (A z T : Nat) : Prop :=
  ∃ q,
    let D := gstAffineMulCarryS 4 1 (z + A*T) (q+1)
    let Z := gstAffineMulCarryS A z T (q+1)
    let W := gstAffineMulCarryS A (1 + 4*z) (4*T) (q+1)
    let C := gstAffineMulCarryS 4 0 T (q+1)
    let Y := T / 3^(q+1)
    GSTSeededBadTraceS D (Z + A*Y) ∧
      GSTSeededBadTraceS C Y ∧
      (C = 2 ∨ C = 3) ∧
      D + 4*Z = W + A*C ∧
      W < A

/-- Canonical phase-zero energy identity, written in the `3*D*T` chart used by
the physical residue tower. -/
theorem gst_canonical_phase0_energy_shape_surgeryS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (s n : Nat) (hs : 1 ≤ s) :
    4^(3^(s+1)*n) =
      1 + 3 * 3^(s+1) * Q (s+1) n := by
  have h := hQ (s+1) n (by omega)
  have hp : 3^(s+2) = 3 * 3^(s+1) := by
    rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
    ac_rfl
  rw [hp] at h
  simpa [Nat.mul_assoc] using h

/-- The phase-one product is exactly the forced seed-one energy chart. -/
theorem gst_canonical_phase1_energy_shape_surgeryS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (s n c z : Nat)
    (hs : 1 ≤ s)
    (hA : 4^(3^s) = 1 + 3^(s+1)*c)
    (hc : c = 1 + 3*z) :
    4^(3^s) * 4^(3^(s+1)*n) =
      1 + 3^(s+1) +
        3 * 3^(s+1) * (z + 4^(3^s) * Q (s+1) n) := by
  have hE := gst_canonical_phase0_energy_shape_surgeryS Q hQ s n hs
  have haxis := gst_prefix_one_pure_power_axisS
    (4^(3^s)) (3^(s+1)) c z (Q (s+1) n)
    (4^(3^(s+1)*n)) hA hc hE
  nlinarith

/-- Failure of the phase-one double jump, together with one phase-zero double
jump, produces the exact finite two-boundary trap. This is a pure reduction:
it introduces no forcing principle. -/
theorem gst_canonical_crossing_failure_traps_surgeryS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (s n c z : Nat)
    (hs : 1 ≤ s)
    (hn : 1 ≤ n)
    (hA : 4^(3^s) = 1 + 3^(s+1)*c)
    (hc : c = 1 + 3*z)
    (hphase0 : ∃ q,
      GSTDoubleJumpS (3*3^(s+1)) (4^(3^(s+1)*n)) q)
    (hphase1 : ∀ q,
      ¬ GSTDoubleJumpS
        (3*3^(s+1))
        (4^(3^s) * 4^(3^(s+1)*n)) q) :
    GSTCanonicalTwoBoundaryTrapS
      (4^(3^s)) z (Q (s+1) n) := by
  let D0 := 3^(s+1)
  let A := 4^(3^s)
  let T := Q (s+1) n
  let H := z + A*T
  let E0 := 4^(3^(s+1)*n)
  let E1 := A*E0

  have hD0 : 3 ≤ D0 := by
    dsimp [D0]
    have h9 : 9 ≤ 3^(s+1) := by
      rw [show (9:Nat) = 3^2 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega

  have hE0 : E0 = 1 + 3*D0*T := by
    dsimp [E0, D0, T]
    exact gst_canonical_phase0_energy_shape_surgeryS Q hQ s n hs

  have hE1 : E1 = 1 + D0 + 3*D0*H := by
    dsimp [E1, A, E0, D0, H, T]
    exact gst_canonical_phase1_energy_shape_surgeryS
      Q hQ s n c z hs hA hc

  have hchildCommon : ∃ q,
      gstDigitS T q = 2 ∧ gstDigitS (4*T) q = 2 := by
    obtain ⟨q, hq⟩ := hphase0
    refine ⟨q, ?_⟩
    apply (gst_phase0_common_two_iff_double_jumpS D0 T E0 q hD0 hE0).2
    simpa [D0, E0] using hq

  have hchild : ∃ q, GSTSeededHappyS 0 T q := by
    obtain ⟨q, hq⟩ := hchildCommon
    refine ⟨q, ?_⟩
    unfold GSTSeededHappyS
    exact (gst_seeded_happy_iff_common_twoS 0 T q (by decide)).2 <| by
      simpa using hq

  have hparentNoCommon : ∀ q,
      ¬ (gstDigitS H q = 2 ∧ gstDigitS (1 + 4*H) q = 2) := by
    intro q hcommon
    have hjump : GSTDoubleJumpS (3*D0) E1 q :=
      (gst_phase1_common_two_iff_double_jumpS D0 H E1 q hD0 hE1).1 hcommon
    apply hphase1 q
    simpa [D0, E1, A, E0] using hjump

  have hparent : GSTSeededBadTraceS 1 H :=
    (gst_seeded_bad_iff_no_common_twoS 1 H (by decide)).2 hparentNoCommon

  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hz1 : 1 + 4*z < A := by
    dsimp [A]
    have hD9 : 9 ≤ 3^(s+1) := by
      rw [show (9:Nat) = 3^2 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    rw [hA, hc]
    nlinarith

  have htrap := gst_canonical_two_boundary_trapS A z T hApos hz1 hparent hchild
  simpa [GSTCanonicalTwoBoundaryTrapS, A, T, H] using htrap

/-- The same trap with the certificate that its conserved word is literally the
wide carry of the actual pure-power rectangle. The last conjunct is the finite
bridge NULL coordinate of this information word; it is not a terminal-NULL
axiom for the GST wave. -/
def GSTCanonicalPhysicalTrapS
    (Q : Nat → Nat → Nat) (s n c z : Nat) : Prop :=
  ∃ q,
    let N := 3^s
    let A := 4^N
    let T := Q (s+1) n
    let D := gstAffineMulCarryS 4 1 (z + A*T) (q+1)
    let Z := gstAffineMulCarryS A z T (q+1)
    let W := gstAffineMulCarryS A (1 + 4*z) (4*T) (q+1)
    let C := gstAffineMulCarryS 4 0 T (q+1)
    let Y := T / 3^(q+1)
    let S := D + 4*Z
    GSTSeededBadTraceS D (Z + A*Y) ∧
      GSTSeededBadTraceS C Y ∧
      (C = 2 ∨ C = 3) ∧
      S = W + A*C ∧
      W < A ∧
      S = gstWideCarryS
        (4^(N+1)) (4^(3^(s+1)*n)) (s+2+(q+1)) ∧
      S / 3^(2*N) = 0

/-- Attach the exact pure-power rectangle and finite bridge coordinate to the
abstract two-boundary trap. Arbitrary affine counterexamples cannot satisfy
this certificate merely from the trap equations. -/
theorem gst_canonical_trap_is_physical_surgeryS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (s n c z : Nat)
    (hs : 1 ≤ s)
    (hA : 4^(3^s) = 1 + 3^(s+1)*c)
    (hc : c = 1 + 3*z)
    (htrap : GSTCanonicalTwoBoundaryTrapS
      (4^(3^s)) z (Q (s+1) n)) :
    GSTCanonicalPhysicalTrapS Q s n c z := by
  obtain ⟨q, hparent, hchild, hC, hEq, hW⟩ := htrap
  refine ⟨q, ?_⟩
  dsimp only
  let N := 3^s
  let A := 4^N
  let T := Q (s+1) n
  let D := gstAffineMulCarryS 4 1 (z + A*T) (q+1)
  let Z := gstAffineMulCarryS A z T (q+1)
  let W := gstAffineMulCarryS A (1 + 4*z) (4*T) (q+1)
  let C := gstAffineMulCarryS 4 0 T (q+1)
  let Y := T / 3^(q+1)
  let S := D + 4*Z

  have hNA : A = 4^N := rfl
  have hN3 : 3 ≤ N := by
    dsimp [N]
    have h3pow : 3^1 ≤ 3^s :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) hs
    simpa using h3pow

  have hE0 : 4^(3^(s+1)*n) = 1 + 3*3^(s+1)*T := by
    dsimp [T]
    exact gst_canonical_phase0_energy_shape_surgeryS Q hQ s n hs

  have hwide0 := gst_shared_state_is_exact_power_rectangleS
    s N c z T (4^(3^(s+1)*n)) (3^(s+1)*n) (q+1)
    hs (by simpa [N, A] using hA) hc hE0 rfl

  have hwide : S = gstWideCarryS
      (4^(N+1)) (4^(3^(s+1)*n)) (s+2+(q+1)) := by
    dsimp [S, D, Z, A, N, T]
    exact hwide0.symm

  have hClt : C < 4 := by
    rcases hC with h2 | h3
    · rw [h2]; decide
    · rw [h3]; decide
  have hHigh : S = W + A*C := by
    dsimp [S, D, Z, W, A, N, T, C]
    simpa [N, A, T] using hEq
  have hword : S < 4*A :=
    gst_information_word_boundS S W A C hW hClt hHigh
  have hnull : S / 3^(2*N) = 0 :=
    gst_information_bridge_nullS S A N hN3 hNA hword

  exact ⟨by simpa [D, Z, A, N, T, Y] using hparent,
    by simpa [C, T, Y] using hchild,
    hC,
    hHigh,
    hW,
    hwide,
    hnull⟩

/-!
## Corrected RED object: provenance is retained

The former RED statement quantified over a bare suffix `GSTCanonicalPhysicalTrapS`.
That object is not itself contradictory: it forgets whether a phase-one Happy
vertex may already have occurred before the selected suffix cut.  The correct
object generated by an *actual crossing failure* must retain:

* complete seed-one badness of the whole canonical parent tail;
* an actual seed-zero child Happy gate;
* the exact local two-digit PLUS/NULL right-chord at that gate; and
* the certified pure-power physical rectangle trap.

This is a strengthening of the physical certificate, not a new axiom.
-/

/-- Full local right-chord certificate, scoped to exactly one actual child
Happy x4 cell. -/
def GSTCanonicalLocalRightChordS (T q : Nat) : Prop :=
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

/-- Failure certificate carrying every theorem-grade object needed by the new
GST-V2 / right-chord / U / canonical-origin forcing step. -/
def GSTCanonicalCrossingFailureCertificateS
    (Q : Nat → Nat → Nat) (s n c z : Nat) : Prop :=
  let A := 4^(3^s)
  let T := Q (s+1) n
  let H := z + A*T
  GSTSeededBadTraceS 1 H ∧
    (∃ q, GSTSeededHappyS 0 T q ∧ GSTCanonicalLocalRightChordS T q) ∧
    GSTCanonicalPhysicalTrapS Q s n c z

/-- Atomic corrected surgery theorem.  An actual phase-zero event together with
complete absence of phase-one events produces the full provenance-preserving
certificate.  No old duality, residual-Omega termination, global mirror, or
terminal-NULL principle occurs in this proof. -/
theorem gst_canonical_crossing_failure_certificate_surgeryS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (s n c z : Nat)
    (hs : 1 ≤ s)
    (hn : 1 ≤ n)
    (hA : 4^(3^s) = 1 + 3^(s+1)*c)
    (hc : c = 1 + 3*z)
    (hphase0 : ∃ q,
      GSTDoubleJumpS (3*3^(s+1)) (4^(3^(s+1)*n)) q)
    (hphase1 : ∀ q,
      ¬ GSTDoubleJumpS
        (3*3^(s+1))
        (4^(3^s) * 4^(3^(s+1)*n)) q) :
    GSTCanonicalCrossingFailureCertificateS Q s n c z := by
  let D0 := 3^(s+1)
  let A := 4^(3^s)
  let T := Q (s+1) n
  let H := z + A*T
  let E0 := 4^(3^(s+1)*n)
  let E1 := A*E0

  have hD0 : 3 ≤ D0 := by
    dsimp [D0]
    have h9 : 9 ≤ 3^(s+1) := by
      rw [show (9:Nat) = 3^2 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega

  have hE0 : E0 = 1 + 3*D0*T := by
    dsimp [E0, D0, T]
    exact gst_canonical_phase0_energy_shape_surgeryS Q hQ s n hs

  have hE1 : E1 = 1 + D0 + 3*D0*H := by
    dsimp [E1, A, E0, D0, H, T]
    exact gst_canonical_phase1_energy_shape_surgeryS
      Q hQ s n c z hs hA hc

  have htrap := gst_canonical_crossing_failure_traps_surgeryS
    Q hQ s n c z hs hn hA hc hphase0 hphase1
  have hphysical := gst_canonical_trap_is_physical_surgeryS
    Q hQ s n c z hs hA hc htrap

  obtain ⟨q0, hq0⟩ := hphase0
  have hcommon0 : gstDigitS T q0 = 2 ∧ gstDigitS (4*T) q0 = 2 :=
    (gst_phase0_common_two_iff_double_jumpS D0 T E0 q0 hD0 hE0).2 <| by
      simpa [D0, E0] using hq0
  have hchild0 : GSTSeededHappyS 0 T q0 := by
    unfold GSTSeededHappyS
    exact (gst_seeded_happy_iff_common_twoS 0 T q0 (by decide)).2 <| by
      simpa using hcommon0

  have hparentNoCommon : ∀ q,
      ¬ (gstDigitS H q = 2 ∧ gstDigitS (1 + 4*H) q = 2) := by
    intro q hcommon
    have hjump : GSTDoubleJumpS (3*D0) E1 q :=
      (gst_phase1_common_two_iff_double_jumpS D0 H E1 q hD0 hE1).1 hcommon
    apply hphase1 q
    simpa [D0, E1, A, E0] using hjump
  have hparent : GSTSeededBadTraceS 1 H :=
    (gst_seeded_bad_iff_no_common_twoS 1 H (by decide)).2 hparentNoCommon

  have hlocal : GSTCanonicalLocalRightChordS T q0 := by
    unfold GSTCanonicalLocalRightChordS
    exact gst_last_child_gate_right_chordS T q0 hchild0

  dsimp [GSTCanonicalCrossingFailureCertificateS, A, T, H]
  exact ⟨hparent, ⟨q0, hchild0, hlocal⟩, hphysical⟩
