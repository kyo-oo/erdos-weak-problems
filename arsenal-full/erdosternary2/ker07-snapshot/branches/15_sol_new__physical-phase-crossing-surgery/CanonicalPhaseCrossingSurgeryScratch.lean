/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0711 / 1132
/-    Path         : branches/sol_physical-phase-crossing-surgery/CanonicalPhaseCrossingSurgeryScratch.lean
/-    Ref          : origin/sol/physical-phase-crossing-surgery
/-    First-commit : 2026-08-17 00:35:44 +0530  (3c51c18)
/-    Last-commit  : 2026-08-17 00:49:41 +0530  (d2ba42c)
/-    Total commits: 4
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/4] 2026-08-17 00:35:44 +0530  3c51c18  (ker07-dev)
/-        Add RED canonical physical crossing target
/- [02/4] 2026-08-17 00:44:21 +0530  ce77d8f  (ker07-dev)
/-        Tighten RED target to exact canonical power orbit
/- [03/4] 2026-08-17 00:45:32 +0530  2078500  (ker07-dev)
/-        Reduce canonical crossing failure to conserved two-boundary trap
/- [04/4] 2026-08-17 00:49:41 +0530  d2ba42c  (ker07-dev)
/-        Attach exact power rectangle and bridge coordinate to canonical trap
/- ====================================================================== -/

import GSTResidueSpacetimeScratch
import PurePowerResidueGraphScratch
import PurePowerBadAxisScratch
import PhaseCycleInformationScratch
import CanonicalTrapScratch

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

/-- Exact remaining separation principle. The forbidden object now contains the
actual power-rectangle certificate, not merely an affine equation. -/
def GSTCanonicalPrefixOnePhysicalTrapImpossibleS : Prop :=
  ∀ (Q : Nat → Nat → Nat),
    GSTCanonicalOriginEnergyS Q →
    ∀ s n c z,
      1 ≤ s → 1 ≤ n →
      4^(3^s) = 1 + 3^(s+1)*c →
      c = 1 + 3*z →
      ¬ GSTCanonicalPhysicalTrapS Q s n c z

/-- The physical phase crossing follows from the canonical physical-trap
separation; no global mirror or residual Ω termination is used. -/
theorem gst_canonical_prefix_one_physical_crossing_of_no_trap_surgeryS
    (hnotrap : GSTCanonicalPrefixOnePhysicalTrapImpossibleS)
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (s n c z : Nat)
    (hs : 1 ≤ s)
    (hn : 1 ≤ n)
    (hA : 4^(3^s) = 1 + 3^(s+1)*c)
    (hc : c = 1 + 3*z) :
    GSTCanonicalPhysicalCrossingS
      (3^(s+1))
      (Q (s+1) n)
      (z + 4^(3^s) * Q (s+1) n)
      (4^(3^(s+1)*n))
      (4^(3^s) * 4^(3^(s+1)*n)) := by
  unfold GSTCanonicalPhysicalCrossingS
  intro hphase0
  by_contra hno
  have hphase1 : ∀ q,
      ¬ GSTDoubleJumpS
        (3*3^(s+1))
        (4^(3^s) * 4^(3^(s+1)*n)) q := by
    simpa using hno
  have htrap := gst_canonical_crossing_failure_traps_surgeryS
    Q hQ s n c z hs hn hA hc hphase0 hphase1
  have hphysical := gst_canonical_trap_is_physical_surgeryS
    Q hQ s n c z hs hA hc htrap
  exact (hnotrap Q hQ s n c z hs hn hA hc) hphysical

/-- RED target: prove that the canonical pure-power origin cannot sustain the
physical two-boundary trap. -/
theorem gst_canonical_prefix_one_physical_trap_impossible_surgeryS :
    GSTCanonicalPrefixOnePhysicalTrapImpossibleS := by
  intro Q hQ s n c z hs hn hA hc htrap
  exact ?_
