/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1050 / 1132
/-    Path         : branches/sol_global-flux-surgery/GlobalPrefixOneRenormalizationSurgeryScratch.lean
/-    Ref          : origin/sol/global-flux-surgery
/-    First-commit : 2026-08-17 14:21:36 +0530  (ac13886)
/-    Last-commit  : 2026-08-17 14:22:07 +0530  (36c1d1c)
/-    Total commits: 2
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/2] 2026-08-17 14:21:36 +0530  ac13886  (ker07-dev)
/-        Add exact three-to-one canonical phase renormalization
/- [02/2] 2026-08-17 14:22:07 +0530  36c1d1c  (ker07-dev)
/-        Use monolith-certified factor-three navigation shifts
/- ====================================================================== -/

import ErdosTernary2
import GlobalPrefixOnePhaseMatrixScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Exact three-to-one renormalization for the prefix-one surgery

The physical matrix reduction shows that the historical seam is a horizontal
BIG2-window transport problem.  This file records the exact scale map that
prevents us from treating the width `3^s` strip as an arbitrary finite strip.

Three consecutive level-s canonical phase steps are exactly one level-(s+1)
step after the factor-three embedding.  The proof below is arithmetic only; it
adds no crossing, reflection, or termination assumption.
-/

/-- Canonical phase multiplier. -/
def gstCanonicalPhaseMultiplierS (s : Nat) : Nat := 4^(3^s)

/-- One canonical origin/phase step `F_s(Y)=c_s+A_s Y`. -/
def gstCanonicalPhaseStepS (s Y : Nat) : Nat :=
  c s + gstCanonicalPhaseMultiplierS s * Y

/-- The next phase multiplier is the cube of the current one. -/
theorem gst_canonical_phase_multiplier_cubeS (s : Nat) :
    gstCanonicalPhaseMultiplierS (s+1) =
      (gstCanonicalPhaseMultiplierS s)^3 := by
  unfold gstCanonicalPhaseMultiplierS
  rw [Nat.pow_succ]
  rw [Nat.pow_mul]

/-- Exact coefficient renormalization

      3*c_(s+1) = c_s * (1 + A_s + A_s^2).
-/
theorem gst_canonical_phase_coefficient_renormalizesS
    (s : Nat) (hs : 1 ≤ s) :
    3 * c (s+1) =
      c s * (1 + gstCanonicalPhaseMultiplierS s +
        (gstCanonicalPhaseMultiplierS s)^2) := by
  have hrec := c_recursion s hs
  have hpow :
      3 * 3^(2*s+1) = (3^(s+1))^2 := by
    calc
      3 * 3^(2*s+1) = 3^(2*s+2) := by
        rw [show 2*s+2 = (2*s+1)+1 by omega, Nat.pow_succ]
        ac_rfl
      _ = 3^((s+1)*2) := by congr 1 <;> omega
      _ = (3^(s+1))^2 := by rw [Nat.pow_mul]
  rw [hrec]
  unfold gstCanonicalPhaseMultiplierS
  rw [lte_identity s hs]
  rw [hpow]
  ring

/-- Three level-s steps on an embedded state equal one level-(s+1) step:

      F_s(F_s(F_s(3Y))) = 3*F_(s+1)(Y).
-/
theorem gst_canonical_phase_three_to_oneS
    (s Y : Nat) (hs : 1 ≤ s) :
    gstCanonicalPhaseStepS s
        (gstCanonicalPhaseStepS s
          (gstCanonicalPhaseStepS s (3*Y))) =
      3 * gstCanonicalPhaseStepS (s+1) Y := by
  have hc := gst_canonical_phase_coefficient_renormalizesS s hs
  have hA := gst_canonical_phase_multiplier_cubeS s
  unfold gstCanonicalPhaseStepS
  let A := gstCanonicalPhaseMultiplierS s
  have hA' : gstCanonicalPhaseMultiplierS (s+1) = A^3 := by
    simpa [A] using hA
  rw [hA']
  calc
    c s + A * (c s + A * (c s + A * (3 * Y))) =
        c s * (1 + A + A^2) + 3 * A^3 * Y := by ring
    _ = 3 * c (s+1) + 3 * A^3 * Y := by
      rw [hc]
    _ = 3 * (c (s+1) + A^3 * Y) := by ring

/-- Forward factor-three Navigation transport.  The monolith already proves
the exact digit and GST-space shifts, so the surgery reuses those certified
coordinate laws rather than reproving division arithmetic. -/
theorem gst_navigation_witness_mul_three_forwardS
    (R : Nat) (h : GSTNavigationWitness R) :
    GSTNavigationWitness (3*R) := by
  obtain ⟨j, hd, hspace⟩ := h
  refine ⟨j+1, ?_, ?_⟩
  · rw [gstDigit_mul_three_shift R j]
    exact hd
  · rw [gstSpace_mul_three_shift R j]
    exact hspace

/-- The renormalization identity and the factor-three state shift together
show that Navigation of the next-level phase-step output embeds as genuine
Navigation of the three-step level-s output. -/
theorem gst_canonical_three_step_navigation_of_next_levelS
    (s Y : Nat) (hs : 1 ≤ s)
    (hnav : GSTNavigationWitness (gstCanonicalPhaseStepS (s+1) Y)) :
    GSTNavigationWitness
      (gstCanonicalPhaseStepS s
        (gstCanonicalPhaseStepS s
          (gstCanonicalPhaseStepS s (3*Y)))) := by
  rw [gst_canonical_phase_three_to_oneS s Y hs]
  exact gst_navigation_witness_mul_three_forwardS
    (gstCanonicalPhaseStepS (s+1) Y) hnav
