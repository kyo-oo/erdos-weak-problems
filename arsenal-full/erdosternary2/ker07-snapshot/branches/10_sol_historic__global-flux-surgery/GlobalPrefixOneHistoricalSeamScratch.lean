/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1051 / 1132
/-    Path         : branches/sol_global-flux-surgery/GlobalPrefixOneHistoricalSeamScratch.lean
/-    Ref          : origin/sol/global-flux-surgery
/-    First-commit : 2026-08-17 14:31:00 +0530  (af38139)
/-    Last-commit  : 2026-08-17 14:31:00 +0530  (af38139)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 14:31:00 +0530  af38139  (ker07-dev)
/-        Isolate historical one-error goal as exact canonical phase counterexample
/- ====================================================================== -/

import ErdosTernary2
import GSTPhaseCrossingScratch
import OmegaUPotentialBridgeScratch
import PurePowerBadAxisScratch
import GlobalPrefixOnePhaseMatrixScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Historical one-error seam, stripped to the exact physical counterexample

This file targets the actual comparator proof state from the 391205-byte
materialized source.  It does not assume phase crossing and it does not reuse
the quarantined residual termination theorem.

The purpose is surgical: show that the historical hypotheses

  * a certified child Happy Gate, and
  * no parent SURVIVE event

are *exactly* a counterexample to canonical physical phase crossing.
The old spacetime variables `hAllActiveFree`, `hTransfer`, and `hChildBelow`
do not add mathematical strength to this final seam; the child gate and the
no-SURVIVE hypothesis already reduce it to the physical double-jump problem.
-/

/-- Canonical child/parent phase-counterexample package corresponding to one
prefix-one Omega state. -/
def GSTPrefixOnePhysicalCrossingCounterexampleS (s n : Nat) : Prop :=
  let D := 3^(s+1)
  let T := gstNavigationConstant (s+1) n
  let A := 4^(3^s)
  let z := c s / 3
  let H := z + A*T
  let E0 := 4^(3^(s+1)*n)
  let E1 := A*E0
  (∃ q0, GSTDoubleJumpS (3*D) E0 q0) ∧
    (∀ q1, ¬ GSTDoubleJumpS (3*D) E1 q1)

/-- `c_s = 1 + 3*(c_s/3)` at every positive canonical level. -/
theorem gst_canonical_c_split_threeS
    (s : Nat) (hs : 1 ≤ s) :
    c s = 1 + 3*(c s / 3) := by
  have hc3 : c s % 3 = 1 := c_mod3 s hs
  have h := Nat.mod_add_div (c s) 3
  rw [hc3] at h
  omega

/-- The child perfect-power energy has exactly the phase-zero affine shape. -/
theorem gst_prefix_one_child_energy_shapeS
    (s n : Nat) (hs : 1 ≤ s) :
    4^(3^(s+1)*n) =
      1 + 3 * 3^(s+1) * gstNavigationConstant (s+1) n := by
  have h := gst_navigation_decomposition (s+1) n (by omega)
  have hp : 3^((s+1)+1) = 3 * 3^(s+1) := by
    rw [show (s+1)+1 = (s+1)+1 by rfl, Nat.pow_succ]
    ac_rfl
  rw [hp] at h
  simpa [Nat.mul_assoc] using h

/-- Multiplying the child energy by the canonical block gives precisely the
phase-one seeded energy chart used by the physical double-jump theorem. -/
theorem gst_prefix_one_parent_energy_shapeS
    (s n : Nat) (hs : 1 ≤ s) :
    let D := 3^(s+1)
    let T := gstNavigationConstant (s+1) n
    let A := 4^(3^s)
    let z := c s / 3
    let H := z + A*T
    let E0 := 4^(3^(s+1)*n)
    A*E0 = 1 + D + 3*D*H := by
  dsimp only
  have hA : 4^(3^s) = 1 + 3^(s+1) * c s := lte_identity s hs
  have hc : c s = 1 + 3*(c s / 3) := gst_canonical_c_split_threeS s hs
  have hE0 := gst_prefix_one_child_energy_shapeS s n hs
  have haxis := gst_prefix_one_pure_power_axisS
    (4^(3^s)) (3^(s+1)) (c s) (c s/3)
    (gstNavigationConstant (s+1) n) (4^(3^(s+1)*n))
    hA hc (by simpa [Nat.mul_assoc] using hE0)
  nlinarith

/-- No parent SURVIVE is exactly a complete seed-one bad trace on the same
canonical affine tail.  This is obtained directly from the Omega event
semantics; no residual termination theorem is used. -/
theorem gst_prefix_one_no_survive_to_seeded_badS
    (s n : Nat) (hs : 1 ≤ s)
    (hNoSurviveAt : ∀ j, gstOmegaEvent s 1 n j ≠ .survive) :
    GSTSeededBadTraceS 1
      (c s / 3 + 4^(3^s) * gstNavigationConstant (s+1) n) := by
  have hBad : GSTOmegaInfiniteBadTrace s 1 n := by
    intro j
    change GSTOmegaGatePolynomial (gstOmega s 1 n j) ≠ 0
    intro hzero
    have hsurvive : gstOmegaEvent s 1 n j = .survive :=
      (gst_omega_prefix_one_survive_iff_gatePolynomial_zero s n j hs).2 hzero
    exact hNoSurviveAt j hsurvive
  have hseeded := gst_prefix_one_omega_bad_to_u_seeded_badS s n hs hBad
  intro j
  simpa [gstPrefixOneUPotentialTailS] using hseeded j

/-- The exact historical final state produces a literal canonical phase
crossing counterexample.  In particular, the old `hTransfer` and finite-index
bounds are diagnostic consequences of the child gate, not the missing forcing
principle. -/
theorem gst_historical_one_error_is_physical_crossing_counterexampleS
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (data : GSTPrefixOneOmegaData s n)
    (hNoSurviveAt : ∀ j, gstOmegaEvent s 1 n j ≠ .survive) :
    GSTPrefixOnePhysicalCrossingCounterexampleS s n := by
  let D := 3^(s+1)
  let T := gstNavigationConstant (s+1) n
  let A := 4^(3^s)
  let z := c s / 3
  let H := z + A*T
  let E0 := 4^(3^(s+1)*n)
  let E1 := A*E0

  have hD3 : 3 ≤ D := by
    dsimp [D]
    have h9 : 9 ≤ 3^(s+1) := by
      rw [show (9:Nat) = 3^2 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega

  have hchild :
      gstDigitS T data.childGateIndex = 2 ∧
      (gstAffineMulCarryS 4 0 T data.childGateIndex = 0 ∨
       gstAffineMulCarryS 4 0 T data.childGateIndex = 3) := by
    simpa [T, gstOmega, gstDigitS, gstDigit, gstAffineMulCarryS,
      gstCarry] using data.childGate

  have hE0 : E0 = 1 + 3*D*T := by
    dsimp [E0, D, T]
    simpa [Nat.mul_assoc] using gst_prefix_one_child_energy_shapeS s n hs

  have hphase0 : GSTDoubleJumpS (3*D) E0 data.childGateIndex :=
    (gst_phase0_seeded_happy_iff_double_jumpS
      D T E0 data.childGateIndex hD3 hE0).1 hchild

  have hParentBad : GSTSeededBadTraceS 1 H := by
    dsimp [H, z, A, T]
    exact gst_prefix_one_no_survive_to_seeded_badS s n hs hNoSurviveAt

  have hE1 : E1 = 1 + D + 3*D*H := by
    dsimp [E1, D, T, A, z, H, E0]
    exact gst_prefix_one_parent_energy_shapeS s n hs

  have hphase1 : ∀ q, ¬ GSTDoubleJumpS (3*D) E1 q :=
    (gst_phase1_seeded_bad_iff_no_double_jumpS
      D H E1 hD3 hE1).1 hParentBad

  dsimp [GSTPrefixOnePhysicalCrossingCounterexampleS,
    D, T, A, z, H, E0, E1]
  exact ⟨⟨data.childGateIndex, by simpa [D, E0] using hphase0⟩,
    by intro q; simpa [D, E1] using hphase1 q⟩

/-- Matrix form of the same historical counterexample.  The left boundary has
an x4 BIG2 window, while the canonical phase-shifted right boundary has no x4
BIG2 window at any ternary row. -/
theorem gst_historical_one_error_matrix_formS
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (data : GSTPrefixOneOmegaData s n)
    (hNoSurviveAt : ∀ j, gstOmegaEvent s 1 n j ≠ .survive) :
    let T := gstNavigationConstant (s+1) n
    let A := 4^(3^s)
    let z := c s / 3
    let H := z + A*T
    let E0 := 4^(3^(s+1)*n)
    let E1 := A*E0
    ∃ q0,
      (gstPhysicalBinaryDigitS E0 0 (s+2+q0) = 2 ∧
       gstPhysicalBinaryDigitS E0 2 (s+2+q0) = 2) ∧
      (∀ q,
        ¬ (gstPhysicalBinaryDigitS E0 (2*3^s) (s+2+q) = 2 ∧
           gstPhysicalBinaryDigitS E0 (2*3^s+2) (s+2+q) = 2)) := by
  dsimp only
  let D := 3^(s+1)
  let T := gstNavigationConstant (s+1) n
  let A := 4^(3^s)
  let z := c s / 3
  let H := z + A*T
  let E0 := 4^(3^(s+1)*n)
  let E1 := A*E0

  have hcounter :=
    gst_historical_one_error_is_physical_crossing_counterexampleS
      s n hs hn data hNoSurviveAt
  dsimp [GSTPrefixOnePhysicalCrossingCounterexampleS,
    D, T, A, z, H, E0, E1] at hcounter
  obtain ⟨⟨q0, h0⟩, hno1⟩ := hcounter

  have hE0shape : E0 = 1 + 3*3^(s+1)*T := by
    dsimp [E0, T]
    exact gst_prefix_one_child_energy_shapeS s n hs
  have hE1shape : E1 = 1 + 3^(s+1) + 3*3^(s+1)*H := by
    dsimp [E1, H, A, z, T, E0]
    simpa [Nat.mul_assoc] using gst_prefix_one_parent_energy_shapeS s n hs
  have hphase : E1 = 4^(3^s) * E0 := by rfl
  have hmatrix := gst_canonical_crossing_matrix_reductionS
    s T H E0 E1 q0 hs hE0shape hE1shape hphase
    (by simpa [D] using h0)

  refine ⟨q0, hmatrix.1, ?_⟩
  intro q hright
  have hjump := (hmatrix.2 q).2 hright
  exact (hno1 q) (by simpa [D] using hjump)
