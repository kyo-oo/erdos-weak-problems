/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0459 / 1132
/-    Path         : branches/sol_5c579-final-bigN-right-chord-atomic/PhaseCycleInformationScratch.lean
/-    Ref          : origin/sol/5c579-final-bigN-right-chord-atomic
/-    First-commit : 2026-08-15 23:16:14 +0530  (e16e375)
/-    Last-commit  : 2026-08-16 02:03:41 +0530  (40a28dc)
/-    Total commits: 5
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/5] 2026-08-15 23:16:14 +0530  e16e375  (ker07-dev)
/-        Kernelize cyclic shared-information transfer across GST phases
/- [02/5] 2026-08-15 23:36:00 +0530  f64a2a0  (ker07-dev)
/-        Fix nonlinear phase-cycle proof tactics
/- [03/5] 2026-08-16 00:35:38 +0530  2da13f8  (ker07-dev)
/-        Compile GST Graph V2 through phase-cycle gate
/- [04/5] 2026-08-16 01:22:11 +0530  8de8e72  (ker07-dev)
/-        Compile prefixed residue spacetime through phase cycle
/- [05/5] 2026-08-16 02:03:41 +0530  40a28dc  (ker07-dev)
/-        Compile GST Graph V2 block law with phase frontier
/- ====================================================================== -/

import InformationDescentScratch
import OriginTransducerScratch
import GSTResidueSpacetimeScratch
import GSTGraphV2BlockScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
Cyclic shared-information algebra for the corrected infinite-wave GST picture.

The phase transitions are not terminal reductions.  They are three exact
realisations of one conserved affine information law, with incoming GST seeds
cycling 0 -> 1 -> 2 -> 0.
-/

/-- Generic seeded commuting-square law.

If the two full integer realisations agree

    B + A*(C + 4*T) = C' + 4*(z + A*T),

then after every ternary cut q the same information splits into the high
A-coordinate (the child seeded carry) and the low base-4 coordinate (the
parent seeded carry):

    beta_q + A*h_q = p'_q + 4*a_q.

No finite cutoff, terminal state, or origin exhaustion is used. -/
theorem gst_seeded_shared_information_equationS
    (A B C C' z T q : Nat)
    (hcommute : B + A*(C + 4*T) = C' + 4*(z + A*T)) :
    gstAffineMulCarryS A B (C + 4*T) q +
        A * gstAffineMulCarryS 4 C T q =
      gstAffineMulCarryS 4 C' (z + A*T) q +
        4 * gstAffineMulCarryS A z T q := by
  have hleft := gst_affine_tail_div_decompositionS B A (C + 4*T) q
  have hchild := gst_affine_tail_div_decompositionS C 4 T q
  have hright := gst_affine_tail_div_decompositionS C' 4 (z + A*T) q
  have htail := gst_affine_tail_div_decompositionS z A T q
  have hfull :
      (B + A*(C + 4*T)) / 3^q =
        (C' + 4*(z + A*T)) / 3^q := by
    rw [hcommute]
  rw [hleft, hright, hchild, htail] at hfull
  nlinarith

/-- Phase 0 -> phase 1: seed zero becomes seed one. -/
theorem gst_phase01_shared_informationS
    (A z T q : Nat) :
    gstAffineMulCarryS A (1 + 4*z) (4*T) q +
        A * gstAffineMulCarryS 4 0 T q =
      gstAffineMulCarryS 4 1 (z + A*T) q +
        4 * gstAffineMulCarryS A z T q := by
  have hcommute :
      (1 + 4*z) + A*(0 + 4*T) =
        1 + 4*(z + A*T) := by ring
  simpa using
    (gst_seeded_shared_information_equationS
      A (1 + 4*z) 0 1 z T q hcommute)

/-- Phase 1 -> phase 2.  Write D=3*N and A=1+D*c.  With c=1+3*z,
    the exact phase-one tail offset is z + N*c.  The information seed advances
    from one to two, while the companion high coordinate remains explicit. -/
theorem gst_phase12_shared_informationS
    (N c z T q : Nat)
    (hc : c = 1 + 3*z) :
    let A := 1 + 3*N*c
    let z12 := z + N*c
    let B12 := 1 + 4*z + N*c
    gstAffineMulCarryS A B12 (1 + 4*T) q +
        A * gstAffineMulCarryS 4 1 T q =
      gstAffineMulCarryS 4 2 (z12 + A*T) q +
        4 * gstAffineMulCarryS A z12 T q := by
  dsimp only
  have hcommute :
      (1 + 4*z + N*c) + (1 + 3*N*c)*(1 + 4*T) =
        2 + 4*((z + N*c) + (1 + 3*N*c)*T) := by
    rw [hc]
    ring
  exact gst_seeded_shared_information_equationS
    (1 + 3*N*c) (1 + 4*z + N*c) 1 2 (z + N*c) T q hcommute

/-- Phase 2 -> the next phase 0.  The seed does not die: the phase prefix wraps
    it back from two to zero while the affine information is retained in the
    new tail offset z + 1 + 2*N*c. -/
theorem gst_phase20_shared_informationS
    (N c z T q : Nat)
    (hc : c = 1 + 3*z) :
    let A := 1 + 3*N*c
    let z20 := z + 1 + 2*N*c
    let B20 := 2 + 4*z + 2*N*c
    gstAffineMulCarryS A B20 (2 + 4*T) q +
        A * gstAffineMulCarryS 4 2 T q =
      gstAffineMulCarryS 4 0 (z20 + A*T) q +
        4 * gstAffineMulCarryS A z20 T q := by
  dsimp only
  have hcommute :
      (2 + 4*z + 2*N*c) + (1 + 3*N*c)*(2 + 4*T) =
        0 + 4*((z + 1 + 2*N*c) + (1 + 3*N*c)*T) := by
    rw [hc]
    ring
  exact gst_seeded_shared_information_equationS
    (1 + 3*N*c) (2 + 4*z + 2*N*c) 2 0 (z + 1 + 2*N*c) T q hcommute

/-- The three companion offsets all remain inside the same horizontal
    multiplier interval.  This keeps every phase in one shared information
    carrier rather than creating or deleting a separate object. -/
theorem gst_phase_cycle_offsets_insideS
    (N c z : Nat)
    (hN : 3 ≤ N)
    (hc : c = 1 + 3*z) :
    let A := 1 + 3*N*c
    z < A ∧
      z + N*c < A ∧
      z + 1 + 2*N*c < A ∧
      1 + 4*z < A ∧
      1 + 4*z + N*c < A ∧
      2 + 4*z + 2*N*c < A := by
  dsimp only
  rw [hc]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith
