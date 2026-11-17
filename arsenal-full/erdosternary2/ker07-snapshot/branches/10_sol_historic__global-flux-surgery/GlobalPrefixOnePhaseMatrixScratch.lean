/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1049 / 1132
/-    Path         : branches/sol_global-flux-surgery/GlobalPrefixOnePhaseMatrixScratch.lean
/-    Ref          : origin/sol/global-flux-surgery
/-    First-commit : 2026-08-17 14:14:50 +0530  (3dfe293)
/-    Last-commit  : 2026-08-17 14:15:28 +0530  (3c34b1c)
/-    Total commits: 2
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/2] 2026-08-17 14:14:50 +0530  3dfe293  (ker07-dev)
/-        Reduce canonical phase crossing to exact binary power-window transport
/- [02/2] 2026-08-17 14:15:28 +0530  3c34b1c  (ker07-dev)
/-        Simplify exact phase-matrix rewrite
/- ====================================================================== -/

import GlobalPrefixOneFluxSurgeryScratch
import GSTPhaseCrossingScratch
import PurePowerBadAxisScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Canonical phase crossing as a physical binary power matrix

This file performs the second reduction in the historical one-error surgery.
A phase-zero/phase-one `GSTDoubleJumpS` is rewritten as an actual two-column
x2 window in the matrix of consecutive powers of two.

The result is deliberately exact: the remaining crossing is no longer an
Omega event, mirror statement, or affine abstraction.  It is the transport of
a BIG2 endpoint pair from binary columns `0,2` to columns `2N,2N+2`, where
`N = 3^s` is the canonical phase width.
-/

/-- `4^N` is the same horizontal displacement as `2N` microscopic x2
columns. -/
theorem gst_four_pow_eq_two_pow_doubleS (N : Nat) :
    4^N = 2^(2*N) := by
  rw [show (4:Nat) = 2^2 by decide, ← Nat.pow_mul]
  congr 1
  omega

/-- The phase-zero residue double jump is literally BIG2 at the two endpoints
of the physical x4 window `E0 -> 4*E0`, at absolute ternary row `s+2+q`. -/
theorem gst_phase0_double_jump_iff_physical_x4_windowS
    (s T E0 q : Nat) (hs : 1 ≤ s)
    (hE0 : E0 = 1 + 3*3^(s+1)*T) :
    GSTDoubleJumpS (3*3^(s+1)) E0 q ↔
      gstPhysicalBinaryDigitS E0 0 (s+2+q) = 2 ∧
      gstPhysicalBinaryDigitS E0 2 (s+2+q) = 2 := by
  let D := 3^(s+1)
  have hD3 : 3 ≤ D := by
    dsimp [D]
    have h9 : 9 ≤ 3^(s+1) := by
      rw [show (9:Nat) = 3^2 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega
  have hE0' : E0 = 1 + 3*D*T := by
    simpa [D, Nat.mul_assoc] using hE0
  have hcommon :
      GSTDoubleJumpS (3*D) E0 q ↔
        (gstDigitS T q = 2 ∧ gstDigitS (4*T) q = 2) := by
    exact (gst_phase0_common_two_iff_double_jumpS D T E0 q hD3 hE0').symm
  have hB : 3*D = 3^(s+2) := by
    dsimp [D]
    rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
    ac_rfl
  have hL1 : 1 < 3^(s+2) := by
    have h27 : 27 ≤ 3^(s+2) := by
      rw [show (27:Nat) = 3^3 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega
  have hL4 : 4 < 3^(s+2) := by omega
  have hd0 : gstWideDigitS E0 (s+2+q) = gstDigitS T q := by
    have h := gst_prefixed_tail_digitS 1 T (s+2) q hL1
    rw [hE0', hB] at h
    simpa [gstWideDigitS, gstDigitS] using h
  have h4shape : 4*E0 = 4 + 3^(s+2)*(4*T) := by
    rw [hE0', hB]
    ring
  have hd2 : gstWideDigitS (4*E0) (s+2+q) = gstDigitS (4*T) q := by
    have h := gst_prefixed_tail_digitS 4 (4*T) (s+2) q hL4
    rw [← h4shape] at h
    simpa [gstWideDigitS, gstDigitS] using h
  rw [show 3*3^(s+1) = 3*D by rfl, hcommon]
  constructor
  · rintro ⟨h0,h2⟩
    constructor
    · simpa [gstPhysicalBinaryDigitS] using hd0.trans h0
    · have hpow2 : 2^2 * E0 = 4*E0 := by norm_num
      simpa [gstPhysicalBinaryDigitS, hpow2] using hd2.trans h2
  · rintro ⟨h0,h2⟩
    constructor
    · have h0' : gstWideDigitS E0 (s+2+q) = 2 := by
        simpa [gstPhysicalBinaryDigitS] using h0
      exact hd0.symm.trans h0'
    · have hpow2 : 2^2 * E0 = 4*E0 := by norm_num
      have h2' : gstWideDigitS (4*E0) (s+2+q) = 2 := by
        simpa [gstPhysicalBinaryDigitS, hpow2] using h2
      exact hd2.symm.trans h2'

/-- The phase-one double jump is likewise a physical x4 BIG2 endpoint pair in
`E1 -> 4*E1`. -/
theorem gst_phase1_double_jump_iff_physical_x4_windowS
    (s H E1 q : Nat) (hs : 1 ≤ s)
    (hE1 : E1 = 1 + 3^(s+1) + 3*3^(s+1)*H) :
    GSTDoubleJumpS (3*3^(s+1)) E1 q ↔
      gstPhysicalBinaryDigitS E1 0 (s+2+q) = 2 ∧
      gstPhysicalBinaryDigitS E1 2 (s+2+q) = 2 := by
  let D := 3^(s+1)
  have hD9 : 9 ≤ D := by
    dsimp [D]
    rw [show (9:Nat) = 3^2 by decide]
    exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  have hD3 : 3 ≤ D := by omega
  have hE1' : E1 = 1 + D + 3*D*H := by
    simpa [D, Nat.mul_assoc] using hE1
  have hcommon :
      GSTDoubleJumpS (3*D) E1 q ↔
        (gstDigitS H q = 2 ∧ gstDigitS (1+4*H) q = 2) := by
    exact (gst_phase1_common_two_iff_double_jumpS D H E1 q hD3 hE1').symm
  have hB : 3*D = 3^(s+2) := by
    dsimp [D]
    rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
    ac_rfl
  have hP0 : 1 + D < 3*D := by omega
  have hP1 : 4 + D < 3*D := by omega
  have hd0 : gstWideDigitS E1 (s+2+q) = gstDigitS H q := by
    have h := gst_prefixed_tail_digitS (1+D) H (s+2) q (by simpa [hB] using hP0)
    rw [hE1', hB] at h
    simpa [gstWideDigitS, gstDigitS] using h
  have h4shape : 4*E1 = (4+D) + 3^(s+2)*(1+4*H) := by
    rw [hE1', hB]
    ring
  have hd2 : gstWideDigitS (4*E1) (s+2+q) = gstDigitS (1+4*H) q := by
    have h := gst_prefixed_tail_digitS (4+D) (1+4*H) (s+2) q
      (by simpa [hB] using hP1)
    rw [← h4shape] at h
    simpa [gstWideDigitS, gstDigitS] using h
  rw [show 3*3^(s+1) = 3*D by rfl, hcommon]
  constructor
  · rintro ⟨h0,h2⟩
    constructor
    · simpa [gstPhysicalBinaryDigitS] using hd0.trans h0
    · have hpow2 : 2^2 * E1 = 4*E1 := by norm_num
      simpa [gstPhysicalBinaryDigitS, hpow2] using hd2.trans h2
  · rintro ⟨h0,h2⟩
    constructor
    · have h0' : gstWideDigitS E1 (s+2+q) = 2 := by
        simpa [gstPhysicalBinaryDigitS] using h0
      exact hd0.symm.trans h0'
    · have hpow2 : 2^2 * E1 = 4*E1 := by norm_num
      have h2' : gstWideDigitS (4*E1) (s+2+q) = 2 := by
        simpa [gstPhysicalBinaryDigitS, hpow2] using h2
      exact hd2.symm.trans h2'

/-- Canonical multiplication by `A=4^N` is exactly a shift by `2N` columns
in the physical binary matrix. -/
theorem gst_phase_shift_is_binary_column_shiftS
    (E0 E1 N i p : Nat)
    (hphase : E1 = 4^N * E0) :
    gstPhysicalBinaryDigitS E1 i p =
      gstPhysicalBinaryDigitS E0 (2*N+i) p := by
  unfold gstPhysicalBinaryDigitS
  rw [hphase, gst_four_pow_eq_two_pow_doubleS]
  have hpow : 2^i * (2^(2*N) * E0) = 2^(2*N+i) * E0 := by
    rw [← Nat.pow_add]
    ac_rfl
  rw [hpow]

/-- Exact matrix form of the canonical phase-crossing seam.  A child double
jump produces a BIG2 x4 window at columns `0,2`; a parent phase jump is exactly
a BIG2 x4 window at columns `2N,2N+2` of the *same* physical power matrix. -/
theorem gst_canonical_crossing_matrix_reductionS
    (s T H E0 E1 q0 : Nat) (hs : 1 ≤ s)
    (hE0 : E0 = 1 + 3*3^(s+1)*T)
    (hE1shape : E1 = 1 + 3^(s+1) + 3*3^(s+1)*H)
    (hphase : E1 = 4^(3^s) * E0)
    (hchild : GSTDoubleJumpS (3*3^(s+1)) E0 q0) :
    (gstPhysicalBinaryDigitS E0 0 (s+2+q0) = 2 ∧
     gstPhysicalBinaryDigitS E0 2 (s+2+q0) = 2) ∧
    (∀ q,
      GSTDoubleJumpS (3*3^(s+1)) E1 q ↔
        (gstPhysicalBinaryDigitS E0 (2*3^s) (s+2+q) = 2 ∧
         gstPhysicalBinaryDigitS E0 (2*3^s+2) (s+2+q) = 2)) := by
  constructor
  · exact (gst_phase0_double_jump_iff_physical_x4_windowS
      s T E0 q0 hs hE0).1 hchild
  · intro q
    rw [gst_phase1_double_jump_iff_physical_x4_windowS s H E1 q hs hE1shape]
    have h0 := gst_phase_shift_is_binary_column_shiftS E0 E1 (3^s) 0 (s+2+q) hphase
    have h2 := gst_phase_shift_is_binary_column_shiftS E0 E1 (3^s) 2 (s+2+q) hphase
    rw [h0, h2]
