/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0109 / 1132
/-    Path         : branches/sol_physical-phase-crossing-surgery/InformationDescentScratch.lean
/-    Ref          : origin/sol/physical-phase-crossing-surgery
/-    First-commit : 2026-08-15 07:05:41 +0530  (48d293d)
/-    Last-commit  : 2026-08-15 09:36:02 +0530  (a9cbf11)
/-    Total commits: 9
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/9] 2026-08-15 07:05:41 +0530  48d293d  (ker07-dev)
/-        test: kernel-check information descent recurrence lemmas
/- [02/9] 2026-08-15 07:10:21 +0530  f49a746  (ker07-dev)
/-        fix: exact seeded recurrence scratch proofs
/- [03/9] 2026-08-15 07:15:15 +0530  aff2042  (ker07-dev)
/-        test: add exact affine block memory invariant
/- [04/9] 2026-08-15 07:19:44 +0530  2df5838  (ker07-dev)
/-        test: formalize conserved shared-information carry equation
/- [05/9] 2026-08-15 07:27:15 +0530  850ce9e  (ker07-dev)
/-        fix: normalize shared-information quotient rewrites
/- [06/9] 2026-08-15 07:33:32 +0530  9af3c34  (ker07-dev)
/-        fix: unfold affine carry at quotient seam
/- [07/9] 2026-08-15 07:39:12 +0530  56cd665  (ker07-dev)
/-        test: bound affine information carry by multiplier
/- [08/9] 2026-08-15 09:30:21 +0530  8952344  (ker07-dev)
/-        Formalize GST information quarter geometry and 22 synchronizer
/- [09/9] 2026-08-15 09:36:02 +0530  a9cbf11  (ker07-dev)
/-        Expose GST step arithmetic in 22 synchronizer proof
/- ====================================================================== -/

import Mathlib

/-!
Temporary RED/GREEN scratch for the corrected GST information-descent surgery.
This file contains only exact arithmetic mechanics; no universal Erdős claim.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

def gstCarryS (R p : Nat) : Nat := (4 * (R % 3^p)) / 3^p

def gstDigitS (R p : Nat) : Nat := R / 3^p % 3

def gstStepCarryS (C d : Nat) : Nat := (C + 4*d) / 3

def gstAffineMulCarryS (A z T p : Nat) : Nat :=
  (z + A * (T % 3^p)) / 3^p

/-- Exact carry recurrence, including the p=0 seam. -/
theorem gstCarryS_forward_exact_all (R p : Nat) :
    gstCarryS R (p+1) = gstStepCarryS (gstCarryS R p) (gstDigitS R p) := by
  simp only [gstCarryS, gstDigitS, gstStepCarryS, Nat.pow_succ]
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  have hsplit : R % (3^p * 3) = R % 3^p + 3^p * (R / 3^p % 3) := by
    rw [Nat.mod_mul]
  rw [hsplit, Nat.mul_add]
  rw [show 4 * (3^p * (R / 3^p % 3)) =
      3^p * (4 * (R / 3^p % 3)) by ac_rfl]
  rw [← Nat.div_div_eq_div_mul]
  rw [Nat.add_mul_div_left _ _ hp]

/-- NULL is regenerative when digit-two information is exposed. -/
theorem gst_null_two_regeneratesS
    (R p : Nat) (hC : gstCarryS R p = 0) (hd : gstDigitS R p = 2) :
    gstCarryS R (p+1) = 2 := by
  rw [gstCarryS_forward_exact_all, hC, hd]
  decide

/-- GST+ digit two propagates its carry-three phase. -/
theorem gst_plus_two_propagatesS
    (R p : Nat) (hC : gstCarryS R p = 3) (hd : gstDigitS R p = 2) :
    gstCarryS R (p+1) = 3 := by
  rw [gstCarryS_forward_exact_all, hC, hd]
  decide

/-- Seeded affine carries compose exactly under a ternary cut. -/
theorem gst_seeded_affine_carry_semigroupS
    (D X q j : Nat) :
    gstAffineMulCarryS 4 D X (q+j) =
      gstAffineMulCarryS 4 (gstAffineMulCarryS 4 D X q) (X / 3^q) j := by
  simp only [gstAffineMulCarryS]
  rw [Nat.pow_add, Nat.mod_mul]
  have hqpos : 0 < 3^q := Nat.pow_pos (by decide)
  have hshape : D + 4 * (X % 3^q + 3^q * (X / 3^q % 3^j)) =
      (D + 4 * (X % 3^q)) + 3^q * (4 * (X / 3^q % 3^j)) := by
    rw [Nat.mul_add]
    ac_rfl
  rw [hshape, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hqpos]

/-- Ternary digits reindex exactly under quotienting. -/
theorem gst_seeded_affine_digit_shiftS
    (X q j : Nat) :
    gstDigitS X (q+j) = gstDigitS (X / 3^q) j := by
  simp only [gstDigitS]
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]

/-- Child carry information becomes the explicit incoming seed after a cut. -/
theorem gst_child_carry_reindex_seededS
    (T q j : Nat) :
    gstCarryS T (q+j) =
      gstAffineMulCarryS 4 (gstCarryS T q) (T / 3^q) j := by
  have h := gst_seeded_affine_carry_semigroupS 0 T q j
  simpa [gstCarryS, gstAffineMulCarryS] using h

/-- Full child state reindexing. -/
theorem gst_child_state_reindex_seededS
    (T q j : Nat) :
    gstDigitS T (q+j) = gstDigitS (T / 3^q) j ∧
    gstCarryS T (q+j) =
      gstAffineMulCarryS 4 (gstCarryS T q) (T / 3^q) j := by
  exact ⟨gst_seeded_affine_digit_shiftS T q j,
    gst_child_carry_reindex_seededS T q j⟩

/-- Full parent affine state reindexing. -/
theorem gst_parent_state_reindex_seededS
    (D X q j : Nat) :
    gstDigitS X (q+j) = gstDigitS (X / 3^q) j ∧
    gstAffineMulCarryS 4 D X (q+j) =
      gstAffineMulCarryS 4 (gstAffineMulCarryS 4 D X q) (X / 3^q) j := by
  exact ⟨gst_seeded_affine_digit_shiftS X q j,
    gst_seeded_affine_carry_semigroupS D X q j⟩

/-- A gate at the cut remains digit-two with exactly its accumulated seed. -/
theorem gst_child_gate_reindex_seededS
    (T q : Nat)
    (hgate : gstDigitS T q = 2 ∧ (gstCarryS T q = 0 ∨ gstCarryS T q = 3)) :
    gstDigitS (T / 3^q) 0 = 2 ∧
      (gstAffineMulCarryS 4 (gstCarryS T q) (T / 3^q) 0 = 0 ∨
       gstAffineMulCarryS 4 (gstCarryS T q) (T / 3^q) 0 = 3) := by
  constructor
  · rw [← gst_seeded_affine_digit_shiftS T q 0]
    simpa using hgate.1
  · rcases hgate.2 with h0 | h3
    · left
      simp [gstAffineMulCarryS, h0, Nat.mod_one]
    · right
      simp [gstAffineMulCarryS, h3, Nat.mod_one]

/-- Exact block-memory identity.  If the affine multiplier has the GST form
    A = 1 + D*c, then after a D-adic cut the processed child residue is not
    erased: it appears explicitly as the carry term c*(T mod D). -/
theorem gst_affine_block_memoryS
    (z A c D T : Nat) (hD : 0 < D) (hA : A = 1 + D*c) :
    (z + A * (T % D)) / D =
      c * (T % D) + (z + T % D) / D := by
  rw [hA]
  have hshape :
      z + (1 + D*c) * (T % D) =
        (z + T % D) + D * (c * (T % D)) := by
    rw [Nat.add_mul, Nat.one_mul]
    ac_rfl
  rw [hshape, Nat.add_mul_div_left _ _ hD]
  omega

/-- Exact quotient decomposition of an affine realization at a ternary cut. -/
theorem gst_affine_tail_div_decompositionS
    (z A T q : Nat) :
    (z + A*T) / 3^q =
      gstAffineMulCarryS A z T q + A*(T / 3^q) := by
  have hqpos : 0 < 3^q := Nat.pow_pos (by decide)
  have hdiv : T = 3^q * (T / 3^q) + T % 3^q :=
    (Nat.div_add_mod T (3^q)).symm
  rw [hdiv, Nat.mul_add]
  rw [show A * (3^q * (T / 3^q)) =
      3^q * (A * (T / 3^q)) by ac_rfl]
  rw [show z + (3^q * (A * (T / 3^q)) + A * (T % 3^q)) =
      (z + A * (T % 3^q)) + 3^q * (A * (T / 3^q)) by ac_rfl]
  rw [Nat.add_mul_div_left _ _ hqpos, ← hdiv]
  simp [gstAffineMulCarryS]

/-- Conserved coupling of the two realizations.  Put X = z + A*T and
    Y = (1+4z) + A*(4T) = 1+4X.  After any ternary cut q, if a0/a1 are the
    two affine carries, h is the child carry and p is the parent seeded carry,
    then a1 + A*h = p + 4*a0. -/
theorem gst_shared_information_carry_equationS
    (A z T q : Nat) :
    gstAffineMulCarryS A (1 + 4*z) (4*T) q + A * gstCarryS T q =
      gstAffineMulCarryS 4 1 (z + A*T) q +
        4 * gstAffineMulCarryS A z T q := by
  have hx := gst_affine_tail_div_decompositionS z A T q
  have hy := gst_affine_tail_div_decompositionS (1 + 4*z) A (4*T) q
  have hp := gst_affine_tail_div_decompositionS 1 4 (z + A*T) q
  have ht := gst_affine_tail_div_decompositionS 0 4 T q
  have ht' : (4*T) / 3^q = gstCarryS T q + 4*(T / 3^q) := by
    simpa [gstCarryS, gstAffineMulCarryS] using ht
  have hnum : (1 + 4*z) + A*(4*T) = 1 + 4*(z + A*T) := by
    ring
  have hfull :
      ((1 + 4*z) + A*(4*T)) / 3^q =
        (1 + 4*(z + A*T)) / 3^q := by rw [hnum]
  rw [hy, hp, hx, ht'] at hfull
  ring_nf at hfull ⊢
  omega

/-- Any affine information carry stays strictly inside the multiplier interval
    when its seed is already inside that interval. -/
theorem gst_affine_carry_lt_multiplierS
    (A z T q : Nat) (hA : 0 < A) (hz : z < A) :
    gstAffineMulCarryS A z T q < A := by
  unfold gstAffineMulCarryS
  have hM : 0 < 3^q := Nat.pow_pos (by decide)
  have hr : T % 3^q < 3^q := Nat.mod_lt T hM
  have hnum : z + A * (T % 3^q) < 3^q * A := by
    calc
      z + A * (T % 3^q) < A + A * (T % 3^q) :=
        Nat.add_lt_add_right hz _
      _ = A * ((T % 3^q) + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        ac_rfl
      _ ≤ A * 3^q := Nat.mul_le_mul_left A (Nat.succ_le_of_lt hr)
      _ = 3^q * A := by ac_rfl
  exact Nat.div_lt_of_lt_mul hnum

/-- For a GST multiplier A = 1 + D*c with D at least 9, both vertical
    offsets used by the commuting square lie strictly below A. -/
theorem gst_gst_offsets_lt_multiplierS
    (D c : Nat) (hD : 9 ≤ D) (hc : 1 ≤ c) :
    c / 3 < 1 + D*c ∧
      1 + 4*(c / 3) < 1 + D*c := by
  have hcpos : 0 < c := by omega
  have hdiv : c / 3 ≤ c := Nat.div_le_self c 3
  have hDc : c < D*c := by
    have h1D : 1 < D := by omega
    simpa [Nat.one_mul] using Nat.mul_lt_mul_of_pos_right h1D hcpos
  have hfour : 4*(c/3) ≤ 4*c := Nat.mul_le_mul_left 4 hdiv
  have h4D : 4*c < D*c := by
    have h4 : 4 < D := by omega
    exact Nat.mul_lt_mul_of_pos_right h4 hcpos
  constructor <;> omega

/-- NULL at the child gate forces the coupled information state into the
    strict low quarter of the multiplier interval. -/
theorem gst_shared_information_null_low_quarterS
    (A z T q : Nat) (hA : 0 < A) (hz1 : 1 + 4*z < A)
    (hnull : gstCarryS T q = 0) :
    gstAffineMulCarryS 4 1 (z + A*T) q +
        4 * gstAffineMulCarryS A z T q < A := by
  have hEq := gst_shared_information_carry_equationS A z T q
  have ha1 : gstAffineMulCarryS A (1 + 4*z) (4*T) q < A :=
    gst_affine_carry_lt_multiplierS A (1 + 4*z) (4*T) q hA hz1
  simp [hnull] at hEq
  omega

/-- GST+ at the child gate forces the coupled information state into the
    strict high quarter [3A,4A) of the multiplier interval. -/
theorem gst_shared_information_plus_high_quarterS
    (A z T q : Nat) (hA : 0 < A) (hz1 : 1 + 4*z < A)
    (hplus : gstCarryS T q = 3) :
    3*A ≤
        gstAffineMulCarryS 4 1 (z + A*T) q +
          4 * gstAffineMulCarryS A z T q ∧
    gstAffineMulCarryS 4 1 (z + A*T) q +
          4 * gstAffineMulCarryS A z T q < 4*A := by
  have hEq := gst_shared_information_carry_equationS A z T q
  have ha1 : gstAffineMulCarryS A (1 + 4*z) (4*T) q < A :=
    gst_affine_carry_lt_multiplierS A (1 + 4*z) (4*T) q hA hz1
  rw [hplus] at hEq
  constructor <;> omega

/-- One-step recurrence for the seed-one affine GST carry. -/
theorem gstAffineS_forward_exact_all (D X p : Nat) :
    gstAffineMulCarryS 4 D X (p+1) =
      gstStepCarryS (gstAffineMulCarryS 4 D X p) (gstDigitS X p) := by
  have h := gst_seeded_affine_carry_semigroupS D X p 1
  simpa [gstAffineMulCarryS, gstStepCarryS, gstDigitS] using h

/-- The consecutive digit word 22 is a universal GST synchronizer: from every
    incoming carry below four, one of its two digit-two vertices is Happy. -/
theorem gst_two_two_forces_happy_gateS
    (D X p : Nat)
    (hC : gstAffineMulCarryS 4 D X p < 4)
    (hd0 : gstDigitS X p = 2)
    (hd1 : gstDigitS X (p+1) = 2) :
    (gstDigitS X p = 2 ∧
      (gstAffineMulCarryS 4 D X p = 0 ∨
       gstAffineMulCarryS 4 D X p = 3)) ∨
    (gstDigitS X (p+1) = 2 ∧
      (gstAffineMulCarryS 4 D X (p+1) = 0 ∨
       gstAffineMulCarryS 4 D X (p+1) = 3)) := by
  have hstep := gstAffineS_forward_exact_all D X p
  rw [hd0] at hstep
  simp [gstStepCarryS] at hstep
  omega
