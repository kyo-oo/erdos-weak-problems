/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0515 / 1132
/-    Path         : branches/sol_right-chord-firepower-base/GSTResidueSpacetimeScratch.lean
/-    Ref          : origin/sol/right-chord-firepower-base
/-    First-commit : 2026-08-16 01:21:28 +0530  (f245249)
/-    Last-commit  : 2026-08-16 01:22:54 +0530  (c879737)
/-    Total commits: 2
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/2] 2026-08-16 01:21:28 +0530  f245249  (ker07-dev)
/-        Add generic prefixed residue spacetime graph
/- [02/2] 2026-08-16 01:22:54 +0530  c879737  (ker07-dev)
/-        Add double-jump residue square to GST V2
/- ====================================================================== -/

import GSTGraphV2Scratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Generic prefixed residue spacetime

A chart `E = P + B*H`, with `P < B`, identifies the ternary digits of `H`
with the successive jumps of the full-energy residue tower modulo `B*3^q`.
-/

def gstPrefixedModulusS (B q : Nat) : Nat := B * 3^q

/-- Exact residue of a prefixed ternary tail. -/
theorem gst_prefixed_residue_exactS
    (P B H E q : Nat)
    (hB : 1 ≤ B) (hP : P < B)
    (hE : E = P + B*H) :
    E % gstPrefixedModulusS B q = P + B*(H % 3^q) := by
  unfold gstPrefixedModulusS
  have hq : 0 < 3^q := Nat.pow_pos (by decide)
  have hM : 0 < B*3^q := Nat.mul_pos (by omega) hq
  have hr : H % 3^q < 3^q := Nat.mod_lt _ hq
  have hsmall : P + B*(H % 3^q) < B*3^q := by
    calc
      P + B*(H % 3^q) < B + B*(H % 3^q) :=
        Nat.add_lt_add_right hP _
      _ = B*((H % 3^q)+1) := by ring
      _ ≤ B*3^q := Nat.mul_le_mul_left B (Nat.succ_le_of_lt hr)
  have hH : H = 3^q*(H/3^q) + H%3^q :=
    (Nat.div_add_mod H (3^q)).symm
  have hdecomp :
      E = (P + B*(H%3^q)) + (B*3^q)*(H/3^q) := by
    rw [hE]
    conv_lhs => rw [hH]
    ring
  have hzero : ((B*3^q)*(H/3^q)) % (B*3^q) = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right _ _)
  rw [hdecomp, Nat.add_mod, hzero, Nat.add_zero, Nat.mod_mod]
  exact Nat.mod_eq_of_lt hsmall

/-- Successive prefixed residues differ by exactly one tail ternary digit. -/
theorem gst_prefixed_residue_stepS
    (P B H q : Nat) :
    P + B*(H % 3^(q+1)) =
      (P + B*(H % 3^q)) +
        gstPrefixedModulusS B q * gstDigitS H q := by
  unfold gstPrefixedModulusS gstDigitS
  rw [Nat.pow_succ, Nat.mod_mul]
  ring

/-- A tail digit two is exactly a `+2` jump in the full-energy residue tower. -/
theorem gst_prefixed_digit_two_iff_residue_jumpS
    (P B H E q : Nat)
    (hB : 1 ≤ B) (hP : P < B)
    (hE : E = P + B*H) :
    gstDigitS H q = 2 ↔
      E % gstPrefixedModulusS B (q+1) =
        E % gstPrefixedModulusS B q +
          2 * gstPrefixedModulusS B q := by
  have hq := gst_prefixed_residue_exactS P B H E q hB hP hE
  have hq1 := gst_prefixed_residue_exactS P B H E (q+1) hB hP hE
  have hstep := gst_prefixed_residue_stepS P B H q
  constructor
  · intro hd
    rw [hq1, hq, hstep, hd]
    ring
  · intro hjump
    rw [hq1, hq] at hjump
    rw [hstep] at hjump
    have hadd :
        gstPrefixedModulusS B q * gstDigitS H q =
          2 * gstPrefixedModulusS B q :=
      Nat.add_left_cancel hjump
    have hM : 0 < gstPrefixedModulusS B q := by
      unfold gstPrefixedModulusS
      exact Nat.mul_pos (by omega) (Nat.pow_pos (by decide))
    have hmul :
        gstPrefixedModulusS B q * gstDigitS H q =
          gstPrefixedModulusS B q * 2 := by
      simpa [Nat.mul_comm] using hadd
    exact Nat.mul_left_cancel hM hmul

/-- A common digit two between two prefixed tails is exactly a simultaneous
`+2` jump of their two full-energy residue towers. -/
theorem gst_prefixed_common_two_iff_double_residue_jumpS
    (P0 P1 B H0 H1 E0 E1 q : Nat)
    (hB : 1 ≤ B) (hP0 : P0 < B) (hP1 : P1 < B)
    (hE0 : E0 = P0 + B*H0)
    (hE1 : E1 = P1 + B*H1) :
    (gstDigitS H0 q = 2 ∧ gstDigitS H1 q = 2) ↔
      (E0 % gstPrefixedModulusS B (q+1) =
          E0 % gstPrefixedModulusS B q + 2*gstPrefixedModulusS B q ∧
       E1 % gstPrefixedModulusS B (q+1) =
          E1 % gstPrefixedModulusS B q + 2*gstPrefixedModulusS B q) := by
  rw [gst_prefixed_digit_two_iff_residue_jumpS P0 B H0 E0 q hB hP0 hE0,
      gst_prefixed_digit_two_iff_residue_jumpS P1 B H1 E1 q hB hP1 hE1]

/-- One graph event: adjacent energies `E` and `4E` both make a digit-two
residue jump at the same ternary row. -/
def GSTDoubleJumpS (B E q : Nat) : Prop :=
  E % gstPrefixedModulusS B (q+1) =
      E % gstPrefixedModulusS B q + 2*gstPrefixedModulusS B q ∧
  (4*E) % gstPrefixedModulusS B (q+1) =
      (4*E) % gstPrefixedModulusS B q + 2*gstPrefixedModulusS B q

/-- Phase-zero SURVIVE/common-two is exactly a double jump of the exact energy
`E = 1 + 3D*T`. -/
theorem gst_phase0_common_two_iff_double_jumpS
    (D T E q : Nat) (hD : 3 ≤ D)
    (hE : E = 1 + 3*D*T) :
    (gstDigitS T q = 2 ∧ gstDigitS (4*T) q = 2) ↔
      GSTDoubleJumpS (3*D) E q := by
  have hE4 : 4*E = 4 + (3*D)*(4*T) := by
    rw [hE]
    ring
  simpa [GSTDoubleJumpS] using
    (gst_prefixed_common_two_iff_double_residue_jumpS
      1 4 (3*D) T (4*T) E (4*E) q
      (by omega) (by omega) (by omega) hE hE4)

/-- Phase-one SURVIVE/common-two is exactly a double jump of the exact energy
`E = 1 + D + 3D*H`.  The microscopic output tail is `1+4H`. -/
theorem gst_phase1_common_two_iff_double_jumpS
    (D H E q : Nat) (hD : 3 ≤ D)
    (hE : E = 1 + D + 3*D*H) :
    (gstDigitS H q = 2 ∧ gstDigitS (1+4*H) q = 2) ↔
      GSTDoubleJumpS (3*D) E q := by
  have hE4 : 4*E = (4+D) + (3*D)*(1+4*H) := by
    rw [hE]
    ring
  simpa [GSTDoubleJumpS] using
    (gst_prefixed_common_two_iff_double_residue_jumpS
      (1+D) (4+D) (3*D) H (1+4*H) E (4*E) q
      (by omega) (by omega) (by omega) hE hE4)
