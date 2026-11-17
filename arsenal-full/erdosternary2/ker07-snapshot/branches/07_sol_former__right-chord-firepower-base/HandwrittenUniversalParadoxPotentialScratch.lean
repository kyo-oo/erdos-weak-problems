/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0958 / 1132
/-    Path         : branches/sol_right-chord-firepower-base/HandwrittenUniversalParadoxPotentialScratch.lean
/-    Ref          : origin/sol/right-chord-firepower-base
/-    First-commit : 2026-08-17 09:49:45 +0530  (ff85341)
/-    Last-commit  : 2026-08-17 09:49:45 +0530  (ff85341)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 09:49:45 +0530  ff85341  (ker07-dev)
/-        Add handwritten U-potential bad/gate detector scratch
/- ====================================================================== -/

import InformationBadTraceScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Handwritten U-potential on the exact GST carry spaces

This scratch is derived from the full handwritten U/Omega/V2 experiment.
It introduces no axiom and no forcing principle.  The potential is a finite
function on the four legal x4 carries.

The constants are the exact six-world/event constants discovered in the
handwritten layer:

* NULL: 5 = 6-1
* ALT-: 15 = 3*(6-1)
* GST+: 21 = 3*7

The key finite fact is that a GST cell is bad exactly when this potential does
not decrease after the ternary scale factor 3 and the digit-information cost
24 = 4*6 are included.  The only negative jumps are the two Happy/SURVIVE
cells.
-/

def gstHandwrittenUChargeS (C : Nat) : Nat :=
  if C = 0 then 5 else if C = 3 then 21 else 15

/-- Exact values on the four physical GST spaces/carries. -/
theorem gst_handwritten_u_charge_tableS :
    gstHandwrittenUChargeS 0 = 5 ∧
    gstHandwrittenUChargeS 1 = 15 ∧
    gstHandwrittenUChargeS 2 = 15 ∧
    gstHandwrittenUChargeS 3 = 21 := by
  decide

/-- Local U-potential characterization of the bad GST language.

For every legal cell, badness is equivalent to nonnegative potential flow

  24*d + q(C) <= 3*q(C').

The two cells for which this inequality fails are precisely NULL/GST+ digit-2
SURVIVE.
-/
theorem gst_bad_pair_iff_u_potential_nondecreaseS
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    GSTBadPairS C d ↔
      24*d + gstHandwrittenUChargeS C ≤
        3 * gstHandwrittenUChargeS (gstStepCarryS C d) := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    decide

/-- Integer signed jump.  Negative means that the physical cell is SURVIVE. -/
def gstHandwrittenUJumpS (C d : Nat) : Int :=
  3 * (gstHandwrittenUChargeS (gstStepCarryS C d) : Int) -
    (gstHandwrittenUChargeS C : Int) - 24*(d : Int)

/-- The exact signed jump table. -/
theorem gst_handwritten_u_jump_tableS :
    gstHandwrittenUJumpS 0 0 = 10 ∧
    gstHandwrittenUJumpS 0 1 = 16 ∧
    gstHandwrittenUJumpS 0 2 = -8 ∧
    gstHandwrittenUJumpS 1 0 = 0 ∧
    gstHandwrittenUJumpS 1 1 = 6 ∧
    gstHandwrittenUJumpS 1 2 = 0 ∧
    gstHandwrittenUJumpS 2 0 = 0 ∧
    gstHandwrittenUJumpS 2 1 = 6 ∧
    gstHandwrittenUJumpS 2 2 = 0 ∧
    gstHandwrittenUJumpS 3 0 = 24 ∧
    gstHandwrittenUJumpS 3 1 = 0 ∧
    gstHandwrittenUJumpS 3 2 = -6 := by
  decide

/-- Negative U-potential jump is exactly a physical Happy/SURVIVE cell. -/
theorem gst_handwritten_u_jump_negative_iff_happyS
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    gstHandwrittenUJumpS C d < 0 ↔
      d = 2 ∧ (C = 0 ∨ C = 3) := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    decide

/-- Exact next ternary-prefix decomposition used by the telescoping potential. -/
theorem gst_prefix_residue_succ_exactS (X K : Nat) :
    X % 3^(K+1) =
      X % 3^K + 3^K * gstDigitS X K := by
  unfold gstDigitS
  rw [Nat.pow_succ, Nat.mod_mul]

/-- A finite bad prefix telescopes the local U-potential inequalities.

  24*(X mod 3^K) + q(D)
    <= 3^K * q(carry_K).
-/
theorem gst_bad_prefix_u_potential_boundS
    (D X K : Nat) (hD : D < 4)
    (hbad : ∀ j, j < K →
      GSTBadPairS (gstAffineMulCarryS 4 D X j) (gstDigitS X j)) :
    24*(X % 3^K) + gstHandwrittenUChargeS D ≤
      3^K * gstHandwrittenUChargeS (gstAffineMulCarryS 4 D X K) := by
  induction K with
  | zero =>
      simp [gstAffineMulCarryS]
  | succ K ih =>
      have hprev :
          24*(X % 3^K) + gstHandwrittenUChargeS D ≤
            3^K * gstHandwrittenUChargeS (gstAffineMulCarryS 4 D X K) :=
        ih (fun j hj => hbad j (by omega))
      have hcarrylt : gstAffineMulCarryS 4 D X K < 4 :=
        gst_affine_carry_lt_multiplierS 4 D X K (by decide) hD
      have hdigitlt : gstDigitS X K < 3 := by
        unfold gstDigitS
        exact Nat.mod_lt _ (by decide)
      have hlocal :=
        (gst_bad_pair_iff_u_potential_nondecreaseS
          (gstAffineMulCarryS 4 D X K) (gstDigitS X K)
          hcarrylt hdigitlt).1 (hbad K (by omega))
      have hcarryStep := gstAffineS_forward_exact_all D X K
      rw [gst_prefix_residue_succ_exactS X K]
      have hpow : 3^(K+1) = 3^K * 3 := by rw [Nat.pow_succ]
      calc
        24 * (X % 3 ^ K + 3 ^ K * gstDigitS X K) +
              gstHandwrittenUChargeS D
            = (24*(X % 3^K) + gstHandwrittenUChargeS D) +
                3^K * (24*gstDigitS X K) := by ring
        _ ≤ 3^K * gstHandwrittenUChargeS (gstAffineMulCarryS 4 D X K) +
                3^K * (24*gstDigitS X K) :=
              Nat.add_le_add_right hprev _
        _ = 3^K *
              (24*gstDigitS X K +
                gstHandwrittenUChargeS (gstAffineMulCarryS 4 D X K)) := by ring
        _ ≤ 3^K *
              (3 * gstHandwrittenUChargeS
                (gstStepCarryS (gstAffineMulCarryS 4 D X K) (gstDigitS X K))) :=
              Nat.mul_le_mul_left _ hlocal
        _ = 3^(K+1) *
              gstHandwrittenUChargeS (gstAffineMulCarryS 4 D X (K+1)) := by
              rw [hpow, hcarryStep]
              ring

/-- If the seeded output has completely emptied by height K, complete badness
forces an exact global U-energy bound. -/
theorem gst_complete_bad_u_potential_terminal_boundS
    (D X K : Nat) (hD : D < 4)
    (hbad : ∀ j, GSTBadPairS
      (gstAffineMulCarryS 4 D X j) (gstDigitS X j))
    (hempty : D + 4*X < 3^K) :
    24*X + gstHandwrittenUChargeS D ≤ 5*3^K := by
  have hXlt : X < 3^K := by omega
  have hmod : X % 3^K = X := Nat.mod_eq_of_lt hXlt
  have hcarry0 : gstAffineMulCarryS 4 D X K = 0 := by
    unfold gstAffineMulCarryS
    rw [hmod]
    exact Nat.div_eq_of_lt hempty
  have h := gst_bad_prefix_u_potential_boundS D X K hD
    (fun j _ => hbad j)
  rw [hmod, hcarry0] at h
  simpa [gstHandwrittenUChargeS, Nat.mul_comm] using h

/-- Phase-one specialization.  This is the sharp global bad-wave inequality
used by the handwritten Omega/U attack. -/
theorem gst_seed_one_complete_bad_u_boundS
    (X K : Nat)
    (hbad : ∀ j, GSTBadPairS
      (gstAffineMulCarryS 4 1 X j) (gstDigitS X j))
    (hempty : 1 + 4*X < 3^K) :
    24*X + 15 ≤ 5*3^K := by
  simpa [gstHandwrittenUChargeS] using
    gst_complete_bad_u_potential_terminal_boundS 1 X K (by decide) hbad hempty
