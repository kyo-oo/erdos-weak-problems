/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0192 / 1132
/-    Path         : branches/sol_global-flux-surgery/StripConservationScratch.lean
/-    Ref          : origin/sol/global-flux-surgery
/-    First-commit : 2026-08-15 10:22:43 +0530  (eec9c9c)
/-    Last-commit  : 2026-08-15 11:16:42 +0530  (b283307)
/-    Total commits: 4
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/4] 2026-08-15 10:22:43 +0530  eec9c9c  (ker07-dev)
/-        Formalize generalized GST strip conservation
/- [02/4] 2026-08-15 10:34:08 +0530  d70341e  (ker07-dev)
/-        Fix generalized GST strip quotient and digit proofs
/- [03/4] 2026-08-15 10:34:43 +0530  2921bce  (ker07-dev)
/-        Make GST strip quotient and digit normalization explicit
/- [04/4] 2026-08-15 11:16:42 +0530  b283307  (ker07-dev)
/-        Fix strip conservation modulo normalization
/- ====================================================================== -/

import Mathlib

/-!
Generalized GST strip conservation.
For an arbitrary multiplier B, the entire horizontal block R -> B*R has one
exact ternary carry law.  No canonical-power or Erdős assumption is used.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

def gstWideCarryS (B R p : Nat) : Nat :=
  (B * (R % 3^p)) / 3^p

def gstWideDigitS (R p : Nat) : Nat :=
  R / 3^p % 3

/-- Arbitrary-multiplier carry recurrence. -/
theorem gst_wide_carry_forward_exactS
    (B R p : Nat) :
    gstWideCarryS B R (p+1) =
      (gstWideCarryS B R p + B * gstWideDigitS R p) / 3 := by
  simp only [gstWideCarryS, gstWideDigitS, Nat.pow_succ]
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  have hsplit : R % (3^p * 3) =
      R % 3^p + 3^p * (R / 3^p % 3) := by
    rw [Nat.mod_mul]
  rw [hsplit, Nat.mul_add]
  rw [show B * (3^p * (R / 3^p % 3)) =
      3^p * (B * (R / 3^p % 3)) by ac_rfl]
  rw [← Nat.div_div_eq_div_mul]
  rw [Nat.add_mul_div_left _ _ hp]

/-- Exact quotient decomposition after multiplying R by B. -/
theorem gst_wide_quotient_decompositionS
    (B R p : Nat) :
    (B*R) / 3^p =
      gstWideCarryS B R p + B * (R / 3^p) := by
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  have hdiv : R = 3^p * (R / 3^p) + R % 3^p :=
    (Nat.div_add_mod R (3^p)).symm
  calc
    (B*R) / 3^p =
        (B * (3^p * (R / 3^p) + R % 3^p)) / 3^p := by rw [← hdiv]
    _ = (B * (R % 3^p) + 3^p * (B * (R / 3^p))) / 3^p := by
      congr 1
      rw [Nat.mul_add]
      ac_rfl
    _ = (B * (R % 3^p)) / 3^p + B * (R / 3^p) := by
      rw [Nat.add_mul_div_left _ _ hp]
    _ = gstWideCarryS B R p + B * (R / 3^p) := by rfl

/-- The output ternary digit of B*R depends only on the incoming wide carry
    and the current input digit. -/
theorem gst_wide_output_digit_exactS
    (B R p : Nat) :
    gstWideDigitS (B*R) p =
      (gstWideCarryS B R p + B * gstWideDigitS R p) % 3 := by
  unfold gstWideDigitS
  rw [gst_wide_quotient_decompositionS]
  have hmul :
      (B * (R / 3^p)) % 3 =
        (B * ((R / 3^p) % 3)) % 3 := by
    calc
      (B * (R / 3^p)) % 3 =
          ((B % 3) * ((R / 3^p) % 3)) % 3 :=
            Nat.mul_mod B (R / 3^p) 3
      _ = (B * ((R / 3^p) % 3)) % 3 := by
        simpa only [Nat.mod_mod] using
          (Nat.mul_mod B ((R / 3^p) % 3) 3).symm
  have haddL := Nat.add_mod
      (gstWideCarryS B R p) (B * (R / 3^p)) 3
  have haddR := Nat.add_mod
      (gstWideCarryS B R p) (B * ((R / 3^p) % 3)) 3
  rw [haddL, haddR, hmul]

/-- Exact finite strip conservation at one ternary row. -/
theorem gst_strip_conservation_exactS
    (B R p : Nat) :
    B * gstWideDigitS R p + gstWideCarryS B R p =
      gstWideDigitS (B*R) p +
        3 * gstWideCarryS B R (p+1) := by
  have hcarry := gst_wide_carry_forward_exactS B R p
  have hdigit := gst_wide_output_digit_exactS B R p
  let X := gstWideCarryS B R p + B * gstWideDigitS R p
  have hdivmod : X = X % 3 + 3 * (X / 3) := by
    have h := Nat.mod_add_div X 3
    omega
  dsimp [X] at hdivmod
  rw [← hcarry, ← hdigit] at hdivmod
  omega

/-- Specialization to a horizontal strip of N+1 ordinary ×4 steps. -/
theorem gst_power_four_strip_conservationS
    (N R p : Nat) :
    4^(N+1) * gstWideDigitS R p +
        gstWideCarryS (4^(N+1)) R p =
      gstWideDigitS (4^(N+1) * R) p +
        3 * gstWideCarryS (4^(N+1)) R (p+1) := by
  exact gst_strip_conservation_exactS (4^(N+1)) R p

/-- At a fixed ternary cut, the generalized carry of 4^(N+1) is exactly the
    quotient storing the N+1 ordinary horizontal GST carries. -/
theorem gst_wide_carry_is_carry_wordS
    (N R p : Nat) :
    gstWideCarryS (4^(N+1)) R p =
      (4^(N+1) * (R % 3^p)) / 3^p := by
  rfl
