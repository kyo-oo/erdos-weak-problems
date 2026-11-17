/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0690 / 1132
/-    Path         : branches/sol_phase-crossing-surgery/GSTPhaseCrossingCarrierScratch.lean
/-    Ref          : origin/sol/phase-crossing-surgery
/-    First-commit : 2026-08-16 23:13:06 +0530  (869395e)
/-    Last-commit  : 2026-08-16 23:16:10 +0530  (264a28f)
/-    Total commits: 3
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/3] 2026-08-16 23:13:06 +0530  869395e  (ker07-dev)
/-        Add exact strip-quotient digit transport lemmas
/- [02/3] 2026-08-16 23:15:28 +0530  f2809e9  (ker07-dev)
/-        Characterize physical SURVIVE in strip carrier coordinates
/- [03/3] 2026-08-16 23:16:10 +0530  264a28f  (ker07-dev)
/-        Fix carrier lemma declaration order and normalize survive proof
/- ====================================================================== -/

import StripConservationScratch
import CarryWordScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Exact horizontal carrier for the phase-crossing surgery

At one fixed ternary row p, let Q_i be the quotient produced by multiplying
only the lower p-digit residue of R by 4^i.  The actual p-th ternary digit of
4^i*R is exactly the initial p-th digit of R plus Q_i modulo 3.

This is the missing exact interpretation of the base-4 carry word.  It does
not assert phase crossing and does not use Omega, a mirror axiom, or a terminal
NULL state.
-/

/-- The wide carry of the physical multiplier 4^i is definitionally the strip
quotient of the lower ternary residue. -/
theorem gst_power_wide_carry_is_strip_quotientS
    (R p i : Nat) :
    gstWideCarryS (4^i) R p =
      gstStripQuotientS (R % 3^p) (3^p) i := by
  rfl

/-- Powers of four are one modulo three. -/
theorem gst_four_pow_mod_threeS (i : Nat) : 4^i % 3 = 1 := by
  induction i with
  | zero => decide
  | succ i ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]
      decide

/-- Exact row transport across i physical power-of-four columns.  The row
cannot be tracked by a pointwise mirror: its phase is the accumulated strip
quotient Q_i modulo three. -/
theorem gst_power_strip_digit_transportS
    (R p i : Nat) :
    gstWideDigitS (4^i * R) p =
      (gstStripQuotientS (R % 3^p) (3^p) i +
        gstWideDigitS R p) % 3 := by
  have hout := gst_wide_output_digit_exactS (4^i) R p
  rw [gst_power_wide_carry_is_strip_quotientS] at hout
  let Q := gstStripQuotientS (R % 3^p) (3^p) i
  let d := gstWideDigitS R p
  have hd : d < 3 := by
    dsimp [d, gstWideDigitS]
    exact Nat.mod_lt _ (by decide)
  have h4 : 4^i % 3 = 1 := gst_four_pow_mod_threeS i
  have hmul : (4^i * d) % 3 = d := by
    rw [Nat.mul_mod, h4, Nat.one_mul]
    exact Nat.mod_eq_of_lt hd
  have hnorm :
      (Q + 4^i * d) % 3 = (Q + d) % 3 := by
    rw [Nat.add_mod, hmul, Nat.add_mod, Nat.mod_eq_of_lt hd]
  simpa [Q, d] using hout.trans hnorm

/-- If the phase-zero row starts with digit two, every later horizontal digit
is controlled solely by the accumulated strip quotient modulo three. -/
theorem gst_power_strip_digit_from_twoS
    (R p i : Nat)
    (h2 : gstWideDigitS R p = 2) :
    gstWideDigitS (4^i * R) p =
      (gstStripQuotientS (R % 3^p) (3^p) i + 2) % 3 := by
  rw [gst_power_strip_digit_transportS, h2]

/-- A zero strip-quotient residue exposes the original digit two at that
physical column. -/
theorem gst_power_strip_digit_two_of_quotient_mod_three_zeroS
    (R p i : Nat)
    (h2 : gstWideDigitS R p = 2)
    (hQ : gstStripQuotientS (R % 3^p) (3^p) i % 3 = 0) :
    gstWideDigitS (4^i * R) p = 2 := by
  rw [gst_power_strip_digit_from_twoS R p i h2]
  rw [Nat.add_mod, hQ]
  decide

/-- At a row whose phase-zero digit is two, a later physical power column has
that same digit two exactly when the accumulated strip quotient vanishes
modulo three. -/
theorem gst_power_strip_digit_two_iff_quotient_mod_three_zeroS
    (R p i : Nat)
    (h2 : gstWideDigitS R p = 2) :
    gstWideDigitS (4^i * R) p = 2 ↔
      gstStripQuotientS (R % 3^p) (3^p) i % 3 = 0 := by
  constructor
  · intro hdigit
    rw [gst_power_strip_digit_from_twoS R p i h2] at hdigit
    let Q := gstStripQuotientS (R % 3^p) (3^p) i
    have hcases : Q % 3 = 0 ∨ Q % 3 = 1 ∨ Q % 3 = 2 := by
      have hlt : Q % 3 < 3 := Nat.mod_lt _ (by decide)
      omega
    rcases hcases with h0 | h1 | h2q
    · exact h0
    · have hbad : (Q + 2) % 3 = 0 := by
        rw [Nat.add_mod, h1]
        decide
      change (Q + 2) % 3 = 2 at hdigit
      omega
    · have hbad : (Q + 2) % 3 = 1 := by
        rw [Nat.add_mod, h2q]
        decide
      change (Q + 2) % 3 = 2 at hdigit
      omega
  · intro hQ
    exact gst_power_strip_digit_two_of_quotient_mod_three_zeroS R p i h2 hQ

/-- One horizontal carry is the next base-4 digit appended to Q_i. -/
theorem gst_power_strip_quotient_stepS
    (R p i : Nat) :
    gstStripQuotientS (R % 3^p) (3^p) (i+1) =
      4 * gstStripQuotientS (R % 3^p) (3^p) i +
        gstStripCarryS (R % 3^p) (3^p) i := by
  exact gst_strip_quotient_succS
    (R % 3^p) (3^p) i (Nat.pow_pos (by decide))

/-- Physical SURVIVE across the two consecutive power columns i and i+1 is
exactly a zero accumulated quotient residue together with a horizontal carry
0 or 3.  Thus the BIG2 packet has an exact base-4 carry-word criterion. -/
theorem gst_power_strip_survive_pair_iffS
    (R p i : Nat)
    (h2 : gstWideDigitS R p = 2) :
    (gstWideDigitS (4^i * R) p = 2 ∧
      gstWideDigitS (4^(i+1) * R) p = 2) ↔
    (gstStripQuotientS (R % 3^p) (3^p) i % 3 = 0 ∧
      (gstStripCarryS (R % 3^p) (3^p) i = 0 ∨
       gstStripCarryS (R % 3^p) (3^p) i = 3)) := by
  let Q := gstStripQuotientS (R % 3^p) (3^p) i
  let C := gstStripCarryS (R % 3^p) (3^p) i
  have hstep :
      gstStripQuotientS (R % 3^p) (3^p) (i+1) = 4*Q + C := by
    simpa [Q, C] using gst_power_strip_quotient_stepS R p i
  have hClt : C < 4 := by
    dsimp [C]
    exact gst_strip_carry_lt_fourS
      (R % 3^p) (3^p) i (Nat.pow_pos (by decide))
  rw [gst_power_strip_digit_two_iff_quotient_mod_three_zeroS R p i h2,
      gst_power_strip_digit_two_iff_quotient_mod_three_zeroS R p (i+1) h2]
  constructor
  · rintro ⟨hQ0, hQnext0⟩
    change Q % 3 = 0 at hQ0
    have hCmod : C % 3 = 0 := by
      rw [hstep, Nat.add_mod, Nat.mul_mod, hQ0] at hQnext0
      norm_num at hQnext0 ⊢
      exact hQnext0
    have hCcases : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
    refine ⟨?_, ?_⟩
    · exact hQ0
    · rcases hCcases with h0 | h1 | h2c | h3
      · exact Or.inl h0
      · rw [h1] at hCmod
        decide at hCmod
      · rw [h2c] at hCmod
        decide at hCmod
      · exact Or.inr h3
  · rintro ⟨hQ0, hC0 | hC3⟩
    · change Q % 3 = 0 at hQ0
      refine ⟨?_, ?_⟩
      · exact hQ0
      · rw [hstep, Nat.add_mod, Nat.mul_mod, hQ0, hC0]
        decide
    · change Q % 3 = 0 at hQ0
      refine ⟨?_, ?_⟩
      · exact hQ0
      · rw [hstep, Nat.add_mod, Nat.mul_mod, hQ0, hC3]
        decide
