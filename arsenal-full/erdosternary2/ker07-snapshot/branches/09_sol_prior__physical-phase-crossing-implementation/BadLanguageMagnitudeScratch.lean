/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0587 / 1132
/-    Path         : branches/sol_physical-phase-crossing-implementation/BadLanguageMagnitudeScratch.lean
/-    Ref          : origin/sol/physical-phase-crossing-implementation
/-    First-commit : 2026-08-16 11:39:01 +0530  (483d6dd)
/-    Last-commit  : 2026-08-16 16:52:14 +0530  (083724f)
/-    Total commits: 5
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/5] 2026-08-16 11:39:01 +0530  483d6dd  (ker07-dev)
/-        Add GST bad-language magnitude bound scratch
/- [02/5] 2026-08-16 11:51:12 +0530  8ffa873  (ker07-dev)
/-        Fix GST bad-language magnitude scratch proof surface
/- [03/5] 2026-08-16 15:00:28 +0530  3719b27  (ker07-dev)
/-        Fix no22 low-pair normalization before omega
/- [04/5] 2026-08-16 15:08:12 +0530  9b5de7f  (ker07-dev)
/-        Normalize no22 pair index before omega
/- [05/5] 2026-08-16 16:52:14 +0530  083724f  (ker07-dev)
/-        Preserve no-22 normalization fix
/- ====================================================================== -/

import InformationBadTraceScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# GST bad-language magnitude axis

A complete seeded bad GST trace cannot contain the consecutive ternary word
`22`.  This file converts that symbolic exclusion into an exact Archimedean
bound on every finite prefix.  It is deliberately independent of any Erdős
claim or canonical-power forcing theorem.
-/

/-- Ternary words with no consecutive pair `22`. -/
def GSTNo22S (X : Nat) : Prop :=
  ∀ j, ¬ (gstDigitS X j = 2 ∧ gstDigitS X (j+1) = 2)

/-- Complete seeded badness implies the purely symbolic no-`22` language. -/
theorem gst_no22_of_seeded_badS
    (D X : Nat) (hD : D < 4)
    (hbad : ∀ j,
      GSTBadPairS (gstAffineMulCarryS 4 D X j) (gstDigitS X j)) :
    GSTNo22S X := by
  intro j
  exact gst_bad_trace_forbids_22S D X hD hbad j

/-- The no-`22` language is stable under every ternary suffix cut. -/
theorem gst_no22_div_three_powS
    (X q : Nat) (hno : GSTNo22S X) :
    GSTNo22S (X / 3^q) := by
  intro j h22
  apply hno (q+j)
  constructor
  · rw [gst_seeded_affine_digit_shiftS X q j]
    exact h22.1
  · rw [show (q+j)+1 = q+(j+1) by omega,
        gst_seeded_affine_digit_shiftS X q (j+1)]
    exact h22.2

/-- A no-`22` word has low two-trit block at most `21₃ = 7`. -/
theorem gst_no22_low_pair_le_sevenS
    (X : Nat) (hno : GSTNo22S X) :
    X % 9 ≤ 7 := by
  have h0lt : gstDigitS X 0 < 3 := by
    unfold gstDigitS
    exact Nat.mod_lt _ (by decide)
  have h1lt : gstDigitS X 1 < 3 := by
    unfold gstDigitS
    exact Nat.mod_lt _ (by decide)
  have hd0 : gstDigitS X 0 = 0 ∨
      gstDigitS X 0 = 1 ∨ gstDigitS X 0 = 2 := by
    omega
  have hd1 : gstDigitS X 1 = 0 ∨
      gstDigitS X 1 = 1 ∨ gstDigitS X 1 = 2 := by
    omega
  have hpair :
      ¬ (gstDigitS X 0 = 2 ∧ gstDigitS X 1 = 2) := by
    simpa using hno 0
  have hmod : X % 9 = gstDigitS X 0 + 3 * gstDigitS X 1 := by
    calc
      X % 9 = X % (3^1 * 3) := by norm_num
      _ = X % 3^1 + 3^1 * (X / 3^1 % 3) := by
        rw [Nat.mod_mul]
      _ = gstDigitS X 0 + 3 * gstDigitS X 1 := by
        simp [gstDigitS]
  rw [hmod]
  rcases hd0 with h00 | h01 | h02 <;>
    rcases hd1 with h10 | h11 | h12
  all_goals omega

/-- Exact finite magnitude bound for an even number of ternary positions.

If `X < 9^m` and its ternary word contains no consecutive `22`, then

`8 X ≤ 7 (9^m - 1)`.

The extremal word is `21 21 ... 21` (most-significant pair first), whose
normalized limiting value is exactly `7/8` of the ambient ternary interval.
-/
theorem gst_no22_nine_power_boundS
    (X m : Nat)
    (hX : X < 9^m)
    (hno : GSTNo22S X) :
    8 * X ≤ 7 * (9^m - 1) := by
  induction m generalizing X with
  | zero =>
      norm_num at hX ⊢
      omega
  | succ m ih =>
      let Y := X / 9
      have hpow : 9^(m+1) = 9 * 9^m := by
        rw [Nat.pow_succ]
        ac_rfl
      have hYlt : Y < 9^m := by
        have hx' : X < 9 * 9^m := by
          simpa [hpow] using hX
        exact Nat.div_lt_of_lt_mul hx'
      have hYno : GSTNo22S Y := by
        have h := gst_no22_div_three_powS X 2 hno
        simpa [Y] using h
      have hYbound := ih Y hYlt hYno
      have hlow : X % 9 ≤ 7 := gst_no22_low_pair_le_sevenS X hno
      have hdecomp : X = X % 9 + 9 * Y := by
        dsimp [Y]
        exact (Nat.mod_add_div X 9).symm
      have hP : 0 < 9^m := Nat.pow_pos (by decide)
      rw [hpow]
      omega

/-- Direct GST consequence: every finite seed-retaining bad word is trapped
strictly below the top eighth of any containing base-nine block. -/
theorem gst_seeded_bad_nine_power_boundS
    (D X m : Nat)
    (hD : D < 4)
    (hbad : ∀ j,
      GSTBadPairS (gstAffineMulCarryS 4 D X j) (gstDigitS X j))
    (hX : X < 9^m) :
    8 * X ≤ 7 * (9^m - 1) := by
  exact gst_no22_nine_power_boundS X m hX
    (gst_no22_of_seeded_badS D X hD hbad)
