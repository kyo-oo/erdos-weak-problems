/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1073 / 1132
/-    Path         : branches/sol_5c579-final-bigN-right-chord-atomic/GSTEventWordValueScratch.lean
/-    Ref          : origin/sol/5c579-final-bigN-right-chord-atomic
/-    First-commit : 2026-08-17 22:06:13 +0530  (deea9a0)
/-    Last-commit  : 2026-08-17 22:06:13 +0530  (deea9a0)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 22:06:13 +0530  deea9a0  (ker07-dev)
/-        surgery: lock 5c579 with full BIG-N right-chord research monolith
/- ====================================================================== -/

import InformationStateScratch
import OmegaSpacetimeScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Exact global value of the GST event word

At each ternary position encode the input/output digit pair as

    J_i = d_i + 3*e_i.

For a seeded multiply-by-four wave `X -> seed + 4X`, the complete finite event
word has exact value `13X + 3*seed`.
-/

/-- Ordinary ternary prefix reconstruction. -/
theorem gst_digit_prefix_valueS (X K : Nat) :
    (∑ i in Finset.range K, 3^i * gstDigitS X i) = X % 3^K := by
  induction K with
  | zero => simp [gstDigitS]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep : X % 3^(K+1) = X % 3^K + 3^K * gstDigitS X K := by
        unfold gstDigitS
        rw [Nat.pow_succ, Nat.mod_mul]
      exact hstep.symm

/-- Every natural word is reconstructed by the explicit ceiling X+1. -/
theorem gst_digit_total_valueS (X : Nat) :
    (∑ i in Finset.range (X+1), 3^i * gstDigitS X i) = X := by
  rw [gst_digit_prefix_valueS]
  have hlt : X < 3^(X+1) := gst_three_pow_succ_gt_pressureS X
  rw [Nat.mod_eq_of_lt hlt]

/-- Event symbol of one seeded x4 GST position. -/
def gstEventSymbolValueS (seed X i : Nat) : Nat :=
  gstDigitS X i + 3 * gstDigitS (seed + 4*X) i

/-- A common natural ceiling large enough for both X and seed+4X when
`seed<4`. -/
def gstEventNaturalCeilingS (seed X : Nat) : Nat := seed + 4*X + 1

/-- The complete seeded event word is exactly `X + 3(seed+4X)`. -/
theorem gst_event_word_value_exactS
    (seed X : Nat) (hseed : seed < 4) :
    (∑ i in Finset.range (gstEventNaturalCeilingS seed X),
      3^i * gstEventSymbolValueS seed X i) =
      13*X + 3*seed := by
  unfold gstEventNaturalCeilingS gstEventSymbolValueS
  rw [Finset.sum_add_distrib]
  have hXlt : X < 3^(seed + 4*X + 1) := by
    have hbase : X < 3^(X+1) := gst_three_pow_succ_gt_pressureS X
    have hidx : X+1 ≤ seed + 4*X + 1 := by omega
    have hp : 3^(X+1) ≤ 3^(seed + 4*X + 1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) hidx
    omega
  have hOlt : seed + 4*X < 3^(seed + 4*X + 1) :=
    gst_three_pow_succ_gt_pressureS (seed + 4*X)
  have hin :
      (∑ i in Finset.range (seed + 4*X + 1),
        3^i * gstDigitS X i) = X := by
    rw [gst_digit_prefix_valueS, Nat.mod_eq_of_lt hXlt]
  have hout :
      (∑ i in Finset.range (seed + 4*X + 1),
        3^i * gstDigitS (seed + 4*X) i) = seed + 4*X := by
    rw [gst_digit_prefix_valueS, Nat.mod_eq_of_lt hOlt]
  rw [hin]
  have hfactor :
      (∑ i in Finset.range (seed + 4*X + 1),
        3^i * (3 * gstDigitS (seed + 4*X) i)) =
      3 * (∑ i in Finset.range (seed + 4*X + 1),
        3^i * gstDigitS (seed + 4*X) i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hfactor, hout]
  ring

/-- Unseeded physical GST event world: exact factor 13. -/
theorem gst_event_word_unseeded_factor_thirteenS (X : Nat) :
    (∑ i in Finset.range (4*X + 1),
      3^i * gstEventSymbolValueS 0 X i) = 13*X := by
  simpa [gstEventNaturalCeilingS] using
    gst_event_word_value_exactS 0 X (by decide)

/-- Prefix-one seed-one event world: factor 13 plus the exact boundary 3. -/
theorem gst_event_word_seed_one_factor_thirteenS (X : Nat) :
    (∑ i in Finset.range (4*X + 2),
      3^i * gstEventSymbolValueS 1 X i) = 13*X + 3 := by
  simpa [gstEventNaturalCeilingS] using
    gst_event_word_value_exactS 1 X (by decide)
