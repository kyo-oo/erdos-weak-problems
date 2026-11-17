/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0138 / 1132
/-    Path         : branches/sol_physical-phase-crossing-surgery-plan/FiniteSupportScratch.lean
/-    Ref          : origin/sol/physical-phase-crossing-surgery-plan
/-    First-commit : 2026-08-15 09:48:06 +0530  (8b20ae5)
/-    Last-commit  : 2026-08-15 09:48:06 +0530  (8b20ae5)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-15 09:48:06 +0530  8b20ae5  (ker07-dev)
/-        Formalize natural ternary finite-support cutoff
/- ====================================================================== -/

import Mathlib

/-!
Finite-support side of the corrected GST separation proof.
This file proves only arithmetic facts about natural ternary origins.
It deliberately does NOT assume or assert the missing GST forcing theorem.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- The k-th least-significant ternary origin digit. -/
def ternaryOriginDigitS (n k : Nat) : Nat :=
  n / 3^k % 3

/-- A genuinely infinite ternary-support origin has a nonzero trit beyond every
    finite cutoff.  Ordinary naturals will be proved not to satisfy this. -/
def InfiniteTernarySupportS (n : Nat) : Prop :=
  ∀ K, ∃ k, K ≤ k ∧ ternaryOriginDigitS n k ≠ 0

/-- Elementary growth bound used to give every natural an explicit ternary
    cutoff without logarithms. -/
theorem three_pow_succ_gt_selfS (n : Nat) :
    n < 3^(n+1) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hp : 0 < 3^(n+1) := Nat.pow_pos (by decide)
      have hle : n+1 ≤ 3^(n+1) := by omega
      rw [show (n+1)+1 = (n+1)+1 by rfl, Nat.pow_succ]
      omega

/-- Every ternary origin digit at or above the explicit cutoff n+1 is zero. -/
theorem ternary_origin_eventually_zeroS
    (n k : Nat) (hk : n+1 ≤ k) :
    ternaryOriginDigitS n k = 0 := by
  have hbase : n < 3^(n+1) := three_pow_succ_gt_selfS n
  have hpow : 3^(n+1) ≤ 3^k :=
    Nat.pow_le_pow_of_le (by decide : 1 < 3) hk
  have hlt : n < 3^k := lt_of_lt_of_le hbase hpow
  have hdiv : n / 3^k = 0 := Nat.div_eq_of_lt hlt
  simp [ternaryOriginDigitS, hdiv]

/-- No natural number has genuinely infinite ternary support. -/
theorem natural_not_infinite_ternary_supportS (n : Nat) :
    ¬ InfiniteTernarySupportS n := by
  intro hinf
  obtain ⟨k, hk, hnz⟩ := hinf (n+1)
  exact hnz (ternary_origin_eventually_zeroS n k hk)

/-- Consumer form for the final GST separation: any theorem forcing a nonzero
    origin trit beyond every cutoff is immediately contradictory for Nat. -/
theorem finite_origin_contradictionS
    (n : Nat)
    (hforce : ∀ K, ∃ k, K ≤ k ∧ ternaryOriginDigitS n k ≠ 0) :
    False := by
  exact natural_not_infinite_ternary_supportS n hforce
