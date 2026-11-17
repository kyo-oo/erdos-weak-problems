/- ======================================================================
/- CHRONOLOGICAL LABEL — #0047 / 1133
/-    Path         : workbench/SolOmegaOccurrence.lean
/-    Ref          : main
/-    First-commit : 2026-08-14 21:44:31 +0530
/-    Last-commit  : 2026-08-14 21:44:31 +0530
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-14 21:44:31 +0530  83dd56f  (ker07-dev)
/- ====================================================================== -/

/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0047 / 1132
/-    Path         : workbench/SolOmegaOccurrence.lean
/-    Ref          : main
/-    First-commit : 2026-08-14 21:44:31 +0530  (83dd56f)
/-    Last-commit  : 2026-08-14 21:44:31 +0530  (83dd56f)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-14 21:44:31 +0530  83dd56f  (ker07-dev)
/-        Import Sol inline surgery handoff and GST graph workspace
/- ====================================================================== -/

import SolOmegaAK

/-- Exact affine tail in the prefix-one (`k = 1`) Ω orbit. -/
def gstPrefixOneTail (s n : Nat) : Nat :=
  c s / 3 + 4^(3^s) * gstNavigationConstant (s+1) n

/-- The prefix-one Ω parent output digit is literally the digit of the seeded
    mirror `1 + 4*X`, where `X` is the exact affine tail. -/
theorem gst_prefix_one_parent_output_is_seeded_mirror_digit
    (s n j : Nat) (hs : 1 ≤ s) :
    gstOmegaParentOutputDigit (gstOmega s 1 n j) =
      gstDigit (1 + 4 * gstPrefixOneTail s n) j := by
  have hc3 : c s % 3 = 1 := c_mod3 s hs
  have hseed : (4 * (c s % 3)) / 3 = 1 := by
    norm_num [hc3]
  have haff := gst_affine_mul_digit_exact 4 1 (gstPrefixOneTail s n) j
  simpa [gstOmegaParentOutputDigit, gstOmega, gstPrefixOneTail,
    Nat.pow_one, hseed, gstOutputDigit] using haff.symm

/-- A prefix-one SURVIVE occurrence is exactly a shared digit-two occurrence
    between the affine tail and its seeded mirror `1 + 4*X`. -/
theorem gst_prefix_one_survive_iff_shared_seeded_two
    (s n j : Nat) (hs : 1 ≤ s) :
    gstOmegaEvent s 1 n j = .survive ↔
      gstDigit (gstPrefixOneTail s n) j = 2 ∧
      gstDigit (1 + 4 * gstPrefixOneTail s n) j = 2 := by
  unfold gstOmegaEvent
  rw [gst_omega_event_survive_iff_raw]
  constructor
  · rintro ⟨hd, hout⟩
    constructor
    · simpa [gstOmega, gstPrefixOneTail] using hd
    · rw [← gst_prefix_one_parent_output_is_seeded_mirror_digit s n j hs]
      exact hout
  · rintro ⟨hd, hmirror⟩
    constructor
    · simpa [gstOmega, gstPrefixOneTail] using hd
    · rw [gst_prefix_one_parent_output_is_seeded_mirror_digit s n j hs]
      exact hmirror

/-- Every natural number lies strictly below the next ternary power indexed by
    itself.  This is the finite-natural ceiling used against an unbounded Ω
    continuation chain; it is not a finite search bound. -/
theorem gst_nat_lt_three_pow_succ (T : Nat) :
    T < 3^(T+1) := by
  induction T with
  | zero => decide
  | succ T ih =>
      rw [show T + 1 + 1 = (T + 1) + 1 by omega, Nat.pow_succ]
      have hp : 0 < 3^(T+1) := Nat.pow_pos (by decide)
      omega

/-- Every ternary digit of a natural `T` at or above position `T+1` is zero. -/
theorem gstDigit_eq_zero_above_nat_ceiling
    (T j : Nat) (hj : T + 1 ≤ j) :
    gstDigit T j = 0 := by
  have hbase : T < 3^(T+1) := gst_nat_lt_three_pow_succ T
  have hpow : 3^(T+1) ≤ 3^j :=
    Nat.pow_le_pow_of_le (by decide : 1 < 3) hj
  have hlt : T < 3^j := by omega
  unfold gstDigit
  rw [Nat.div_eq_of_lt hlt]

/-- Hence no child Happy Gate can occur at or above the finite-natural ceiling
    of the exact child Navigation Constant. -/
theorem gst_prefix_one_no_child_gate_above_ceiling
    (s n j : Nat)
    (hj : gstNavigationConstant (s+1) n + 1 ≤ j) :
    ¬ ((gstOmega s 1 n j).childDigit = 2 ∧
       ((gstOmega s 1 n j).childCarry = 0 ∨
        (gstOmega s 1 n j).childCarry = 3)) := by
  intro hgate
  have hd0 : gstDigit (gstNavigationConstant (s+1) n) j = 0 :=
    gstDigit_eq_zero_above_nat_ceiling _ _ hj
  have hd2 : gstDigit (gstNavigationConstant (s+1) n) j = 2 := by
    simpa only [gstOmega, Nat.add_assoc] using hgate.1
  omega

/-- Any child gate therefore lies strictly below the natural ceiling. -/
theorem gst_prefix_one_child_gate_below_ceiling
    (s n j : Nat)
    (hgate :
      (gstOmega s 1 n j).childDigit = 2 ∧
      ((gstOmega s 1 n j).childCarry = 0 ∨
       (gstOmega s 1 n j).childCarry = 3)) :
    j < gstNavigationConstant (s+1) n + 1 := by
  by_contra hnot
  have hj : gstNavigationConstant (s+1) n + 1 ≤ j := by omega
  exact gst_prefix_one_no_child_gate_above_ceiling s n j hj hgate
