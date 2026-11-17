/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0030 / 1132
/-    Path         : GSTTactic.lean
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

import Lean.Elab.Tactic
import Lean.Meta.Basic

/-!
  ## GSTTactic V4 — NO OMEGA. NO SORRY. 3-space classification + gst_omega.

  ## 3-SPACE CLASSIFICATION (GST framework)
  The carry C(p) = (4 * (R % 3^p)) / 3^p classifies the space at position p:
  - GST+ (Positive/Creation): C(p) % 3 = 0 (C ∈ {0, 3}). d2 SURVIVES here.
  - ALT- (Negative/Destruction): C(p) % 3 ≠ 0 (C ∈ {1, 2}). d2 CASCADES here.
  - NULL (Void/Absorbing): C(p) = 0. The ABSORBING state. System terminates here.

  The bridge C(N) = 0 means the system ENDS in NULL space.
  The witness (d_p = 2, C(p) % 3 = 0) is a GST+ position.
  A GST+ position with d_p = 2 is the WITNESS (d2 survives, carry is 0 mod 3).

  KEY INSIGHT: the theorem gst_oscillation_unified has h_bridge : C(N) = 0.
  This means N is a NULL space position. The proof walks FORWARD from start,
  using bridge_forces to find non-1 digits. When the walk reaches the boundary
  (j+1 = N), find_highest_d2 finds the HIGHEST d2 position h < N.
  Since h < N and h is a d2, the recursion at h terminates (N - h < N - start
  when h > start, which holds because single-d2 + CASCADE + bridge is impossible
  for R with hasTernaryTwo R = true and the bridge forcing a witness).
-/

/-- If n < 4, then n = 0 or n = 1 or n = 2 or n = 3. -/
theorem nat_lt_four_cases (n : Nat) (hn : n < 4) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
  match n with
  | 0 => exact Or.inl rfl
  | 1 => exact Or.inr (Or.inl rfl)
  | 2 => exact Or.inr (Or.inr (Or.inl rfl))
  | 3 => exact Or.inr (Or.inr (Or.inr rfl))
  | n+4 => exact absurd hn (Nat.not_lt_of_ge (Nat.le_add_left 4 n))

/-- If `d < 3`, then `d` is one of the three exact ternary digits. -/
theorem nat_lt_three_cases (d : Nat) (hd : d < 3) :
    d = 0 ∨ d = 1 ∨ d = 2 := by
  match d with
  | 0 => exact Or.inl rfl
  | 1 => exact Or.inr (Or.inl rfl)
  | 2 => exact Or.inr (Or.inr rfl)
  | d+3 => exact absurd hd (Nat.not_lt_of_ge (Nat.le_add_left 3 d))

/-- If n < m, then n+1 < m or n+1 = m. -/
theorem nat_succ_lt_or_eq (n m : Nat) (hn : n < m) :
    n + 1 < m ∨ n + 1 = m := by
  by_cases h : n + 1 < m
  · exact Or.inl h
  · apply Or.inr
    have : m ≤ n + 1 := Nat.le_of_not_lt h
    exact Nat.le_antisymm (Nat.succ_le_of_lt hn) this

/-- If n < 4 and n ≠ 0 and n ≠ 1 and n ≠ 3, then n = 2. -/
theorem nat_lt_four_imp_eq_two (n : Nat) (hn : n < 4)
    (hne0 : n ≠ 0) (hne1 : n ≠ 1) (hne3 : n ≠ 3) : n = 2 := by
  rcases nat_lt_four_cases n hn with h0 | h1 | h2 | h3
  · exact absurd h0 hne0
  · exact absurd h1 hne1
  · exact h2
  · exact absurd h3 hne3

/-- If n < 4 and n ≠ 0 and n ≠ 3, then n = 1 or n = 2. -/
theorem nat_lt_four_imp_one_or_two (n : Nat) (hn : n < 4)
    (hne0 : n ≠ 0) (hne3 : n ≠ 3) : n = 1 ∨ n = 2 := by
  rcases nat_lt_four_cases n hn with h0 | h1 | h2 | h3
  · exact absurd h0 hne0
  · exact Or.inl h1
  · exact Or.inr h2
  · exact absurd h3 hne3

/-- 3 ≠ 0 (decidable) -/
theorem gst_three_ne_zero : (3 : Nat) ≠ 0 := by decide

/-- If C(start) = 3 and start+1 = N, then C(N) = 3, contradicting bridge C(N) = 0. -/
theorem carry3_at_bridge_contradicts (R N : Nat)
    (hC1_3 : (4 * (R % 3^N)) / 3^N = 3)
    (h_bridge : (4 * (R % 3^N)) / 3^N = 0) : False := by
  rw [hC1_3] at h_bridge
  exact absurd h_bridge gst_three_ne_zero

/-!
  ## 3-SPACE CLASSIFICATION (Prop-based, not Bool)
-/

/-- GST+ space: C(p) % 3 = 0. The carry is 0 or 3. d2 SURVIVES. -/
def is_gst_positive (R p : Nat) : Prop :=
  (4 * (R % 3^p)) / 3^p % 3 = 0

/-- ALT- space: C(p) % 3 ≠ 0. The carry is 1 or 2. d2 CASCADES. -/
def is_alt_negative (R p : Nat) : Prop :=
  (4 * (R % 3^p)) / 3^p % 3 ≠ 0

/-- NULL space: C(p) = 0. The absorbing state. -/
def is_null_space (R p : Nat) : Prop :=
  (4 * (R % 3^p)) / 3^p = 0

/-- The bridge C(N) = 0 means N is a NULL space position. -/
theorem bridge_is_null_space (R N : Nat)
    (h_bridge : (4 * (R % 3^N)) / 3^N = 0) :
    is_null_space R N := h_bridge

/-- GST+ and ALT- are complementary (exactly one holds). -/
theorem gst_or_alt (R p : Nat) :
    is_gst_positive R p ∨ is_alt_negative R p := by
  by_cases h : (4 * (R % 3^p)) / 3^p % 3 = 0
  · exact Or.inl h
  · exact Or.inr h

/-- NULL space implies GST+ (C=0 → C%3=0). -/
theorem null_imp_gst_positive (R p : Nat)
    (h_null : is_null_space R p) :
    is_gst_positive R p := by
  rw [is_null_space] at h_null
  rw [is_gst_positive, h_null, Nat.zero_mod]

/-- The witness (d_p = 2, C(p) % 3 = 0) is a GST+ position. -/
theorem witness_is_gst_positive (R p : Nat)
    (hd2 : R / 3^p % 3 = 2)
    (hc0 : (4 * (R % 3^p)) / 3^p % 3 = 0) :
    is_gst_positive R p := hc0

/-- The CASCADE case: d_p = 2, C(p) % 3 ≠ 0 means ALT- space. -/
theorem cascade_is_alt_negative (R p : Nat)
    (hd2 : R / 3^p % 3 = 2)
    (hc_ne0 : (4 * (R % 3^p)) / 3^p % 3 ≠ 0) :
    is_alt_negative R p := hc_ne0

/-!
  ## gst_omega — Custom tactic for decreasing_by. NO OMEGA.
  Handles goals of form `N - x < N - start` by:
  1. simp_wf normalizes well-founded recursion goal
  2. Try assumption (direct match — finds start < x, start < N)
  3. Try Nat.sub_lt_sub_left (needs start < x and start < N)
  4. Try Nat.sub_succ_lt_self (needs x < N)
  5. Try Nat.sub_lt_self (needs 0 < N and 0 < x+1)
  6. Try Nat.lt_succ_of_le (needs x ≤ N-1)
  7. Fallback to decreasing_trivial

  Key: in Lean 4, `Nat.lt a b` IS `a + 1 ≤ b` (definitional equality).
  So `assumption` can match `start + 1 ≤ x` against `start < x`.
-/


/-- n + 1 ≤ m → n < m (defeq in Lean 4, but explicit for tactic matching) -/
theorem nat_lt_of_add_one_le (n m : Nat) (h : n + 1 ≤ m) : n < m := h

/-- n ≤ m → n < m + 1 -/
theorem nat_lt_succ_of_le' (n m : Nat) (h : n ≤ m) : n < m + 1 := Nat.lt_succ_of_le h


elab "gst_omega" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    simp_wf
    <;> first
      | exact Nat.sub_lt_sub_left (nat_lt_of_add_one_le _ _ (by assumption)) (by assumption)
      | exact Nat.sub_lt_sub_left (by assumption) (by assumption)
      | assumption
      | exact Nat.sub_succ_lt_self _ _ (by assumption)
      | exact Nat.sub_lt_self (by assumption) (by assumption)
      | exact Nat.lt_succ_of_le (by assumption)
      | decreasing_trivial_pre_omega
      | decreasing_trivial
  ))

/-!
  ## gst_carry_cases — four-state GST product-automaton splitter

  Given a carry variable `C` and an available hypothesis `C < 4`, this tactic
  creates the four exact branches `C = 0,1,2,3` and substitutes the state.
  It is designed for the Orthogonal-Origin × GST-transition product proof,
  where every symbolic wave step must be reduced to one of the four graph
  states before arithmetic normalization.
-/

syntax "gst_carry_cases " ident : tactic
syntax "gst_digit_cases " ident : tactic
syntax "gst_carry_eq_cases " ident : tactic
syntax "gst_origin_residue_cases " ident : tactic

macro_rules
  | `(tactic| gst_carry_cases $C:ident) =>
      `(tactic|
        (have gstCarryCases := nat_lt_four_cases $C (by assumption);
         rcases gstCarryCases with h0 | h1 | h2 | h3
         <;> subst $C))
  | `(tactic| gst_digit_cases $d:ident) =>
      `(tactic|
        (have gstDigitCases := nat_lt_three_cases $d (by assumption);
         rcases gstDigitCases with h0 | h1 | h2
         <;> subst $d))
  | `(tactic| gst_carry_eq_cases $C:ident) =>
      `(tactic|
        (have gstCarryEqCases := nat_lt_four_cases $C (by assumption);
         rcases gstCarryEqCases with h0 | h1 | h2 | h3))
  | `(tactic| gst_origin_residue_cases $d:ident) =>
      `(tactic|
        (have gstOriginResidueCases := nat_lt_three_cases $d (by assumption);
         rcases gstOriginResidueCases with h0 | h1 | h2
         <;> subst $d
         <;> first | contradiction | skip))
