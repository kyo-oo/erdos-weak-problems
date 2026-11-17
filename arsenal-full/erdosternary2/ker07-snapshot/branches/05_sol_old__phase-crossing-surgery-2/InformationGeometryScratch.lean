/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0150 / 1132
/-    Path         : branches/sol_phase-crossing-surgery-2/InformationGeometryScratch.lean
/-    Ref          : origin/sol/phase-crossing-surgery-2
/-    First-commit : 2026-08-15 09:56:22 +0530  (311824f)
/-    Last-commit  : 2026-08-15 10:08:10 +0530  (ece839f)
/-    Total commits: 3
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/3] 2026-08-15 09:56:22 +0530  311824f  (ker07-dev)
/-        Formalize shared GST information coordinates
/- [02/3] 2026-08-15 09:59:24 +0530  edd5277  (ker07-dev)
/-        Formalize aligned 6-power GST information boundary
/- [03/3] 2026-08-15 10:08:10 +0530  ece839f  (ker07-dev)
/-        Fix shared information bound and gate endpoint proofs
/- ====================================================================== -/

import Mathlib

/-!
Pure arithmetic geometry of the shared GST information integer.
No Erdős theorem and no global wave assumption is used here.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- Read the low base-4 coordinate of an exact decomposition S = p + 4 Z. -/
theorem gst_information_low_coordinatesS
    (S p Z : Nat) (hp : p < 4) (hS : S = p + 4*Z) :
    S % 4 = p ∧ S / 4 = Z := by
  subst S
  constructor
  · rw [Nat.add_mod]
    simp [Nat.mod_eq_of_lt hp]
  · have h4 : 0 < (4:Nat) := by decide
    rw [Nat.add_mul_div_left p Z h4]
    have hpdiv : p / 4 = 0 := Nat.div_eq_of_lt hp
    simp [hpdiv]

/-- Read the high A-coordinate of an exact decomposition S = W + A C. -/
theorem gst_information_high_coordinatesS
    (S W A C : Nat) (hA : 0 < A) (hW : W < A)
    (hS : S = W + A*C) :
    S % A = W ∧ S / A = C := by
  subst S
  constructor
  · rw [Nat.add_mod]
    simp [Nat.mod_eq_of_lt hW]
  · rw [Nat.add_mul_div_left W C hA]
    have hWdiv : W / A = 0 := Nat.div_eq_of_lt hW
    simp [hWdiv]

/-- Quaternary coordinate at depth i inside one shared information word. -/
def gstInformationCarryAtS (S i : Nat) : Nat :=
  S / 4^i % 4

/-- When A=4^N, the two GST decompositions are literally the bottom and top
    base-4 coordinates of one finite information word. -/
theorem gst_information_bottom_top_coordinatesS
    (S p Z W A C N : Nat)
    (hA : A = 4^N)
    (hp : p < 4) (hC : C < 4)
    (hW : W < A)
    (hLow : S = p + 4*Z)
    (hHigh : S = W + A*C) :
    gstInformationCarryAtS S 0 = p ∧
      gstInformationCarryAtS S N = C := by
  have hlow := gst_information_low_coordinatesS S p Z hp hLow
  have hApos : 0 < A := by
    rw [hA]
    exact Nat.pow_pos (by decide)
  have hhigh := gst_information_high_coordinatesS S W A C hApos hW hHigh
  constructor
  · simpa [gstInformationCarryAtS] using hlow.1
  · rw [gstInformationCarryAtS, ← hA]
    rw [hhigh.2]
    exact Nat.mod_eq_of_lt hC

/-- The shared information word has exactly one more possible base-4 digit
    than the multiplier A=4^N. -/
theorem gst_information_word_boundS
    (S W A C : Nat)
    (hW : W < A) (hC : C < 4)
    (hHigh : S = W + A*C) :
    S < 4*A := by
  rw [hHigh]
  have h1 : W + A*C < A + A*C := Nat.add_lt_add_right hW (A*C)
  have h2 : A + A*C = A*(C+1) := by
    rw [Nat.mul_add, Nat.mul_one]
    ac_rfl
  have hC1 : C+1 ≤ 4 := by omega
  have h3 : A*(C+1) ≤ A*4 := Nat.mul_le_mul_left A hC1
  rw [h2] at h1
  have h4 : A*4 = 4*A := by ac_rfl
  rw [h4] at h3
  exact lt_of_lt_of_le h1 h3

/-- Endpoint form used at a child Happy Gate: NULL means the top quaternary
    coordinate is 0; GST+ carry-three means it is 3. -/
theorem gst_information_gate_endpointS
    (S W A C N : Nat)
    (hA : A = 4^N)
    (hC : C = 0 ∨ C = 3)
    (hW : W < A)
    (hHigh : S = W + A*C) :
    gstInformationCarryAtS S N = 0 ∨
      gstInformationCarryAtS S N = 3 := by
  have hApos : 0 < A := by
    rw [hA]
    exact Nat.pow_pos (by decide)
  have hhigh := gst_information_high_coordinatesS S W A C hApos hW hHigh
  rw [gstInformationCarryAtS, ← hA, hhigh.2]
  rcases hC with h0 | h3
  · left
    simp [h0]
  · right
    simp [h3]

/-- Exact 2-adic/3-adic scale inequality behind the GST bridge.  For N≥3,
    an (N+1)-digit base-4 information word fits strictly below ternary depth
    2N. -/
theorem four_pow_succ_lt_three_pow_doubleS
    (N : Nat) (hN : 3 ≤ N) :
    4^(N+1) < 3^(2*N) := by
  induction N with
  | zero => omega
  | succ N ih =>
      by_cases hprev : 3 ≤ N
      · have hprevBound := ih hprev
        have h3pos : 0 < 3^(2*N) := Nat.pow_pos (by decide)
        calc
          4^((N+1)+1) = 4 * 4^(N+1) := by
            rw [Nat.pow_succ]
            ac_rfl
          _ < 4 * 3^(2*N) :=
            Nat.mul_lt_mul_of_pos_left hprevBound (by decide)
          _ < 9 * 3^(2*N) :=
            Nat.mul_lt_mul_of_pos_right (by decide : 4 < 9) h3pos
          _ = 3^(2*(N+1)) := by
            rw [show 2*(N+1) = 2*N + 2 by omega, Nat.pow_add]
            norm_num
            ac_rfl
      · have hN2 : N = 2 := by omega
        subst N
        decide

/-- The finite shared information word lies below the aligned ternary bridge. -/
theorem gst_information_bridge_boundS
    (S A N : Nat)
    (hN : 3 ≤ N)
    (hA : A = 4^N)
    (hS : S < 4*A) :
    S < 3^(2*N) := by
  have h4 : 4*A = 4^(N+1) := by
    rw [hA, Nat.pow_succ]
    ac_rfl
  rw [h4] at hS
  exact lt_trans hS (four_pow_succ_lt_three_pow_doubleS N hN)

/-- At the aligned bridge depth, the stored information word has zero quotient.
    This is a finite NULL boundary of the information carrier; it is not a
    claim that the global GST wave terminates. -/
theorem gst_information_bridge_nullS
    (S A N : Nat)
    (hN : 3 ≤ N)
    (hA : A = 4^N)
    (hS : S < 4*A) :
    S / 3^(2*N) = 0 := by
  exact Nat.div_eq_of_lt (gst_information_bridge_boundS S A N hN hA hS)
