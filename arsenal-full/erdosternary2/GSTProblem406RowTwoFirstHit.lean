import GSTFourPowerDirectResidue
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST exact first row-two collision along the physical four-power orbit

This is a source-specific first-hit theorem, not an all-row global gate.
Using the existing exact period 3^2 = 9 of physical ternary row 2,
it determines the LEAST shift j >= 0 for which the original neighbors
4^(K+j) and 4^(K+j+1) have a shared ternary digit two at row 2.

The exact table for K mod 9 = 0,...,8 is
    5,4,3,2,1,0,0,7,6.

In particular, a first row-two hit occurs by shift six if and only if
K mod 9 != 7. The distinguished residue seven needs exactly seven
shifts AT THIS ROW; this does not assert that earlier hits at higher
rows do not exist. All results are binder-free and axiom-free.
-/

namespace GSTProblem406RowTwoFirstHit

open GSTFourPowerDirectResidue

def RowTwoGate (K : Nat) : Prop :=
  digit3 (4^K) 2 = 2 ∧ digit3 (4^(K+1)) 2 = 2

/-- The exact least forward shift to a simultaneous-two at ternary row 2. -/
def firstRowTwoShift : Nat → Nat
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 0
  | 7 => 7
  | 8 => 6
  | _ => 7

/-- Finite base-nine GST first-hit automaton; every earlier shift is checked. -/
private theorem finite_first_row_two :
    ∀ r : Fin 9,
      firstRowTwoShift r.val ≤ 7 ∧
      RowTwoGate (r.val + firstRowTwoShift r.val) ∧
      (∀ i : Fin 8, i.val < firstRowTwoShift r.val →
        ¬ RowTwoGate (r.val + i.val)) := by
  intro r
  fin_cases r <;>
    (constructor
     · decide
     constructor
     · apply (row_two_overlap_iff_mod9_five_or_six _).2
       decide
     · intro i hi hgate
       have hres :=
         (row_two_overlap_iff_mod9_five_or_six _).1 hgate
       fin_cases i <;> norm_num [firstRowTwoShift] at *)

private theorem finite_only_seven_has_shift_seven :
    ∀ r : Fin 9,
      (firstRowTwoShift r.val = 7 ↔ r.val = 7) := by
  decide

/-- GST physical row-two periodicity is exact for both neighbors,
not an inference from sampled exponents. -/
theorem rowTwoGate_exponent_period (K j : Nat) :
    RowTwoGate (K+j) ↔ RowTwoGate ((K%9)+j) := by
  have hsplit : K%9 + 9*(K/9) = K := Nat.mod_add_div K 9
  have he : K+j = ((K%9)+j) + 9*(K/9) := by omega
  have he1 : (K+j)+1 = (((K%9)+j)+1) + 9*(K/9) := by omega
  have h0 :
      digit3 (4^(K+j)) 2 = digit3 (4^((K%9)+j)) 2 := by
    rw [he]
    simpa [show (3:Nat)^2 = 9 by decide] using
      (pow4_digit_period 2 ((K%9)+j) (K/9))
  have h1 :
      digit3 (4^((K+j)+1)) 2 =
      digit3 (4^(((K%9)+j)+1)) 2 := by
    rw [he1]
    simpa [show (3:Nat)^2 = 9 by decide] using
      (pow4_digit_period 2 (((K%9)+j)+1) (K/9))
  unfold RowTwoGate
  rw [h0, h1]

/-- Exact minimum forward row-two witness for EVERY natural K. -/
theorem physical_first_row_two_gate_exact (K : Nat) :
    firstRowTwoShift (K%9) ≤ 7 ∧
    RowTwoGate (K + firstRowTwoShift (K%9)) ∧
    (∀ i : Nat, i < firstRowTwoShift (K%9) →
      ¬ RowTwoGate (K+i)) := by
  let r : Fin 9 := ⟨K%9, Nat.mod_lt K (by decide)⟩
  obtain ⟨hj,hgate,hfirst⟩ := finite_first_row_two r
  dsimp [r] at hj hgate hfirst
  refine ⟨hj, (rowTwoGate_exponent_period K _).2 hgate, ?_⟩
  intro i hi
  have hi8 : i < 8 := by omega
  intro hbad
  exact (hfirst ⟨i,hi8⟩ hi)
    ((rowTwoGate_exponent_period K i).1 hbad)

/-- A precise six-shift GST dichotomy: only the K=7 mod 9 column
can fail to exhibit a row-two gate in shifts 0,...,6. -/
theorem physical_six_shift_row_two_iff (K : Nat) :
    (∃ j : Nat, j ≤ 6 ∧ RowTwoGate (K+j)) ↔ K%9 ≠ 7 := by
  constructor
  · rintro ⟨j,hj,hgate⟩ h7
    have hs : firstRowTwoShift (K%9) = 7 := by
      simp [h7, firstRowTwoShift]
    have hfirst := (physical_first_row_two_gate_exact K).2.2
    exact (hfirst j (by omega)) hgate
  · intro hneq
    obtain ⟨hj,hgate,_⟩ := physical_first_row_two_gate_exact K
    have hnot7 : firstRowTwoShift (K%9) ≠ 7 := by
      intro hseven
      have hres := (finite_only_seven_has_shift_seven
        ⟨K%9, Nat.mod_lt K (by decide)⟩).mp hseven
      exact hneq hres
    exact ⟨firstRowTwoShift (K%9), by omega, hgate⟩

/-- At the exceptional low-row residue, shift seven is sharp at
row two. It does NOT exclude earlier collisions at other heights. -/
theorem physical_seven_shift_row_two_sharp
    (K : Nat) (h7 : K%9=7) :
    (∀ j : Nat, j ≤ 6 → ¬ RowTwoGate (K+j)) ∧
    RowTwoGate (K+7) := by
  have hs : firstRowTwoShift (K%9) = 7 := by
    simp [h7, firstRowTwoShift]
  obtain ⟨_,hgate,hfirst⟩ := physical_first_row_two_gate_exact K
  constructor
  · intro j hj
    exact hfirst j (by omega)
  · simpa [hs] using hgate

#print axioms rowTwoGate_exponent_period
#print axioms physical_first_row_two_gate_exact
#print axioms physical_six_shift_row_two_iff
#print axioms physical_seven_shift_row_two_sharp

end GSTProblem406RowTwoFirstHit
