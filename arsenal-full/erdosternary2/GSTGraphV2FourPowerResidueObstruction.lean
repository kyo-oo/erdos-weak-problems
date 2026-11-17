import GSTGraphV2FourPowerRelocation

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2FourPowerResidueObstruction

open GSTCanonicalSevenAxisBridge
open GSTGraphV2InfiniteControl
open GSTGraphV2HandwrittenExponentialLTE
open GSTU2DEventTransport

/-- A ternary digit at row `p` is determined by the residue modulo `3^(p+1)`. -/
theorem digit3_eq_of_mod_next
    (R S p : Nat)
    (hmod : R % 3^(p+1) = S % 3^(p+1)) :
    digit3 R p = digit3 S p := by
  unfold digit3
  have hpow : 3^(p+1) = 3^p * 3 := by
    rw [Nat.pow_succ]
  have hfull : R % (3^p * 3) = S % (3^p * 3) := by
    simpa [hpow] using hmod
  have hR : R % (3^p * 3) =
      R % 3^p + 3^p * (R / 3^p % 3) := by
    rw [Nat.mod_mul]
  have hS : S % (3^p * 3) =
      S % 3^p + 3^p * (S / 3^p % 3) := by
    rw [Nat.mod_mul]
  have hdvd : 3^p ∣ 3^(p+1) := Nat.pow_dvd_pow 3 (by omega)
  have hRlow := Nat.mod_mod_of_dvd R hdvd
  have hSlow := Nat.mod_mod_of_dvd S hdvd
  have hlow : R % 3^p = S % 3^p := by
    calc
      R % 3^p = (R % 3^(p+1)) % 3^p := hRlow.symm
      _ = (S % 3^(p+1)) % 3^p := by rw [hmod]
      _ = S % 3^p := hSlow
  rw [hR, hS, hlow] at hfull
  have hmul : 3^p * (R / 3^p % 3) =
      3^p * (S / 3^p % 3) := by omega
  exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 3^p) hmul

/-- The row-`p` ternary digit of `4^K` is periodic in the exponent with
period `3^p`.  The proof is the exact handwritten LTE congruence. -/
theorem pow4_digit_period
    (p K u : Nat) :
    digit3 (4^(K + 3^p*u)) p = digit3 (4^K) p := by
  apply digit3_eq_of_mod_next
  rw [Nat.pow_add, Nat.mul_mod]
  rw [pow4_scaled_mod_next p u]
  simp

/-- At row two, exponent residues five and six modulo nine force a common
ternary digit `2` in two consecutive powers. -/
theorem row_two_overlap_of_mod9_five_or_six
    (L : Nat) (hres : L % 9 = 5 ∨ L % 9 = 6) :
    digit3 (4^L) 2 = 2 ∧ digit3 (4^(L+1)) 2 = 2 := by
  rcases hres with h5 | h6
  · have hs := Nat.mod_add_div L 9
    rw [h5] at hs
    have hshape : L = 5 + 9 * (L / 9) := by
      simpa [Nat.add_comm, Nat.mul_comm] using hs.symm
    have hshape1 : L+1 = 6 + 9 * (L / 9) := by omega
    constructor
    · rw [hshape]
      calc
        digit3 (4 ^ (5 + 9 * (L / 9))) 2 = digit3 (4^5) 2 :=
          pow4_digit_period 2 5 (L/9)
        _ = 2 := by norm_num [digit3]
    · rw [hshape1]
      calc
        digit3 (4 ^ (6 + 9 * (L / 9))) 2 = digit3 (4^6) 2 :=
          pow4_digit_period 2 6 (L/9)
        _ = 2 := by norm_num [digit3]
  · have hs := Nat.mod_add_div L 9
    rw [h6] at hs
    have hshape : L = 6 + 9 * (L / 9) := by
      simpa [Nat.add_comm, Nat.mul_comm] using hs.symm
    have hshape1 : L+1 = 7 + 9 * (L / 9) := by omega
    constructor
    · rw [hshape]
      calc
        digit3 (4 ^ (6 + 9 * (L / 9))) 2 = digit3 (4^6) 2 :=
          pow4_digit_period 2 6 (L/9)
        _ = 2 := by norm_num [digit3]
    · rw [hshape1]
      calc
        digit3 (4 ^ (7 + 9 * (L / 9))) 2 = digit3 (4^7) 2 :=
          pow4_digit_period 2 7 (L/9)
        _ = 2 := by norm_num [digit3]

/-- Exact row-two residue classification.  A shared row-two digit `2` occurs
exactly in exponent classes five and six modulo nine. -/
theorem row_two_overlap_iff_mod9_five_or_six
    (L : Nat) :
    (digit3 (4^L) 2 = 2 ∧ digit3 (4^(L+1)) 2 = 2) ↔
      (L % 9 = 5 ∨ L % 9 = 6) := by
  constructor
  · intro hov
    let r := L % 9
    have hr : r < 9 := by
      dsimp [r]
      exact Nat.mod_lt _ (by norm_num)
    have hs := Nat.mod_add_div L 9
    have hshape : L = r + 9 * (L / 9) := by
      dsimp [r]
      omega
    have hshape1 : L + 1 = (r + 1) + 9 * (L / 9) := by
      omega
    have h0 : digit3 (4^r) 2 = 2 := by
      have h := hov.1
      rw [hshape] at h
      have hperiod := pow4_digit_period 2 r (L / 9)
      norm_num at hperiod
      rw [hperiod] at h
      exact h
    have h1 : digit3 (4^(r+1)) 2 = 2 := by
      have h := hov.2
      rw [hshape1] at h
      have hperiod := pow4_digit_period 2 (r+1) (L / 9)
      norm_num at hperiod
      rw [hperiod] at h
      exact h
    have hres : r = 5 ∨ r = 6 := by
      interval_cases r <;> norm_num [digit3] at *
    simpa [r] using hres
  · exact row_two_overlap_of_mod9_five_or_six L

/-- Pure-arithmetic consequence of global common-two failure: a counterexample
cannot lie in either exact row-two overlap class.  This is deliberately stated
without any source Happy witness or relocation hypothesis. -/
theorem no_common_two_forbids_mod9_five_six
    (K : Nat)
    (hNo : ¬ ∃ p : Nat, 1 ≤ p ∧
      digit3 (4^K) p = 2 ∧ digit3 (4^(K+1)) p = 2) :
    K % 9 ≠ 5 ∧ K % 9 ≠ 6 := by
  constructor
  · intro h5
    apply hNo
    refine ⟨2, by norm_num, ?_⟩
    exact row_two_overlap_of_mod9_five_or_six K (Or.inl h5)
  · intro h6
    apply hNo
    refine ⟨2, by norm_num, ?_⟩
    exact row_two_overlap_of_mod9_five_or_six K (Or.inr h6)

/-- Therefore global absence of a relocated Happy cell on sheet `K+1`
forbids the exponent residues five and six modulo nine. -/
theorem no_relocated_happy_forbids_mod9_five_six
    (K : Nat)
    (hNo : ¬ ∃ q : Nat, 1 ≤ q ∧
      HappyCell (graph 1 (K+1) q).seven.carry
        (graph 1 (K+1) q).seven.digit) :
    (K+1) % 9 ≠ 5 ∧ (K+1) % 9 ≠ 6 := by
  constructor
  · intro h5
    apply hNo
    refine ⟨2, by norm_num, ?_⟩
    have hov := row_two_overlap_of_mod9_five_or_six (K+1) (Or.inl h5)
    exact (GSTGraphV2FourPowerRelocation.graph_happy_iff_consecutive_digit_two
      1 (K+1) 2).2 (by
        simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hov)
  · intro h6
    apply hNo
    refine ⟨2, by norm_num, ?_⟩
    have hov := row_two_overlap_of_mod9_five_or_six (K+1) (Or.inr h6)
    exact (GSTGraphV2FourPowerRelocation.graph_happy_iff_consecutive_digit_two
      1 (K+1) 2).2 (by
        simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hov)

#check digit3_eq_of_mod_next
#check pow4_digit_period
#check row_two_overlap_of_mod9_five_or_six
#check row_two_overlap_iff_mod9_five_or_six
#check no_common_two_forbids_mod9_five_six
#check no_relocated_happy_forbids_mod9_five_six
#print axioms digit3_eq_of_mod_next
#print axioms pow4_digit_period
#print axioms row_two_overlap_of_mod9_five_or_six
#print axioms row_two_overlap_iff_mod9_five_or_six
#print axioms no_common_two_forbids_mod9_five_six
#print axioms no_relocated_happy_forbids_mod9_five_six

end GSTGraphV2FourPowerResidueObstruction
