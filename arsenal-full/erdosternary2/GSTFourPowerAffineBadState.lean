import GSTFourPowerDirectExistence
import GSTFourPowerAffineExponentPeel

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineBadState

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineExponentPeel

/-- Common ternary digit two at one coordinate of an arbitrary pair. -/
def PairCommonTwo (x y : Nat) : Prop :=
  ∃ j : Nat, digit3 x j = 2 ∧ digit3 y j = 2

/-- The direct power predicate is exactly the affine-orbit pair predicate. -/
theorem commonTwo_iff_affineCommonTwo (K : Nat) :
    CommonTwo K ↔ AffineCommonTwo K := by
  simpa [CommonTwo] using power_common_two_iff_affine K

/-- A direct counterexample is equivalently an affine-orbit counterexample. -/
theorem noCommonTwo_iff_noAffineCommonTwo (K : Nat) :
    (¬ CommonTwo K) ↔ (¬ AffineCommonTwo K) := by
  exact not_congr (commonTwo_iff_affineCommonTwo K)

/-- Lowest exponent trit `0`: after discarding the non-common low pair `(0,1)`,
    the entire remaining problem is the exact tail pair `(peel0, peel1)`. -/
theorem affineCommonTwo_three_mul_iff (q : Nat) :
    AffineCommonTwo (3*q) ↔
      PairCommonTwo (peel0 (affineOrbit q)) (peel1 (affineOrbit q)) := by
  constructor
  · rintro ⟨j, hj0, hj1⟩
    cases j with
    | zero =>
        have h0 := affineOrbit_low_trit_zero q
        rw [h0] at hj0
        omega
    | succ j =>
        refine ⟨j, ?_, ?_⟩
        · have h := digit_peel_zero q j
          rw [hj0] at h
          exact h.symm
        · have h := digit_peel_one q j
          rw [hj1] at h
          exact h.symm
  · rintro ⟨j, hj0, hj1⟩
    refine ⟨j+1, ?_, ?_⟩
    · rw [digit_peel_zero q j]
      exact hj0
    · rw [digit_peel_one q j]
      exact hj1

/-- Lowest exponent trit `1`: after discarding the non-common low pair `(1,2)`,
    the remaining problem is the consecutive affine tail pair `(peel1, peel2)`. -/
theorem affineCommonTwo_three_mul_add_one_iff (q : Nat) :
    AffineCommonTwo (3*q + 1) ↔
      PairCommonTwo (peel1 (affineOrbit q)) (peel2 (affineOrbit q)) := by
  constructor
  · rintro ⟨j, hj0, hj1⟩
    cases j with
    | zero =>
        have h0 := affineOrbit_low_trit_one q
        rw [h0] at hj0
        omega
    | succ j =>
        refine ⟨j, ?_, ?_⟩
        · have h := digit_peel_one q j
          rw [hj0] at h
          exact h.symm
        · have h := digit_peel_two q j
          rw [hj1] at h
          exact h.symm
  · rintro ⟨j, hj0, hj1⟩
    refine ⟨j+1, ?_, ?_⟩
    · rw [digit_peel_one q j]
      exact hj0
    · rw [digit_peel_two q j]
      exact hj1

/-- The tail appearing after the exponent trit `2` is literally the `+3`
    affine channel of the first tail. -/
theorem peel_zero_next_eq_state3 (q : Nat) :
    peel0 (affineOrbit (q+1)) = 4 * peel2 (affineOrbit q) + 3 := by
  rw [affineOrbit_succ]
  exact peel0_affine_succ (affineOrbit q)

/-- Lowest exponent trit `2`: the low pair is `(2,0)`, hence never common;
    after removing it the full problem enters the exact `x ↦ 4x+3` channel. -/
theorem affineCommonTwo_three_mul_add_two_iff (q : Nat) :
    AffineCommonTwo (3*q + 2) ↔
      PairCommonTwo (peel2 (affineOrbit q))
        (4 * peel2 (affineOrbit q) + 3) := by
  have htail := peel_zero_next_eq_state3 q
  constructor
  · rintro ⟨j, hj0, hj1⟩
    cases j with
    | zero =>
        have hnext : 3*q + 2 + 1 = 3*(q+1) := by omega
        rw [hnext] at hj1
        have h0 := affineOrbit_low_trit_zero (q+1)
        rw [h0] at hj1
        omega
    | succ j =>
        refine ⟨j, ?_, ?_⟩
        · have h := digit_peel_two q j
          rw [hj0] at h
          exact h.symm
        · have hnext : 3*q + 2 + 1 = 3*(q+1) := by omega
          rw [hnext] at hj1
          have h := digit_peel_zero (q+1) j
          rw [hj1] at h
          rw [htail] at h
          exact h.symm
  · rintro ⟨j, hj0, hj1⟩
    refine ⟨j+1, ?_, ?_⟩
    · rw [digit_peel_two q j]
      exact hj0
    · have hnext : 3*q + 2 + 1 = 3*(q+1) := by omega
      rw [hnext, digit_peel_zero (q+1) j, htail]
      exact hj1

#check commonTwo_iff_affineCommonTwo
#check noCommonTwo_iff_noAffineCommonTwo
#check affineCommonTwo_three_mul_iff
#check affineCommonTwo_three_mul_add_one_iff
#check affineCommonTwo_three_mul_add_two_iff
#print axioms affineCommonTwo_three_mul_iff
#print axioms affineCommonTwo_three_mul_add_one_iff
#print axioms affineCommonTwo_three_mul_add_two_iff

end GSTFourPowerAffineBadState
