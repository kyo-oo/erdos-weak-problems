import GSTMathboxCorrectedZetaGeometry
import Mathlib

/-!
# Mathbox: exact INFINITE sum of user's corrected Equation (3)

With integer n>=1 and x=y=2, the corrected denominator is
  2^n - 2^(n+1) = -2^n.
Its reciprocal is a convergent geometric sequence, with exact sum -1.
This is a genuine infinite `tsum` theorem over real numbers, not a
finite numerical approximation or an undefined infinite index `n -> R`.

Analytical consequence: for the real factor zeta(2)=pi^2/6 the
scalar expression equals -pi^2/6 (but is not a rational cycle scalar);
for zeta(0)=-1/2 it equals +1/2 (rational as a scalar).

No claim that a zeta value alone creates an algebraic cycle.
-/

set_option maxHeartbeats 20000000

noncomputable section

open scoped BigOperators
open GSTMathboxCorrectedZetaGeometry

namespace GSTMathboxCorrectedZetaInfinite

/-- This is the exact corrected reciprocal for equal bases 2. -/
theorem corrected_term_two (m : ℕ) :
    indexedKernel 2 2 m = -((1/2 : ℝ) ^ (m+1)) := by
  unfold indexedKernel
  rw [equal_base_two_denominator]
  simp [inv_pow, one_div]

/-- The corrected integer-indexed infinite series is summable. -/
theorem corrected_series_two_summable :
    Summable (fun m : ℕ => indexedKernel 2 2 m) := by
  have hgeo : Summable (fun m : ℕ => (1/2 : ℝ) ^ m) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  have htail : Summable (fun m : ℕ => ((1/2 : ℝ) ^ m) * (1/2 : ℝ)) :=
    hgeo.mul_right _
  have hnew : Summable (fun m : ℕ => -((1/2 : ℝ) ^ (m+1))) := by
    simpa only [pow_succ] using htail.neg
  simpa only [corrected_term_two] using hnew

/-- Exact evaluation, under the user's corrected exponent, with n>=1. -/
theorem corrected_series_two_tsum :
    (∑' m : ℕ, indexedKernel 2 2 m) = -1 := by
  have hgeo : (∑' m : ℕ, (1/2 : ℝ) ^ m) = 2 := by
    have h := tsum_geometric_of_abs_lt_one (by norm_num : |(1/2 : ℝ)| < 1)
    norm_num at h ⊢
    exact h
  calc
    (∑' m : ℕ, indexedKernel 2 2 m) =
        ∑' m : ℕ, -(((1/2 : ℝ) ^ m) * (1/2 : ℝ)) := by
      congr 1
      funext m
      rw [corrected_term_two, pow_succ]
    _ = -((∑' m : ℕ, (1/2 : ℝ) ^ m) * (1/2 : ℝ)) := by
      rw [← tsum_mul_right]
      rw [← tsum_neg]
    _ = -1 := by rw [hgeo]; norm_num

/-- The exact infinite geometric sum stays nonzero when weighted by
a nonzero REAL scalar, including any separately justified nonzero
zeta(s) value. Rational cycle descent is a distinct requirement. -/
theorem corrected_infinite_zeta_amplitude
    (zetaAtS : ℝ) (h : zetaAtS ≠ 0) :
    zetaAtS * (∑' m : ℕ, indexedKernel 2 2 m) = -zetaAtS ∧
      zetaAtS * (∑' m : ℕ, indexedKernel 2 2 m) ≠ 0 := by
  rw [corrected_series_two_tsum]
  constructor
  · ring
  · simpa using h

#check summable_geometric_of_abs_lt_one
#check tsum_geometric_of_abs_lt_one
#check tsum_mul_right
#check corrected_term_two
#check corrected_series_two_summable
#check corrected_series_two_tsum
#check corrected_infinite_zeta_amplitude

#print axioms corrected_series_two_tsum
#print axioms corrected_infinite_zeta_amplitude

end GSTMathboxCorrectedZetaInfinite
