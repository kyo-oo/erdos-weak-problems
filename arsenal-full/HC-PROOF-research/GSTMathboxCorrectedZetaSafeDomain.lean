import GSTMathboxCorrectedZetaGeometry
import Mathlib

/-!
# GST corrected Equation (3): a general safe positive parameter regime

The corrected original denominator is x^n - y^(n+1), n>=1.
No change of kernel. We prove a NON-TOY infinite family of
parameter inputs for which every actual reciprocal is legally defined
and positive: 1<=y and x>y^2. This removes any hypothesis that an
individual denominator or a finite sum is nonzero: both are DERIVED.

The corrected full infinite sum also converges under these
conditions by factorization and geometric comparison, explained
in docs/MATHBOX_CORRECTED_ZETA_GEOMETRIC_ROUTE_20261014.md.
This file establishes the exact domain/finite-cutoff Lean theorems.
-/

set_option maxHeartbeats 20000000

noncomputable section

open scoped BigOperators
open GSTMathboxCorrectedZetaGeometry

namespace GSTMathboxCorrectedZetaSafeDomain

/-- Main exact denominator positivity in the genuine corrected
indexed family. It is derived inductively from x>y² and y>=1. -/
theorem correctedDenominator_pos
    (x y : ℝ)
    (hy : 1 ≤ y)
    (hx : y ^ 2 < x)
    (n : ℕ) :
    0 < indexedDenominator x y n := by
  have hy0 : 0 ≤ y := by linarith
  have hy2 : y ≤ y ^ 2 := by
    nlinarith [sq_nonneg (y - 1)]
  have hxy : y < x := lt_of_le_of_lt hy2 hx
  have hx0 : 0 < x := by linarith
  induction n with
  | zero =>
    norm_num [indexedDenominator] at *
    linarith
  | succ n ih =>
    have hprev : y ^ (n + 2) < x ^ (n + 1) := by
      exact sub_pos.mp ih
    have hfirst : y ^ (n + 2) * y ≤ y ^ (n + 2) * x :=
      mul_le_mul_of_nonneg_left (le_of_lt hxy) (pow_nonneg hy0 _)
    have hsecond : y ^ (n + 2) * x < x ^ (n + 1) * x :=
      mul_lt_mul_of_pos_right hprev hx0
    have hproduct : y ^ (n + 2) * y < x ^ (n + 1) * x :=
      lt_of_le_of_lt hfirst hsecond
    change 0 < x ^ (Nat.succ n + 1) - y ^ (Nat.succ n + 2)
    have ex : Nat.succ n + 1 = (n + 1) + 1 := by omega
    have ey : Nat.succ n + 2 = (n + 2) + 1 := by omega
    rw [ex, ey, pow_succ, pow_succ]
    exact sub_pos.mpr hproduct

/-- Every member of the infinite index family has a genuine nonzero
denominator, excluding the 4,2 pole found elsewhere. -/
theorem corrected_all_indices_legal
    (x y : ℝ) (hy : 1 ≤ y) (hx : y ^ 2 < x) :
    ∀ n : ℕ, legalIndex x y n := by
  intro n
  exact ne_of_gt (correctedDenominator_pos x y hy hx n)

/-- Exact genuine reciprocal positivity, with no nonzero assumption on
the denominator. -/
theorem correctedKernel_pos
    (x y : ℝ)
    (hy : 1 ≤ y)
    (hx : y ^ 2 < x)
    (n : ℕ) :
    0 < indexedKernel x y n := by
  unfold indexedKernel
  exact inv_pos.mpr (correctedDenominator_pos x y hy hx n)

/-- Every nonempty finite cutoff in the new unrestricted-parameter
family has a STRICTLY POSITIVE scalar sum. -/
theorem correctedPartialSum_pos
    (x y : ℝ)
    (hy : 1 ≤ y)
    (hx : y ^ 2 < x)
    (N : ℕ)
    (hN : 0 < N) :
    0 < correctedPartialSum x y N := by
  cases N with
  | zero => omega
  | succ N =>
    unfold correctedPartialSum
    rw [Finset.sum_range_succ]
    have hs : 0 ≤ ∑ n ∈ Finset.range N, indexedKernel x y n :=
      Finset.sum_nonneg (fun n _ => le_of_lt (correctedKernel_pos x y hy hx n))
    exact add_pos_of_nonneg_of_pos hs (correctedKernel_pos x y hy hx N)

/-- Nonvanishing of the full corrected finite zeta amplitude holds in
the open family x>y², without a chosen numeric x=y=2 example. -/
theorem correctedZetaPartial_nonzero_safe_domain
    (zetaAtS x y : ℝ)
    (hy : 1 ≤ y)
    (hx : y ^ 2 < x)
    (hZeta : zetaAtS ≠ 0)
    (N : ℕ) (hN : 0 < N) :
    correctedZetaPartial zetaAtS x y N ≠ 0 := by
  unfold correctedZetaPartial
  exact mul_ne_zero hZeta (ne_of_gt (correctedPartialSum_pos x y hy hx N hN))

#check correctedDenominator_pos
#check corrected_all_indices_legal
#check correctedKernel_pos
#check correctedPartialSum_pos
#check correctedZetaPartial_nonzero_safe_domain

#print axioms correctedDenominator_pos
#print axioms correctedZetaPartial_nonzero_safe_domain

end GSTMathboxCorrectedZetaSafeDomain
