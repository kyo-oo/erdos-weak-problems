import GSTMathboxCorrectedZetaSafeDomain

/-!
# GST Number Manipulation (NM): exact corrected-series algebra

A NEW precise, testable *candidate* for the user's proposed NM
(Number Manipulation) method, whose full operator rules were
mentioned but not explicitly defined in the earlier equation page.

The candidate NM law turns a problematic indexed rational kernel
into two explicit rational moments plus an exact controlled
remainder. This is an EQUALITY, not an asymptotic approximation.

For a != 0, a != b:
  1/(a-b) = 1/a + b/a² + b²/(a²(a-b)).

For the user's corrected Equation (3), set
  a = x^(m+1), b = y^(m+2), m>=0.
Then ALL indexed terms have the exact 2nd-order decomposition.

On the non-singular parameter region y>=1, x>y², the theorem
needs no assumed nonzero denominators; these follow from
the already-verified safe-domain geometric-series law.

This arithmetic new theorem neither presumes nor constructs
an algebraic correspondence. The open task is a genuine period
comparison showing a canonical geometric readout equals the
transformed NM expression, with rational descent.
-/

set_option maxHeartbeats 20000000
noncomputable section

open scoped BigOperators
open GSTMathboxCorrectedZetaGeometry
open GSTMathboxCorrectedZetaSafeDomain

namespace GSTNumberManipulation

/-- Exact second-order rational Number Manipulation law with a
nonzero pole certificate, and ZERO truncated-series error. -/
theorem nm_order_two_exact
    (a b : ℝ) (ha : a ≠ 0) (hab : a - b ≠ 0) :
    (a - b)⁻¹ =
      a⁻¹ + b / a ^ 2 + b ^ 2 / (a ^ 2 * (a - b)) := by
  field_simp
  <;> ring

/-- NM's exact corrected index-dependent term decomposition.
Unlike approximating the radical or zeta amplitude, this identity
has an explicit *exact* remainder and does not choose any target
Hodge class or a free coefficient. -/
theorem nm_indexed_kernel_exact
    (x y : ℝ) (m : ℕ)
    (hx : x ≠ 0)
    (hlegal : legalIndex x y m) :
    indexedKernel x y m =
      (x ^ (m+1))⁻¹ +
      y ^ (m+2) / (x ^ (m+1)) ^ 2 +
      (y ^ (m+2)) ^ 2 /
        ((x ^ (m+1)) ^ 2 *
          (x ^ (m+1) - y ^ (m+2))) := by
  exact nm_order_two_exact (x ^ (m+1)) (y ^ (m+2))
    (pow_ne_zero _ hx) hlegal

/-- The corrected safe-domain parameter region makes the whole
NM term expansion *well-defined for every index*, not only
for numerical examples. -/
theorem nm_safe_domain_all_indices
    (x y : ℝ) (hy : 1 ≤ y) (hx : y ^ 2 < x) :
    ∀ m : ℕ,
      indexedKernel x y m =
        (x ^ (m+1))⁻¹ +
        y ^ (m+2) / (x ^ (m+1)) ^ 2 +
        (y ^ (m+2)) ^ 2 /
          ((x ^ (m+1)) ^ 2 *
            (x ^ (m+1) - y ^ (m+2))) := by
  intro m
  have hx0 : x ≠ 0 := by
    have hnonneg : 0 ≤ y ^ 2 := sq_nonneg y
    linarith
  exact nm_indexed_kernel_exact x y m hx0
    (corrected_all_indices_legal x y hy hx m)

/-- All finite corrected Equation (3) sums admit the exact NM
second-order transformation. No limit/summability assumptions occur. -/
theorem nm_exact_finite_sum
    (x y : ℝ) (hy : 1 ≤ y) (hx : y ^ 2 < x)
    (N : ℕ) :
    correctedPartialSum x y N =
      ∑ m ∈ Finset.range N,
        ((x ^ (m+1))⁻¹ +
          y ^ (m+2) / (x ^ (m+1)) ^ 2 +
          (y ^ (m+2)) ^ 2 /
            ((x ^ (m+1)) ^ 2 *
              (x ^ (m+1) - y ^ (m+2)))) := by
  unfold correctedPartialSum
  apply Finset.sum_congr rfl
  intro m hm
  exact nm_safe_domain_all_indices x y hy hx m

#check nm_order_two_exact
#check nm_indexed_kernel_exact
#check nm_safe_domain_all_indices
#check nm_exact_finite_sum

#print axioms nm_order_two_exact
#print axioms nm_safe_domain_all_indices
#print axioms nm_exact_finite_sum

end GSTNumberManipulation
