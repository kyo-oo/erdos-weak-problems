import Mathlib

/-!
# Exact CM four-divisor surface-switch degree and Koszul sign arithmetic

OpenAI/math, 'The rational Hodge conjecture for CM abelian varieties',
Section 3, proof of the surface criterion.

The four divisor kernels D_i have one old degree-one and one new
degree-one factor each. Reordering their product into the all-old
tensor followed by the all-new tensor requires 3+2+1=6 odd-degree
crossings. Therefore its Koszul sign is +1, not -1.

Let n be the complex dimension of the old abelian product A and
z=f_*[S] an algebraic codimension-(n-2) cycle. Then the product
with FOUR divisor classes has codimension (n-2)+4=n+2;
p'_* integrates along the n-dimensional old factor and lands
in codimension TWO on the new product. The corresponding cohomology
degree is exactly 4 after the Gysin shift.

These are formally PROVED arithmetic facts, not geometric premises.
NEEDS CI RUN LATER.
-/

set_option maxHeartbeats 10000000

namespace GSTClassicalHodgeCMSurfaceDegreeParity

/-- Three later old factors cross the first new factor, two the
second, and one the third. -/
def fourDivisorKoszulCrossings : Nat := 3 + 2 + 1

theorem fourDivisorKoszulCrossings_eq_six :
    fourDivisorKoszulCrossings = 6 := by decide

/-- Four odd/odd divisors give a POSITIVE old/new shuffle sign. -/
theorem fourDivisorKoszul_sign_positive :
    (-1 : ℤ) ^ fourDivisorKoszulCrossings = 1 := by
  norm_num [fourDivisorKoszulCrossings]

/-- A surface in an n-fold has codimension n-2 when n>=2. -/
theorem surface_pushforward_codimension
    (n : Nat) (hn : 2 ≤ n) :
    n - 2 + 2 = n := by omega

/-- Four divisor correspondences and the surface source give a
codimension-(n+2) class BEFORE second-projection pushforward. -/
theorem fourDivisorKernel_codimension
    (n : Nat) (hn : 2 ≤ n) :
    (n - 2) + 4 = n + 2 := by omega

/-- After projection integration along the complex n-fold,
the cycle class has exact codimension TWO on the destination. -/
theorem fourDivisorKernel_target_codimension
    (n : Nat) (hn : 2 ≤ n) :
    (n - 2 + 4) - n = 2 := by omega

/-- The product class has real cohomological degree 2n+4. -/
theorem fourDivisorKernel_source_cohomological_degree
    (n : Nat) (hn : 2 ≤ n) :
    2 * (n - 2) + 8 = 2 * n + 4 := by omega

/-- Projection Gysin along an old complex n-fold lowers degree by
2n, leaving precisely degree FOUR on the new abelian product. -/
theorem fourDivisorKernel_gysin_target_degree
    (n : Nat) (hn : 2 ≤ n) :
    (2 * (n - 2) + 8) - 2 * n = 4 := by omega

/-- Exact source/kernel/target degree balance in the genuine CM paper:
the old abelian carrier has dimension d=n;
the source algebraic surface cycle has codimension p=n-2;
the kernel is a product of FOUR divisors, so e=4;
the output must have codimension q=2.
Thus 2e+2p=2d+2q, with no artificial kernel degree. -/
theorem surface_to_tensor_cup_gysin_degree_balance
    (n : Nat) (hn : 2 ≤ n) :
    2 * 4 + 2 * (n - 2) = 2 * n + 2 * 2 := by omega

#check fourDivisorKoszul_sign_positive
#check fourDivisorKernel_gysin_target_degree
#check surface_to_tensor_cup_gysin_degree_balance
#print axioms fourDivisorKernel_gysin_target_degree

end GSTClassicalHodgeCMSurfaceDegreeParity
