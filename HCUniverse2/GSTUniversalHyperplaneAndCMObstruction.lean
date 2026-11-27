import Mathlib

/-!
# Universal projective hyperplane seed and CM dominance boundary

These are NEW unconditional algebraic proof kernels for the two
most important logical steps in the genuine CM+NM route.

1. For any graded cohomology ring, if the top hyperplane power h^d
is nonzero then h^p is nonzero at EVERY 0<=p<=d.
The actual projective-geometric input is STANDARD, NOT a conjecture:
for a smooth projective complex d-fold X with ample hyperplane
class h, the top intersection integral is
  ∫_X h^d = deg(X) > 0.
So standard geometry supplies an actual algebraic codimension-p
nonzero Hodge cycle h^p, universally in X and p. No mysterious
projective mass law or free zeta coefficient is required for this
one genuine source-existence fact.

2. A nonconstant finite covering from an elliptic curve to a
smooth projective curve of genus >= 2 contradicts the actual
Riemann-Hurwitz genus formula. Consequently a universal transfer
claim that a fixed Gaussian CM elliptic power dominates EVERY
projective variety cannot be correct: already dimension-one
hyperbolic projective curves obstruct it.

This module tests only the abstract graded-ring implication and
the exact numerical Riemann-Hurwitz obstruction. Its results are
independent of any GST Hodge surjectivity or assumptions about
preexisting target-cycle representatives.

These facts do not establish the original universal Hodge
conjecture. Arithmetic CM+NM must produce independent algebraic
directions BEYOND the ample-hyperplane subalgebra, through a
geometric comparison that applies to arbitrary X.
-/

set_option maxHeartbeats 20000000

namespace GSTUniversalHyperplaneAndCMObstruction

/-- **Universal nonzero algebraic-source propagation.**
No arbitrary codimension is excluded except those beyond the
finite dimension of the individual variety. The family of
dimensions remains UNBOUNDED across smooth projective X. -/
theorem lower_power_nonzero_of_top_power_nonzero
    {R : Type*} [MonoidWithZero R]
    (h : R) (d p : ℕ) (hp : p ≤ d)
    (htop : h ^ d ≠ 0) :
    h ^ p ≠ 0 := by
  intro hzero
  have hindex : p + (d-p) = d := by omega
  have htopzero : h ^ d = 0 := by
    rw [← hindex, pow_add, hzero, zero_mul]
  exact htop htopzero

/-- All codimensions 0<=p<=d have nonzero hyperplane powers once
the ample top degree is nonzero. This is the actual finite-dimensional
universal seed mechanism, not an existence hypothesis for each p. -/
theorem all_admissible_hyperplane_powers_nonzero
    {R : Type*} [MonoidWithZero R]
    (h : R) (d : ℕ)
    (htop : h ^ d ≠ 0) :
    ∀ p : ℕ, p ≤ d → h ^ p ≠ 0 := by
  intro p hp
  exact lower_power_nonzero_of_top_power_nonzero h d p hp htop

/-- Positive top intersection pairing by a linear functional
implies the hyperplane's top class is nonzero, even when there
are many additional primitive Hodge directions. -/
theorem top_hyperplane_power_nonzero_of_positive_degree
    {R : Type*} [MonoidWithZero R]
    (h : R) (d : ℕ)
    (degree : R → ℚ)
    (hzero : degree 0 = 0)
    (hpos : 0 < degree (h ^ d)) :
    h ^ d ≠ 0 := by
  intro hz
  rw [hz, hzero] at hpos
  exact (not_lt_of_ge le_rfl) hpos

/-- Universal arbitrary-dimensional source from the geometric
top-degree identity: this theorem produces ALL p<=d without a
separately supplied nonzero seed at each p. -/
theorem all_hyperplane_sources_of_top_intersection
    {R : Type*} [MonoidWithZero R]
    (h : R) (d : ℕ)
    (degree : R → ℚ)
    (hzero : degree 0 = 0)
    (hpos : 0 < degree (h ^ d)) :
    ∀ p : ℕ, p ≤ d → h ^ p ≠ 0 := by
  exact all_admissible_hyperplane_powers_nonzero h d
    (top_hyperplane_power_nonzero_of_positive_degree h d degree hzero hpos)

/-- Riemann-Hurwitz for a nonconstant morphism of degree m from
genus-one to genus-g curve: 0=m(2g-2)+ramification.
For target genus>=2, its right side is STRICTLY POSITIVE.
This rules out any such finite CM elliptic-curve cover. -/
theorem no_elliptic_cover_of_hyperbolic_curve
    (g m ramification : ℕ)
    (hg : 2 ≤ g)
    (hm : 0 < m)
    (hRH : 0 = m * (2*g-2) + ramification) :
    False := by
  have hgap : 0 < 2*g-2 := by omega
  have hpositive : 0 < m*(2*g-2) :=
    Nat.mul_pos hm hgap
  omega

/-- A projective genus-two curve is the smallest genus
counterexample to the universal-CM-elliptic-cover shortcut. -/
theorem no_positive_degree_elliptic_cover_of_genus_two
    (m ramification : ℕ)
    (hm : 0 < m)
    (hRH : 0 = m*(2*2-2)+ramification) :
    False :=
  no_elliptic_cover_of_hyperbolic_curve 2 m ramification
    (by omega) hm hRH

#check lower_power_nonzero_of_top_power_nonzero
#check all_hyperplane_sources_of_top_intersection
#check no_elliptic_cover_of_hyperbolic_curve
#print axioms lower_power_nonzero_of_top_power_nonzero
#print axioms all_hyperplane_sources_of_top_intersection
#print axioms no_elliptic_cover_of_hyperbolic_curve

end GSTUniversalHyperplaneAndCMObstruction
