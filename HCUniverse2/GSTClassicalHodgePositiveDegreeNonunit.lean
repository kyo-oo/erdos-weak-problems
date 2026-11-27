import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# GST CLASSICAL HODGE — POSITIVE HOMOGENEOUS ELEMENTS ARE NONUNITS

The projective separator is homogeneous of strictly positive degree.  The
fundamental graded-ring obstruction to invertibility is completely general:
in an N-graded nontrivial ring, the degree-zero projection is a ring
homomorphism, every positive-degree homogeneous element projects to zero, and
a ring homomorphism sends units to units.  Since zero is not a unit, no such
positive-degree homogeneous element can be invertible.

This module isolates that fact once so it can be reused for homogeneous prime
quotients, projective local coordinate rings, and later graded operator
constructions.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open DirectSum

namespace GSTClassicalHodgePositiveDegreeNonunit

variable {A σ : Type*}
variable [CommRing A]
variable [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ℕ → σ)
variable [GradedRing 𝒜]

/-- Positive homogeneous elements have zero degree-zero projection. -/
theorem projZero_eq_zero_of_positive
    {n : Nat} {x : A}
    (hx : x ∈ 𝒜 n)
    (hn : 0 < n) :
    GradedRing.projZeroRingHom 𝒜 x = 0 := by
  change (DirectSum.decompose 𝒜 x 0 : A) = 0
  exact DirectSum.decompose_of_mem_ne 𝒜 hx (Nat.ne_of_gt hn)

/-- **POSITIVE HOMOGENEOUS NONUNIT THEOREM.** -/
theorem not_isUnit_of_mem_positive
    [Nontrivial A]
    {n : Nat} {x : A}
    (hx : x ∈ 𝒜 n)
    (hn : 0 < n) :
    ¬ IsUnit x := by
  intro hunit
  have hmap : IsUnit (GradedRing.projZeroRingHom 𝒜 x) :=
    hunit.map (GradedRing.projZeroRingHom 𝒜)
  rw [projZero_eq_zero_of_positive 𝒜 hx hn] at hmap
  exact not_isUnit_zero hmap

/-- A nonzero positive homogeneous element simultaneously gives a genuine
principal equation and is automatically a nonunit. -/
theorem positive_homogeneous_equation_crown
    [Nontrivial A]
    {n : Nat} {x : A}
    (hx : x ∈ 𝒜 n)
    (hn : 0 < n)
    (hx0 : x ≠ 0) :
    x ≠ 0 ∧ ¬ IsUnit x := by
  exact ⟨hx0, not_isUnit_of_mem_positive 𝒜 hx hn⟩

#check projZero_eq_zero_of_positive
#check not_isUnit_of_mem_positive
#check positive_homogeneous_equation_crown

#print axioms projZero_eq_zero_of_positive
#print axioms not_isUnit_of_mem_positive
#print axioms positive_homogeneous_equation_crown

end GSTClassicalHodgePositiveDegreeNonunit
