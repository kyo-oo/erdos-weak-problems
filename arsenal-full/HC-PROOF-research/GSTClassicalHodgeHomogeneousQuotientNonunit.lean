import GSTClassicalHodgePositiveDegreeNonunit
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Lattice

/-!
# GST CLASSICAL HODGE — POSITIVE HOMOGENEOUS NONUNITS IN HOMOGENEOUS QUOTIENTS

A quotient grading is not required to prove that a positive homogeneous
separator remains a nonunit modulo a proper homogeneous ideal.

Suppose a positive homogeneous element `f` became a unit modulo a homogeneous
ideal `P`.  Then for some `g`, `f*g - 1 ∈ P`.  The degree-zero projection is a
ring homomorphism.  Since `f` has positive degree, its degree-zero projection is
zero, hence the degree-zero projection of `f*g - 1` is `-1`.  Homogeneity of
`P` forces that projection back into `P`, contradicting properness.

This is exactly the algebraic argument required for the projective-separator
quotient at a Proj point.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open DirectSum

namespace GSTClassicalHodgeHomogeneousQuotientNonunit

variable {A σ : Type*}
variable [CommRing A]
variable [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ℕ → σ)
variable [GradedRing 𝒜]

/-- Multiplication by a positive homogeneous element has zero degree-zero
projection. -/
theorem projZero_mul_eq_zero_of_positive
    {n : Nat} {f g : A}
    (hf : f ∈ 𝒜 n) (hn : 0 < n) :
    GradedRing.projZeroRingHom 𝒜 (f * g) = 0 := by
  rw [map_mul]
  rw [GSTClassicalHodgePositiveDegreeNonunit.projZero_eq_zero_of_positive
    𝒜 hf hn]
  simp

/-- Therefore the degree-zero projection of `f*g - 1` is `-1`. -/
theorem projZero_mul_sub_one_of_positive
    {n : Nat} {f g : A}
    (hf : f ∈ 𝒜 n) (hn : 0 < n) :
    GradedRing.projZeroRingHom 𝒜 (f * g - 1) = -1 := by
  rw [map_sub, projZero_mul_eq_zero_of_positive 𝒜 hf hn, map_one]
  simp

/-- **HOMOGENEOUS QUOTIENT NONUNIT THEOREM.**
A positive homogeneous element cannot become invertible modulo a proper
homogeneous ideal. -/
theorem quotient_mk_not_isUnit_of_positive
    (P : HomogeneousIdeal 𝒜)
    (hP : P.toIdeal ≠ ⊤)
    {n : Nat} {f : A}
    (hf : f ∈ 𝒜 n) (hn : 0 < n) :
    ¬ IsUnit (Ideal.Quotient.mk P.toIdeal f) := by
  intro hunit
  obtain ⟨u, hu⟩ := hunit
  let uinv : (A ⧸ P.toIdeal)ˣ := u⁻¹
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (I := P.toIdeal)
    (uinv : A ⧸ P.toIdeal)
  have hmulq :
      Ideal.Quotient.mk P.toIdeal (f * g) = 1 := by
    rw [map_mul, hg]
    rw [← hu]
    exact u.mul_inv
  have hmem : f * g - 1 ∈ P.toIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [map_sub, hmulq, map_one, sub_self]
  have hproj_mem :
      GradedRing.projZeroRingHom 𝒜 (f * g - 1) ∈ P.toIdeal :=
    (Ideal.IsHomogeneous.mem_iff 𝒜 P.isHomogeneous
      (x := f * g - 1)).mp hmem 0
  have hneg_one : (-1 : A) ∈ P.toIdeal := by
    simpa [projZero_mul_sub_one_of_positive 𝒜 hf hn] using hproj_mem
  have hone : (1 : A) ∈ P.toIdeal := by
    simpa using P.toIdeal.neg_mem hneg_one
  exact hP ((Ideal.eq_top_iff_one (I := P.toIdeal)).mpr hone)

/-- Prime homogeneous ideals are automatically proper, so the theorem applies
directly to homogeneous prime quotients. -/
theorem quotient_mk_not_isUnit_of_positive_prime
    (P : HomogeneousIdeal 𝒜)
    [P.toIdeal.IsPrime]
    {n : Nat} {f : A}
    (hf : f ∈ 𝒜 n) (hn : 0 < n) :
    ¬ IsUnit (Ideal.Quotient.mk P.toIdeal f) := by
  exact quotient_mk_not_isUnit_of_positive 𝒜 P
    (Ideal.IsPrime.ne_top ‹P.toIdeal.IsPrime›) hf hn

#check projZero_mul_eq_zero_of_positive
#check projZero_mul_sub_one_of_positive
#check quotient_mk_not_isUnit_of_positive
#check quotient_mk_not_isUnit_of_positive_prime

#print axioms projZero_mul_eq_zero_of_positive
#print axioms projZero_mul_sub_one_of_positive
#print axioms quotient_mk_not_isUnit_of_positive
#print axioms quotient_mk_not_isUnit_of_positive_prime

end GSTClassicalHodgeHomogeneousQuotientNonunit
