import GSTClassicalHodgeKrullPrincipalCut
import GSTClassicalHodgeProjectivePrincipalSection
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Polynomial.Basic

/-!
# GST CLASSICAL HODGE — PROJECTIVE SEPARATOR KRULL DICHOTOMY

The relevance-selected homogeneous separator at a point `x : Proj` lies
outside the homogeneous prime of `x`.  Passing to the quotient by that prime
therefore produces a nonzero element of a Noetherian domain.

Krull's principal ideal theorem then gives an unconditional dichotomy:

* if the surviving separator is a unit in the quotient, the local principal
  zero locus disappears at that component;
* otherwise its principal ideal has height exactly one.

This is the local algebraic bridge between the generator-specific projective
separator and an exact codimension-one step.  No Hodge data occurs here.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTClassicalHodgeProjectivePrincipalSection
open GSTClassicalHodgeKrullPrincipalCut

namespace GSTClassicalHodgeProjectiveSeparatorKrull

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Quotient of the projective coordinate ring by the homogeneous prime of a
Proj point.  The homogeneous prime is converted to a genuine ideal through
`HomogeneousIdeal.toIdeal`, which is the coercion under which Mathlib's
quotient-ring API (membership, domain, Noetherianity) is available. -/
abbrev pointQuotient
    (n : Nat) (x : projectiveSpace n) :=
  ProjectiveCoordinateRing n ⧸ x.asHomogeneousIdeal.toIdeal

/-- Image of the canonical positive homogeneous separator in the point-prime
quotient. -/
noncomputable def separatorClass
    (n : Nat) (x : projectiveSpace n) : pointQuotient n x :=
  Ideal.Quotient.mk x.asHomogeneousIdeal.toIdeal
    (positiveHomogeneousSeparator n x).equation

/-- The separator survives nontrivially after quotienting by the point prime. -/
theorem separatorClass_ne_zero
    (n : Nat) (x : projectiveSpace n) :
    separatorClass n x ≠ 0 := by
  intro h
  have hmem :
      (positiveHomogeneousSeparator n x).equation ∈ x.asHomogeneousIdeal := by
    exact HomogeneousIdeal.mem_iff.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp h)
  exact (positiveHomogeneousSeparator n x).not_mem_prime hmem

/-- The point-prime quotient is a domain: the point prime is a genuine prime
ideal, and quotients of prime ideals are domains. -/
noncomputable def pointQuotientIsDomain
    (n : Nat) (x : projectiveSpace n) :
    IsDomain (pointQuotient n x) := by
  haveI : (x.asHomogeneousIdeal.toIdeal).IsPrime := x.isPrime
  infer_instance

/-- The point-prime quotient is Noetherian: the polynomial coordinate ring is
Noetherian (Hilbert basis theorem for finitely many variables over a field),
and quotients of Noetherian rings are Noetherian. -/
noncomputable def pointQuotientIsNoetherian
    (n : Nat) (x : projectiveSpace n) :
    IsNoetherianRing (pointQuotient n x) := by
  infer_instance

/-- **PROJECTIVE KRULL DICHOTOMY.**  At every projective source point the
surviving positive homogeneous separator is either a unit in the prime
quotient, or its principal ideal has exact height one. -/
theorem separator_unit_or_height_one
    (n : Nat) (x : projectiveSpace n) :
    IsUnit (separatorClass n x) ∨
      (Ideal.span ({separatorClass n x} : Set (pointQuotient n x))).height = 1 := by
  letI : IsDomain (pointQuotient n x) := pointQuotientIsDomain n x
  letI : IsNoetherianRing (pointQuotient n x) := pointQuotientIsNoetherian n x
  by_cases hu : IsUnit (separatorClass n x)
  · exact Or.inl hu
  · exact Or.inr
      (principal_height_eq_one (separatorClass_ne_zero n x) hu)

/-- Nonunit branch extracted explicitly for downstream principal-section
components. -/
theorem separator_height_one_of_nonunit
    (n : Nat) (x : projectiveSpace n)
    (hu : ¬ IsUnit (separatorClass n x)) :
    (Ideal.span ({separatorClass n x} : Set (pointQuotient n x))).height = 1 := by
  letI : IsDomain (pointQuotient n x) := pointQuotientIsDomain n x
  letI : IsNoetherianRing (pointQuotient n x) := pointQuotientIsNoetherian n x
  exact principal_height_eq_one (separatorClass_ne_zero n x) hu

/-- Every minimal prime over the nonunit separator component is a genuine prime
above an exact height-one principal ideal. -/
theorem separator_minimalPrime_height_one
    (n : Nat) (x : projectiveSpace n)
    (hu : ¬ IsUnit (separatorClass n x))
    {q : Ideal (pointQuotient n x)}
    (hq : q ∈ (Ideal.span ({separatorClass n x} : Set (pointQuotient n x))).minimalPrimes) :
    (Ideal.span ({separatorClass n x} : Set (pointQuotient n x))).height = 1
      ∧ Ideal.span ({separatorClass n x} : Set (pointQuotient n x)) ≤ q
      ∧ q.IsPrime := by
  letI : IsDomain (pointQuotient n x) := pointQuotientIsDomain n x
  letI : IsNoetherianRing (pointQuotient n x) := pointQuotientIsNoetherian n x
  exact minimalPrime_over_principal_height_one
    (separatorClass_ne_zero n x) hu hq

#check pointQuotient
#check separatorClass
#check separatorClass_ne_zero
#check separator_unit_or_height_one
#check separator_height_one_of_nonunit
#check separator_minimalPrime_height_one

#print axioms separatorClass_ne_zero
#print axioms separator_unit_or_height_one
#print axioms separator_height_one_of_nonunit
#print axioms separator_minimalPrime_height_one

end GSTClassicalHodgeProjectiveSeparatorKrull
