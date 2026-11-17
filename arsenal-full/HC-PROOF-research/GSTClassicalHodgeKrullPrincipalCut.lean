import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import GSTClassicalHodgePrincipalSectionDescent

/-!
# GST CLASSICAL HODGE — KRULL PRINCIPAL-CUT CODIMENSION ENGINE

A strict one-equation cut must advance codimension by exactly one, not merely
by at least one.  The pinned Mathlib revision contains Krull's principal ideal
theorem in the form needed for this transition.

This module packages the commutative-algebra core independently of any Hodge
semantics.  In a Noetherian domain a nonzero nonunit is a non-zero-divisor,
so its principal ideal has height exactly one.  More generally every minimal
prime over a proper principal ideal has height at most one.

These are the local algebraic facts used by the projective principal-section
recursion to turn strict geometric cuts into exact coheight successors.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open scoped nonZeroDivisors

namespace GSTClassicalHodgeKrullPrincipalCut

/-- A nonzero element of a domain is a non-zero-divisor. -/
theorem nonzero_mem_nonZeroDivisors
    {R : Type*} [CommRing R] [IsDomain R]
    {f : R} (hf : f ≠ 0) :
    f ∈ nonZeroDivisors R := by
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun g hfg => (mul_eq_zero.mp hfg).resolve_left hf,
    fun g hfg => (mul_eq_zero.mp hfg).resolve_right hf⟩

/-- **EXACT PRINCIPAL CODIMENSION.**
In a Noetherian domain every nonzero nonunit principal equation has height one. -/
theorem principal_height_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {f : R} (hf0 : f ≠ 0) (hfunit : ¬ IsUnit f) :
    (Ideal.span {f}).height = 1 := by
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (nonzero_mem_nonZeroDivisors hf0) hfunit

/-- Krull upper bound for an arbitrary proper principal equation in a
Noetherian ring. -/
theorem principal_height_le_one
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {f : R} (hfunit : ¬ IsUnit f) :
    (Ideal.span {f}).height ≤ 1 := by
  exact Ideal.height_span_singleton_le_one hfunit

/-- A minimal prime over a nonzero nonunit principal ideal in a Noetherian
domain therefore lies on an exact codimension-one principal component. -/
theorem minimalPrime_over_principal_height_one
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {f : R} (hf0 : f ≠ 0) (hfunit : ¬ IsUnit f)
    {q : Ideal R} (hq : q ∈ (Ideal.span {f}).minimalPrimes) :
    (Ideal.span {f}).height = 1 ∧
      Ideal.span {f} ≤ q ∧ q.IsPrime := by
  refine ⟨principal_height_eq_one hf0 hfunit, hq.1.2, ?_⟩
  exact hq.1.1

/-- The exact-height result is stable under replacing the equation by an
associate; projective local equations may therefore be normalized by units. -/
theorem principal_height_eq_one_of_associated
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {f g : R} (hfg : Associated f g)
    (hf0 : f ≠ 0) (hfunit : ¬ IsUnit f) :
    (Ideal.span {g}).height = 1 := by
  have hg0 : g ≠ 0 := by
    intro hg
    have : f = 0 := hfg.eq_zero_iff.mpr hg
    exact hf0 this
  have hgunit : ¬ IsUnit g := by
    intro hg
    exact hfunit (hfg.isUnit_iff.mpr hg)
  exact principal_height_eq_one hg0 hgunit

#check nonzero_mem_nonZeroDivisors
#check principal_height_eq_one
#check principal_height_le_one
#check minimalPrime_over_principal_height_one
#check principal_height_eq_one_of_associated

#print axioms nonzero_mem_nonZeroDivisors
#print axioms principal_height_eq_one
#print axioms principal_height_le_one
#print axioms minimalPrime_over_principal_height_one
#print axioms principal_height_eq_one_of_associated

end GSTClassicalHodgeKrullPrincipalCut
