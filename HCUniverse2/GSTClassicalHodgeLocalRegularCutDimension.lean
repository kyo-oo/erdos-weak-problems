import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# GST CLASSICAL HODGE — LOCAL REGULAR PRINCIPAL-CUT DIMENSION

The recursive projective cut is controlled locally at a generic component by
one equation in a Noetherian local ring.  The pinned Mathlib regular-sequence
Krull-dimension theorem states that quotienting by one regular element in the
maximal ideal lowers ring dimension by exactly one.

This module isolates that exact one-step dimension law for later use on scheme
stalks.  It is pure commutative algebra: no Hodge data and no cycle-class map.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open Ideal RingTheory IsLocalRing

namespace GSTClassicalHodgeLocalRegularCutDimension

/-- Exact local dimension drop by one regular equation. -/
theorem ringKrullDim_quotient_regular_succ
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {f : R}
    (hreg : IsSMulRegular R f)
    (hf : f ∈ maximalIdeal R) :
    ringKrullDim (R ⧸ Ideal.span {f}) + 1 = ringKrullDim R := by
  exact ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hreg hf

/-- In a local domain every nonzero element is regular on the ring itself. -/
theorem regular_of_nonzero_domain
    {R : Type*} [CommRing R] [IsDomain R]
    {f : R} (hf : f ≠ 0) :
    IsSMulRegular R f := by
  intro a b h
  apply sub_eq_zero.mp
  apply (mul_left_cancel₀ hf)
  simpa [mul_sub] using sub_eq_zero.mpr h

/-- Exact local dimension drop for a nonzero nonunit equation in a Noetherian
local domain.  Nonunit implies membership in the unique maximal ideal. -/
theorem ringKrullDim_quotient_nonzero_nonunit_succ
    {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsLocalRing R]
    {f : R} (hf0 : f ≠ 0) (hfunit : ¬ IsUnit f) :
    ringKrullDim (R ⧸ Ideal.span {f}) + 1 = ringKrullDim R := by
  have hfmax : f ∈ maximalIdeal R :=
    (IsLocalRing.mem_maximalIdeal f).2 (mem_nonunits_iff.mpr hfunit)
  exact ringKrullDim_quotient_regular_succ
    (regular_of_nonzero_domain hf0) hfmax

/-- The same local equation has principal ideal height exactly one. -/
theorem principal_height_one_of_local_domain
    {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsLocalRing R]
    {f : R} (hf0 : f ≠ 0) (hfunit : ¬ IsUnit f) :
    (Ideal.span {f}).height = 1 := by
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr hf0)
    hfunit

/-- Local one-equation crown: exact quotient-dimension decrement and exact
principal height are two views of the same regular cut. -/
theorem local_regular_cut_crown
    {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsLocalRing R]
    {f : R} (hf0 : f ≠ 0) (hfunit : ¬ IsUnit f) :
    ringKrullDim (R ⧸ Ideal.span {f}) + 1 = ringKrullDim R
      ∧ (Ideal.span {f}).height = 1 := by
  exact ⟨ringKrullDim_quotient_nonzero_nonunit_succ hf0 hfunit,
    principal_height_one_of_local_domain hf0 hfunit⟩

#check ringKrullDim_quotient_regular_succ
#check ringKrullDim_quotient_nonzero_nonunit_succ
#check principal_height_one_of_local_domain
#check local_regular_cut_crown

#print axioms ringKrullDim_quotient_regular_succ
#print axioms ringKrullDim_quotient_nonzero_nonunit_succ
#print axioms principal_height_one_of_local_domain
#print axioms local_regular_cut_crown

end GSTClassicalHodgeLocalRegularCutDimension
