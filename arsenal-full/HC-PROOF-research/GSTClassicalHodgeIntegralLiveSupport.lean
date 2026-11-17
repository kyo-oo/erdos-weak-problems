import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Ring.Rat
import GSTClassicalHodgeFiniteSupportArsenalConjugation
import GSTWorldRecoordinationGroupoid
import GSTTransferBridgeV2

/-!
# GST CLASSICAL HODGE — INTEGRAL LIVE SUPPORT

Every genuine rational Hodge class has finite support in the unrestricted
classical Hodge basis.  A finite family of rational coefficients admits one
common positive denominator.  Multiplying by that denominator converts the
entire live support into integer coefficients.

This is the exact interface needed to feed an arbitrary rational Hodge state
into the strongest integer-valued GST cosmology.  No rational information is
lost: division by the same nonzero integer recovers the original state over
`Q`.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiniteSupportArsenalConjugation

namespace GSTClassicalHodgeIntegralLiveSupport

universe u

/-- Product of the denominators occurring on the finite support. -/
def commonDenominator {ι : Type u} [DecidableEq ι]
    (f : ι →₀ ℚ) : Nat :=
  f.support.prod (fun i => (f i).den)

/-- The common denominator is positive. -/
theorem commonDenominator_pos {ι : Type u} [DecidableEq ι]
    (f : ι →₀ ℚ) : 0 < commonDenominator f := by
  unfold commonDenominator
  exact Finset.prod_pos fun i hi => Rat.pos (f i)

/-- Every live coordinate denominator divides the common denominator. -/
theorem den_dvd_commonDenominator {ι : Type u} [DecidableEq ι]
    (f : ι →₀ ℚ) {i : ι} (hi : i ∈ f.support) :
    (f i).den ∣ commonDenominator f := by
  unfold commonDenominator
  exact Finset.dvd_prod_of_mem (fun j => (f j).den) hi

/-- Every coordinate becomes integral after multiplication by the common
denominator; outside the support both sides are zero. -/
theorem commonDenominator_mul_coordinate_isInt
    {ι : Type u} [DecidableEq ι]
    (f : ι →₀ ℚ) (i : ι) :
    ∃ z : ℤ, (commonDenominator f : ℚ) * f i = (z : ℚ) := by
  classical
  by_cases hi : i ∈ f.support
  · obtain ⟨k, hk⟩ := den_dvd_commonDenominator f hi
    refine ⟨(k : ℤ) * (f i).num, ?_⟩
    have hden := Rat.den_mul_eq_num (f i)
    rw [hk, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
    linear_combination (k : ℚ) * hden
  · have hzero : f i = 0 := Finsupp.notMem_support_iff.mp hi
    exact ⟨0, by simp [hzero]⟩

/-- Chosen integral coefficient of one coordinate after common-denominator
scaling. -/
noncomputable def integralCoefficient
    {ι : Type u} [DecidableEq ι]
    (f : ι →₀ ℚ) (i : ι) : ℤ :=
  Classical.choose (commonDenominator_mul_coordinate_isInt f i)

@[simp]
theorem integralCoefficient_spec
    {ι : Type u} [DecidableEq ι]
    (f : ι →₀ ℚ) (i : ι) :
    (commonDenominator f : ℚ) * f i =
      (integralCoefficient f i : ℚ) :=
  Classical.choose_spec (commonDenominator_mul_coordinate_isInt f i)

/-- The integralized finite-support address. -/
noncomputable def integralize
    {ι : Type u} [DecidableEq ι]
    (f : ι →₀ ℚ) : ι →₀ ℤ :=
  Finsupp.onFinset f.support (integralCoefficient f)
    (by
      intro i hi
      by_contra hmem
      have hzero : f i = 0 := Finsupp.notMem_support_iff.mp hmem
      have hspec := integralCoefficient_spec f i
      rw [hzero, mul_zero] at hspec
      exact hi (by exact_mod_cast hspec.symm))

/-- Exact coordinatewise scaling law for integralization. -/
theorem integralize_spec
    {ι : Type u} [DecidableEq ι]
    (f : ι →₀ ℚ) (i : ι) :
    ((integralize f i : ℤ) : ℚ) =
      (commonDenominator f : ℚ) * f i := by
  classical
  by_cases hi : i ∈ f.support
  · simp [integralize, hi, integralCoefficient_spec]
  · have hzero : f i = 0 := Finsupp.notMem_support_iff.mp hi
    have hspec := integralCoefficient_spec f i
    rw [hzero, mul_zero] at hspec
    simp only [integralize, Finsupp.onFinset_apply, hzero, mul_zero]
    exact hspec.symm

/-- The scaling integer is nonzero in `Q`. -/
theorem commonDenominator_cast_ne_zero
    {ι : Type u} [DecidableEq ι]
    (f : ι →₀ ℚ) :
    (commonDenominator f : ℚ) ≠ 0 := by
  exact_mod_cast Nat.ne_of_gt (commonDenominator_pos f)

/-- Rational coordinates are recovered exactly from their integralization. -/
theorem recover_from_integralize
    {ι : Type u} [DecidableEq ι]
    (f : ι →₀ ℚ) (i : ι) :
    f i = (commonDenominator f : ℚ)⁻¹ * (integralize f i : ℚ) := by
  rw [integralize_spec]
  field_simp [commonDenominator_cast_ne_zero f]

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Integral finite address of one genuine Hodge class. -/
noncomputable def integralHodgeAddress
    (alpha : ClassicalHodgeFiber V H p) :
    ClassicalHodgeBasisIndex V H p →₀ ℤ :=
  integralize ((classicalHodgeBasis V H p).repr alpha)

/-- Exact rational recovery of every genuine Hodge basis coordinate. -/
theorem integralHodgeAddress_recovers
    (alpha : ClassicalHodgeFiber V H p)
    (i : ClassicalHodgeBasisIndex V H p) :
    ((classicalHodgeBasis V H p).repr alpha) i =
      (commonDenominator ((classicalHodgeBasis V H p).repr alpha) : ℚ)⁻¹ *
        (integralHodgeAddress alpha i : ℚ) := by
  exact recover_from_integralize
    ((classicalHodgeBasis V H p).repr alpha) i

/-- Nonzero Hodge classes remain nonzero after integralization. -/
theorem integralHodgeAddress_ne_zero
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    integralHodgeAddress alpha ≠ 0 := by
  intro hzero
  apply halpha
  apply (classicalHodgeBasis V H p).repr.injective
  apply Finsupp.ext
  intro i
  have hi := integralHodgeAddress_recovers alpha i
  have hz := congrArg (fun f : ClassicalHodgeBasisIndex V H p →₀ ℤ => f i) hzero
  simp at hz
  simpa [hz] using hi

/-- **INTEGRAL LIVE-SUPPORT CROWN.** Every nonzero rational Hodge state has a
nonzero finitely-supported integer address and is recovered exactly by one
nonzero rational rescaling. -/
theorem integral_live_support_crown
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    integralHodgeAddress alpha ≠ 0
    ∧ (∀ i : ClassicalHodgeBasisIndex V H p,
      ((classicalHodgeBasis V H p).repr alpha) i =
        (commonDenominator ((classicalHodgeBasis V H p).repr alpha) : ℚ)⁻¹ *
          (integralHodgeAddress alpha i : ℚ)) := by
  exact ⟨integralHodgeAddress_ne_zero alpha halpha,
    integralHodgeAddress_recovers alpha⟩

#check commonDenominator
#check commonDenominator_pos
#check den_dvd_commonDenominator
#check commonDenominator_mul_coordinate_isInt
#check integralCoefficient
#check integralize
#check integralize_spec
#check recover_from_integralize
#check integralHodgeAddress
#check integralHodgeAddress_recovers
#check integralHodgeAddress_ne_zero
#check integral_live_support_crown

#print axioms commonDenominator_mul_coordinate_isInt
#print axioms integralize_spec
#print axioms recover_from_integralize
#print axioms integralHodgeAddress_recovers
#print axioms integral_live_support_crown

end GSTClassicalHodgeIntegralLiveSupport
