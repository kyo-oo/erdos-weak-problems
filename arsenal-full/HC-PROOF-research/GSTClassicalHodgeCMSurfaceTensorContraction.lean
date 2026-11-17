import GSTClassicalHodgeCrossCarrierPointIncidence
import GSTClassicalHodgeCMThetaPeriodExtraction

/-!
# Algebraic core of surface-to-tensor Gysin extraction

Source: OpenAI/math, 2026, "The rational Hodge conjecture for CM abelian
varieties", Section 3 ("A surface criterion for the switch"), particularly

    p'_*(p^* Z cup K) = (integral_A Z cup t_alpha) * t_beta.

The geometric push/pull/cup operator is a rank-one contraction: it evaluates
an old-carrier cohomology class using a rational period functional, and scales
the chosen new-carrier tensor.

This module does not identify an arbitrary rational linear map with Gysin.
Instead it proves:
* the exact rank-one Betti linear map and its action;
* the ordered composition law for two such contractions;
* the normalized target cycle when a NATIVE incidence operator is shown
  pointwise to realize that rank-one Betti action;
* the surface period normalization comes from the functional's value,
  so the class equality is DERIVED, not added as an extra hypothesis.

The decisive independent input is the point-incidence equality between the
genuine correspondence on native algebraic cycles and the cohomological
rank-one kernel.  The original CM paper obtains that identity by divisor
cycles, Kunneth projection, Gysin pushforward and the projection formula.
That scheme-theoretic construction is not manufactured in this file.

NEEDS CI RUN LATER.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 800000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCrossCarrierPointIncidence

namespace GSTClassicalHodgeCMSurfaceTensorContraction

variable {A B C : Type*}
variable [AddCommGroup A] [Module ℚ A]
variable [AddCommGroup B] [Module ℚ B]
variable [AddCommGroup C] [Module ℚ C]

/-- The exact rank-one cohomological kernel: an old-carrier class is
integrated against the old tensor and the resulting scalar multiplies the
new tensor. -/
def rankOneBettiKernel
    (period : A →ₗ[ℚ] ℚ) (target : B) : A →ₗ[ℚ] B where
  toFun := fun alpha => period alpha • target
  map_add' := by
    intro x y
    simp [add_smul]
  map_smul' := by
    intro c x
    simp [smul_smul]

@[simp]
theorem rankOneBettiKernel_apply
    (period : A →ₗ[ℚ] ℚ) (target : B) (alpha : A) :
    rankOneBettiKernel period target alpha = period alpha • target := rfl

/-- The Kunneth rank-one correspondence composition formula; its middle
period is evaluated on the intermediate target tensor. -/
theorem rankOneBettiKernel_comp_apply
    (period₁ : A →ₗ[ℚ] ℚ) (middle : B)
    (period₂ : B →ₗ[ℚ] ℚ) (target : C)
    (alpha : A) :
    ((rankOneBettiKernel period₂ target).comp
      (rankOneBettiKernel period₁ middle)) alpha =
      (period₁ alpha * period₂ middle) • target := by
  simp [rankOneBettiKernel, smul_smul, mul_comm]

/-- A double Gysin contraction is again a single rank-one contraction.
This is the kernel-level algebra behind composing divisor correspondences. -/
theorem rankOneBettiKernel_comp_eq
    (period₁ : A →ₗ[ℚ] ℚ) (middle : B)
    (period₂ : B →ₗ[ℚ] ℚ) (target : C) :
    (rankOneBettiKernel period₂ target).comp
      (rankOneBettiKernel period₁ middle) =
        rankOneBettiKernel
          ((period₂ middle) • period₁) target := by
  ext alpha
  simp [rankOneBettiKernel, smul_smul, mul_comm]

variable {V W : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {J : HodgeBigradedBettiData W}
variable {p q : Nat}

/-- The paper's SURFACE-TO-TENSOR EXTRACTION with exactly the geometric
incidence obligation exposed.

If a native rational algebraic-cycle correspondence N is proved on every
irreducible codimension-p source point to realize the rank-one tensor
kernel `period ⊗ target`, then ANY source cycle with nonzero
period has an EXPLICIT target cycle obtained by dividing its native image
by that scalar.

The period equality on the target is proved here, not assumed. -/
theorem surface_period_normalizes_native_tensor
    (N : codimensionCycles V.X p →ₗ[ℚ] codimensionCycles W.X q)
    (period :
      RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ)
    (target :
      GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber W J q)
    (hIncidence : HasCrossCarrierPointIncidence
      (V := V) (W := W) (H := H) (J := J)
      N (rankOneBettiKernel period target.1))
    (Z : codimensionCycles V.X p)
    (hNonzero : period (H.cycleClass p Z) ≠ 0) :
    J.cycleClass q
      ((period (H.cycleClass p Z))⁻¹ • N Z) = target.1 := by
  have hperiod :
      rankOneBettiKernel period target.1 (H.cycleClass p Z) =
        period (H.cycleClass p Z) • target.1 := rfl
  exact normalized_target_from_point_incidence
    N (rankOneBettiKernel period target.1)
    hIncidence Z target (period (H.cycleClass p Z)) hNonzero hperiod

/-- The rank-one normalization also produces a witness of membership
in the exact algebraic-cycle range on the final destination variety. -/
theorem surface_period_target_is_algebraic
    (N : codimensionCycles V.X p →ₗ[ℚ] codimensionCycles W.X q)
    (period :
      RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ)
    (target :
      GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber W J q)
    (hIncidence : HasCrossCarrierPointIncidence
      (V := V) (W := W) (H := H) (J := J)
      N (rankOneBettiKernel period target.1))
    (Z : codimensionCycles V.X p)
    (hNonzero : period (H.cycleClass p Z) ≠ 0) :
    target.1 ∈ LinearMap.range (J.cycleClass q) :=
  ⟨_, surface_period_normalizes_native_tensor N period target
    hIncidence Z hNonzero⟩

#check rankOneBettiKernel_comp_eq
#check surface_period_normalizes_native_tensor
#check surface_period_target_is_algebraic
#print axioms surface_period_normalizes_native_tensor

end GSTClassicalHodgeCMSurfaceTensorContraction
