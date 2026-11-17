import GSTClassicalHodgeCrossCarrierPointIncidence
import GSTClassicalHodgePointKernelOperatorLift

/-!
# Explicit finite point-incidence kernels BETWEEN algebraic varieties

The old cross-carrier layer requested a fully formed linear native-cycle map.
This replacement CONSTRUCTS that map from genuine finite point-cycle incidence
data, using the repository's compact native-cycle/presentation linear
equivalence.

For a codimension-p generic point x on a projective source variety, a kernel
K gives a FINITE rational presentation of codimension-q generic points on a
different target variety. The native map of ANY rational algebraic source
cycle is computed by linear extension, with an explicit finite-sum formula.

Unlike an unrestricted cohomological endomorphism, this kernel intrinsically
has native algebraic-cycle output.  A pointwise geometric Betti identity then
implies global naturality as a theorem; the old multicarrier transfer is built
as an output, not postulated.

A finite point-incidence assignment is not on its own a scheme-theoretic
correspondence.  To claim a proper Gysin/push-pull interpretation one must
prove that K comes from the selected geometric incidence construction.

NEEDS CI RUN LATER.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 800000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgePointKernelOperatorLift
open GSTClassicalHodgeGeometricCycleClassPointRigidity
open GSTClassicalHodgeCrossCarrierGeometricTransfer
open GSTClassicalHodgeCrossCarrierPointIncidence

namespace GSTClassicalHodgeCrossCarrierExplicitPointKernel

variable {V W U : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {J : HodgeBigradedBettiData W}
variable {L : HodgeBigradedBettiData U}
variable {p q r : Nat}

/-- Every source generic codimension-p point is assigned an actual FINITELY
SUPPORTED rational target codimension-q cycle presentation. -/
abbrev FiniteCrossCarrierPointKernel
    (V W : SmoothProjectiveComplexScheme) (p q : Nat) :=
  CodimensionPoint V.X p → FiniteCodimensionPresentation W.X q

/-- ACTUAL native rational algebraic-cycle map manufactured by rational-linear
extension from finite point incidence. No independent native operator field. -/
noncomputable def nativeOfFinitePointKernel
    (K : FiniteCrossCarrierPointKernel V W p q) :
    codimensionCycles V.X p →ₗ[ℚ] codimensionCycles W.X q := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  exact (realizePresentationLinear W.X q).comp
    ((Finsupp.linearCombination ℚ K).comp
      (compactCyclePresentationLinearEquiv V.X p).symm.toLinearMap)

/-- The constructed native map takes each source atom to the corresponding
FINITE target algebraic cycle, not merely to an abstract Betti class. -/
@[simp]
theorem nativeOfFinitePointKernel_point
    (K : FiniteCrossCarrierPointKernel V W p q)
    (x : CodimensionPoint V.X p) :
    nativeOfFinitePointKernel K (codimensionPointCycle V.X p x) =
      realizeFiniteCodimensionPresentation W.X q (K x) := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  simp [nativeOfFinitePointKernel,
    compactCyclePresentationLinearEquiv_symm_apply,
    presentationOfNativeCycle_point,
    realizePresentationLinear_apply, Finsupp.linearCombination]

/-- Every correspondence action is a FINITE rational sum of the assigned
point cycles.  This directly exposes the actual native-cycle output. -/
theorem nativeOfFinitePointKernel_finite_sum
    (K : FiniteCrossCarrierPointKernel V W p q)
    (Z : codimensionCycles V.X p) :
    nativeOfFinitePointKernel K Z =
      (letI : CompactSpace V.X := smoothProjectiveCompactSpace V
       (presentationOfNativeCycle V.X p Z).sum
         (fun x a => a • realizeFiniteCodimensionPresentation W.X q (K x))) := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  simp [nativeOfFinitePointKernel, realizePresentationLinear_apply,
    Finsupp.linearCombination, Finsupp.sum, map_sum]

/-- The one real geometric law: cohomological push/pull must agree on a
genuine source point with the finite native target incidence cycle. -/
def RealizesFinitePointKernelOnBetti
    (K : FiniteCrossCarrierPointKernel V W p q)
    (B : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology J.analytification (2 * q)) : Prop :=
  ∀ x : CodimensionPoint V.X p,
    J.cycleClass q
      (realizeFiniteCodimensionPresentation W.X q (K x)) =
      B (H.cycleClass p (codimensionPointCycle V.X p x))

/-- The independent Betti point-incidence criterion is precisely the old
global interface criterion for the constructed native operator. -/
theorem pointKernel_realizes_iff_point_incidence
    (K : FiniteCrossCarrierPointKernel V W p q)
    (B : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology J.analytification (2 * q)) :
    RealizesFinitePointKernelOnBetti (H := H) (J := J) K B ↔
      HasCrossCarrierPointIncidence (H := H) (J := J)
        (nativeOfFinitePointKernel K) B := by
  simp only [RealizesFinitePointKernelOnBetti,
    HasCrossCarrierPointIncidence, nativeOfFinitePointKernel_point]

/-- The global naturality theorem is derived from the FINITE kernel and
one-point geometric identities; there is no additional global assumption. -/
theorem finitePointKernel_naturality
    (K : FiniteCrossCarrierPointKernel V W p q)
    (B : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology J.analytification (2 * q))
    (hB : RealizesFinitePointKernelOnBetti (H := H) (J := J) K B)
    (Z : codimensionCycles V.X p) :
    J.cycleClass q (nativeOfFinitePointKernel K Z) =
      B (H.cycleClass p Z) := by
  exact global_naturality_of_point_incidence
    (nativeOfFinitePointKernel K) B
    ((pointKernel_realizes_iff_point_incidence K B).mp hB) Z

/-- Concrete cross-carrier transfer constructed from actual finite
point-incidence support, with global naturality DERIVED. -/
noncomputable def transferOfFinitePointKernel
    (K : FiniteCrossCarrierPointKernel V W p q)
    (B : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology J.analytification (2 * q))
    (hB : RealizesFinitePointKernelOnBetti (H := H) (J := J) K B) :
    CrossCarrierTransfer V W H J p q where
  native := nativeOfFinitePointKernel K
  betti := B
  naturality := finitePointKernel_naturality K B hB

/-- Extract actual geometry rather than an existential operator: a
nonzero period k for a finite point kernel gives a specified native-cycle
expression and its exact target Hodge class. -/
theorem finitePointKernel_normalized_period
    (K : FiniteCrossCarrierPointKernel V W p q)
    (B : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology J.analytification (2 * q))
    (hB : RealizesFinitePointKernelOnBetti (H := H) (J := J) K B)
    (Z : codimensionCycles V.X p)
    (target : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber W J q)
    (k : ℚ) (hk : k ≠ 0)
    (hperiod : B (H.cycleClass p Z) = k • target.1) :
    J.cycleClass q
      (k⁻¹ • nativeOfFinitePointKernel K Z) = target.1 := by
  rw [map_smul, finitePointKernel_naturality K B hB Z, hperiod, smul_smul]
  simp [hk]

#check nativeOfFinitePointKernel
#check nativeOfFinitePointKernel_finite_sum
#check finitePointKernel_naturality
#check transferOfFinitePointKernel
#print axioms finitePointKernel_naturality

end GSTClassicalHodgeCrossCarrierExplicitPointKernel
