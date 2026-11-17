import GSTClassicalHodgeStrictCorrespondenceTransferFromPrimitives
import GSTNativeCodimensionCyclePresentation
import GSTClassicalHodgeGeometricCycleClassPointRigidity

/-!
# GST CLASSICAL HODGE — STRICT KERNEL RANGE STABILITY

The low-level cup/Gysin/intersection construction proves that a genuine strict
projective correspondence and its genuine factor-swap transpose preserve the
actual rational cycle-class range.  This file records that consequence at the
level needed by the finite GST matrix-unit engine.

Nothing here assumes Hodge surjectivity, spectral saturation, cyclicity, or an
abstract cohomology endomorphism.  The two cohomology operators are the ambient
kernel actions forced by the correspondence classes themselves.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeStrictKernelRangeStability

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAmbientBettiSelfProduct
open GSTClassicalHodgeBettiCupGysinPrimitives
open GSTClassicalHodgeAmbientCorrespondenceKernelAction
open GSTClassicalHodgeAmbientIntersectionFromPrimitives
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeCycleClassIntersectionPrimitives
open GSTClassicalHodgeStrictCorrespondenceTransferFromPrimitives
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeGeometricCycleClassPointRigidity

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {d p : Nat}

/-- The actual cycle-class range in degree `2p`. -/
abbrev AlgebraicBettiRange :
    Submodule ℚ (RationalSingularCohomology H.analytification (2 * p)) :=
  LinearMap.range (H.cycleClass p)

/-- A strict ambient correspondence kernel constructed from the low-level
intersection primitives preserves the genuine cycle-class range. -/
theorem kernelAction_range_stable
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (kappa : MiddleBettiCorrespondenceKernel H.analytification d K)
    (pt : PointBettiClass (V := V) p H.analytification)
    (hpoint : ∀ x : CodimensionPoint V.X p,
      H.cycleClass p (codimensionPointCycle V.X p x) = pt x)
    (I : GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p) P K kappa pt) :
    ∀ alpha ∈ AlgebraicBettiRange (H := H) (p := p),
      kernelAction H.analytification P kappa (2 * p) alpha ∈
        AlgebraicBettiRange (H := H) (p := p) := by
  intro alpha halpha
  rcases halpha with ⟨Z, rfl⟩
  refine ⟨K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
      |>.nativeOperator p Z, ?_⟩
  exact supplied_cycleClass_nativeOperator P K kappa pt hpoint I Z

/-- The genuine factor-swapped transpose preserves the same algebraic range. -/
theorem transposeKernelAction_range_stable
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (kappa : MiddleBettiCorrespondenceKernel H.analytification d K)
    (pt : PointBettiClass (V := V) p H.analytification)
    (hpoint : ∀ x : CodimensionPoint V.X p,
      H.cycleClass p (codimensionPointCycle V.X p x) = pt x)
    (It : GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p)
      P K.transpose kappa.transposeKernel pt) :
    ∀ alpha ∈ AlgebraicBettiRange (H := H) (p := p),
      kernelAction H.analytification P kappa.transposeKernel (2 * p) alpha ∈
        AlgebraicBettiRange (H := H) (p := p) := by
  intro alpha halpha
  rcases halpha with ⟨Z, rfl⟩
  refine ⟨K.transpose.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
      |>.nativeOperator p Z, ?_⟩
  exact supplied_cycleClass_nativeOperator
    P K.transpose kappa.transposeKernel pt hpoint It Z

/-- Forward and genuine transpose stability in one theorem. -/
theorem forward_transpose_range_stable
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (kappa : MiddleBettiCorrespondenceKernel H.analytification d K)
    (pt : PointBettiClass (V := V) p H.analytification)
    (hpoint : ∀ x : CodimensionPoint V.X p,
      H.cycleClass p (codimensionPointCycle V.X p x) = pt x)
    (I : GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p) P K kappa pt)
    (It : GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p)
      P K.transpose kappa.transposeKernel pt) :
    (∀ alpha ∈ AlgebraicBettiRange (H := H) (p := p),
      kernelAction H.analytification P kappa (2 * p) alpha ∈
        AlgebraicBettiRange (H := H) (p := p)) ∧
    (∀ alpha ∈ AlgebraicBettiRange (H := H) (p := p),
      kernelAction H.analytification P kappa.transposeKernel (2 * p) alpha ∈
        AlgebraicBettiRange (H := H) (p := p)) := by
  exact ⟨kernelAction_range_stable P K kappa pt hpoint I,
    transposeKernelAction_range_stable P K kappa pt hpoint It⟩

#check kernelAction_range_stable
#check transposeKernelAction_range_stable
#check forward_transpose_range_stable

#print axioms kernelAction_range_stable
#print axioms transposeKernelAction_range_stable
#print axioms forward_transpose_range_stable

end GSTClassicalHodgeStrictKernelRangeStability
