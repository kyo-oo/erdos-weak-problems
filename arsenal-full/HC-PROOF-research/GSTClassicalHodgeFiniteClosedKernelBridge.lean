import GSTClassicalHodgeCrossCarrierExplicitPointKernel
import GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
import GSTClassicalHodgeDiagonalIdentityCorrespondence

/-!
# GST finite-closed correspondence -> explicit finite point kernel

This is a construction, not a universal Hodge-generation assumption.

A previously realized finite closed correspondence has an ACTUAL scheme
carrier, finite left fibers, right projection and residue-degree coefficients.
Its finite point kernel is the existing geometric transition function.

We prove that the new cross-carrier point-kernel engine reproduces the
OLD geometry's native operator exactly, and carries precisely its verified
Betti realization. No arbitrary native cycle operator, point-incidence
certificate, or Hodge basis lift is provided as an input.

As a concrete universal inhabitant, the true diagonal graph gives an
explicit cross-carrier identity-Betti transfer in every codimension.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeCrossCarrierGeometricTransfer
open GSTClassicalHodgeCrossCarrierExplicitPointKernel
open GSTClassicalHodgeDiagonalIdentityCorrespondence

namespace GSTClassicalHodgeFiniteClosedKernelBridge

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Actual finite point incidence extracted from a finite closed geometric
correspondence's left fibers, right projection, and rational residue degrees. -/
noncomputable def closedPointKernel
    (K : FiniteClosedCorrespondence V) (p : Nat) :
    FiniteCrossCarrierPointKernel V V p p :=
  K.transition p

/-- Both independent engines compute exactly the same transported algebraic
point atom: no conjectural cohomological realization is involved. -/
theorem closedPointKernel_native_point
    (K : FiniteClosedCorrespondence V)
    (x : CodimensionPoint V.X p) :
    nativeOfFinitePointKernel (closedPointKernel K p)
      (codimensionPointCycle V.X p x) =
        K.nativeOperator p (codimensionPointCycle V.X p x) := by
  rw [nativeOfFinitePointKernel_point, K.nativeOperator_point]
  rfl

/-- This geometric equality holds on ALL rational algebraic cycles, not just
on the finite point-generators: the projective point normal form supplies
exact native operator extensionality. -/
theorem closedPointKernel_native_eq
    (K : FiniteClosedCorrespondence V) :
    nativeOfFinitePointKernel (closedPointKernel K p) =
      K.nativeOperator p := by
  apply sub_eq_zero.mp
  apply nativeLinearMap_eq_zero_of_points V p
  intro x
  simp only [LinearMap.sub_apply, sub_eq_zero]
  exact closedPointKernel_native_point K x

/-- The correct Betti point-incidence law is DERIVED from the actual
realization theorem of the old finite closed correspondence. -/
theorem closedPointKernel_realizes
    (R : RealizedFiniteClosedCorrespondence V H p) :
    RealizesFinitePointKernelOnBetti
      (H := H) (J := H)
      (closedPointKernel R.geometry p) R.cohomologyOperator := by
  intro x
  change H.cycleClass p (R.geometry.nativePointImage p x) =
    R.cohomologyOperator
      (H.cycleClass p (codimensionPointCycle V.X p x))
  exact R.realizes_on_points x

/-- A full cross-carrier action constructed from a genuine closed
correspondence. Neither native nor Betti operator is independently chosen. -/
noncomputable def closedRealizedCrossCarrier
    (R : RealizedFiniteClosedCorrespondence V H p) :
    CrossCarrierTransfer V V H H p p :=
  transferOfFinitePointKernel
    (closedPointKernel R.geometry p)
    R.cohomologyOperator
    (closedPointKernel_realizes R)

/-- The finite-kernel cross-carrier action IS the older GST native geometry,
not merely equal after mapping into cohomology. -/
theorem closedRealizedCrossCarrier_native
    (R : RealizedFiniteClosedCorrespondence V H p) :
    (closedRealizedCrossCarrier R).native =
      R.geometry.nativeOperator p :=
  closedPointKernel_native_eq R.geometry

/-- Its whole-Betti operator is exactly the previously realized action. -/
theorem closedRealizedCrossCarrier_betti
    (R : RealizedFiniteClosedCorrespondence V H p) :
    (closedRealizedCrossCarrier R).betti = R.cohomologyOperator := rfl

/-- A genuinely geometric, assumption-free example: the diagonal graph
induces a cross-carrier transfer with identity action on rational Betti. -/
noncomputable def diagonalCrossCarrier :
    CrossCarrierTransfer V V H H p p :=
  closedRealizedCrossCarrier
    (diagonalRealized (V := V) (H := H) (p := p))

@[simp]
theorem diagonalCrossCarrier_betti :
    (diagonalCrossCarrier (V := V) (H := H) (p := p)).betti =
      (LinearMap.id :
        RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
          RationalSingularCohomology H.analytification (2 * p)) := rfl

/-- Its native action is precisely the actual diagonal's geometrically
constructed finite-correspondence operator. -/
theorem diagonalCrossCarrier_native :
    (diagonalCrossCarrier (V := V) (H := H) (p := p)).native =
      (diagonalRealized (V := V) (H := H) (p := p)).geometry.nativeOperator p :=
  closedRealizedCrossCarrier_native _

#check closedPointKernel
#check closedPointKernel_native_eq
#check closedPointKernel_realizes
#check closedRealizedCrossCarrier
#check closedRealizedCrossCarrier_native
#check diagonalCrossCarrier
#print axioms closedPointKernel_native_eq
#print axioms closedPointKernel_realizes
#print axioms diagonalCrossCarrier_native

end GSTClassicalHodgeFiniteClosedKernelBridge
