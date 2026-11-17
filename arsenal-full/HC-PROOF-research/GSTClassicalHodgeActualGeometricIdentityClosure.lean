import GSTClassicalHodgeFiniteClosedKernelBridge
import GSTClassicalHodgeGeometricCorrespondencePolynomialCalculus

/-!
# GST actual geometric identity and zeroth correspondence power

The original noncommutative realized-correspondence expression algebra
declared HasGeometricIdentity but only constructed strictly positive iteration.
This file closes that genuine geometric requirement, without assuming a
spanning theorem, Hodge algebraicity, or abstract native operator.

For the actual diagonal graph of X -> X, the finite-fiber native operator
is literally the identity on every codimension-p native algebraic cycle.
This uses the projective point-normal-form extensionality theorem and the
residue degree of the identity scheme morphism.

Consequently the expression algebra has a true geometric unit and a power
operator for ALL n >= 0, not only positive iteration.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgeProjectivePointTransport
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
open GSTClassicalHodgeGeometricCorrespondencePolynomialCalculus
open GSTClassicalHodgeDiagonalIdentityCorrespondence
open GSTClassicalHodgeFiniteClosedKernelBridge

namespace GSTClassicalHodgeActualGeometricIdentityClosure

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The native-cycle operator of the ACTUAL graph of the identity morphism
is literally the identity map. This is stronger than having identity action
only AFTER passage to Betti cycle classes. -/
theorem diagonalGraph_native_eq_id
    (V : SmoothProjectiveComplexScheme) (p : Nat) :
    (FiniteClosedCorrespondence.graphCorrespondence
      (GSTClassicalHodgeAnalytificationFunctoriality.ComplexSchemeEndomorphism.id V)
      ).nativeOperator p =
      (LinearMap.id : codimensionCycles V.X p →ₗ[ℚ]
        codimensionCycles V.X p) := by
  apply sub_eq_zero.mp
  apply nativeLinearMap_eq_zero_of_points V p
  intro x
  simp only [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  rw [FiniteClosedCorrespondence.nativeOperator_point]
  rw [FiniteClosedCorrespondence.graphCorrespondence_nativePointImage_eq]
  have hcod : Order.coheight ((𝟙 V.X) x.1) = p := by
    simpa using x.2
  change nativePointPushforward (𝟙 V.X) p x =
    codimensionPointCycle V.X p x
  rw [nativePointPushforward_eq (𝟙 V.X) p x hcod]
  simp [pointResidueWeight]

/-- The geometric diagonal atom supplies the native as well as the
cohomological identity on the full rational cycle space. -/
theorem diagonalExpr_native_eq_id :
    (diagonalExpr (V := V) (H := H) (p := p)).cycleOperator =
      (LinearMap.id : codimensionCycles V.X p →ₗ[ℚ]
        codimensionCycles V.X p) := by
  exact diagonalGraph_native_eq_id V p

/-- Discharge the previously open genuine-identity capability of the
realized GST correspondence expression algebra. No hypotheses are supplied. -/
theorem has_actual_geometric_identity :
    RealizedCorrespondenceExpr.HasGeometricIdentity
      (V := V) (H := H) (p := p) := by
  refine ⟨diagonalExpr (V := V) (H := H) (p := p), ?_, ?_⟩
  · apply LinearMap.ext
    intro alpha
    exact diagonalExpr_cohomology alpha
  · exact diagonalExpr_native_eq_id

/-- Native algebraic correspondence powers, including n=0, built only
from the already constructed diagonal and actual realized correspondences. -/
noncomputable def geometricPow
    (E : RealizedCorrespondenceExpr V H p) :
    Nat → RealizedCorrespondenceExpr V H p
  | 0 => diagonalExpr (V := V) (H := H) (p := p)
  | n + 1 => .comp E (geometricPow E n)

/-- The zeroth native iterate is the geometric identity. -/
theorem geometricPow_zero_native
    (E : RealizedCorrespondenceExpr V H p) :
    (geometricPow E 0).cycleOperator =
      (LinearMap.id : codimensionCycles V.X p →ₗ[ℚ]
        codimensionCycles V.X p) := by
  exact diagonalExpr_native_eq_id

/-- The zeroth Betti iterate is likewise the identity, with no arbitrary
cohomology endomorphism smuggled into the correspondence language. -/
theorem geometricPow_zero_betti
    (E : RealizedCorrespondenceExpr V H p) :
    (geometricPow E 0).cohomologyOperator =
      (LinearMap.id :
        RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
          RationalSingularCohomology H.analytification (2 * p)) := by
  apply LinearMap.ext
  intro alpha
  exact diagonalExpr_cohomology alpha

/-- Every positive power is genuine ordered geometric composition. -/
theorem geometricPow_succ_native
    (E : RealizedCorrespondenceExpr V H p)
    (n : Nat) (Z : codimensionCycles V.X p) :
    (geometricPow E (n + 1)).cycleOperator Z =
      E.cycleOperator ((geometricPow E n).cycleOperator Z) := rfl

/-- All powers, including the zeroth diagonal, preserve actual cycle-class
naturality, since every stage is a genuine correspondence expression. -/
theorem geometricPow_cycleClass_natural
    (E : RealizedCorrespondenceExpr V H p)
    (n : Nat) (Z : codimensionCycles V.X p) :
    H.cycleClass p ((geometricPow E n).cycleOperator Z) =
      (geometricPow E n).cohomologyOperator (H.cycleClass p Z) :=
  (geometricPow E n).cycleClass_natural Z

#check diagonalGraph_native_eq_id
#check has_actual_geometric_identity
#check geometricPow
#check geometricPow_cycleClass_natural
#print axioms diagonalGraph_native_eq_id
#print axioms has_actual_geometric_identity

end GSTClassicalHodgeActualGeometricIdentityClosure
