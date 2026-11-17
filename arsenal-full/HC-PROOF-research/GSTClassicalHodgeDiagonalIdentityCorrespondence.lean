import GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra

/-!
# GST CLASSICAL HODGE — GENUINE DIAGONAL IDENTITY CORRESPONDENCE

Polynomial correspondence calculus needs a constant term.  We do not insert
an abstract identity operator.  Instead use the graph of the actual identity
endomorphism of X, i.e. the diagonal correspondence.

On every genuine codimension-p point atom its native correspondence image is
the same point cycle with residue degree one.  Therefore the diagonal realizes
`LinearMap.id` on rational cohomology point classes, and the point-kernel engine
upgrades this to an exact native/cohomology commuting square on all cycles.

No Hodge algebraicity statement is used.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeDiagonalIdentityCorrespondence

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeAnalytificationFunctoriality
open GSTClassicalHodgeProjectivePointTransport
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The genuine graph-of-identity correspondence realizes the identity on the
cycle class of every point generator. -/
theorem diagonal_realizes_identity_on_points :
    (FiniteClosedCorrespondence.graphCorrespondence
      (ComplexSchemeEndomorphism.id V)).RealizesAmbientOnPoints
        (H := H) (LinearMap.id :
          RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
            RationalSingularCohomology H.analytification (2 * p)) := by
  intro x
  rw [FiniteClosedCorrespondence.graphCorrespondence_nativePointImage_eq]
  have hcod : Order.coheight ((𝟙 V.X) x.1) = p := by
    simpa using x.2
  show (H.cycleClass p) (nativePointPushforward (𝟙 V.X) p x) =
    LinearMap.id ((H.cycleClass p) (codimensionPointCycle V.X p x))
  rw [nativePointPushforward_eq (𝟙 V.X) p x hcod]
  simp [pointResidueWeight]

/-- Genuine realized diagonal correspondence with literal cohomological
identity action. -/
noncomputable def diagonalRealized :
    RealizedFiniteClosedCorrespondence V H p where
  geometry := FiniteClosedCorrespondence.graphCorrespondence
    (ComplexSchemeEndomorphism.id V)
  cohomologyOperator := LinearMap.id
  realizes_on_points := diagonal_realizes_identity_on_points

@[simp] theorem diagonalRealized_cohomologyOperator :
    (diagonalRealized (V := V) (H := H) (p := p)).cohomologyOperator =
      LinearMap.id := rfl

/-- Full native cycle-class naturality of the genuine diagonal. -/
theorem diagonal_cycleClass_natural
    (Z : codimensionCycles V.X p) :
    H.cycleClass p
        ((diagonalRealized (V := V) (H := H) (p := p)).geometry.nativeOperator p Z) =
      H.cycleClass p Z := by
  simpa using
    (diagonalRealized (V := V) (H := H) (p := p)).cycleClass_natural Z

#check diagonal_realizes_identity_on_points
#check diagonalRealized
#check diagonal_cycleClass_natural

#print axioms diagonal_realizes_identity_on_points
#print axioms diagonal_cycleClass_natural

end GSTClassicalHodgeDiagonalIdentityCorrespondence
