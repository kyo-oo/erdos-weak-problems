import GSTClassicalHodgeFiniteClosedCorrespondence
import GSTClassicalHodgePointKernelOperatorLift
import GSTClassicalHodgeCrossWeightNativePropagation

/-!
# GST CLASSICAL HODGE — GRADED FINITE CLOSED CORRESPONDENCES

The existing finite closed correspondence machinery was deliberately exposed
first in the same-codimension case.  Its geometric point kernel is already
more general: every correspondence point can be filtered by an arbitrary
target codimension.  This file unlocks that latent graded structure.

For one genuine finite closed correspondence K in X x X and arbitrary source
and target codimensions p,q we construct

  codimensionCycles X p -> codimensionCycles X q

by:

1. enumerate the finite left fiber over each codimension-p source point;
2. retain right images of exact codimension q;
3. form the resulting finite q-presentation;
4. extend the point kernel linearly on finite presentations;
5. conjugate through the exact compact cycle/presentation linear equivalence.

No Hodge statement enters this construction.

A separate pointwise cycle-class naturality structure supplies only the
cohomological action and its equation on genuine point generators.  Compact
point normal form then upgrades that generator law to the full cycle-class
commuting square, manufacturing an actual `GradedCycleClassOperatorPair`.

This gives the complementary-defect reciprocity route a concrete geometric
carrier: its return map may now be sought among actual finite closed
correspondences rather than postulated as an abstract graded operator.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeGradedFiniteClosedCorrespondence

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgePointKernelOperatorLift
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeCrossWeightNativePropagation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p q : Nat}

end GSTClassicalHodgeGradedFiniteClosedCorrespondence

namespace GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgePointKernelOperatorLift
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeCrossWeightNativePropagation

/-- Finite target-q presentation over one source point of codimension p.
Unlike the older `transition`, source and target codimensions are independent. -/
noncomputable def gradedTransition
    (K : FiniteClosedCorrespondence V)
    (q : Nat)
    (x : CodimensionPoint V.X p) :
    FiniteCodimensionPresentation V.X q :=
  (K.leftFiberFinset x.1).sum (K.targetAtomPresentation q)

/-- The old same-codimension transition is the p=q specialization. -/
theorem gradedTransition_self
    (K : FiniteClosedCorrespondence V)
    (x : CodimensionPoint V.X p) :
    K.gradedTransition p x = K.transition p x := by
  rfl

/-- Real native target-q cycle of one source codimension-p point. -/
noncomputable def gradedNativePointImage
    (K : FiniteClosedCorrespondence V)
    (q : Nat)
    (x : CodimensionPoint V.X p) :
    codimensionCycles V.X q :=
  realizeFiniteCodimensionPresentation V.X q (K.gradedTransition q x)

/-- Same-codimension compatibility with the original point-image definition. -/
theorem gradedNativePointImage_self
    (K : FiniteClosedCorrespondence V)
    (x : CodimensionPoint V.X p) :
    K.gradedNativePointImage p x = K.nativePointImage p x := by
  rfl

/-- Free rational-linear extension of the graded point transition. -/
noncomputable def gradedPresentationOperator
    (K : FiniteClosedCorrespondence V)
    (p q : Nat) :
    FiniteCodimensionPresentation V.X p →ₗ[ℚ]
      FiniteCodimensionPresentation V.X q :=
  Finsupp.linearCombination ℚ (fun x : CodimensionPoint V.X p =>
    K.gradedTransition q x)

@[simp]
theorem gradedPresentationOperator_single
    (K : FiniteClosedCorrespondence V)
    (p q : Nat)
    (x : CodimensionPoint V.X p) :
    K.gradedPresentationOperator p q (Finsupp.single x 1) =
      K.gradedTransition q x := by
  simp [gradedPresentationOperator]

/-- **GENUINE GRADED FINITE-CORRESPONDENCE OPERATOR.**
Conjugate the free point transition through the exact compact native-cycle
normal form. -/
noncomputable def gradedNativeCycleOperator
    (K : FiniteClosedCorrespondence V)
    (p q : Nat) :
    codimensionCycles V.X p →ₗ[ℚ] codimensionCycles V.X q := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  exact
    (compactCyclePresentationLinearEquiv V.X q).toLinearMap.comp
      ((K.gradedPresentationOperator p q).comp
        (compactCyclePresentationLinearEquiv V.X p).symm.toLinearMap)

/-- The graded native operator acts on every source point by the explicitly
enumerated finite correspondence fiber. -/
@[simp]
theorem gradedNativeCycleOperator_point
    (K : FiniteClosedCorrespondence V)
    (p q : Nat)
    (x : CodimensionPoint V.X p) :
    K.gradedNativeCycleOperator p q (codimensionPointCycle V.X p x) =
      K.gradedNativePointImage q x := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  change
    realizeFiniteCodimensionPresentation V.X q
      (K.gradedPresentationOperator p q
        (presentationOfNativeCycle V.X p
          (codimensionPointCycle V.X p x))) =
      realizeFiniteCodimensionPresentation V.X q
        (K.gradedTransition q x)
  have hpresentation :
      presentationOfNativeCycle V.X p
          (codimensionPointCycle V.X p x) =
        Finsupp.single x 1 := by
    have h := presentation_realizeFiniteCodimensionPresentation
      V.X p (Finsupp.single x 1)
    simpa using h
  rw [hpresentation, gradedPresentationOperator_single]

/-- Every point-generator image has an explicit finite target presentation. -/
theorem gradedNativeCycleOperator_has_finite_target
    (K : FiniteClosedCorrespondence V)
    (p q : Nat)
    (x : CodimensionPoint V.X p) :
    ∃ φ : FiniteCodimensionPresentation V.X q,
      K.gradedNativeCycleOperator p q (codimensionPointCycle V.X p x) =
        realizeFiniteCodimensionPresentation V.X q φ := by
  exact ⟨K.gradedTransition q x, K.gradedNativeCycleOperator_point p q x⟩

end GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence

namespace GSTClassicalHodgeGradedFiniteClosedCorrespondence

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgePointKernelOperatorLift
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence

/-- Point-generator cycle-class naturality for a genuine graded finite closed
correspondence.  No equation on arbitrary Hodge classes is supplied: the only
semantic input is the cohomological action and its equality on actual point
cycles. -/
structure GradedCorrespondencePointNaturality
    (K : FiniteClosedCorrespondence V)
    (H : HodgeBigradedBettiData V)
    (p q : Nat) where
  cohomologyOperator :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * q)
  point_natural :
    ∀ x : CodimensionPoint V.X p,
      H.cycleClass q (K.gradedNativePointImage q x) =
        cohomologyOperator
          (H.cycleClass p (codimensionPointCycle V.X p x))

namespace GradedCorrespondencePointNaturality

/-- Pointwise naturality extends to the complete native codimension-p cycle
space by compact point normal form and linearity. -/
theorem cycleClass_natural
    {K : FiniteClosedCorrespondence V}
    (N : GradedCorrespondencePointNaturality K H p q) :
    ∀ Z : codimensionCycles V.X p,
      H.cycleClass q (K.gradedNativeCycleOperator p q Z) =
        N.cohomologyOperator (H.cycleClass p Z) := by
  have hzero :
      (H.cycleClass q).comp (K.gradedNativeCycleOperator p q) -
          N.cohomologyOperator.comp (H.cycleClass p) = 0 := by
    apply nativeLinearMap_eq_zero_of_points V p
    intro x
    simp [N.point_natural x]
  have heq :
      (H.cycleClass q).comp (K.gradedNativeCycleOperator p q) =
        N.cohomologyOperator.comp (H.cycleClass p) :=
    sub_eq_zero.mp hzero
  intro Z
  exact LinearMap.congr_fun heq Z

/-- **POINTWISE-TO-GLOBAL GRADED NATURALITY.**
A genuine finite closed correspondence with point-generator naturality
canonically becomes the full graded native/cohomological operator pair used by
the cross-weight defect machinery. -/
noncomputable def toGradedCycleClassOperatorPair
    {K : FiniteClosedCorrespondence V}
    (N : GradedCorrespondencePointNaturality K H p q) :
    GradedCycleClassOperatorPair V H p q where
  cycleOperator := K.gradedNativeCycleOperator p q
  cohomologyOperator := N.cohomologyOperator
  cycleClass_natural := N.cycleClass_natural

/-- The resulting pair uses exactly the geometry-built correspondence operator
on native cycles. -/
@[simp]
theorem toGradedCycleClassOperatorPair_cycleOperator
    {K : FiniteClosedCorrespondence V}
    (N : GradedCorrespondencePointNaturality K H p q) :
    N.toGradedCycleClassOperatorPair.cycleOperator =
      K.gradedNativeCycleOperator p q := by
  rfl

/-- Its cohomological half is exactly the supplied pointwise-natural action. -/
@[simp]
theorem toGradedCycleClassOperatorPair_cohomologyOperator
    {K : FiniteClosedCorrespondence V}
    (N : GradedCorrespondencePointNaturality K H p q) :
    N.toGradedCycleClassOperatorPair.cohomologyOperator =
      N.cohomologyOperator := by
  rfl

end GradedCorrespondencePointNaturality

#check GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence.gradedTransition
#check GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence.gradedNativePointImage
#check GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence.gradedPresentationOperator
#check GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence.gradedNativeCycleOperator
#check GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence.gradedNativeCycleOperator_point
#check GradedCorrespondencePointNaturality
#check GradedCorrespondencePointNaturality.cycleClass_natural
#check GradedCorrespondencePointNaturality.toGradedCycleClassOperatorPair

#print axioms GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence.gradedNativeCycleOperator_point
#print axioms GradedCorrespondencePointNaturality.cycleClass_natural
#print axioms GradedCorrespondencePointNaturality.toGradedCycleClassOperatorPair

end GSTClassicalHodgeGradedFiniteClosedCorrespondence
