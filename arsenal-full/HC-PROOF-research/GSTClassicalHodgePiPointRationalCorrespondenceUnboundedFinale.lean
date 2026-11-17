import GSTClassicalHodgeProjectivePointOmniverseSource
import GSTClassicalHodgeRationalCorrespondenceOperatorSynthesis
import GSTClassicalHodgePiUnboundedOmniverseCrown
import GSTClassicalHodgePiOmniverseCanonicalSupportSpectral
import GSTClassicalHodgeExactClayStatement

/-!
# GST CLASSICAL HODGE — PI POINT / RATIONAL CORRESPONDENCE / UNBOUNDED FINALE

This is the correspondence-strengthened form of the point-source omniverse
attack.

The source is one genuine codimension-p projective point.  Projective degree
proves its Betti cycle class is nonzero, so no native-mass bridge or conserved
charge is required.

The target operator is not restricted to a scheme self-map.  It is a finite
rational sum of genuine closed correspondences in X x_C X.  Primitive
pointwise realization gives an exact cycle-class-natural operator pair for each
summand, and `rationalPair` synthesizes the rational combination.  If that
actual correspondence action performs the GST source hit, its normalized
native image is an actual target-basis cycle.

After algebraicity is established by correspondence geometry, the target is
placed in all three GST sectors, exact N-cohomology, and every finite level of
the unbounded higher-causal cosmos.  Thus no abstract omniverse edge is used as
an algebraicity axiom.
-/

set_option maxHeartbeats 260000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgePiPointRationalCorrespondenceUnboundedFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeProjectivePointOmniverseSource
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator
open GSTClassicalHodgeRationalCorrespondenceOperatorSynthesis
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgeOmniverseStrictEventStability
open GSTClassicalHodgePiOmniverseBranchSynthesis
open GSTClassicalHodgePiOmniverseCanonicalSupportSpectral
open GSTClassicalHodgePiUnboundedOmniverseCrown
open GSTClassicalHodgeExactClayStatement
open GSTGraphV2OmniversalCore

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Canonical live source coordinate selected from the nonzero projective-point
Hodge class. -/
noncomputable def pointSourceIndex
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    ClassicalHodgeBasisIndex V H p :=
  (chosenLiveSource (pointHodgeSource G p x)
    (pointHodgeSource_ne_zero G D p x)).1

/-- The selected coefficient of the point source is nonzero. -/
theorem pointSourceCoefficient_ne_zero
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    (classicalHodgeBasis V H p).repr (pointHodgeSource G p x)
      (pointSourceIndex G D p x) ≠ 0 := by
  exact chosenLiveSource_coefficient_ne_zero
    (pointHodgeSource G p x) (pointHodgeSource_ne_zero G D p x)

/-- Normalize the native action of a genuine rational correspondence on the
unit point source. -/
noncomputable def pointTargetCycleOfRationalCorrespondence
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (j : ClassicalHodgeBasisIndex V H p)
    (A : RationalClosedCorrespondenceCycle V)
    (T : ∀ K : FiniteClosedCorrespondence V,
      RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
        RationalSingularCohomology H.analytification (2 * p))
    (hT : ∀ K : FiniteClosedCorrespondence V,
      K.RealizesAmbientOnPoints (H := H) (T K)) :
    codimensionCycles V.X p :=
  let c := (classicalHodgeBasis V H p).repr
    (pointHodgeSource G p x) (pointSourceIndex G D p x)
  c⁻¹ • (rationalPair A T hT).cycleOperator
    (codimensionPointCycle V.X p x)

/-- If the actual rational correspondence performs the GST rank-one source hit,
its normalized native image is exactly the requested Hodge basis vector. -/
theorem pointTargetCycleOfRationalCorrespondence_spec
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (j : ClassicalHodgeBasisIndex V H p)
    (A : RationalClosedCorrespondenceCycle V)
    (T : ∀ K : FiniteClosedCorrespondence V,
      RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
        RationalSingularCohomology H.analytification (2 * p))
    (hT : ∀ K : FiniteClosedCorrespondence V,
      K.RealizesAmbientOnPoints (H := H) (T K))
    (hA :
      (rationalPair A T hT).cohomologyOperator (pointHodgeSource G p x).1 =
        (classicalHodgeBasis V H p).repr (pointHodgeSource G p x)
            (pointSourceIndex G D p x) •
          (classicalHodgeBasis V H p j).1) :
    H.cycleClass p
      (pointTargetCycleOfRationalCorrespondence G D p x j A T hT) =
        (classicalHodgeBasis V H p j).1 := by
  let c : ℚ := (classicalHodgeBasis V H p).repr
    (pointHodgeSource G p x) (pointSourceIndex G D p x)
  have hc : c ≠ 0 := pointSourceCoefficient_ne_zero G D p x
  have hnat := (rationalPair A T hT).cycleClass_cycleOperator
    (codimensionPointCycle V.X p x)
  change H.cycleClass p (codimensionPointCycle V.X p x) =
    (pointHodgeSource G p x).1 at rfl
  rw [show H.cycleClass p (codimensionPointCycle V.X p x) =
      (pointHodgeSource G p x).1 by rfl, hA] at hnat
  unfold pointTargetCycleOfRationalCorrespondence
  rw [LinearMap.map_smul, hnat]
  simp [c, hc]

/-- The unnormalized target branch is already algebraic before entering the GST
causal cosmos. -/
theorem pointCorrespondenceMatrixUnit_algebraic
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (j : ClassicalHodgeBasisIndex V H p)
    (A : RationalClosedCorrespondenceCycle V)
    (T : ∀ K : FiniteClosedCorrespondence V,
      RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
        RationalSingularCohomology H.analytification (2 * p))
    (hT : ∀ K : FiniteClosedCorrespondence V,
      K.RealizesAmbientOnPoints (H := H) (T K))
    (hA :
      (rationalPair A T hT).cohomologyOperator (pointHodgeSource G p x).1 =
        (classicalHodgeBasis V H p).repr (pointHodgeSource G p x)
            (pointSourceIndex G D p x) •
          (classicalHodgeBasis V H p j).1) :
    (hodgeMatrixUnit (pointSourceIndex G D p x) j
      (pointHodgeSource G p x)).1 ∈ LinearMap.range (H.cycleClass p) := by
  let c := (classicalHodgeBasis V H p).repr
    (pointHodgeSource G p x) (pointSourceIndex G D p x)
  have hbasis :
      (classicalHodgeBasis V H p j).1 ∈ LinearMap.range (H.cycleClass p) := by
    exact ⟨pointTargetCycleOfRationalCorrespondence G D p x j A T hT,
      pointTargetCycleOfRationalCorrespondence_spec
        G D p x j A T hT hA⟩
  have hscaled := (LinearMap.range (H.cycleClass p)).smul_mem c hbasis
  simpa [c, hodgeMatrixUnit_apply, hodgeCoordinate, pointSourceIndex] using hscaled

/-- Correspondence algebraicity plus the full three-sector/unbounded GST
certificate for one target direction. -/
theorem pointCorrespondenceTarget_allSectors_unbounded
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (A : ∀ j : ClassicalHodgeBasisIndex V H p,
      RationalClosedCorrespondenceCycle V)
    (T : ∀ j : ClassicalHodgeBasisIndex V H p,
      ∀ K : FiniteClosedCorrespondence V,
        RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
          RationalSingularCohomology H.analytification (2 * p))
    (hT : ∀ j : ClassicalHodgeBasisIndex V H p,
      ∀ K : FiniteClosedCorrespondence V,
        K.RealizesAmbientOnPoints (H := H) (T j K))
    (hA : ∀ j : ClassicalHodgeBasisIndex V H p,
      (rationalPair (A j) (T j) (hT j)).cohomologyOperator
          (pointHodgeSource G p x).1 =
        (classicalHodgeBasis V H p).repr (pointHodgeSource G p x)
            (pointSourceIndex G D p x) •
          (classicalHodgeBasis V H p j).1)
    (s : Sector)
    (j : ClassicalHodgeBasisIndex V H p) :
    let target : HodgeBranchNode (V := V) (H := H) (p := p) :=
      ⟨s, hodgeMatrixUnit (pointSourceIndex G D p x) j
        (pointHodgeSource G p x)⟩
    AlgebraicBranchNode (V := V) (H := H) (p := p) target
      ∧ (hodgeBranchGraph (V := V) (H := H) (p := p)).Event
          ⟨Sector.gstPlus, pointHodgeSource G p x⟩ target
      ∧ ∀ n : Nat,
        ∃ c : (hodgeHigherCausalCosmos (V := V) (H := H) (p := p)).Cell n,
          c = target ∧ AlgebraicBranchNode (V := V) (H := H) (p := p) c := by
  dsimp
  have hAlg := pointCorrespondenceMatrixUnit_algebraic
    G D p x j (A j) (T j) (hT j) (hA j)
  have hEvent :
      (hodgeBranchGraph (V := V) (H := H) (p := p)).Event
        ⟨Sector.gstPlus, pointHodgeSource G p x⟩
        ⟨s, hodgeMatrixUnit (pointSourceIndex G D p x) j
          (pointHodgeSource G p x)⟩ :=
    HodgeBranchEvent.matrixUnit (pointHodgeSource G p x)
      (pointSourceIndex G D p x) j s
  exact ⟨hAlg, hEvent,
    algebraicBranch_has_unbounded_higher_certificate
      (V := V) (H := H) (p := p)
      ⟨s, hodgeMatrixUnit (pointSourceIndex G D p x) j
        (pointHodgeSource G p x)⟩ hAlg⟩

/-- Finite rational collapse of an arbitrary Hodge class from the genuine
correspondence target cycles. -/
noncomputable def correspondenceCollapseCycle
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (A : ∀ j : ClassicalHodgeBasisIndex V H p,
      RationalClosedCorrespondenceCycle V)
    (T : ∀ j : ClassicalHodgeBasisIndex V H p,
      ∀ K : FiniteClosedCorrespondence V,
        RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
          RationalSingularCohomology H.analytification (2 * p))
    (hT : ∀ j : ClassicalHodgeBasisIndex V H p,
      ∀ K : FiniteClosedCorrespondence V,
        K.RealizesAmbientOnPoints (H := H) (T j K))
    (alpha : ClassicalHodgeFiber V H p) :
    codimensionCycles V.X p :=
  ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
    ((classicalHodgeBasis V H p).repr alpha j) •
      pointTargetCycleOfRationalCorrespondence
        G D p x j (A j) (T j) (hT j)

/-- Exact collapse identity, assuming the rational correspondence family
performs the GST source hit on every basis direction. -/
theorem correspondenceCollapseCycle_spec
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (A : ∀ j : ClassicalHodgeBasisIndex V H p,
      RationalClosedCorrespondenceCycle V)
    (T : ∀ j : ClassicalHodgeBasisIndex V H p,
      ∀ K : FiniteClosedCorrespondence V,
        RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
          RationalSingularCohomology H.analytification (2 * p))
    (hT : ∀ j : ClassicalHodgeBasisIndex V H p,
      ∀ K : FiniteClosedCorrespondence V,
        K.RealizesAmbientOnPoints (H := H) (T j K))
    (hA : ∀ j : ClassicalHodgeBasisIndex V H p,
      (rationalPair (A j) (T j) (hT j)).cohomologyOperator
          (pointHodgeSource G p x).1 =
        (classicalHodgeBasis V H p).repr (pointHodgeSource G p x)
            (pointSourceIndex G D p x) •
          (classicalHodgeBasis V H p j).1)
    (alpha : ClassicalHodgeFiber V H p) :
    H.cycleClass p (correspondenceCollapseCycle G D p x A T hT alpha) = alpha.1 := by
  rw [correspondenceCollapseCycle, map_sum]
  simp only [LinearMap.map_smul]
  rw [show alpha =
      ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
        ((classicalHodgeBasis V H p).repr alpha j) •
          classicalHodgeBasis V H p j by
    exact (classicalHodgeBasis V H p).sum_repr alpha]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pointTargetCycleOfRationalCorrespondence_spec
    G D p x j (A j) (T j) (hT j) (hA j)]

/-- **PI-WIDE POINT / RATIONAL-CORRESPONDENCE / FULL OMNIVERSE LANDING.** -/
theorem bigradedBettiHodge_of_point_rationalCorrespondence_omniverse
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (hpoint : ∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥ →
        Nonempty (CodimensionPoint V.X p))
    (A : ∀ p : Nat,
      ∀ hp : rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        RationalClosedCorrespondenceCycle V)
    (T : ∀ p : Nat,
      ∀ hp : rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥,
      ∀ j : ClassicalHodgeBasisIndex V H p,
      ∀ K : FiniteClosedCorrespondence V,
        RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
          RationalSingularCohomology H.analytification (2 * p))
    (hT : ∀ p : Nat,
      ∀ hp : rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥,
      ∀ j : ClassicalHodgeBasisIndex V H p,
      ∀ K : FiniteClosedCorrespondence V,
        K.RealizesAmbientOnPoints (H := H) (T p hp j K))
    (hA : ∀ p : Nat,
      ∀ hp : rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥,
      ∀ j : ClassicalHodgeBasisIndex V H p,
      let x := Classical.choice (hpoint p hp)
      (rationalPair (A p hp j) (T p hp j) (hT p hp j)).cohomologyOperator
          (pointHodgeSource G p x).1 =
        (classicalHodgeBasis V H p).repr (pointHodgeSource G p x)
            (pointSourceIndex G D p x) •
          (classicalHodgeBasis V H p j).1) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  by_cases hp : rationalHodgeSubspace (H.hodgeBigrading p) = ⊥
  · have hzero : alpha = 0 := by
      have : alpha ∈
          (⊥ : Submodule ℚ
            (RationalSingularCohomology H.analytification (2 * p))) := by
        simpa [hp] using halpha
      simpa using this
    subst alpha
    exact LinearMap.zero_mem _
  · let x := Classical.choice (hpoint p hp)
    let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
    exact ⟨correspondenceCollapseCycle G D p x
        (A p hp) (T p hp) (hT p hp) alphaH,
      correspondenceCollapseCycle_spec G D p x
        (A p hp) (T p hp) (hT p hp) (hA p hp) alphaH⟩

/-- Exact Clay finite-rational-combination form of the same correspondence
landing. -/
theorem everyHodgeClassIsFiniteRationalCombination_of_pointCorrespondences
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (hpoint : ∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥ →
        Nonempty (CodimensionPoint V.X p))
    (A : ∀ p : Nat,
      ∀ hp : rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        RationalClosedCorrespondenceCycle V)
    (T : ∀ p : Nat,
      ∀ hp : rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥,
      ∀ j : ClassicalHodgeBasisIndex V H p,
      ∀ K : FiniteClosedCorrespondence V,
        RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
          RationalSingularCohomology H.analytification (2 * p))
    (hT : ∀ p : Nat,
      ∀ hp : rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥,
      ∀ j : ClassicalHodgeBasisIndex V H p,
      ∀ K : FiniteClosedCorrespondence V,
        K.RealizesAmbientOnPoints (H := H) (T p hp j K))
    (hA : ∀ p : Nat,
      ∀ hp : rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥,
      ∀ j : ClassicalHodgeBasisIndex V H p,
      let x := Classical.choice (hpoint p hp)
      (rationalPair (A p hp j) (T p hp j) (hT p hp j)).cohomologyOperator
          (pointHodgeSource G p x).1 =
        (classicalHodgeBasis V H p).repr (pointHodgeSource G p x)
            (pointSourceIndex G D p x) •
          (classicalHodgeBasis V H p j).1) :
    EveryHodgeClassIsFiniteRationalCombination H := by
  exact (exact_rational_hodge_conjecture_finite_sum H).1
    (bigradedBettiHodge_of_point_rationalCorrespondence_omniverse
      G D hpoint A T hT hA)

#check pointSourceIndex
#check pointSourceCoefficient_ne_zero
#check pointTargetCycleOfRationalCorrespondence
#check pointTargetCycleOfRationalCorrespondence_spec
#check pointCorrespondenceMatrixUnit_algebraic
#check pointCorrespondenceTarget_allSectors_unbounded
#check correspondenceCollapseCycle
#check correspondenceCollapseCycle_spec
#check bigradedBettiHodge_of_point_rationalCorrespondence_omniverse
#check everyHodgeClassIsFiniteRationalCombination_of_pointCorrespondences

#print axioms pointTargetCycleOfRationalCorrespondence_spec
#print axioms pointCorrespondenceMatrixUnit_algebraic
#print axioms correspondenceCollapseCycle_spec
#print axioms bigradedBettiHodge_of_point_rationalCorrespondence_omniverse
#print axioms everyHodgeClassIsFiniteRationalCombination_of_pointCorrespondences

end GSTClassicalHodgePiPointRationalCorrespondenceUnboundedFinale
