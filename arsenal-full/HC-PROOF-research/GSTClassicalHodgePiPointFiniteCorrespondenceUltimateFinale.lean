import GSTClassicalHodgeProjectivePointOmniverseSource
import GSTClassicalHodgeFiniteClosedCorrespondence
import GSTClassicalHodgePointwiseNativeCosmicClosure
import GSTClassicalHodgePiUnboundedOmniverseCrown
import GSTClassicalHodgePiOmniverseCanonicalSupportSpectral
import GSTClassicalHodgeExactClayStatement

/-!
# GST CLASSICAL HODGE — PI POINT / FINITE-CORRESPONDENCE ULTIMATE FINALE

This file removes the remaining arbitrary ambient-operator layer from the
point-source correspondence route.

A live weight is represented by one genuine codimension-p projective point.
Projective degree makes its cycle class nonzero, hence it is a genuine
nonzero algebraic Hodge seed.  From that seed the GST support calculus chooses
one live source coordinate.

For each target Hodge basis sheet we now ask only for an ACTUAL finite closed
self-correspondence of X.  Its left fiber is finite, its native point image is
already constructed in `FiniteClosedCorrespondence`, and the only realization
law is the literal generatorwise equation saying that this native point image
has the cycle class of the canonical GST matrix unit on every genuine point
cycle.

No arbitrary cohomology endomorphism, no separately supplied native operator,
no native-mass bridge, no conserved charge, no all-events materialization, and
no target cycle is input.

The pointwise correspondence law is promoted to atomic-span stability by the
existing point-normal-form theorem.  One live algebraic source then generates
every Hodge basis direction, finite support reconstructs every Hodge class,
and the same matrix-unit branches are simultaneously placed in all three GST
sectors and every finite level of the unbounded higher-causal cosmos.
-/

set_option maxHeartbeats 280000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgePiPointFiniteCorrespondenceUltimateFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeProjectivePointOmniverseSource
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgePointwiseNativeCosmicClosure
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgePiOmniverseCanonicalSupportSpectral
open GSTClassicalHodgePiUnboundedOmniverseCrown
open GSTClassicalHodgeExactClayStatement
open GSTGraphV2OmniversalCore

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- A genuine projective point is already a synchronized nonzero algebraic
Hodge orbit seed. -/
noncomputable def pointOrbitSeed
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := p) where
  cycle := codimensionPointCycle V.X p x
  hodge := pointHodgeSource G p x
  hodge_ne_zero := pointHodgeSource_ne_zero G D p x
  class_eq := rfl

/-- The only weight-local externalization packet retained in the final route:
one genuine point source and one actual finite closed correspondence from its
GST-selected live coordinate to each target basis direction. -/
structure PointFiniteCorrespondenceWeightRealization
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat) where
  source : CodimensionPoint V.X p
  correspondence :
    ∀ j : ClassicalHodgeBasisIndex V H p,
      FiniteClosedCorrespondence V
  realizes :
    ∀ j : ClassicalHodgeBasisIndex V H p,
      (correspondence j).RealizesCosmicOnPoints
        (H := H)
        (pointOrbitSeed G D p source).sourceIndex j

namespace PointFiniteCorrespondenceWeightRealization

variable {G : GeometricCycleClassSpine V H}
variable {D : ProjectiveDegreeTraceSemantics V H}
variable {p : Nat}

/-- The point source packaged as the exact synchronized seed consumed by the
GST live-source closure theorem. -/
noncomputable def seed
    (R : PointFiniteCorrespondenceWeightRealization
      (V := V) (H := H) G D p) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := p) :=
  pointOrbitSeed G D p R.source

/-- Every target correspondence gives the minimal pointwise native lift of the
canonical GST matrix unit. -/
theorem cosmicPointLifts
    (R : PointFiniteCorrespondenceWeightRealization
      (V := V) (H := H) G D p)
    (j : ClassicalHodgeBasisIndex V H p) :
    CosmicNativePointLifts
      (V := V) (H := H) (R.seed.sourceIndex) j := by
  exact (R.correspondence j).cosmicNativePointLifts
    R.seed.sourceIndex j (R.realizes j)

/-- The finite-correspondence packet algebraizes every Hodge basis direction. -/
theorem basis_mem_cycleClassRange
    (R : PointFiniteCorrespondenceWeightRealization
      (V := V) (H := H) G D p)
    (j : ClassicalHodgeBasisIndex V H p) :
    (classicalHodgeBasis V H p j).1 ∈
      LinearMap.range (H.cycleClass p) := by
  exact basis_native_cycle_of_liveSource_pointLifts
    R.seed R.cosmicPointLifts j

/-- Explicit native target-basis cycle selected from the proved range
membership. -/
noncomputable def basisCycle
    (R : PointFiniteCorrespondenceWeightRealization
      (V := V) (H := H) G D p)
    (j : ClassicalHodgeBasisIndex V H p) :
    codimensionCycles V.X p :=
  Classical.choose (R.basis_mem_cycleClassRange j)

/-- Exact cycle-class specification of the selected target-basis cycle. -/
theorem basisCycle_spec
    (R : PointFiniteCorrespondenceWeightRealization
      (V := V) (H := H) G D p)
    (j : ClassicalHodgeBasisIndex V H p) :
    H.cycleClass p (R.basisCycle j) =
      (classicalHodgeBasis V H p j).1 :=
  Classical.choose_spec (R.basis_mem_cycleClassRange j)

/-- Finite-support native collapse of one arbitrary rational Hodge state. -/
noncomputable def collapseCycle
    (R : PointFiniteCorrespondenceWeightRealization
      (V := V) (H := H) G D p)
    (alpha : ClassicalHodgeFiber V H p) :
    codimensionCycles V.X p :=
  ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
    ((classicalHodgeBasis V H p).repr alpha j) • R.basisCycle j

/-- **EXACT FINITE CORRESPONDENCE COLLAPSE.**
The native finite-support sum reconstructs the requested Hodge class exactly. -/
theorem collapseCycle_spec
    (R : PointFiniteCorrespondenceWeightRealization
      (V := V) (H := H) G D p)
    (alpha : ClassicalHodgeFiber V H p) :
    H.cycleClass p (R.collapseCycle alpha) = alpha.1 := by
  rw [collapseCycle, map_sum]
  simp only [LinearMap.map_smul]
  rw [show alpha =
      ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
        ((classicalHodgeBasis V H p).repr alpha j) •
          classicalHodgeBasis V H p j by
    exact (classicalHodgeBasis V H p).sum_repr alpha]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
  apply Finset.sum_congr rfl
  intro j hj
  rw [R.basisCycle_spec j]

/-- Fixed-weight exact Hodge landing from the genuine finite-correspondence
packet. -/
theorem hodge_weight
    (R : PointFiniteCorrespondenceWeightRealization
      (V := V) (H := H) G D p) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  exact hodge_weight_of_liveSource_pointLifts R.seed R.cosmicPointLifts

/-- The same genuine correspondence target is an algebraic GST branch in any
of the three sectors and persists, with identical algebraic semantics, through
every finite higher-causal dimension. -/
theorem target_allSectors_unbounded
    (R : PointFiniteCorrespondenceWeightRealization
      (V := V) (H := H) G D p)
    (s : Sector)
    (j : ClassicalHodgeBasisIndex V H p) :
    let target : HodgeBranchNode (V := V) (H := H) (p := p) :=
      ⟨s, hodgeMatrixUnit R.seed.sourceIndex j R.seed.hodge⟩
    AlgebraicBranchNode (V := V) (H := H) (p := p) target
      ∧ (hodgeBranchGraph (V := V) (H := H) (p := p)).Event
          ⟨Sector.gstPlus, R.seed.hodge⟩ target
      ∧ ∀ n : Nat,
        ∃ c : (hodgeHigherCausalCosmos (V := V) (H := H) (p := p)).Cell n,
          c = target ∧ AlgebraicBranchNode (V := V) (H := H) (p := p) c := by
  dsimp
  let c : ℚ :=
    (classicalHodgeBasis V H p).repr R.seed.hodge R.seed.sourceIndex
  have hbasis :
      (classicalHodgeBasis V H p j).1 ∈
        LinearMap.range (H.cycleClass p) :=
    R.basis_mem_cycleClassRange j
  have hscaled :=
    (LinearMap.range (H.cycleClass p)).smul_mem c hbasis
  have hAlg :
      (hodgeMatrixUnit R.seed.sourceIndex j R.seed.hodge).1 ∈
        LinearMap.range (H.cycleClass p) := by
    simpa [c, hodgeMatrixUnit_apply, hodgeCoordinate] using hscaled
  have hEvent :
      (hodgeBranchGraph (V := V) (H := H) (p := p)).Event
        ⟨Sector.gstPlus, R.seed.hodge⟩
        ⟨s, hodgeMatrixUnit R.seed.sourceIndex j R.seed.hodge⟩ :=
    HodgeBranchEvent.matrixUnit R.seed.hodge R.seed.sourceIndex j s
  exact ⟨hAlg, hEvent,
    algebraicBranch_has_unbounded_higher_certificate
      (V := V) (H := H) (p := p)
      ⟨s, hodgeMatrixUnit R.seed.sourceIndex j R.seed.hodge⟩ hAlg⟩

end PointFiniteCorrespondenceWeightRealization

/-- Global geometric realization principle left by the complete reduction.
For each genuinely live Hodge weight, one actual projective point and a family
of actual finite closed point correspondences realize the GST source-to-target
matrix units generatorwise. -/
def PiPointFiniteCorrespondenceRealization
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H) : Prop :=
  ∀ p : Nat,
    rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥ →
      Nonempty
        (PointFiniteCorrespondenceWeightRealization
          (V := V) (H := H) G D p)

/-- **PI-WIDE EXACT STAGE-2G LANDING.**
Once the genuine pointwise finite-correspondence realization principle is
proved, every rational (p,p) Hodge class has an actual native algebraic-cycle
representative. -/
theorem bigradedBettiHodge_of_piPointFiniteCorrespondenceRealization
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (R : PiPointFiniteCorrespondenceRealization
      (V := V) (H := H) G D) :
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
  · let W := Classical.choice (R p hp)
    let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
    exact ⟨W.collapseCycle alphaH, W.collapseCycle_spec alphaH⟩

/-- Exact Clay finite-rational-combination formulation of the same landing. -/
theorem everyHodgeClassIsFiniteRationalCombination_of_piPointFiniteCorrespondences
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (R : PiPointFiniteCorrespondenceRealization
      (V := V) (H := H) G D) :
    EveryHodgeClassIsFiniteRationalCombination H := by
  exact (exact_rational_hodge_conjecture_finite_sum H).1
    (bigradedBettiHodge_of_piPointFiniteCorrespondenceRealization G D R)

/-- Exact N-cohomology packet on the canonical finite live support of any
requested Hodge state.  This is independent of the correspondence
externalization and therefore remains available in the final route. -/
theorem exact_ncohomology_packet
    (depth : Nat)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    ∃ basis : Fin (liveRank alpha) →
        GSTNCohomology.nCohoClasses depth (liveSupportNShape alpha) 1,
      ∀ i : Fin (liveRank alpha),
        (basis i).1 i =
          GSTNCohomology.towerWindow depth
            ((liveSupportNShape alpha).channel i) 1 := by
  simpa using canonicalWindow_has_ncohomology_packet
    (V := V) (H := H) (p := p) depth alpha

/-- **FULL PI / FINITE-CORRESPONDENCE / GST OMNIVERSE CROWN.**
For one live weight realization and one requested Hodge state, the same package
simultaneously supplies an actual native representative, exact N-cohomology,
and algebraic target branches in every sector at every finite causal depth. -/
theorem pi_finiteCorrespondence_unbounded_crown
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p depth : Nat)
    (W : PointFiniteCorrespondenceWeightRealization
      (V := V) (H := H) G D p)
    (alpha : ClassicalHodgeFiber V H p) :
    (∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1)
    ∧ (∃ basis : Fin (liveRank alpha) →
        GSTNCohomology.nCohoClasses depth (liveSupportNShape alpha) 1,
      ∀ i : Fin (liveRank alpha),
        (basis i).1 i =
          GSTNCohomology.towerWindow depth
            ((liveSupportNShape alpha).channel i) 1)
    ∧ (∀ s : Sector, ∀ j : ClassicalHodgeBasisIndex V H p,
      let target : HodgeBranchNode (V := V) (H := H) (p := p) :=
        ⟨s, hodgeMatrixUnit W.seed.sourceIndex j W.seed.hodge⟩
      AlgebraicBranchNode (V := V) (H := H) (p := p) target
        ∧ (hodgeBranchGraph (V := V) (H := H) (p := p)).Event
            ⟨Sector.gstPlus, W.seed.hodge⟩ target
        ∧ ∀ n : Nat,
          ∃ c : (hodgeHigherCausalCosmos
            (V := V) (H := H) (p := p)).Cell n,
            c = target ∧
              AlgebraicBranchNode (V := V) (H := H) (p := p) c) := by
  refine ⟨⟨W.collapseCycle alpha, W.collapseCycle_spec alpha⟩,
    exact_ncohomology_packet depth p alpha, ?_⟩
  intro s j
  exact W.target_allSectors_unbounded s j

#check pointOrbitSeed
#check PointFiniteCorrespondenceWeightRealization
#check PointFiniteCorrespondenceWeightRealization.cosmicPointLifts
#check PointFiniteCorrespondenceWeightRealization.basisCycle
#check PointFiniteCorrespondenceWeightRealization.collapseCycle
#check PointFiniteCorrespondenceWeightRealization.collapseCycle_spec
#check PointFiniteCorrespondenceWeightRealization.hodge_weight
#check PointFiniteCorrespondenceWeightRealization.target_allSectors_unbounded
#check PiPointFiniteCorrespondenceRealization
#check bigradedBettiHodge_of_piPointFiniteCorrespondenceRealization
#check everyHodgeClassIsFiniteRationalCombination_of_piPointFiniteCorrespondences
#check exact_ncohomology_packet
#check pi_finiteCorrespondence_unbounded_crown

#print axioms PointFiniteCorrespondenceWeightRealization.cosmicPointLifts
#print axioms PointFiniteCorrespondenceWeightRealization.collapseCycle_spec
#print axioms PointFiniteCorrespondenceWeightRealization.hodge_weight
#print axioms PointFiniteCorrespondenceWeightRealization.target_allSectors_unbounded
#print axioms bigradedBettiHodge_of_piPointFiniteCorrespondenceRealization
#print axioms everyHodgeClassIsFiniteRationalCombination_of_piPointFiniteCorrespondences
#print axioms pi_finiteCorrespondence_unbounded_crown

end GSTClassicalHodgePiPointFiniteCorrespondenceUltimateFinale
