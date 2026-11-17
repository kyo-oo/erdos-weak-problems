import GSTClassicalHodgeProjectivePointOmniverseSource
import GSTClassicalHodgeProjectiveTwoGeneratorExternalization
import GSTClassicalHodgePiUnboundedOmniverseCrown
import GSTClassicalHodgePiOmniverseCanonicalSupportSpectral

/-!
# GST CLASSICAL HODGE — PI POINT / TWO-GENERATOR / UNBOUNDED FINALE

This route removes BOTH of the broad interfaces used by the earlier global
spine crown:

* no native-mass/conserved-charge bridge;
* no universal strict materialization of every abstract GST branch event.

In a live weight, one genuine codimension-p projective point is enough.
Projective degree proves that its cycle class is nonzero.  The genuine
cycle-class spine makes it a Hodge state.  From one live coordinate of that
state, two actual projective primitive maps generate the exact finite GST
rank-one word to every requested Hodge basis direction.  The synchronized word
therefore constructs genuine native target cycles.

The resulting target directions are simultaneously placed in all three GST
sectors, the exact N-cohomology packet, and the unbounded higher-causal cosmos.
No algebraicity is inferred merely from an abstract branch: it is established
first by the actual projective word and only then carried as semantic data into
the omniverse certificate.
-/

set_option maxHeartbeats 240000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgePiPointTwoGeneratorUnboundedFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeProjectivePointOmniverseSource
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeProjectiveTwoGeneratorExternalization
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgeOmniverseStrictEventStability
open GSTClassicalHodgePiOmniverseBranchSynthesis
open GSTClassicalHodgePiOmniverseCanonicalSupportSpectral
open GSTClassicalHodgePiUnboundedOmniverseCrown
open GSTGraphV2OmniversalCore

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- One genuine projective point gives a synchronized nonzero algebraic orbit
seed, with nonvanishing proved by projective degree rather than native mass. -/
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

/-- Two genuine projective primitives from the point seed's selected live
coordinate produce an actual native cycle for an arbitrary target sheet. -/
noncomputable def pointTargetCycle
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (j : ClassicalHodgeBasisIndex V H p)
    (R : ProjectiveTwoGenerator (V := V) (H := H)
      (pointOrbitSeed G D p x).sourceIndex j) :
    codimensionCycles V.X p :=
  (pointOrbitSeed G D p x).targetCycle j R.toGeometryFirst

/-- Exact synchronization of the point-source projective word. -/
theorem pointTargetCycle_spec
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (j : ClassicalHodgeBasisIndex V H p)
    (R : ProjectiveTwoGenerator (V := V) (H := H)
      (pointOrbitSeed G D p x).sourceIndex j) :
    H.cycleClass p (pointTargetCycle G D p x j R) =
      (classicalHodgeBasis V H p j).1 := by
  exact (pointOrbitSeed G D p x).targetCycle_spec j R.toGeometryFirst

/-- The corresponding GST matrix-unit branch is algebraic before entering the
unbounded branch cosmos. -/
theorem pointMatrixUnitBranch_algebraic
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (j : ClassicalHodgeBasisIndex V H p)
    (R : ProjectiveTwoGenerator (V := V) (H := H)
      (pointOrbitSeed G D p x).sourceIndex j) :
    (hodgeMatrixUnit
      (pointOrbitSeed G D p x).sourceIndex j
      (pointOrbitSeed G D p x).hodge).1 ∈
        LinearMap.range (H.cycleClass p) := by
  let S := pointOrbitSeed G D p x
  let c := (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex
  have hbasis :
      (classicalHodgeBasis V H p j).1 ∈ LinearMap.range (H.cycleClass p) :=
    ⟨pointTargetCycle G D p x j R,
      pointTargetCycle_spec G D p x j R⟩
  have hscaled := (LinearMap.range (H.cycleClass p)).smul_mem c hbasis
  simpa [S, c, hodgeMatrixUnit_apply, hodgeCoordinate] using hscaled

/-- All three GST sectors carry the same geometrically algebraic target branch,
with an algebraic certificate at every higher causal dimension. -/
theorem pointTarget_allSectors_unbounded
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      ProjectiveTwoGenerator (V := V) (H := H)
        (pointOrbitSeed G D p x).sourceIndex j)
    (s : Sector)
    (j : ClassicalHodgeBasisIndex V H p) :
    let target : HodgeBranchNode (V := V) (H := H) (p := p) :=
      ⟨s, hodgeMatrixUnit
        (pointOrbitSeed G D p x).sourceIndex j
        (pointOrbitSeed G D p x).hodge⟩
    AlgebraicBranchNode (V := V) (H := H) (p := p) target
      ∧ (hodgeBranchGraph (V := V) (H := H) (p := p)).Event
          ⟨Sector.gstPlus, (pointOrbitSeed G D p x).hodge⟩ target
      ∧ ∀ n : Nat,
        ∃ c : (hodgeHigherCausalCosmos (V := V) (H := H) (p := p)).Cell n,
          c = target ∧ AlgebraicBranchNode (V := V) (H := H) (p := p) c := by
  dsimp
  let S := pointOrbitSeed G D p x
  have hAlg :
      (hodgeMatrixUnit S.sourceIndex j S.hodge).1 ∈
        LinearMap.range (H.cycleClass p) := by
    simpa [S] using pointMatrixUnitBranch_algebraic G D p x j (R j)
  have hEvent :
      (hodgeBranchGraph (V := V) (H := H) (p := p)).Event
        ⟨Sector.gstPlus, S.hodge⟩
        ⟨s, hodgeMatrixUnit S.sourceIndex j S.hodge⟩ :=
    HodgeBranchEvent.matrixUnit S.hodge S.sourceIndex j s
  exact ⟨hAlg, hEvent,
    algebraicBranch_has_unbounded_higher_certificate
      (V := V) (H := H) (p := p)
      ⟨s, hodgeMatrixUnit S.sourceIndex j S.hodge⟩ hAlg⟩

/-- Finite native collapse of an arbitrary Hodge class from the point source. -/
noncomputable def pointCollapseCycle
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      ProjectiveTwoGenerator (V := V) (H := H)
        (pointOrbitSeed G D p x).sourceIndex j)
    (alpha : ClassicalHodgeFiber V H p) :
    codimensionCycles V.X p :=
  ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
    ((classicalHodgeBasis V H p).repr alpha j) •
      pointTargetCycle G D p x j (R j)

/-- Exact cycle-class identity for the finite point-source collapse. -/
theorem pointCollapseCycle_spec
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      ProjectiveTwoGenerator (V := V) (H := H)
        (pointOrbitSeed G D p x).sourceIndex j)
    (alpha : ClassicalHodgeFiber V H p) :
    H.cycleClass p (pointCollapseCycle G D p x R alpha) = alpha.1 := by
  rw [pointCollapseCycle, map_sum]
  simp only [LinearMap.map_smul]
  rw [show alpha =
      ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
        ((classicalHodgeBasis V H p).repr alpha j) •
          classicalHodgeBasis V H p j by
    exact (classicalHodgeBasis V H p).sum_repr alpha]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pointTargetCycle_spec G D p x j (R j)]

/-- Weight-local complete crown: actual target cycle, exact N-cohomology, and
three-sector unbounded algebraic target branches. -/
theorem point_twoGenerator_fullOmniverse_crown
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p depth : Nat)
    (x : CodimensionPoint V.X p)
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      ProjectiveTwoGenerator (V := V) (H := H)
        (pointOrbitSeed G D p x).sourceIndex j)
    (alpha : ClassicalHodgeFiber V H p) :
    (∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha.1)
    ∧ (∃ basis : Fin (liveRank alpha) →
        GSTNCohomology.nCohoClasses depth (liveSupportNShape alpha) 1,
      ∀ i : Fin (liveRank alpha),
        (basis i).1 i = GSTNCohomology.towerWindow depth
          ((liveSupportNShape alpha).channel i) 1)
    ∧ (∀ s : Sector, ∀ j : ClassicalHodgeBasisIndex V H p,
      let target : HodgeBranchNode (V := V) (H := H) (p := p) :=
        ⟨s, hodgeMatrixUnit
          (pointOrbitSeed G D p x).sourceIndex j
          (pointOrbitSeed G D p x).hodge⟩
      AlgebraicBranchNode (V := V) (H := H) (p := p) target
        ∧ (hodgeBranchGraph (V := V) (H := H) (p := p)).Event
            ⟨Sector.gstPlus, (pointOrbitSeed G D p x).hodge⟩ target
        ∧ ∀ n : Nat,
          ∃ c : (hodgeHigherCausalCosmos (V := V) (H := H) (p := p)).Cell n,
            c = target ∧ AlgebraicBranchNode (V := V) (H := H) (p := p) c) := by
  refine ⟨⟨pointCollapseCycle G D p x R alpha,
      pointCollapseCycle_spec G D p x R alpha⟩,
    packet_has_exact_ncohomology depth alpha, ?_⟩
  intro s j
  exact pointTarget_allSectors_unbounded G D p x R s j

/-- **PI-WIDE POINT / PROJECTIVE TWO-GENERATOR / FULL OMNIVERSE FINALE.**
In every live rational Hodge weight, one genuine codimension-p point plus two
actual projective primitives from its selected live coordinate to each target
basis direction suffices for the exact Stage-2G statement.

Compared with the strict-event global crown this removes all-events
materialization.  Compared with the spine-mass crown it removes the native-mass
bridge and its successor-scalar law. -/
theorem bigradedBettiHodge_of_point_projectiveTwoGenerator_omniverse
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (hpoint : ∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥ →
        Nonempty (CodimensionPoint V.X p))
    (R : ∀ p : Nat,
      ∀ hp : rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        ProjectiveTwoGenerator (V := V) (H := H)
          (pointOrbitSeed G D p (Classical.choice (hpoint p hp))).sourceIndex j) :
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
    exact ⟨pointCollapseCycle G D p x (R p hp) alphaH,
      pointCollapseCycle_spec G D p x (R p hp) alphaH⟩

#check pointOrbitSeed
#check pointTargetCycle
#check pointTargetCycle_spec
#check pointMatrixUnitBranch_algebraic
#check pointTarget_allSectors_unbounded
#check pointCollapseCycle
#check pointCollapseCycle_spec
#check point_twoGenerator_fullOmniverse_crown
#check bigradedBettiHodge_of_point_projectiveTwoGenerator_omniverse

#print axioms pointTargetCycle_spec
#print axioms pointMatrixUnitBranch_algebraic
#print axioms pointCollapseCycle_spec
#print axioms point_twoGenerator_fullOmniverse_crown
#print axioms bigradedBettiHodge_of_point_projectiveTwoGenerator_omniverse

end GSTClassicalHodgePiPointTwoGeneratorUnboundedFinale
