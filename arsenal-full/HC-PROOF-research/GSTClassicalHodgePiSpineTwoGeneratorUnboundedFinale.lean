import GSTClassicalHodgeProjectiveTwoGeneratorExternalization
import GSTClassicalHodgePiUnboundedOmniverseCrown
import GSTClassicalHodgePiOmniverseCanonicalSupportSpectral
import GSTClassicalHodgeThreeUniverseSeedIdentification
import CardinalWorldsV2

/-!
# GST CLASSICAL HODGE — PI SPINE / TWO-GENERATOR / UNBOUNDED FINALE

This file removes the universal strict-materialization premise from the
spine/omniverse route.

A single canonical nonzero algebraic Hodge seed is generated in each weight by
the genuine projective spine.  For every target basis direction we ask only for
the two genuine projective primitive realizations already isolated by
`ProjectiveTwoGeneratorExternalization`.  Their normalized finite GST word is a
cycle-class-natural matrix unit.  Applying that word to the one canonical
spine cycle produces an ACTUAL native target-basis cycle.

The same target direction is simultaneously present in the three-sector GST
branch graph and in every finite level of the unbounded higher-causal cosmos.
Thus algebraicity no longer has to be propagated through every abstract GST
edge: it is manufactured independently by the genuine projective word, while
the omniverse supplies the full branch/cause/recoordination geometry.

This is the intended separation of roles:

  projective geometry  -> actual algebraic target cycle,
  GST two-generator    -> exact rank-one selection,
  Cardinal/3-sector    -> omniversal address semantics,
  N-cohomology         -> exact finite live-support packet,
  higher causality     -> unbounded branch persistence,
  finite Hodge support -> collapse to the original class on the same X.
-/

set_option maxHeartbeats 240000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgePiSpineTwoGeneratorUnboundedFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
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

/-- The canonical spine gives one synchronized nonzero algebraic orbit seed in
every weight once a conserved geometric charge is available. -/
noncomputable def canonicalSpineSeed
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (p : Nat) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := p) :=
  conservedSpineOrbitSeed G D p

/-- Applying the two genuine projective primitives to the canonical spine seed
constructs an actual native cycle for every requested Hodge basis direction. -/
noncomputable def canonicalTargetCycle
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (p : Nat)
    (j : ClassicalHodgeBasisIndex V H p)
    (R : ProjectiveTwoGenerator (V := V) (H := H)
      (canonicalSpineSeed G D p).sourceIndex j) :
    codimensionCycles V.X p :=
  (canonicalSpineSeed G D p).targetCycle j R.toGeometryFirst

/-- Exact cycle-class synchronization of the projective GST word. -/
theorem canonicalTargetCycle_spec
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (p : Nat)
    (j : ClassicalHodgeBasisIndex V H p)
    (R : ProjectiveTwoGenerator (V := V) (H := H)
      (canonicalSpineSeed G D p).sourceIndex j) :
    H.cycleClass p (canonicalTargetCycle G D p j R) =
      (classicalHodgeBasis V H p j).1 := by
  exact (canonicalSpineSeed G D p).targetCycle_spec j R.toGeometryFirst

/-- Hence the unnormalized GST matrix-unit branch itself is algebraic.  Its
coefficient is the canonical live source coefficient selected from the spine. -/
theorem canonicalMatrixUnitBranch_algebraic
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (p : Nat)
    (j : ClassicalHodgeBasisIndex V H p)
    (R : ProjectiveTwoGenerator (V := V) (H := H)
      (canonicalSpineSeed G D p).sourceIndex j) :
    (hodgeMatrixUnit
      (canonicalSpineSeed G D p).sourceIndex j
      (canonicalSpineSeed G D p).hodge).1 ∈
        LinearMap.range (H.cycleClass p) := by
  let S := canonicalSpineSeed G D p
  let c := (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex
  have htarget :
      (classicalHodgeBasis V H p j).1 ∈ LinearMap.range (H.cycleClass p) := by
    exact ⟨canonicalTargetCycle G D p j R,
      canonicalTargetCycle_spec G D p j R⟩
  have hscaled := (LinearMap.range (H.cycleClass p)).smul_mem c htarget
  simpa [S, c, hodgeMatrixUnit_apply, hodgeCoordinate] using hscaled

/-- **PROJECTIVE ALGEBRAICITY + UNBOUNDED OMNIVERSE CERTIFICATE.**
For every one of the three GST sectors and every target basis sheet, the same
canonical spine source gives a branch state which is already an actual cycle
class by the projective two-generator word and persists through every higher
causal dimension. -/
theorem canonicalTarget_allSectors_unbounded
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (R : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        ProjectiveTwoGenerator (V := V) (H := H)
          (canonicalSpineSeed G D p).sourceIndex j)
    (p : Nat)
    (s : Sector)
    (j : ClassicalHodgeBasisIndex V H p) :
    let target : HodgeBranchNode (V := V) (H := H) (p := p) :=
      ⟨s, hodgeMatrixUnit
        (canonicalSpineSeed G D p).sourceIndex j
        (canonicalSpineSeed G D p).hodge⟩
    AlgebraicBranchNode (V := V) (H := H) (p := p) target
      ∧ (hodgeBranchGraph (V := V) (H := H) (p := p)).Event
          ⟨Sector.gstPlus, (canonicalSpineSeed G D p).hodge⟩ target
      ∧ ∀ n : Nat,
        ∃ c : (hodgeHigherCausalCosmos (V := V) (H := H) (p := p)).Cell n,
          c = target ∧
          AlgebraicBranchNode (V := V) (H := H) (p := p) c := by
  dsimp
  let S := canonicalSpineSeed G D p
  have hAlg :
      (hodgeMatrixUnit S.sourceIndex j S.hodge).1 ∈
        LinearMap.range (H.cycleClass p) := by
    simpa [S] using canonicalMatrixUnitBranch_algebraic G D p j (R p j)
  have hEvent :
      (hodgeBranchGraph (V := V) (H := H) (p := p)).Event
        ⟨Sector.gstPlus, S.hodge⟩
        ⟨s, hodgeMatrixUnit S.sourceIndex j S.hodge⟩ := by
    exact HodgeBranchEvent.matrixUnit S.hodge S.sourceIndex j s
  have hHigher := algebraicBranch_has_unbounded_higher_certificate
    (V := V) (H := H) (p := p)
    ⟨s, hodgeMatrixUnit S.sourceIndex j S.hodge⟩ hAlg
  exact ⟨hAlg, hEvent, hHigher⟩

/-- Every arbitrary rational Hodge state collapses to one native cycle by a
finite sum of the actual projective-word target cycles. -/
noncomputable def collapseCycle
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (R : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        ProjectiveTwoGenerator (V := V) (H := H)
          (canonicalSpineSeed G D p).sourceIndex j)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    codimensionCycles V.X p :=
  ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
    ((classicalHodgeBasis V H p).repr alpha j) •
      canonicalTargetCycle G D p j (R p j)

/-- Exact finite rational collapse law on the original projective carrier. -/
theorem collapseCycle_spec
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (R : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        ProjectiveTwoGenerator (V := V) (H := H)
          (canonicalSpineSeed G D p).sourceIndex j)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    H.cycleClass p (collapseCycle G D R p alpha) = alpha.1 := by
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
  rw [canonicalTargetCycle_spec G D p j (R p j)]

/-- The same concrete Hodge state carries the exact GST N-cohomology packet at
arbitrary depth. -/
theorem collapse_exact_ncohomology
    (p depth : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    ∃ basis : Fin (liveRank alpha) →
        GSTNCohomology.nCohoClasses depth (liveSupportNShape alpha) 1,
      ∀ i : Fin (liveRank alpha),
        (basis i).1 i =
          GSTNCohomology.towerWindow depth
            ((liveSupportNShape alpha).channel i) 1 := by
  exact packet_has_exact_ncohomology depth alpha

/-- **PI-WIDE TWO-GENERATOR / FULL GST OMNIVERSE FINALE.**
The global rational Hodge statement is obtained from one canonical nonzero
projective spine source per weight and two genuine projective primitive maps
from its selected live coordinate to each target direction. -/
theorem bigradedBettiHodge_of_spine_projectiveTwoGenerator_omniverse
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (R : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        ProjectiveTwoGenerator (V := V) (H := H)
          (canonicalSpineSeed G D p).sourceIndex j) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  exact ⟨collapseCycle G D R p alphaH, collapseCycle_spec G D R p alphaH⟩

/-- Strong simultaneous crown matching the handwritten Pi route: exact Hodge
landing, finite native collapse, exact N-cohomology at every depth, and
three-sector unbounded higher-causal target certificates all arise from the
same canonical projective spine. -/
theorem pi_spine_twoGenerator_fullOmniverse_crown
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (R : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        ProjectiveTwoGenerator (V := V) (H := H)
          (canonicalSpineSeed G D p).sourceIndex j) :
    BigradedBettiHodgeStatement V H
    ∧ (∀ p depth : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
      ∃ basis : Fin (liveRank alpha) →
          GSTNCohomology.nCohoClasses depth (liveSupportNShape alpha) 1,
        ∀ i : Fin (liveRank alpha),
          (basis i).1 i = GSTNCohomology.towerWindow depth
            ((liveSupportNShape alpha).channel i) 1)
    ∧ (∀ p : Nat, ∀ s : Sector,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        let target : HodgeBranchNode (V := V) (H := H) (p := p) :=
          ⟨s, hodgeMatrixUnit
            (canonicalSpineSeed G D p).sourceIndex j
            (canonicalSpineSeed G D p).hodge⟩
        AlgebraicBranchNode (V := V) (H := H) (p := p) target
          ∧ (hodgeBranchGraph (V := V) (H := H) (p := p)).Event
              ⟨Sector.gstPlus, (canonicalSpineSeed G D p).hodge⟩ target
          ∧ ∀ n : Nat,
            ∃ c : (hodgeHigherCausalCosmos
              (V := V) (H := H) (p := p)).Cell n,
              c = target ∧
              AlgebraicBranchNode (V := V) (H := H) (p := p) c) := by
  refine ⟨bigradedBettiHodge_of_spine_projectiveTwoGenerator_omniverse G D R,
    ?_, ?_⟩
  · intro p depth alpha
    exact collapse_exact_ncohomology p depth alpha
  · intro p s j
    exact canonicalTarget_allSectors_unbounded G D R p s j

#check canonicalSpineSeed
#check canonicalTargetCycle
#check canonicalTargetCycle_spec
#check canonicalMatrixUnitBranch_algebraic
#check canonicalTarget_allSectors_unbounded
#check collapseCycle
#check collapseCycle_spec
#check collapse_exact_ncohomology
#check bigradedBettiHodge_of_spine_projectiveTwoGenerator_omniverse
#check pi_spine_twoGenerator_fullOmniverse_crown

#print axioms canonicalTargetCycle_spec
#print axioms canonicalMatrixUnitBranch_algebraic
#print axioms collapseCycle_spec
#print axioms bigradedBettiHodge_of_spine_projectiveTwoGenerator_omniverse
#print axioms pi_spine_twoGenerator_fullOmniverse_crown

end GSTClassicalHodgePiSpineTwoGeneratorUnboundedFinale
