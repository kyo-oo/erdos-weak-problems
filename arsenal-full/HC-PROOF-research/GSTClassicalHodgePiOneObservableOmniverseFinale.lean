import GSTClassicalHodgePiOmniverseCanonicalSupportSpectral
import GSTClassicalHodgeProjectivePointOmniverseSource
import GSTClassicalHodgePiUnboundedOmniverseCrown

/-!
# GST CLASSICAL HODGE — PI ONE-OBSERVABLE OMNIVERSE FINALE

The handwritten Pi construction is class-local.  A requested rational Hodge
state has finite live support even though the ambient GST omniverse is
unbounded.  Consequently it is unnecessary to externalize every primitive
matrix-unit event in the full Hodge branch graph.

This file makes the smaller geometric target exact.

For one nonzero target state `alpha`:

* its canonical live window is exactly `supp(alpha)`;
* that same finite packet carries the GST N-cohomology channels;
* the Hodge branch graph reaches every target slot and every reached world
  persists through the unbounded higher-causal tower;
* one genuine codimension-p projective point gives an algebraic Hodge source;
* ONE realized closed-correspondence spectral observable on the canonical
  window, provided that source is visible in the active slots, extracts every
  live basis sheet by polynomial functional calculus;
* finite rational reconstruction then produces an actual native
  codimension-p cycle whose class is exactly `alpha`.

Thus the previous all-events strict-materialization requirement is not needed
for the elementwise Pi landing.  The remaining geometric task is sharply
localized to one realized observable on the finite active packet of the class
being reconstructed.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgePiOneObservableOmniverseFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeProjectivePointOmniverseSource
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgePiOmniverseCanonicalSupportSpectral
open GSTClassicalHodgePrincipalCutSpectralFusion
open GSTClassicalHodgeClosedCorrespondenceSpectralAmplifier
open GSTClassicalHodgePiUnboundedOmniverseCrown
open GSTGraphV2OmniversalCore

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- One genuine projective point supplies the synchronized algebraic source
used by the one-observable Pi packet. -/
abbrev PointSource
    (G : GeometricCycleClassSpine V H)
    (x : CodimensionPoint V.X p) : ClassicalHodgeFiber V H p :=
  pointHodgeSource G p x

/-- Visibility of one genuine projective-point Hodge seed on the exact
finite packet of a requested Hodge state. Projective-degree semantics
PROVES the seed is nonzero; no inferred inhabitant or placeholder proof. -/
def PointSourceVisibleOnCanonicalPacket
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (alpha : ClassicalHodgeFiber V H p)
    (x : CodimensionPoint V.X p)
    (R : ClosedCorrespondenceWindowRealization G (canonicalLiveWindow alpha)) :
    Prop :=
  ∀ r : Fin (canonicalLiveWindow alpha).N,
    SeedVisible R
      ({ cycle := codimensionPointCycle V.X p x
         hodge := PointSource G x
         hodge_ne_zero := pointHodgeSource_ne_zero G D p x
         class_eq := rfl } :
        GSTClassicalHodgeSynchronizedDefectOrbit.NativeHodgeOrbitSeed
          (V := V) (H := H) (p := p)) r

/-- Degree-certified synchronized source attached to an arbitrary genuine
codimension-p point. -/
noncomputable def degreePointOrbitSeed
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (x : CodimensionPoint V.X p) :
    GSTClassicalHodgeSynchronizedDefectOrbit.NativeHodgeOrbitSeed
      (V := V) (H := H) (p := p) where
  cycle := codimensionPointCycle V.X p x
  hodge := PointSource G x
  hodge_ne_zero := pointHodgeSource_ne_zero G D p x
  class_eq := rfl

/-- Correct class-local visibility predicate using the degree-certified point
orbit seed. -/
def DegreePointVisibleOnCanonicalPacket
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (alpha : ClassicalHodgeFiber V H p)
    (x : CodimensionPoint V.X p)
    (R : ClosedCorrespondenceWindowRealization G (canonicalLiveWindow alpha)) :
    Prop :=
  ∀ r : Fin (canonicalLiveWindow alpha).N,
    SeedVisible R (degreePointOrbitSeed G D x) r

/-- The repaired source-visibility definition is EXACTLY the established
degree-certified Pi live-packet predicate. The old source name is now
usable without inventing nonzero evidence, and no new semantic
hypothesis was added to the one-observable geometric finale. -/
theorem pointSourceVisible_iff_degreePointVisible
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (alpha : ClassicalHodgeFiber V H p)
    (x : CodimensionPoint V.X p)
    (R : ClosedCorrespondenceWindowRealization G (canonicalLiveWindow alpha)) :
    PointSourceVisibleOnCanonicalPacket G D alpha x R ↔
      DegreePointVisibleOnCanonicalPacket G D alpha x R := by
  rfl

/-- **ONE OBSERVABLE PI TARGET CYCLE.**
A single realized spectral observable on the target's own finite live packet,
together with one degree-certified projective point source visible on those
slots, reconstructs the exact target class as a genuine native cycle. -/
theorem target_cycle_of_oneObservable_pointPacket
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (alpha : ClassicalHodgeFiber V H p)
    (x : CodimensionPoint V.X p)
    (R : ClosedCorrespondenceWindowRealization G (canonicalLiveWindow alpha))
    (hvisible : DegreePointVisibleOnCanonicalPacket G D alpha x R) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 := by
  exact target_cycle_of_canonical_omniverse_spectral_packet
    G alpha R (degreePointOrbitSeed G D x) hvisible

/-- The same packet exposes exactly the N-cohomology channels carried by the
canonical finite support of the requested Hodge class. -/
theorem oneObservablePacket_has_ncohomology
    (depth : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    ∃ basis : Fin (canonicalLiveWindow alpha).N →
        GSTNCohomology.nCohoClasses depth (liveSupportNShape alpha) 1,
      ∀ i : Fin (canonicalLiveWindow alpha).N,
        (basis i).1 i =
          GSTNCohomology.towerWindow depth
            ((liveSupportNShape alpha).channel i) 1 := by
  exact canonicalWindow_has_ncohomology_packet depth alpha

/-- Every primitive target world reached from the target state itself persists
through every finite level of the unbounded GST higher-causal cosmos.  This is
pure omniverse geometry and does not assert algebraicity of the target. -/
theorem targetBranch_has_unbounded_causal_certificate
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (s : Sector)
    (j : ClassicalHodgeBasisIndex V H p) :
    ∃ i : HodgeSupportIndex alpha,
      hodgeCoordinate i.1 alpha ≠ 0 ∧
      (hodgeBranchGraph (V := V) (H := H) (p := p)).Event
        ⟨Sector.gstPlus, alpha⟩
        ⟨s, hodgeMatrixUnit i.1 j alpha⟩
      ∧ ∀ n : Nat,
        ∃ c : (hodgeHigherCausalCosmos
          (V := V) (H := H) (p := p)).Cell n,
          c = ⟨s, hodgeMatrixUnit i.1 j alpha⟩ := by
  obtain ⟨i, hevent, hi⟩ :=
    event_to_arbitrary_target
      (V := V) (H := H) alpha halpha s j
  refine ⟨i, hi, hevent, ?_⟩
  exact branchWorld_has_unbounded_higher_tower
    (V := V) (H := H) (p := p)
    ⟨s, hodgeMatrixUnit i.1 j alpha⟩

/-- **FULL CLASS-LOCAL PI / GST / N-COHOMOLOGY / PROJECTIVE CROWN.**
The handwritten ingredients occur simultaneously for one nonzero target:
finite branch collapse, exact N-cohomology packet, unbounded higher-causal
persistence, and an actual native cycle landing back on the same projective
carrier. -/
theorem oneObservable_pi_omniverse_crown
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (depth : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (x : CodimensionPoint V.X p)
    (R : ClosedCorrespondenceWindowRealization G (canonicalLiveWindow alpha))
    (hvisible : DegreePointVisibleOnCanonicalPacket G D alpha x R) :
    (∃ i : HodgeSupportIndex alpha,
      hodgeCoordinate i.1 alpha ≠ 0 ∧
      alpha =
        ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
          (((classicalHodgeBasis V H p).repr alpha j) *
              (hodgeCoordinate i.1 alpha)⁻¹) •
            hodgeMatrixUnit i.1 j alpha)
    ∧
    (∃ basis : Fin (canonicalLiveWindow alpha).N →
        GSTNCohomology.nCohoClasses depth (liveSupportNShape alpha) 1,
      ∀ i : Fin (canonicalLiveWindow alpha).N,
        (basis i).1 i =
          GSTNCohomology.towerWindow depth
            ((liveSupportNShape alpha).channel i) 1)
    ∧
    (∀ s : Sector, ∀ j : ClassicalHodgeBasisIndex V H p,
      ∃ i : HodgeSupportIndex alpha,
        hodgeCoordinate i.1 alpha ≠ 0 ∧
        (hodgeBranchGraph (V := V) (H := H) (p := p)).Event
          ⟨Sector.gstPlus, alpha⟩
          ⟨s, hodgeMatrixUnit i.1 j alpha⟩
        ∧ ∀ n : Nat,
          ∃ c : (hodgeHigherCausalCosmos
            (V := V) (H := H) (p := p)).Cell n,
            c = ⟨s, hodgeMatrixUnit i.1 j alpha⟩)
    ∧
    (∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1) := by
  refine ⟨branch_collapse_identity alpha halpha,
    oneObservablePacket_has_ncohomology depth alpha, ?_,
    target_cycle_of_oneObservable_pointPacket G D alpha x R hvisible⟩
  intro s j
  exact targetBranch_has_unbounded_causal_certificate alpha halpha s j

/-- **PI-WIDE ONE-OBSERVABLE LANDING.**
For every nonzero rational Hodge state, it is enough to construct one genuine
codimension-p point and one realized spectral observable on that state's own
finite support for which the point source is visible.  No global finite rank,
no all-events strict materialization, no native-mass bridge and no family of
matrix-unit correspondences is assumed. -/
theorem bigradedBettiHodge_of_oneObservablePiPackets
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (packet :
      ∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
        alpha ≠ 0 →
          ∃ x : CodimensionPoint V.X p,
          ∃ R : ClosedCorrespondenceWindowRealization G
            (canonicalLiveWindow alpha),
            DegreePointVisibleOnCanonicalPacket G D alpha x R) :
    BigradedBettiHodgeStatement V H := by
  intro p a ha
  let alpha : ClassicalHodgeFiber V H p := ⟨a, ha⟩
  by_cases hzero : alpha = 0
  · have hazero : a = 0 := congrArg Subtype.val hzero
    subst a
    exact LinearMap.zero_mem _
  · obtain ⟨x, R, hvis⟩ := packet p alpha hzero
    exact target_cycle_of_oneObservable_pointPacket
      G D alpha x R hvis

#check degreePointOrbitSeed
#check DegreePointVisibleOnCanonicalPacket
#check target_cycle_of_oneObservable_pointPacket
#check oneObservablePacket_has_ncohomology
#check targetBranch_has_unbounded_causal_certificate
#check oneObservable_pi_omniverse_crown
#check bigradedBettiHodge_of_oneObservablePiPackets

#print axioms target_cycle_of_oneObservable_pointPacket
#print axioms targetBranch_has_unbounded_causal_certificate
#print axioms oneObservable_pi_omniverse_crown
#print axioms bigradedBettiHodge_of_oneObservablePiPackets

end GSTClassicalHodgePiOneObservableOmniverseFinale
