import GSTClassicalHodgeOmniverseCausalBranchPacket
import GSTClassicalHodgeStrictKernelRangeStability
import GSTClassicalHodgeGSTDegreeCertifiedSource
import GSTClassicalHodgeExactClayStatement

/-!
# GST CLASSICAL HODGE — OMNIVERSE STRICT-EVENT STABILITY

The causal branch packet is purely GST: from one live source it constructs a
path to every target Hodge sheet.  This file supplies the geometric semantic
principle needed to turn that reachability into algebraicity.

A branch event is *strictly materialized* when its action on the source state
is literally the whole-Betti cup/Gysin action of a genuine bi-finite closed
scheme correspondence, with the point-cycle compatibility derived from the
low-level incidence primitives.  `GSTClassicalHodgeStrictKernelRangeStability`
then proves that such an event preserves the true cycle-class range.

The omniversal semantic-closure theorem does the rest: once one nonzero
algebraic Hodge source is present, every causally reachable target branch is
algebraic.  Since the branch graph reaches every basis direction, the complete
Hodge weight lies in the cycle-class range.

The final theorem specializes the source to the already-proved projective-
degree-certified successor seed, so no native-mass bridge is used.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeOmniverseStrictEventStability

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTGraphV2OmniversalCore
open GSTClassicalHodgeAmbientBettiSelfProduct
open GSTClassicalHodgeBettiCupGysinPrimitives
open GSTClassicalHodgeAmbientCorrespondenceKernelAction
open GSTClassicalHodgeAmbientIntersectionFromPrimitives
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeCycleClassIntersectionPrimitives
open GSTClassicalHodgeStrictCorrespondenceTransferFromPrimitives
open GSTClassicalHodgeStrictKernelRangeStability
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGSTDegreeCertifiedSource

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Semantic predicate saying that a Hodge-omniverse node is represented by a
true rational algebraic cycle class on the original projective variety. -/
def AlgebraicNode
    (x : HodgeBranchNode (V := V) (H := H) (p := p)) : Prop :=
  x.state.1 ∈ LinearMap.range (H.cycleClass p)

/-- Low-level geometric materialization of one GST branch event.  No Hodge
surjectivity or target cycle is supplied.  The witness is an actual strict
scheme correspondence, its ambient Betti kernel, genuine point fundamental
classes, and the cup/Gysin/incidence primitive packet from which cycle-class
naturality is already derived.

Only the final equality identifies the already-constructed GST branch state
with that independently constructed geometric kernel action. -/
def StrictlyMaterializedBranch
    (x y : HodgeBranchNode (V := V) (H := H) (p := p)) : Prop :=
  ∃ d : Nat,
  ∃ P : RationalBettiIntersectionPrimitives H.analytification d,
  ∃ K : SchemeBiFiniteClosedCorrespondence V,
  ∃ kappa : MiddleBettiCorrespondenceKernel H.analytification d K,
  ∃ pt : PointBettiClass (V := V) p H.analytification,
    (∀ z : CodimensionPoint V.X p,
      H.cycleClass p (codimensionPointCycle V.X p z) = pt z) ∧
    ∃ I : GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p) P K kappa pt,
      y.state.1 =
        kernelAction H.analytification P kappa (2 * p) x.state.1

/-- Every strictly materialized primitive branch preserves the true algebraic
cycle-class range. -/
theorem strictlyMaterialized_preserves_algebraic
    {x y : HodgeBranchNode (V := V) (H := H) (p := p)}
    (hxy : StrictlyMaterializedBranch x y)
    (hx : AlgebraicNode x) :
    AlgebraicNode y := by
  rcases hxy with ⟨d, P, K, kappa, pt, hpoint, I, haction⟩
  have hstable :=
    kernelAction_range_stable
      (H := H) (d := d) (p := p) P K kappa pt hpoint I
  unfold AlgebraicNode at hx ⊢
  rw [haction]
  exact hstable x.state.1 hx

/-- If every primitive GST branch event admits the strict geometric
materialization above, algebraicity is an event-stable semantic property of
the full omniversal branch graph. -/
theorem algebraic_eventStable_of_strictMaterialization
    (hgeom :
      ∀ {x y : HodgeBranchNode (V := V) (H := H) (p := p)},
        (hodgeBranchGraph (V := V) (H := H) (p := p)).Event x y →
          StrictlyMaterializedBranch x y) :
    OmniversalGraph.EventStable
      (hodgeBranchGraph (V := V) (H := H) (p := p))
      AlgebraicNode := by
  intro x y e hx
  exact strictlyMaterialized_preserves_algebraic (hgeom e) hx

/-- One nonzero algebraic source plus strict materialization of every primitive
causal event makes every genuine Hodge basis sheet algebraic. -/
theorem every_basis_algebraic_of_strictOmniverse
    (a : ClassicalHodgeFiber V H p)
    (ha0 : a ≠ 0)
    (haAlg : a.1 ∈ LinearMap.range (H.cycleClass p))
    (hgeom :
      ∀ {x y : HodgeBranchNode (V := V) (H := H) (p := p)},
        (hodgeBranchGraph (V := V) (H := H) (p := p)).Event x y →
          StrictlyMaterializedBranch x y) :
    ∀ j : ClassicalHodgeBasisIndex V H p,
      (classicalHodgeBasis V H p j).1 ∈
        LinearMap.range (H.cycleClass p) := by
  intro j
  obtain ⟨i, hreach, hi⟩ :=
    reachable_arbitrary_target
      (V := V) (H := H) a ha0 Sector.gstPlus j
  rcases hreach with ⟨path⟩
  have htarget :
      AlgebraicNode
        (V := V) (H := H) (p := p)
        ⟨Sector.gstPlus, hodgeMatrixUnit i.1 j a⟩ := by
    exact OmniversalGraph.Path.preserves
      (hodgeBranchGraph (V := V) (H := H) (p := p))
      (algebraic_eventStable_of_strictMaterialization hgeom)
      path haAlg
  unfold AlgebraicNode at htarget
  rw [hodgeMatrixUnit_apply] at htarget
  have hscaled :=
    (LinearMap.range (H.cycleClass p)).smul_mem
      (hodgeCoordinate i.1 a)⁻¹ htarget
  simpa [smul_smul, hi] using hscaled

/-- **FIXED-WEIGHT OMNIVERSE HODGE CROWN.**
Strict geometric materialization of the causal GST branch events, together
with one nonzero algebraic Hodge source, forces the entire rational Hodge fiber
into the true cycle-class range. -/
theorem hodge_weight_of_strictOmniverse
    (a : ClassicalHodgeFiber V H p)
    (ha0 : a ≠ 0)
    (haAlg : a.1 ∈ LinearMap.range (H.cycleClass p))
    (hgeom :
      ∀ {x y : HodgeBranchNode (V := V) (H := H) (p := p)},
        (hodgeBranchGraph (V := V) (H := H) (p := p)).Event x y →
          StrictlyMaterializedBranch x y) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  intro alpha halpha
  let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  have hbasis :=
    every_basis_algebraic_of_strictOmniverse a ha0 haAlg hgeom
  rw [show alphaH =
      ∑ j ∈ ((classicalHodgeBasis V H p).repr alphaH).support,
        ((classicalHodgeBasis V H p).repr alphaH j) •
          classicalHodgeBasis V H p j by
    exact (classicalHodgeBasis V H p).sum_repr alphaH]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
  apply Submodule.sum_mem
  intro j hj
  exact (LinearMap.range (H.cycleClass p)).smul_mem
    ((classicalHodgeBasis V H p).repr alphaH j) (hbasis j)

/-- **PROJECTIVE-DEGREE + OMNIVERSE CROWN.**
The projective-degree-certified successor supplies the nonzero algebraic source
in weight `p+1`; strict materialization of the GST branch events then forces
that whole Hodge weight to be algebraic. -/
theorem hodge_weight_succ_of_degreeCertified_strictOmniverse
    (G : GeometricCycleClassSpine V H)
    (D : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : GSTClassicalHodgePointClosureRelativeCut.ProjectivelyLiveSource
      V.projective.n (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (GSTClassicalHodgePrincipalCutSuccessorOperator.ambientSuccessorPoint
          V x.1
          (GSTClassicalHodgePointClosureRelativeCut.relativeHeightOneSeparatorSuccessor
            V x.1 hlive)) = p + 1)
    (hgeom :
      ∀ {u v : HodgeBranchNode (V := V) (H := H) (p := p + 1)},
        (hodgeBranchGraph (V := V) (H := H) (p := p + 1)).Event u v →
          StrictlyMaterializedBranch u v) :
    rationalHodgeSubspace (H.hodgeBigrading (p + 1)) ≤
      LinearMap.range (H.cycleClass (p + 1)) := by
  let S := degreeCertifiedSuccessorSeed G D p x hlive hExact
  have hSrange : S.hodge.1 ∈ LinearMap.range (H.cycleClass (p + 1)) :=
    ⟨S.cycle, S.class_eq⟩
  exact hodge_weight_of_strictOmniverse
    S.hodge S.hodge_ne_zero hSrange hgeom

#check AlgebraicNode
#check StrictlyMaterializedBranch
#check strictlyMaterialized_preserves_algebraic
#check algebraic_eventStable_of_strictMaterialization
#check every_basis_algebraic_of_strictOmniverse
#check hodge_weight_of_strictOmniverse
#check hodge_weight_succ_of_degreeCertified_strictOmniverse

#print axioms strictlyMaterialized_preserves_algebraic
#print axioms algebraic_eventStable_of_strictMaterialization
#print axioms every_basis_algebraic_of_strictOmniverse
#print axioms hodge_weight_of_strictOmniverse
#print axioms hodge_weight_succ_of_degreeCertified_strictOmniverse

end GSTClassicalHodgeOmniverseStrictEventStability
