import GSTClassicalHodgeOmniverseStrictRelationRayCompiler
import GSTClassicalHodgeGSTDegreeCertifiedSource

/-!
# GST CLASSICAL HODGE — ROOTED STRICT-RELATION FAN

The omniverse branch graph previously admitted two useful but logically
different geometric interfaces:

* a global primitive compiler, assigning a strict-relation packet to every
  primitive event in the entire graph;
* a targetwise strict-relation finale, assigning one direct correspondence to
  every requested Hodge basis direction.

The handwritten GST Graph V2 fan suggests the genuinely weaker intermediate
principle formalized here.

Choose one nonzero algebraic Hodge seed as an apex.  Its canonical live source
coordinate is fixed ONCE.  A target basis direction need not be joined to the
apex by one giant correspondence, and the entire omniverse need not be globally
compiled.  It is enough to exhibit one finite causal ray

  apex = v₀ -> v₁ -> ... -> vₙ = c • e_j

such that every edge of that ray carries a raw strict correspondence relation.
The strict-relation compiler already proves that one such edge preserves the
actual cycle-class range.  Induction therefore propagates algebraicity along
the chosen ray only.  The common apex coefficient `c` is nonzero, so the final
scaled basis vector immediately yields the genuine basis vector.  Doing this
for every target direction closes the whole rational Hodge weight by finite
basis expansion.

Thus the geometric burden is reduced from GLOBAL EVENT MATERIALIZATION to ONE
LOCALLY MATERIALIZED RAY PER TARGET.  This is the formal rooted-fan reading of
the upgraded GST Graph V2 ontology.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeRootedStrictRelationFan

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgePiOmniverseBranchSynthesis
open GSTClassicalHodgeOmniverseStrictRelationRayCompiler
open GSTClassicalHodgeGSTDegreeCertifiedSource
open GSTGraphV2OmniversalCore

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Apex node determined by one genuine nonzero algebraic Hodge seed. -/
def rootedFanApex
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) :
    HodgeBranchNode (V := V) (H := H) (p := p) :=
  ⟨Sector.gstPlus, S.hodge⟩

/-- The j-th endpoint of the rooted fan.  It is the exact GST matrix-unit
image of the fixed live source coordinate of the apex. -/
def rootedFanTarget
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p) :
    HodgeBranchNode (V := V) (H := H) (p := p) :=
  ⟨Sector.gstPlus, hodgeMatrixUnit S.sourceIndex j S.hodge⟩

/-- The canonical live source index of a nonzero orbit seed, bundled as an
actual support index so that it can be reused for EVERY outgoing fan ray. -/
noncomputable def rootedFanSourceSupport
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) :
    HodgeSupportIndex S.hodge := by
  refine ⟨S.sourceIndex, ?_⟩
  apply Finsupp.mem_support_iff.mpr
  simpa [hodgeCoordinate] using S.sourceCoefficient_ne_zero

/-- **ONE FIXED SOURCE DRIVES EVERY GST FAN EDGE.**
The current branch event definition does not require a target-specific source
choice.  The single canonical live source of `S` gives a primitive GST event to
EVERY matrix-unit target. -/
theorem rootedFan_event_to_target
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p) :
    HodgeBranchEvent
      (rootedFanApex S)
      (rootedFanTarget S j) := by
  refine ⟨j, rootedFanSourceSupport S, ?_⟩
  exact (GSTClassicalHodgeAugmentedTargetMatrixUnit.augmentedConcreteHodgeMatrixUnit_eq
    S.hodge j (rootedFanSourceSupport S)).symm

/-- A locally materialized causal ray.  Unlike `PrimitiveStrictRelationCompiler`,
this structure carries strict geometry ONLY on the finitely many edges actually
used by one selected path. -/
inductive StrictRelationRay :
    HodgeBranchNode (V := V) (H := H) (p := p) →
      HodgeBranchNode (V := V) (H := H) (p := p) → Type
  | nil (u) : StrictRelationRay u u
  | cons {u v w}
      (event : HodgeBranchEvent u v)
      (relation : StrictRelationEdgePacket u v)
      (tail : StrictRelationRay v w) :
      StrictRelationRay u w

namespace StrictRelationRay

/-- Forget the local correspondence certificates and retain the underlying GST
Graph V2 causal path. -/
def toPath :
    {u v : HodgeBranchNode (V := V) (H := H) (p := p)} →
      StrictRelationRay u v →
      OmniversalGraph.Path
        (hodgeBranchGraph (V := V) (H := H) (p := p)) u v
  | _, _, .nil u => OmniversalGraph.Path.nil u
  | _, _, .cons event _ tail =>
      OmniversalGraph.Path.cons event tail.toPath

/-- Every locally materialized ray is genuine ordinary graph reachability. -/
theorem reachable
    {u v : HodgeBranchNode (V := V) (H := H) (p := p)}
    (r : StrictRelationRay u v) :
    OmniversalGraph.Reachable
      (hodgeBranchGraph (V := V) (H := H) (p := p)) u v :=
  ⟨r.toPath⟩

/-- **PATH-LOCAL STRICT RELATIONS PRESERVE ALGEBRAICITY.**
No global compiler is used: only the raw relation packets attached to this one
finite ray are consumed. -/
theorem preserves_algebraic
    {u v : HodgeBranchNode (V := V) (H := H) (p := p)}
    (r : StrictRelationRay u v) :
    AlgebraicBranchNode (V := V) (H := H) (p := p) u →
      AlgebraicBranchNode (V := V) (H := H) (p := p) v := by
  induction r with
  | nil u =>
      exact fun hu => hu
  | @cons u v w event relation tail ih =>
      intro hu
      have hv : AlgebraicBranchNode (V := V) (H := H) (p := p) v :=
        exprMaterializesBranch_preserves_range
          relation.expression_materializes hu
      exact ih hv

end StrictRelationRay

/-- A rooted strict-relation fan asks for exactly ONE locally materialized ray
from the algebraic apex to each basis target.  It does not ask for geometry on
unused omniverse edges. -/
structure RootedStrictRelationFan
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) where
  ray : ∀ j : ClassicalHodgeBasisIndex V H p,
    StrictRelationRay (rootedFanApex S) (rootedFanTarget S j)

/-- Direct one-edge packets are a special case of the rooted-ray interface.
This also records that the same canonical live source is used for every target. -/
noncomputable def RootedStrictRelationFan.ofDirect
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      StrictRelationEdgePacket (rootedFanApex S) (rootedFanTarget S j)) :
    RootedStrictRelationFan S where
  ray := fun j =>
    StrictRelationRay.cons
      (rootedFan_event_to_target S j)
      (R j)
      (StrictRelationRay.nil (rootedFanTarget S j))

/-- The apex is algebraic by construction of `NativeHodgeOrbitSeed`; this is
not an extra graph assumption. -/
theorem rootedFanApex_algebraic
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) :
    AlgebraicBranchNode (V := V) (H := H) (p := p)
      (rootedFanApex S) := by
  unfold AlgebraicBranchNode rootedFanApex
  exact ⟨S.cycle, S.class_eq⟩

/-- Every scaled endpoint `c • e_j` of a rooted strict-relation fan lies in the
actual cycle-class range. -/
theorem rootedFanTarget_algebraic
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (F : RootedStrictRelationFan S)
    (j : ClassicalHodgeBasisIndex V H p) :
    AlgebraicBranchNode (V := V) (H := H) (p := p)
      (rootedFanTarget S j) :=
  (F.ray j).preserves_algebraic (rootedFanApex_algebraic S)

/-- **ROOTED RAY -> GENUINE BASIS CYCLE.**
The fan endpoint is the common nonzero source coefficient times the j-th basis
vector.  Inverting that one coefficient turns path-local algebraicity into
algebraicity of the genuine target basis vector. -/
theorem basis_mem_cycleClass_range_of_rootedFan
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (F : RootedStrictRelationFan S)
    (j : ClassicalHodgeBasisIndex V H p) :
    (classicalHodgeBasis V H p j).1 ∈
      LinearMap.range (H.cycleClass p) := by
  let c : ℚ := (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex
  have hc : c ≠ 0 := S.sourceCoefficient_ne_zero
  have htarget := rootedFanTarget_algebraic S F j
  unfold AlgebraicBranchNode rootedFanTarget at htarget
  have hscaled :
      c • (classicalHodgeBasis V H p j).1 ∈
        LinearMap.range (H.cycleClass p) := by
    simpa [hodgeMatrixUnit_apply, hodgeCoordinate, c] using htarget
  have hinv :=
    (LinearMap.range (H.cycleClass p)).smul_mem c⁻¹ hscaled
  simpa [smul_smul, c, hc] using hinv

/-- **ROOTED STRICT-RELATION FAN CLOSES THE WHOLE HODGE WEIGHT.**
One algebraic apex plus one locally materialized ray to each basis direction is
sufficient.  No global primitive compiler and no direct apex-target
correspondence family is required. -/
theorem hodge_weight_of_rootedStrictRelationFan
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (F : RootedStrictRelationFan S) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  intro alpha halpha
  let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  have hbasis : ∀ j : ClassicalHodgeBasisIndex V H p,
      (classicalHodgeBasis V H p j).1 ∈
        LinearMap.range (H.cycleClass p) :=
    fun j => basis_mem_cycleClass_range_of_rootedFan S F j
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

/-- Degree-certified specialization: the projective-degree seed supplies the
nonzero algebraic apex, after which ONLY targetwise local strict-relation rays
remain. -/
abbrev DegreeCertifiedRootedStrictRelationFan
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (D : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H)
    (q : Nat)
    (x : GSTGeometricRealizationStage2D.CodimensionPoint V.X q)
    (hlive : GSTClassicalHodgeSingleExactSuccessorSurvival.ProjectivelyLiveSource
      V.projective.n (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (GSTClassicalHodgePrincipalCutSuccessorOperator.ambientSuccessorPoint
          V x.1
          (GSTClassicalHodgePointClosureRelativeCut.relativeHeightOneSeparatorSuccessor
            V x.1 hlive)) = q + 1) :=
  RootedStrictRelationFan
    (degreeCertifiedSuccessorSeed G D q x hlive hExact)

/-- The degree-certified apex plus one local relation ray per target closes the
entire successor Hodge weight. -/
theorem hodge_weight_of_degreeCertifiedRootedFan
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (D : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H)
    (q : Nat)
    (x : GSTGeometricRealizationStage2D.CodimensionPoint V.X q)
    (hlive : GSTClassicalHodgeSingleExactSuccessorSurvival.ProjectivelyLiveSource
      V.projective.n (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (GSTClassicalHodgePrincipalCutSuccessorOperator.ambientSuccessorPoint
          V x.1
          (GSTClassicalHodgePointClosureRelativeCut.relativeHeightOneSeparatorSuccessor
            V x.1 hlive)) = q + 1)
    (F : DegreeCertifiedRootedStrictRelationFan G D q x hlive hExact) :
    rationalHodgeSubspace (H.hodgeBigrading (q + 1)) ≤
      LinearMap.range (H.cycleClass (q + 1)) :=
  hodge_weight_of_rootedStrictRelationFan
    (degreeCertifiedSuccessorSeed G D q x hlive hExact) F

#check rootedFanApex
#check rootedFanTarget
#check rootedFanSourceSupport
#check rootedFan_event_to_target
#check StrictRelationRay
#check StrictRelationRay.toPath
#check StrictRelationRay.reachable
#check StrictRelationRay.preserves_algebraic
#check RootedStrictRelationFan
#check RootedStrictRelationFan.ofDirect
#check rootedFanTarget_algebraic
#check basis_mem_cycleClass_range_of_rootedFan
#check hodge_weight_of_rootedStrictRelationFan
#check DegreeCertifiedRootedStrictRelationFan
#check hodge_weight_of_degreeCertifiedRootedFan

#print axioms rootedFan_event_to_target
#print axioms StrictRelationRay.preserves_algebraic
#print axioms basis_mem_cycleClass_range_of_rootedFan
#print axioms hodge_weight_of_rootedStrictRelationFan
#print axioms hodge_weight_of_degreeCertifiedRootedFan

end GSTClassicalHodgeRootedStrictRelationFan
