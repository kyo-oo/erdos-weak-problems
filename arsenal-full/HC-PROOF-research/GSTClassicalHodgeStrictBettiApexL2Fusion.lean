import GSTClassicalHodgeVerticalRayProjectiveApexFinale
import GSTClassicalHodgeOmniverseStrictRelationRayCompiler

/-!
# GST CLASSICAL HODGE — STRICT BETTI / APEX L² FUSION

The branch already has the correct geometry-first primitive:
`StrictRelationEdgePacket`.  Such a packet contains one genuine scheme-bi-finite
correspondence, a nonzero finite right Betti trace, point-cycle compatibility,
and only the intrinsic analytic relation

  l^*(source) = r^*(target).

The strict-relation compiler proves from those data that the trace push-pull is
the unique related target and then compiles the correspondence into the genuine
realized-expression algebra.  This file therefore does NOT introduce a second
copy of that machinery.

Instead it identifies the exact apex-localized `L²` target used by the upgraded
omniverse with the target node of one canonical `StrictRelationEdgePacket`.
A family of these packets immediately manufactures the
`ApexLocalizedL2Realization` consumed by the vertical-ray omniverse finale.
Thus the horizontal input is literally raw strict correspondence geometry; no
ambient `source_action` equation and no duplicate correspondence interface
remain.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeStrictBettiApexL2Fusion

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgePrimitiveArsenalRationalization
open GSTClassicalHodgeTwoSlotLefschetzCollapse
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgePiOmniverseBranchSynthesis
open GSTClassicalHodgeOmniverseLefschetzRayCompiler
open GSTClassicalHodgeOmniverseStrictRelationRayCompiler
open GSTClassicalHodgeVerticalRayProjectiveApexFinale
open GSTClassicalHodgeLiveApexSpineFanFinale
open GSTClassicalHodgeExactVerticalCutRay
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Apex node of the upgraded omniverse. -/
def apexNode
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) :
    HodgeBranchNode (V := V) (H := H) (p := p) :=
  ⟨Sector.gstPlus, S.hodge⟩

/-- The genuine Hodge-fiber state produced by the bare localized two-slot `L²`
firing from the apex's canonical live source coordinate to target `j`. -/
noncomputable def apexL2TargetState
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p) :
    ClassicalHodgeFiber V H p :=
  liftFiniteHodgeOperator (pairBasisIndex S.sourceIndex j)
    (diagonalLefschetzQ 2 2) S.hodge

/-- Target node carrying the unnormalized localized `L²` firing. -/
noncomputable def apexL2TargetNode
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p) :
    HodgeBranchNode (V := V) (H := H) (p := p) :=
  ⟨Sector.gstPlus, apexL2TargetState S j⟩

/-- **ONE STRICT-BETTI APEX L² SPOKE.**
This is exactly the branch's canonical raw strict-relation packet, specialized
to the algebraic apex and its localized `L²` target. -/
abbrev StrictBettiApexL2Spoke
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p) :=
  StrictRelationEdgePacket (apexNode S) (apexL2TargetNode S j)

namespace StrictBettiApexL2Spoke

variable
  {S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)}
  {j : ClassicalHodgeBasisIndex V H p}

/-- The canonical strict-relation compiler turns the raw pullback relation into
the exact realized-expression action required by the apex-localized omniverse.
No separate operator-action field is used here. -/
theorem expression_on_apex
    (R : StrictBettiApexL2Spoke S j) :
    R.expression.cohomologyOperator S.hodge.1 =
      (liftFiniteHodgeOperator (pairBasisIndex S.sourceIndex j)
        (diagonalLefschetzQ 2 2) S.hodge).1 := by
  have h := R.expression_materializes
  unfold ExprMaterializesBranch at h
  simpa [apexNode, apexL2TargetNode, apexL2TargetState] using h.symm

/-- In obstruction language, every strict apex spoke automatically certifies
that the apex lies in the transferable subspace of its genuine correspondence. -/
theorem transferObstruction_apex_eq_zero
    (R : StrictBettiApexL2Spoke S j) :
    GSTClassicalHodgeStrictCorrespondenceBettiObstruction.transferObstruction
      H.analytification R.correspondence (2 * p) S.hodge.1 = 0 := by
  exact
    (GSTClassicalHodgeStrictCorrespondenceBettiObstruction.
      transferObstruction_apply_eq_zero_iff_exists_related
        H.analytification R.correspondence (2 * p) S.hodge.1).2
      ⟨(apexL2TargetState S j).1, by
        simpa [apexNode, apexL2TargetNode, apexL2TargetState] using R.related⟩

end StrictBettiApexL2Spoke

/-- One canonical strict-relation packet to every localized `L²` target sheet. -/
structure StrictBettiApexL2Fan
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) where
  spoke : ∀ j : ClassicalHodgeBasisIndex V H p,
    StrictBettiApexL2Spoke S j

namespace StrictBettiApexL2Fan

/-- Raw strict relations manufacture exactly the apex-localized realized `L²`
receipt consumed by the upgraded omniverse finale. -/
noncomputable def toApexLocalizedL2Realization
    {S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)}
    (F : StrictBettiApexL2Fan S) :
    ApexLocalizedL2Realization S := by
  intro j
  exact ⟨(F.spoke j).expression, (F.spoke j).expression_on_apex⟩

end StrictBettiApexL2Fan

/-- **VERTICAL-RAY + RAW STRICT-BETTI OMNIVERSE FINALE.**

At every live Hodge weight, one exact vertical ray supplies the genuine
algebraic apex.  A family of actual bi-finite strict-relation packets from that
apex to the localized `L²` targets discharges the entire horizontal omniverse.
The historical arbitrary cohomology `source_action` interface is absent. -/
theorem exactHodge_of_verticalRays_and_strictBettiApexL2Fans
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (vertical : ∀ q : Nat, HodgeWeightLive H q →
      ExactVerticalCutRayCertificate V q)
    (fan : ∀ q : Nat, ∀ hlive : HodgeWeightLive H q,
      StrictBettiApexL2Fan
        (canonicalCutOrbitSeed G q
          (cycleClass_projectiveCutTower_ne_zero_of_certificate
            D (vertical q hlive)))) :
    EveryHodgeClassIsRationalAlgebraic H := by
  apply exactHodge_of_verticalRays_and_apexLocalizedL2 G D vertical
  intro q hlive
  exact (fan q hlive).toApexLocalizedL2Realization

#check apexNode
#check apexL2TargetState
#check apexL2TargetNode
#check StrictBettiApexL2Spoke
#check StrictBettiApexL2Spoke.expression_on_apex
#check StrictBettiApexL2Spoke.transferObstruction_apex_eq_zero
#check StrictBettiApexL2Fan
#check StrictBettiApexL2Fan.toApexLocalizedL2Realization
#check exactHodge_of_verticalRays_and_strictBettiApexL2Fans

#print axioms StrictBettiApexL2Spoke.expression_on_apex
#print axioms StrictBettiApexL2Spoke.transferObstruction_apex_eq_zero
#print axioms exactHodge_of_verticalRays_and_strictBettiApexL2Fans

end GSTClassicalHodgeStrictBettiApexL2Fusion
