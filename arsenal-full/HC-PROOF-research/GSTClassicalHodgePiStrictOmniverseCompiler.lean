import GSTClassicalHodgeDegreeCertifiedOmniverseCausalCompiler
import GSTClassicalHodgeOmniverseStrictEventStability
import GSTClassicalHodgeThreeUniverseSeedIdentification
import CardinalWorldsV2

/-!
# GST CLASSICAL HODGE — PI STRICT OMNIVERSE COMPILER

This file splices two previously parallel parts of the Hodge development.

* `OmniverseStrictEventStability` materializes one GST branch by an actual
  bi-finite projective correspondence together with cup/Gysin/incidence
  primitives.
* `DegreeCertifiedOmniverseCausalCompiler` consumes a
  `PrimitiveBranchCompiler`, i.e. a realized-correspondence expression for
  every primitive GST branch.

The bridge is constructive: a strictly materialized branch itself supplies a
`RealizedFiniteClosedCorrespondence`; its whole-Betti operator is the kernel
cup/Gysin action and its point realization is the theorem already derived from
intersection primitives.  Hence no independent `PrimitiveBranchCompiler`
package is needed once strict geometric materialization is available.

This is the geometric splice required by the handwritten Pi/omniverse route:

  projective-degree algebraic source
    -> three-sector GST causal branch
    -> actual strict scheme correspondence
    -> realized correspondence expression
    -> exact source/target GST program
    -> explicit native target cycles
    -> finite rational collapse of an arbitrary Hodge state.

The same degree-certified source sheet is also identified with the native
projective point shadow and the original limitless transfer seed by the
three-universe theorem.
-/

set_option maxHeartbeats 140000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgePiStrictOmniverseCompiler

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgeSingleExactSuccessorSurvival
open GSTClassicalHodgeGSTDegreeCertifiedSource
open GSTClassicalHodgeDegreeCertifiedOmniverseCausalCompiler
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgePiOmniverseBranchSynthesis
open GSTClassicalHodgeOmniverseStrictEventStability
open GSTClassicalHodgeStrictCorrespondenceTransferFromPrimitives
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
open GSTClassicalHodgeAmbientCorrespondenceKernelAction
open GSTClassicalHodgeThreeUniverseSeedIdentification

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- **STRICT BRANCH -> REALIZED EXPRESSION.**

A low-level strictly materialized GST branch already contains enough data to
construct the exact realized-correspondence atom demanded by the omniverse
causal compiler.  In particular, cycle-class naturality is not assumed here:
it is supplied by `realizesAmbientOnPoints`, which was itself proved from the
cup/Gysin/incidence primitive packet. -/
theorem strictBranch_has_realizedExpression
    {u v : HodgeBranchNode (V := V) (H := H) (p := p)}
    (h : StrictlyMaterializedBranch u v) :
    ∃ E : RealizedCorrespondenceExpr V H p,
      ExprMaterializesBranch E u v := by
  rcases h with ⟨d, P, K, kappa, pt, hpoint, I, haction⟩
  let R : RealizedFiniteClosedCorrespondence V H p :=
    { geometry :=
        K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
      cohomologyOperator :=
        kernelAction H.analytification P kappa (2 * p)
      realizes_on_points :=
        realizesAmbientOnPoints P K kappa pt hpoint I }
  refine ⟨RealizedCorrespondenceExpr.atom R, ?_⟩
  change v.state.1 =
    kernelAction H.analytification P kappa (2 * p) u.state.1
  exact haction

/-- **STRICT OMNIVERSE -> PRIMITIVE BRANCH COMPILER.**
The abstract compiler required by the earlier causal file is therefore derived
from actual scheme geometry rather than supplied separately. -/
theorem primitiveBranchCompiler_of_strictMaterialization
    (hgeom :
      ∀ {u v : HodgeBranchNode (V := V) (H := H) (p := p)},
        (hodgeBranchGraph (V := V) (H := H) (p := p)).Event u v →
          StrictlyMaterializedBranch u v) :
    PrimitiveBranchCompiler (V := V) (H := H) (p := p) := by
  intro u v huv
  exact strictBranch_has_realizedExpression (hgeom huv)

/-- The degree-certified source sheet sits literally on the common artery of
all three universes: classical Hodge multiplicity, an actual native
codimension-`p+1` projective point, and the limitless GST transfer seed. -/
theorem degreeCertified_source_threeUniverse_identity
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1) :
    let S := degreeCertifiedSuccessorSeed G D p x hlive hExact
    let y : CodimensionPoint V.X (p + 1) :=
      ⟨ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive), hExact⟩
    GSTClassicalHodgeFiberedTransferCompletion.forgetMultiplicityToGST
        (GSTClassicalHodgeFiberedTransferCompletion.fiberedSheetGenerator
          V H ⟨p + 1, S.sourceIndex⟩) =
      GSTClassicalHodgeNativeTransferAddressIdentification.pureWeightToUniversalAddress
        (GSTClassicalHodgeNativeCycleCosmicShadow.nativeCycleCosmicShadow
          V (p + 1)
          (codimensionPointCycle V.X (p + 1) y))
    ∧ GSTClassicalHodgeNativeTransferAddressIdentification.pureWeightToUniversalAddress
        (GSTClassicalHodgeNativeCycleCosmicShadow.nativeCycleCosmicShadow
          V (p + 1)
          (codimensionPointCycle V.X (p + 1) y)) =
      GSTTransferBridgeV2.rationalizeCompactAddress
        (GSTClassicalHodgeTransferSeedUniverse.compactClMono (p + 1)) := by
  dsimp
  exact classicalSheet_eq_nativePoint_eq_transfer
    V H (p + 1)
      (degreeCertifiedSuccessorSeed G D p x hlive hExact).sourceIndex
      ⟨ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive), hExact⟩

/-- The handwritten de-Rham/Betti/Cardinal transform is compositional at every
pair of depths: the mixed period factors exactly and the three-world packet
concatenates by coordinatewise multiplication. -/
theorem pi_period_threeWorld_composition
    (j k : Nat) :
    HodgeDeRhamBridge.MixedPeriodLayer (j + k) =
        HodgeDeRhamBridge.MixedPeriodLayer j *
          HodgeDeRhamBridge.MixedPeriodLayer k
    ∧ gstThreeWorldExponentialPacketS (j + k) =
        CardinalWorldsV2.packetMul
          (gstThreeWorldExponentialPacketS j)
          (gstThreeWorldExponentialPacketS k) := by
  exact ⟨HodgeDeRhamBridge.mixed_period_multiplicative j k,
    CardinalWorldsV2.packet_add j k⟩

/-- **PI STRICT-OMNIVERSE EXACT COLLAPSE.**

For the degree-certified successor weight, strict geometric materialization of
all primitive three-sector GST causal arrows is enough to construct an actual
native algebraic cycle for EVERY rational Hodge state.  The former abstract
`PrimitiveBranchCompiler` premise has disappeared: it is derived above from
scheme correspondences and their cup/Gysin/incidence semantics. -/
theorem target_has_native_cycle_of_strict_pi_omniverse
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1)
    (hgeom :
      ∀ {u v : HodgeBranchNode (V := V) (H := H) (p := p + 1)},
        (hodgeBranchGraph (V := V) (H := H) (p := p + 1)).Event u v →
          StrictlyMaterializedBranch u v)
    (alpha : ClassicalHodgeFiber V H (p + 1)) :
    ∃ Z : codimensionCycles V.X (p + 1),
      H.cycleClass (p + 1) Z = alpha.1 := by
  let C : PrimitiveBranchCompiler (V := V) (H := H) (p := p + 1) :=
    primitiveBranchCompiler_of_strictMaterialization hgeom
  exact target_has_native_cycle_of_primitive_omniverse_compiler
    G D p x hlive hExact C alpha

/-- Fixed-weight range form of the exact collapse. -/
theorem hodge_weight_succ_of_strict_pi_omniverse
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1)
    (hgeom :
      ∀ {u v : HodgeBranchNode (V := V) (H := H) (p := p + 1)},
        (hodgeBranchGraph (V := V) (H := H) (p := p + 1)).Event u v →
          StrictlyMaterializedBranch u v) :
    rationalHodgeSubspace (H.hodgeBigrading (p + 1)) ≤
      LinearMap.range (H.cycleClass (p + 1)) := by
  intro alpha halpha
  let alphaH : ClassicalHodgeFiber V H (p + 1) := ⟨alpha, halpha⟩
  obtain ⟨Z, hZ⟩ :=
    target_has_native_cycle_of_strict_pi_omniverse
      G D p x hlive hExact hgeom alphaH
  exact ⟨Z, hZ⟩

#check strictBranch_has_realizedExpression
#check primitiveBranchCompiler_of_strictMaterialization
#check degreeCertified_source_threeUniverse_identity
#check pi_period_threeWorld_composition
#check target_has_native_cycle_of_strict_pi_omniverse
#check hodge_weight_succ_of_strict_pi_omniverse

#print axioms strictBranch_has_realizedExpression
#print axioms primitiveBranchCompiler_of_strictMaterialization
#print axioms degreeCertified_source_threeUniverse_identity
#print axioms target_has_native_cycle_of_strict_pi_omniverse
#print axioms hodge_weight_succ_of_strict_pi_omniverse

end GSTClassicalHodgePiStrictOmniverseCompiler
