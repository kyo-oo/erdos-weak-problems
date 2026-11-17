import GSTClassicalHodgePiOmniverseBranchSynthesis
import GSTClassicalHodgeDegreeCertifiedStrictRelationFinale

/-!
# GST CLASSICAL HODGE — OMNIVERSE STRICT-RELATION RAY COMPILER

The previous omniverse compiler asked each primitive causal edge to be already
materialized by a realized correspondence expression, i.e. it consumed the
operator equation

  E_*(source) = target.

That is stronger than the geometry supplies natively.

For an actual scheme-bi-finite closed correspondence `K`, the intrinsic
analytic carrier already gives canonical left/right pullbacks.  The primitive
geometric datum is only the raw relation

  leftPullback(source) = rightPullback(target).

A nonzero finite Betti trace on the right leg makes the right pullback
injective.  Hence the target related to a fixed source is unique.  The trace
push-pull is itself related to the source, so uniqueness DERIVES the operator
action equation.  Point-cycle compatibility then turns that push-pull into an
honest realized finite closed correspondence expression.

Consequently GST Graph V2 may consume RAW STRICT RELATIONS at its primitive
edges.  All existing path, closure, higher-event, and finite branch-synthesis
theorems then propagate genuine algebraicity automatically.  A long diagonal
ray in the handwritten fan therefore requires no separately assumed operator
identity at any stage.

This file deliberately does not assert that every causal edge already has such
a strict relation.  It proves that constructing those geometric relations is
the exact remaining edge-level burden; the operator layer above them is fully
compiled away.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeOmniverseStrictRelationRayCompiler

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgePiOmniverseBranchSynthesis
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeStrictCorrespondenceBettiObstruction
open GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer
open GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull
open GSTClassicalHodgeDegreeCertifiedStrictRelationFinale
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
open GSTGraphV2OmniversalCore
open GSTGraphV2OmniversalHyperEvents

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- **GENERIC STRICT-RELATION UNIQUENESS.**
For any actual strict correspondence with nonzero finite right trace, a raw
Betti relation determines the target exactly as the trace push-pull of the
source.  This is the basis-free version of
`pushPull_source_action_of_related`. -/
theorem pushPull_eq_of_related
    (K : SchemeBiFiniteClosedCorrespondence V)
    (T : RightFiniteBettiTrace H.analytification K (2 * p))
    {alpha beta : RationalSingularCohomology H.analytification (2 * p)}
    (hrel : BettiRelated H.analytification K (2 * p) alpha beta) :
    T.pushPull alpha = beta :=
  T.pushPull_eq_of_bettiRelated hrel

/-- The genuine geometric packet required for ONE primitive GST causal edge.

There is no cohomological action equation in this structure.  The only
source/target statement is the intrinsic pullback relation on the actual
analytic correspondence carrier. -/
structure StrictRelationEdgePacket
    (u v : HodgeBranchNode (V := V) (H := H) (p := p)) where
  correspondence : SchemeBiFiniteClosedCorrespondence V
  trace : RightFiniteBettiTrace H.analytification correspondence (2 * p)
  pointCompatibility :
    PointCycleCompatibility (n := p) correspondence trace
  related :
    BettiRelated H.analytification correspondence (2 * p)
      u.state.1 v.state.1

namespace StrictRelationEdgePacket

/-- The raw relation uniquely determines the edge's whole-Betti push-pull
value. -/
theorem pushPull_source_eq_target
    {u v : HodgeBranchNode (V := V) (H := H) (p := p)}
    (R : StrictRelationEdgePacket u v) :
    R.trace.pushPull u.state.1 = v.state.1 :=
  pushPull_eq_of_related R.correspondence R.trace R.related

/-- Compile one raw geometric relation into the already-established genuine
realized correspondence expression algebra. -/
noncomputable def expression
    {u v : HodgeBranchNode (V := V) (H := H) (p := p)}
    (R : StrictRelationEdgePacket u v) :
    RealizedCorrespondenceExpr V H p :=
  traceExpr R.correspondence R.trace R.pointCompatibility

/-- **RAW RELATION -> MATERIALIZED GRAPH EDGE.** -/
theorem expression_materializes
    {u v : HodgeBranchNode (V := V) (H := H) (p := p)}
    (R : StrictRelationEdgePacket u v) :
    ExprMaterializesBranch R.expression u v := by
  unfold ExprMaterializesBranch
  change v.state.1 = R.trace.pushPull u.state.1
  exact R.pushPull_source_eq_target.symm

end StrictRelationEdgePacket

/-- Primitive GST graph compiler whose ONLY edge-level Hodge datum is a raw
strict correspondence relation. -/
def PrimitiveStrictRelationCompiler : Prop :=
  ∀ {u v : HodgeBranchNode (V := V) (H := H) (p := p)},
    HodgeBranchEvent u v → Nonempty (StrictRelationEdgePacket u v)

/-- **STRICT RELATIONS COMPILE THE ORDINARY OMNIVERSE GRAPH.** -/
noncomputable def primitiveBranchCompiler_of_strictRelations
    (C : PrimitiveStrictRelationCompiler (V := V) (H := H) (p := p)) :
    PrimitiveBranchCompiler (V := V) (H := H) (p := p) := by
  intro u v huv
  obtain ⟨R⟩ := C huv
  exact ⟨R.expression, R.expression_materializes⟩

/-- A primitive strict-relation compiler makes every ordinary causal edge
algebraicity-stable, without assuming any edge operator equation. -/
theorem primitive_event_algebraic_of_strictRelations
    (C : PrimitiveStrictRelationCompiler (V := V) (H := H) (p := p)) :
    OmniversalGraph.EventStable
      (hodgeBranchGraph (V := V) (H := H) (p := p))
      (AlgebraicBranchNode (V := V) (H := H) (p := p)) :=
  primitive_event_algebraic
    (primitiveBranchCompiler_of_strictRelations C)

/-- **RAW-RELATION FULL OMNIVERSE STABILITY.**
All unary causal edges and all finite higher-arity branch synthesis preserve the
actual cycle-class range once primitive edges carry only the raw geometric
strict-relation packets above. -/
theorem algebraicBranchNode_semanticallyStable_of_strictRelations
    (C : PrimitiveStrictRelationCompiler (V := V) (H := H) (p := p)) :
    HyperEventSystem.SemanticallyStable
      (hodgeBranchHyperEvents (V := V) (H := H) (p := p))
      (AlgebraicBranchNode (V := V) (H := H) (p := p)) :=
  algebraicBranchNode_semanticallyStable
    (primitiveBranchCompiler_of_strictRelations C)

/-- Any state generated anywhere in the handwritten fan from algebraic seed
nodes is algebraic under raw strict relation geometry on the primitive spokes. -/
theorem generated_from_algebraic_seeds_of_strictRelations
    (C : PrimitiveStrictRelationCompiler (V := V) (H := H) (p := p))
    (Seed : HodgeBranchNode (V := V) (H := H) (p := p) → Prop)
    (hSeed : ∀ u, Seed u →
      AlgebraicBranchNode (V := V) (H := H) (p := p) u) :
    ∀ {u},
      HyperEventSystem.Generated
        (hodgeBranchHyperEvents (V := V) (H := H) (p := p)) Seed u →
      AlgebraicBranchNode (V := V) (H := H) (p := p) u :=
  generated_from_algebraic_seeds_is_algebraic
    (primitiveBranchCompiler_of_strictRelations C) Seed hSeed

/-- Ordinary graph reachability alone already preserves algebraicity under raw
strict-relation edge geometry.  This is the direct formal version of walking
along one diagonal ray in the handwritten GST fan. -/
theorem reachable_preserves_algebraic_of_strictRelations
    (C : PrimitiveStrictRelationCompiler (V := V) (H := H) (p := p))
    {u v : HodgeBranchNode (V := V) (H := H) (p := p)}
    (hu : AlgebraicBranchNode (V := V) (H := H) (p := p) u)
    (hreach : OmniversalGraph.Reachable
      (hodgeBranchGraph (V := V) (H := H) (p := p)) u v) :
    AlgebraicBranchNode (V := V) (H := H) (p := p) v := by
  rcases hreach with ⟨gamma⟩
  exact gamma.preserves
    (primitive_event_algebraic_of_strictRelations C) hu

#check pushPull_eq_of_related
#check StrictRelationEdgePacket
#check StrictRelationEdgePacket.pushPull_source_eq_target
#check StrictRelationEdgePacket.expression
#check StrictRelationEdgePacket.expression_materializes
#check PrimitiveStrictRelationCompiler
#check primitiveBranchCompiler_of_strictRelations
#check primitive_event_algebraic_of_strictRelations
#check algebraicBranchNode_semanticallyStable_of_strictRelations
#check generated_from_algebraic_seeds_of_strictRelations
#check reachable_preserves_algebraic_of_strictRelations

#print axioms pushPull_eq_of_related
#print axioms StrictRelationEdgePacket.expression_materializes
#print axioms primitiveBranchCompiler_of_strictRelations
#print axioms generated_from_algebraic_seeds_of_strictRelations
#print axioms reachable_preserves_algebraic_of_strictRelations

end GSTClassicalHodgeOmniverseStrictRelationRayCompiler
