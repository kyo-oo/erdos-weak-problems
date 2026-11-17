import GSTClassicalHodgeOmniverseTwoSlotLefschetzBranch
import GSTClassicalHodgePiOmniverseBranchSynthesis
import GSTClassicalHodgeDiagonalIdentityCorrespondence
import GSTClassicalHodgePiOneSourceCompositionalCorrespondenceFinale

/-!
# GST CLASSICAL HODGE — OMNIVERSE LEFSCHETZ RAY COMPILER

A primitive branch arrow in the handwritten GST omniverse is already proved to
be a normalized localized two-slot `L^2` firing.  Therefore it is unnecessary
to geometrically materialize every matrix unit or every graph edge separately.

There are two useful levels of geometric input.

The stronger reusable level asks for one realized correspondence expression for
each ordered two-slot chart and requires that expression to realize bare local
`L^2` on the whole Hodge fiber.

The sharper sourcewise level allows the realized expression to depend on the
actual source state.  This is all a causal graph edge ever consumes.  For the
Hodge conclusion itself we can weaken once more: one genuine algebraic apex
seed only needs one source-specific local-`L^2` expression for each target
basis sheet.  No behavior on any other Hodge vector is required.

The graph ontology contributes the second compression.  A long causal ray is
not a new primitive operator; it is a finite `OmniversalGraph.Path`.  Genuine
correspondence expressions are closed under noncommutative composition, so an
entire ray compiles to one realized expression.  The empty path is materialized
by the actual diagonal graph correspondence, not by an inserted formal
identity.

Thus the handwritten fan admits the hierarchy

  global localized L^2 geometry
      -> sourcewise localized L^2 geometry
      -> every primitive branch event
      -> every finite causal ray
      -> every event-generated closure node,

while the exact fixed-weight Hodge landing only needs

  one algebraic apex seed
      + source-specific localized L^2 spokes from that apex.

Higher-arity branch synthesis remains handled by the already-proved omniverse
semantic-stability theorem once the primitive compiler has been manufactured.
No Hodge-surjectivity conclusion is assumed in any geometric input below.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeOmniverseLefschetzRayCompiler

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgePrimitiveArsenalRationalization
open GSTClassicalHodgeTwoSlotLefschetzCollapse
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgeOmniverseTwoSlotLefschetzBranch
open GSTClassicalHodgePiOmniverseBranchSynthesis
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
open GSTClassicalHodgeDiagonalIdentityCorrespondence
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgePiOneSourceCompositionalCorrespondenceFinale
open GSTGraphV2OmniversalCore
open GSTGraphV2OmniversalHyperEvents

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Reusable whole-fiber localized `L^2` realization.

For every ordered Hodge-basis pair `(i,j)`, one expression in actual realized
closed correspondences agrees on EVERY genuine Hodge-fiber state with the bare
localized two-step Lefschetz operator on the corresponding two-slot chart. -/
def LocalizedL2PrimitiveRealization : Prop :=
  forall i j : ClassicalHodgeBasisIndex V H p,
    exists E : RealizedCorrespondenceExpr V H p,
      forall alpha : ClassicalHodgeFiber V H p,
        E.cohomologyOperator alpha.1 =
          (liftFiniteHodgeOperator (pairBasisIndex i j)
            (diagonalLefschetzQ 2 2) alpha).1

/-- **SOURCEWISE LOCALIZED L² REALIZATION.**

This is strictly weaker than `LocalizedL2PrimitiveRealization`: the actual
realized expression is allowed to depend on the source state `alpha`.  A graph
edge only evaluates its operator on that source, so no stronger equality is
needed for causal-ray compilation. -/
def SourcewiseLocalizedL2PrimitiveRealization : Prop :=
  forall alpha : ClassicalHodgeFiber V H p,
    forall i j : ClassicalHodgeBasisIndex V H p,
      exists E : RealizedCorrespondenceExpr V H p,
        E.cohomologyOperator alpha.1 =
          (liftFiniteHodgeOperator (pairBasisIndex i j)
            (diagonalLefschetzQ 2 2) alpha).1

/-- Whole-fiber realization automatically supplies the weaker sourcewise
realization. -/
theorem sourcewiseLocalizedL2_of_global
    (C : LocalizedL2PrimitiveRealization (V := V) (H := H) (p := p)) :
    SourcewiseLocalizedL2PrimitiveRealization
      (V := V) (H := H) (p := p) := by
  intro alpha i j
  obtain ⟨E, hE⟩ := C i j
  exact ⟨E, hE alpha⟩

/-- **APEX-ONLY LOCALIZED L² REALIZATION.**

For one already genuine algebraic Hodge seed `S`, it is enough to realize bare
localized `L^2` only on `S.hodge`, from its canonically selected nonzero source
coordinate to each requested target sheet.  This is the exact geometric input
consumed by the one-source compositional correspondence finale. -/
def ApexLocalizedL2Realization
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) : Prop :=
  forall j : ClassicalHodgeBasisIndex V H p,
    exists E : RealizedCorrespondenceExpr V H p,
      E.cohomologyOperator S.hodge.1 =
        (liftFiniteHodgeOperator (pairBasisIndex S.sourceIndex j)
          (diagonalLefschetzQ 2 2) S.hodge).1

/-- A sourcewise realization family restricts to the spokes leaving any chosen
algebraic apex seed. -/
theorem apexLocalizedL2_of_sourcewise
    (C : SourcewiseLocalizedL2PrimitiveRealization
      (V := V) (H := H) (p := p))
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) :
    ApexLocalizedL2Realization S := by
  intro j
  exact C S.hodge S.sourceIndex j

/-- Sourcewise bare localized `L^2` geometry automatically materializes EVERY
primitive omniverse branch edge.  The only extra operation is multiplication
by the already-proved nonzero universal inverse scalar. -/
theorem primitiveBranchCompiler_of_sourcewiseLocalizedL2
    (C : SourcewiseLocalizedL2PrimitiveRealization
      (V := V) (H := H) (p := p)) :
    PrimitiveBranchCompiler (V := V) (H := H) (p := p) := by
  intro u v huv
  obtain ⟨j, i, htarget⟩ :=
    event_target_eq_normalized_localized_L2
      (V := V) (H := H) (p := p) huv
  obtain ⟨E, hE⟩ := C u.state i.1 j
  refine ⟨.smul (twoSlotScalar)⁻¹ E, ?_⟩
  unfold ExprMaterializesBranch
  change v.state.1 =
    (twoSlotScalar)⁻¹ • E.cohomologyOperator u.state.1
  rw [hE]
  simpa using congrArg Subtype.val htarget

/-- Whole-fiber localized `L^2` is therefore more than enough for the primitive
branch compiler. -/
theorem primitiveBranchCompiler_of_localizedL2
    (C : LocalizedL2PrimitiveRealization (V := V) (H := H) (p := p)) :
    PrimitiveBranchCompiler (V := V) (H := H) (p := p) :=
  primitiveBranchCompiler_of_sourcewiseLocalizedL2
    (sourcewiseLocalizedL2_of_global C)

/-- The genuine diagonal graph correspondence materializes the zero-length
causal ray. -/
theorem diagonal_materializes_reflexive_branch
    (u : HodgeBranchNode (V := V) (H := H) (p := p)) :
    ExprMaterializesBranch
      (.atom (diagonalRealized (V := V) (H := H) (p := p))) u u := by
  unfold ExprMaterializesBranch
  change u.state.1 =
    (diagonalRealized (V := V) (H := H) (p := p)).cohomologyOperator u.state.1
  rw [diagonalRealized_cohomologyOperator]
  rfl

/-- **SOURCEWISE CAUSAL-RAY COMPILER.**
Every finite GST Graph V2 causal path is one genuine noncommutative expression
of realized closed correspondences.  At each edge the geometric expression may
be specialized to the actual source node of that edge. -/
theorem causalPath_has_realized_expression_sourcewise
    (C : SourcewiseLocalizedL2PrimitiveRealization
      (V := V) (H := H) (p := p))
    {u v : HodgeBranchNode (V := V) (H := H) (p := p)}
    (gamma : OmniversalGraph.Path
      (hodgeBranchGraph (V := V) (H := H) (p := p)) u v) :
    exists E : RealizedCorrespondenceExpr V H p,
      ExprMaterializesBranch E u v := by
  have Cedge : PrimitiveBranchCompiler (V := V) (H := H) (p := p) :=
    primitiveBranchCompiler_of_sourcewiseLocalizedL2 C
  induction gamma with
  | nil x =>
      exact ⟨.atom (diagonalRealized (V := V) (H := H) (p := p)),
        diagonal_materializes_reflexive_branch x⟩
  | cons e tail ih =>
      obtain ⟨Eedge, hEdge⟩ := Cedge e
      obtain ⟨Etail, hTail⟩ := ih
      refine ⟨.comp Etail Eedge, ?_⟩
      unfold ExprMaterializesBranch at hEdge hTail ⊢
      rw [RealizedCorrespondenceExpr.comp_cohomology_apply]
      rw [← hEdge]
      exact hTail

/-- Whole-fiber form retained as a convenience corollary. -/
theorem causalPath_has_realized_expression
    (C : LocalizedL2PrimitiveRealization (V := V) (H := H) (p := p))
    {u v : HodgeBranchNode (V := V) (H := H) (p := p)}
    (gamma : OmniversalGraph.Path
      (hodgeBranchGraph (V := V) (H := H) (p := p)) u v) :
    exists E : RealizedCorrespondenceExpr V H p,
      ExprMaterializesBranch E u v :=
  causalPath_has_realized_expression_sourcewise
    (sourcewiseLocalizedL2_of_global C) gamma

/-- Sourcewise reachability compiles to one genuine correspondence expression. -/
theorem reachable_has_realized_expression_sourcewise
    (C : SourcewiseLocalizedL2PrimitiveRealization
      (V := V) (H := H) (p := p))
    {u v : HodgeBranchNode (V := V) (H := H) (p := p)}
    (h : OmniversalGraph.Reachable
      (hodgeBranchGraph (V := V) (H := H) (p := p)) u v) :
    exists E : RealizedCorrespondenceExpr V H p,
      ExprMaterializesBranch E u v := by
  rcases h with ⟨gamma⟩
  exact causalPath_has_realized_expression_sourcewise C gamma

/-- Whole-fiber reachability corollary. -/
theorem reachable_has_realized_expression
    (C : LocalizedL2PrimitiveRealization (V := V) (H := H) (p := p))
    {u v : HodgeBranchNode (V := V) (H := H) (p := p)}
    (h : OmniversalGraph.Reachable
      (hodgeBranchGraph (V := V) (H := H) (p := p)) u v) :
    exists E : RealizedCorrespondenceExpr V H p,
      ExprMaterializesBranch E u v :=
  reachable_has_realized_expression_sourcewise
    (sourcewiseLocalizedL2_of_global C) h

/-- **SOURCEWISE FULL FAN / CLOSURE REALIZATION.**
Every node in the event closure of a seed family is connected to one actual
seed by a single compiled genuine correspondence expression. -/
theorem closure_node_has_realized_ray_sourcewise
    (C : SourcewiseLocalizedL2PrimitiveRealization
      (V := V) (H := H) (p := p))
    (Seed : HodgeBranchNode (V := V) (H := H) (p := p) → Prop)
    {v : HodgeBranchNode (V := V) (H := H) (p := p)}
    (hv : OmniversalGraph.Closure
      (hodgeBranchGraph (V := V) (H := H) (p := p)) Seed v) :
    exists u : HodgeBranchNode (V := V) (H := H) (p := p),
      Seed u ∧
        exists E : RealizedCorrespondenceExpr V H p,
          ExprMaterializesBranch E u v := by
  rcases hv with ⟨u, hu, huv⟩
  exact ⟨u, hu, reachable_has_realized_expression_sourcewise C huv⟩

/-- Whole-fiber fan/closure corollary. -/
theorem closure_node_has_realized_ray
    (C : LocalizedL2PrimitiveRealization (V := V) (H := H) (p := p))
    (Seed : HodgeBranchNode (V := V) (H := H) (p := p) → Prop)
    {v : HodgeBranchNode (V := V) (H := H) (p := p)}
    (hv : OmniversalGraph.Closure
      (hodgeBranchGraph (V := V) (H := H) (p := p)) Seed v) :
    exists u : HodgeBranchNode (V := V) (H := H) (p := p),
      Seed u ∧
        exists E : RealizedCorrespondenceExpr V H p,
          ExprMaterializesBranch E u v :=
  closure_node_has_realized_ray_sourcewise
    (sourcewiseLocalizedL2_of_global C) Seed hv

/-- Sourcewise local `L^2` geometry certifies algebraicity stability of all
unary graph arrows and every finite higher-arity omniverse synthesis. -/
theorem sourcewiseLocalizedL2_semanticallyStable
    (C : SourcewiseLocalizedL2PrimitiveRealization
      (V := V) (H := H) (p := p)) :
    HyperEventSystem.SemanticallyStable
      (hodgeBranchHyperEvents (V := V) (H := H) (p := p))
      (AlgebraicBranchNode (V := V) (H := H) (p := p)) := by
  exact algebraicBranchNode_semanticallyStable
    (primitiveBranchCompiler_of_sourcewiseLocalizedL2 C)

/-- Whole-fiber semantic-stability corollary. -/
theorem localizedL2_semanticallyStable
    (C : LocalizedL2PrimitiveRealization (V := V) (H := H) (p := p)) :
    HyperEventSystem.SemanticallyStable
      (hodgeBranchHyperEvents (V := V) (H := H) (p := p))
      (AlgebraicBranchNode (V := V) (H := H) (p := p)) :=
  sourcewiseLocalizedL2_semanticallyStable
    (sourcewiseLocalizedL2_of_global C)

/-- Consequently every unary/higher-event state generated from algebraic seeds
stays in the genuine cycle-class range under only sourcewise local geometry. -/
theorem generated_from_algebraic_seeds_of_sourcewiseLocalizedL2
    (C : SourcewiseLocalizedL2PrimitiveRealization
      (V := V) (H := H) (p := p))
    (Seed : HodgeBranchNode (V := V) (H := H) (p := p) → Prop)
    (hSeed : forall u, Seed u →
      AlgebraicBranchNode (V := V) (H := H) (p := p) u) :
    forall {u},
      HyperEventSystem.Generated
        (hodgeBranchHyperEvents (V := V) (H := H) (p := p)) Seed u →
      AlgebraicBranchNode (V := V) (H := H) (p := p) u := by
  exact generated_from_algebraic_seeds_is_algebraic
    (primitiveBranchCompiler_of_sourcewiseLocalizedL2 C) Seed hSeed

/-- Whole-fiber generated-closure corollary. -/
theorem generated_from_algebraic_seeds_of_localizedL2
    (C : LocalizedL2PrimitiveRealization (V := V) (H := H) (p := p))
    (Seed : HodgeBranchNode (V := V) (H := H) (p := p) → Prop)
    (hSeed : forall u, Seed u →
      AlgebraicBranchNode (V := V) (H := H) (p := p) u) :
    forall {u},
      HyperEventSystem.Generated
        (hodgeBranchHyperEvents (V := V) (H := H) (p := p)) Seed u →
      AlgebraicBranchNode (V := V) (H := H) (p := p) u :=
  generated_from_algebraic_seeds_of_sourcewiseLocalizedL2
    (sourcewiseLocalizedL2_of_global C) Seed hSeed

/-- **APEX SPOKES -> ONE-SOURCE COMPOSITIONAL REALIZATION.**

Apex-only local `L^2` geometry already supplies the exact source-hit packet of
the one-source correspondence finale.  The target scalar is the universal
nonzero two-slot Lefschetz scalar times the canonically selected nonzero source
coefficient. -/
noncomputable def oneSourceRealization_of_apexLocalizedL2
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (C : ApexLocalizedL2Realization S) :
    OneSourceCompositionalCorrespondenceRealization
      (V := V) (H := H) p := by
  classical
  choose E hE using C
  let c : ℚ := hodgeCoordinate S.sourceIndex S.hodge
  have hc : c ≠ 0 := by
    simpa [c, hodgeCoordinate] using S.sourceCoefficient_ne_zero
  refine {
    seed := S
    expression := E
    scalar := fun _ => twoSlotScalar * c
    scalar_ne_zero := fun _ => mul_ne_zero twoSlotScalar_ne_zero hc
    source_hit := ?_
  }
  intro j
  rw [hE j]
  have hL := LinearMap.congr_fun
    (localized_L2_eq_scaled_matrixUnit
      (V := V) (H := H) (p := p) S.sourceIndex j)
    S.hodge
  have hLval := congrArg Subtype.val hL
  rw [hLval]
  simp [hodgeMatrixUnit_apply, c, smul_smul, mul_assoc]

/-- **APEX-FAN FIXED-WEIGHT HODGE LANDING.**
One genuine algebraic apex and source-specific local `L^2` spokes to every
basis target already force the entire rational Hodge weight into the genuine
cycle-class range.  No whole-fiber operator realization and no downstream edge
materialization is needed. -/
theorem hodge_weight_of_apexLocalizedL2
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (C : ApexLocalizedL2Realization S) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) :=
  (oneSourceRealization_of_apexLocalizedL2 S C).hodge_weight

#check LocalizedL2PrimitiveRealization
#check SourcewiseLocalizedL2PrimitiveRealization
#check ApexLocalizedL2Realization
#check sourcewiseLocalizedL2_of_global
#check apexLocalizedL2_of_sourcewise
#check primitiveBranchCompiler_of_sourcewiseLocalizedL2
#check primitiveBranchCompiler_of_localizedL2
#check diagonal_materializes_reflexive_branch
#check causalPath_has_realized_expression_sourcewise
#check causalPath_has_realized_expression
#check reachable_has_realized_expression_sourcewise
#check closure_node_has_realized_ray_sourcewise
#check sourcewiseLocalizedL2_semanticallyStable
#check generated_from_algebraic_seeds_of_sourcewiseLocalizedL2
#check oneSourceRealization_of_apexLocalizedL2
#check hodge_weight_of_apexLocalizedL2

#print axioms primitiveBranchCompiler_of_sourcewiseLocalizedL2
#print axioms causalPath_has_realized_expression_sourcewise
#print axioms closure_node_has_realized_ray_sourcewise
#print axioms sourcewiseLocalizedL2_semanticallyStable
#print axioms oneSourceRealization_of_apexLocalizedL2
#print axioms hodge_weight_of_apexLocalizedL2

end GSTClassicalHodgeOmniverseLefschetzRayCompiler
