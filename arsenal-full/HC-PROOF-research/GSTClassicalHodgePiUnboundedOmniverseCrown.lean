import GSTClassicalHodgePiStrictOmniverseCompiler
import GSTClassicalHodgePiOmniverseBranchSynthesis
import GSTGraphV2SelfExpandingCosmology
import GSTGraphV2UnboundedHigherCausality

/-!
# GST CLASSICAL HODGE — PI UNBOUNDED OMNIVERSE CROWN

This file makes the full GST omniverse essential to the Hodge branch argument.
The earlier causal compiler handled a primitive source-to-target edge.  Here we
close the semantics under all of the additional structure used in the
handwritten Pi construction:

* the three historical GST sectors;
* recursively born branch worlds;
* arbitrary-arity hyper-events;
* the unbounded higher-causal tower;
* exact algebraicity on the original fixed projective variety throughout.

No branch is allowed to change the projective carrier: a world is a genuine
`HodgeBranchNode V H p`.  The global Pi quantification is obtained by leaving
`V`, `H`, and `p` arbitrary.  The unbounded ambient cosmos therefore expands
around the chosen projective world while the final collapse lands back in the
cycle group of exactly that same `V`.
-/

set_option maxHeartbeats 160000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgePiUnboundedOmniverseCrown

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgePiOmniverseBranchSynthesis
open GSTClassicalHodgeOmniverseStrictEventStability
open GSTClassicalHodgePiStrictOmniverseCompiler
open GSTGraphV2OmniversalCore
open GSTGraphV2OmniversalHyperEvents
open GSTGraphV2SelfExpandingCosmology
open GSTGraphV2UnboundedHigherCausality

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The Hodge branch graph promoted from a graph of states to a recursively
self-expanding cosmos of worlds.  Each Hodge branch node is itself a world.
The three roots are the zero Hodge state in the three historical sectors.
A world birth is certified whenever one source world has a genuine primitive
GST causal event to the target; the source family may have arbitrary arity. -/
def hodgeSelfExpandingCosmos : SelfExpandingCosmos where
  World := HodgeBranchNode (V := V) (H := H) (p := p)
  State := fun _ => PUnit
  Law := fun _ => PUnit
  root := fun s => ⟨s, 0⟩
  LocalEvent := fun _ _ => PUnit
  Transport := fun {A B} _ _ => HodgeBranchEvent A B
  Birth := fun {I} src target => ∃ i : I, HodgeBranchEvent (src i) target

/-- Canonical unbounded globular extension of the Hodge-world cosmos.  A
world remains literally the same Hodge/projective world under higher identity
coherence; hence there is no artificial change of carrier at higher dimension.
Primitive and higher-arity causal content is carried by the underlying
self-expanding/hyper-event systems, while this tower certifies that there is no
maximum coherence dimension. -/
def hodgeHigherCausalCosmos :
    HigherCausalCosmos (hodgeSelfExpandingCosmos (V := V) (H := H) (p := p)) where
  Cell := fun _ => HodgeBranchNode (V := V) (H := H) (p := p)
  worldCell := fun W => W
  source := fun x => x
  target := fun x => x
  identity := fun x => x
  source_identity := by intro n x; rfl
  target_identity := by intro n x; rfl
  source_source := by intro n x; rfl
  target_source := by intro n x; rfl

/-- Every Hodge branch world therefore persists as an actual cell at every
finite causal dimension of one unbounded GST higher-causal cosmos. -/
theorem branchWorld_has_unbounded_higher_tower
    (u : HodgeBranchNode (V := V) (H := H) (p := p)) :
    ∀ n : Nat,
      ∃ c : (hodgeHigherCausalCosmos (V := V) (H := H) (p := p)).Cell n,
        c = u := by
  intro n
  refine ⟨HigherCausalCosmos.identityTower
      (hodgeSelfExpandingCosmos (V := V) (H := H) (p := p))
      (hodgeHigherCausalCosmos (V := V) (H := H) (p := p)) u n, ?_⟩
  induction n with
  | zero => rfl
  | succ n ih =>
      change HigherCausalCosmos.identity
        (hodgeHigherCausalCosmos (V := V) (H := H) (p := p))
        (HigherCausalCosmos.identityTower
          (hodgeSelfExpandingCosmos (V := V) (H := H) (p := p))
          (hodgeHigherCausalCosmos (V := V) (H := H) (p := p)) u n) = u
      simpa [hodgeHigherCausalCosmos] using ih

/-- Strict scheme materialization of the primitive GST edges makes genuine
cycle-class algebraicity stable under every unary AND arbitrary-arity
hyper-event in the Pi branch cosmos. -/
theorem fullHyperEvent_algebraic_of_strictMaterialization
    (hgeom :
      ∀ {u v : HodgeBranchNode (V := V) (H := H) (p := p)},
        (hodgeBranchGraph (V := V) (H := H) (p := p)).Event u v →
          StrictlyMaterializedBranch u v)
    (Seed : HodgeBranchNode (V := V) (H := H) (p := p) → Prop)
    (hSeed : ∀ u, Seed u →
      AlgebraicBranchNode (V := V) (H := H) (p := p) u)
    {u : HodgeBranchNode (V := V) (H := H) (p := p)}
    (hu : HyperEventSystem.Generated
      (hodgeBranchHyperEvents (V := V) (H := H) (p := p)) Seed u) :
    AlgebraicBranchNode (V := V) (H := H) (p := p) u := by
  let C : PrimitiveBranchCompiler (V := V) (H := H) (p := p) :=
    primitiveBranchCompiler_of_strictMaterialization hgeom
  exact generated_from_algebraic_seeds_is_algebraic C Seed hSeed hu

/-- The semantic content of an algebraic branch is unchanged throughout the
entire unbounded higher identity tower, because every higher cell is still the
same projective/Hodge branch world. -/
theorem algebraicBranch_has_unbounded_higher_certificate
    (u : HodgeBranchNode (V := V) (H := H) (p := p))
    (hu : AlgebraicBranchNode (V := V) (H := H) (p := p) u) :
    ∀ n : Nat,
      ∃ c : (hodgeHigherCausalCosmos (V := V) (H := H) (p := p)).Cell n,
        c = u ∧ AlgebraicBranchNode (V := V) (H := H) (p := p) c := by
  intro n
  obtain ⟨c, hc⟩ := branchWorld_has_unbounded_higher_tower
    (V := V) (H := H) (p := p) u n
  refine ⟨c, hc, ?_⟩
  simpa [hc] using hu

/-- **FULL UNBOUNDED PI-OMNIVERSE STABILITY CROWN.**
Anything generated from algebraic seeds by the complete three-sector
unary/higher-arity branch system is simultaneously

1. a genuine algebraic cycle class on the original `V`; and
2. present with that same algebraic semantics at every higher causal
   dimension.
-/
theorem generatedBranch_algebraic_at_every_causal_dimension
    (hgeom :
      ∀ {u v : HodgeBranchNode (V := V) (H := H) (p := p)},
        (hodgeBranchGraph (V := V) (H := H) (p := p)).Event u v →
          StrictlyMaterializedBranch u v)
    (Seed : HodgeBranchNode (V := V) (H := H) (p := p) → Prop)
    (hSeed : ∀ u, Seed u →
      AlgebraicBranchNode (V := V) (H := H) (p := p) u)
    {u : HodgeBranchNode (V := V) (H := H) (p := p)}
    (hu : HyperEventSystem.Generated
      (hodgeBranchHyperEvents (V := V) (H := H) (p := p)) Seed u) :
    AlgebraicBranchNode (V := V) (H := H) (p := p) u
    ∧ ∀ n : Nat,
      ∃ c : (hodgeHigherCausalCosmos (V := V) (H := H) (p := p)).Cell n,
        c = u ∧ AlgebraicBranchNode (V := V) (H := H) (p := p) c := by
  have halg := fullHyperEvent_algebraic_of_strictMaterialization
    hgeom Seed hSeed hu
  exact ⟨halg, algebraicBranch_has_unbounded_higher_certificate u halg⟩

/-- Every target basis branch of a nonzero algebraic source has an unbounded
higher-causal algebraic certificate once primitive branches are strictly
materialized.  This is the full-omniverse version of the rank-one reachability
step. -/
theorem targetBasis_has_unbounded_algebraic_branch
    (a : ClassicalHodgeFiber V H p)
    (ha0 : a ≠ 0)
    (haAlg : a.1 ∈ LinearMap.range (H.cycleClass p))
    (hgeom :
      ∀ {u v : HodgeBranchNode (V := V) (H := H) (p := p)},
        (hodgeBranchGraph (V := V) (H := H) (p := p)).Event u v →
          StrictlyMaterializedBranch u v)
    (j : ClassicalHodgeBasisIndex V H p) :
    ∃ i : HodgeSupportIndex a,
      let target : HodgeBranchNode (V := V) (H := H) (p := p) :=
        ⟨Sector.gstPlus,
          GSTClassicalHodgeRankFreeArsenalIrreducibility.hodgeMatrixUnit
            i.1 j a⟩
      AlgebraicBranchNode (V := V) (H := H) (p := p) target
      ∧ ∀ n : Nat,
        ∃ c : (hodgeHigherCausalCosmos (V := V) (H := H) (p := p)).Cell n,
          c = target ∧
          AlgebraicBranchNode (V := V) (H := H) (p := p) c := by
  obtain ⟨i, hreach, hi⟩ := reachable_arbitrary_target
    (V := V) (H := H) a ha0 Sector.gstPlus j
  refine ⟨i, ?_⟩
  let source : HodgeBranchNode (V := V) (H := H) (p := p) :=
    ⟨Sector.gstPlus, a⟩
  let target : HodgeBranchNode (V := V) (H := H) (p := p) :=
    ⟨Sector.gstPlus,
      GSTClassicalHodgeRankFreeArsenalIrreducibility.hodgeMatrixUnit i.1 j a⟩
  rcases hreach with ⟨path⟩
  have hstable :=
    algebraic_eventStable_of_strictMaterialization hgeom
  have htarget : AlgebraicNode (V := V) (H := H) (p := p) target := by
    exact OmniversalGraph.Path.preserves
      (hodgeBranchGraph (V := V) (H := H) (p := p))
      hstable path haAlg
  have htarget' : AlgebraicBranchNode (V := V) (H := H) (p := p) target :=
    htarget
  exact ⟨htarget', algebraicBranch_has_unbounded_higher_certificate target htarget'⟩

#check hodgeSelfExpandingCosmos
#check hodgeHigherCausalCosmos
#check branchWorld_has_unbounded_higher_tower
#check fullHyperEvent_algebraic_of_strictMaterialization
#check generatedBranch_algebraic_at_every_causal_dimension
#check targetBasis_has_unbounded_algebraic_branch

#print axioms fullHyperEvent_algebraic_of_strictMaterialization
#print axioms generatedBranch_algebraic_at_every_causal_dimension
#print axioms targetBasis_has_unbounded_algebraic_branch

end GSTClassicalHodgePiUnboundedOmniverseCrown
