import GSTClassicalHodgeRootedStrictRelationFan

/-!
# GST CLASSICAL HODGE — ROOTED STRICT-RELATION TREE

The rooted fan reduces geometry to one locally materialized ray per Hodge basis
target.  The handwritten GST Graph V2 picture has an additional feature: many
rays share a long common trunk and split only near their targets.

This file formalizes that reuse.  A strict-relation ray can be concatenated
without introducing any global compiler.  Hence one may certify

  apex  --->  hub

once, and then certify only the shorter branches

  hub  --->  c e_j.

The full apex-to-target rays are obtained by concatenation.  Algebraicity is
transported through the shared trunk once and then fanned out to every target.
This is a genuine reduction in duplicated geometric obligations whenever many
targets share the same correspondence prefix.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeRootedStrictRelationTree

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgePiOmniverseBranchSynthesis
open GSTClassicalHodgeRootedStrictRelationFan
open GSTGraphV2OmniversalCore

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

namespace StrictRelationRay

/-- Concatenate two locally materialized strict-relation rays.  Every edge
certificate is reused verbatim; no new correspondence or global compiler is
introduced. -/
def comp
    {u v w : HodgeBranchNode (V := V) (H := H) (p := p)} :
    StrictRelationRay u v → StrictRelationRay v w → StrictRelationRay u w
  | .nil _, q => q
  | .cons event relation tail, q =>
      .cons event relation (comp tail q)

@[simp]
theorem nil_comp
    {u v : HodgeBranchNode (V := V) (H := H) (p := p)}
    (r : StrictRelationRay u v) :
    comp (StrictRelationRay.nil u) r = r := rfl

@[simp]
theorem comp_nil
    {u v : HodgeBranchNode (V := V) (H := H) (p := p)}
    (r : StrictRelationRay u v) :
    comp r (StrictRelationRay.nil v) = r := by
  induction r with
  | nil => rfl
  | cons event relation tail ih =>
      simp [comp, ih]

/-- Concatenation agrees exactly with GST Graph V2 path concatenation after
forgetting strict-relation certificates. -/
theorem toPath_comp
    {u v w : HodgeBranchNode (V := V) (H := H) (p := p)}
    (r : StrictRelationRay u v)
    (s : StrictRelationRay v w) :
    (comp r s).toPath =
      OmniversalGraph.Path.comp
        (hodgeBranchGraph (V := V) (H := H) (p := p))
        r.toPath s.toPath := by
  induction r with
  | nil => rfl
  | cons event relation tail ih =>
      simp [comp, StrictRelationRay.toPath, OmniversalGraph.Path.comp, ih]

/-- Algebraicity transport through a concatenated ray factors through the hub.
This is the semantic reason a shared trunk need only be proved once. -/
theorem preserves_algebraic_comp
    {u v w : HodgeBranchNode (V := V) (H := H) (p := p)}
    (r : StrictRelationRay u v)
    (s : StrictRelationRay v w)
    (hu : AlgebraicBranchNode (V := V) (H := H) (p := p) u) :
    AlgebraicBranchNode (V := V) (H := H) (p := p) w :=
  s.preserves_algebraic (r.preserves_algebraic hu)

end StrictRelationRay

/-- A rooted fan with one explicitly shared strict-relation trunk.

`hub` may be any intermediate omniverse state.  The same trunk is reused for
all target branches. -/
structure RootedStrictRelationTrunkFan
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) where
  hub : HodgeBranchNode (V := V) (H := H) (p := p)
  trunk : StrictRelationRay (rootedFanApex S) hub
  branch : ∀ j : ClassicalHodgeBasisIndex V H p,
    StrictRelationRay hub (rootedFanTarget S j)

namespace RootedStrictRelationTrunkFan

/-- Expand a trunk-and-branches certificate into the ordinary rooted fan by
concatenating the shared prefix with each target branch. -/
noncomputable def toRootedFan
    (T : RootedStrictRelationTrunkFan
      (V := V) (H := H) (p := p) S) :
    RootedStrictRelationFan S where
  ray := fun j => StrictRelationRay.comp T.trunk (T.branch j)

/-- The shared hub is algebraic after transporting the genuine algebraic apex
through the one common trunk. -/
theorem hub_algebraic
    (T : RootedStrictRelationTrunkFan
      (V := V) (H := H) (p := p) S) :
    AlgebraicBranchNode (V := V) (H := H) (p := p) T.hub :=
  T.trunk.preserves_algebraic (rootedFanApex_algebraic S)

/-- Every target endpoint is algebraic by reusing the hub theorem and traversing
only its target-specific suffix. -/
theorem target_algebraic
    (T : RootedStrictRelationTrunkFan
      (V := V) (H := H) (p := p) S)
    (j : ClassicalHodgeBasisIndex V H p) :
    AlgebraicBranchNode (V := V) (H := H) (p := p)
      (rootedFanTarget S j) :=
  (T.branch j).preserves_algebraic T.hub_algebraic

/-- **SHARED-TRUNK GST FAN CLOSES THE WHOLE HODGE WEIGHT.**
One algebraic apex, one common strict-relation trunk, and one suffix ray per
basis target suffice for the exact rational Hodge range statement. -/
theorem hodge_weight
    (T : RootedStrictRelationTrunkFan
      (V := V) (H := H) (p := p) S) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) :=
  hodge_weight_of_rootedStrictRelationFan S T.toRootedFan

end RootedStrictRelationTrunkFan

#check StrictRelationRay.comp
#check StrictRelationRay.toPath_comp
#check StrictRelationRay.preserves_algebraic_comp
#check RootedStrictRelationTrunkFan
#check RootedStrictRelationTrunkFan.toRootedFan
#check RootedStrictRelationTrunkFan.hub_algebraic
#check RootedStrictRelationTrunkFan.target_algebraic
#check RootedStrictRelationTrunkFan.hodge_weight

#print axioms StrictRelationRay.toPath_comp
#print axioms StrictRelationRay.preserves_algebraic_comp
#print axioms RootedStrictRelationTrunkFan.hodge_weight

end GSTClassicalHodgeRootedStrictRelationTree
