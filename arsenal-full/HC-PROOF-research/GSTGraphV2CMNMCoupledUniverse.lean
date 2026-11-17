import GSTGraphV2CMNMPrimitiveUpgrade

/-!
# GST Graph V2 — coupled infinite arithmetic and CM–NM Hodge cosmos

This upgrades ONE already-defined GST three-sector event ontology
with a product of TWO ACTUAL existing realizations:
1. original all-depth x4/base3 arithmetic states and horizontal/vertical
   successor events from GSTGraphV2ArithmeticOmniversalRealization;
2. original Mathlib native algebraic-cycle constructor nodes with
   two-channel CM–NM operations from GSTGraphV2CMNMPrimitiveUpgrade.

Every arithmetic step changes only its arithmetic component. Every
actual geometry event changes only its geometry component.
Both are freely interleaved through genuine finite GST paths.
There is no alternative finite rectangle posing as the limitless
graph; no invented scalar Hodge-to-cycle inverse is added.

A sector-faithful EventHom forgets the arithmetic coordinate and
is rigorously graph-functorial. The historical seven-axis sector is
still observable from its arithmetic node, while the graph sector
encodes the actual geometric construction stage.

The indexed union of all finite seed stages has EXACT reachability
semantics, and ANY reachable Hodge node retains a real algebraic
cycle witness. Hence a future graph-level completeness proof can
only succeed by genuine new geometry, not by inventing connectivity.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000
noncomputable section

open AlgebraicGeometry

namespace GSTGraphV2CMNMCoupledUniverse

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeOmniversalConstructorGraph
open GSTGraphV2OmniversalCore
open GSTGraphV2ArithmeticOmniversalRealization
open GSTGraphV2CMNMPrimitiveUpgrade

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- A SINGLE state in the product of the EXISTING GST arithmetical
cosmology and the upgraded genuine Hodge constructor graph. -/
structure CoupledNode where
  arithmetic : ArithmeticNode
  geometry : ConstructorNode V H

/-- The three GST sectors now encode the geometric construction
stage; arithmetic retains its independently computable sector. -/
def coupledSector (s : CoupledNode (V := V) (H := H)) : Sector :=
  constructorSector s.geometry

def physicalSector (s : CoupledNode (V := V) (H := H)) : Sector :=
  (arithmeticOmniversalGraph.sector s.arithmetic)

/-- Two disjoint certified transition types, on the exact existing
carriers. No artificial reverse-Hodge event is introduced. -/
inductive CoupledEvent :
    CoupledNode (V := V) (H := H) →
    CoupledNode (V := V) (H := H) → Prop
  | arithmetic (a b : ArithmeticNode) (z : ConstructorNode V H)
      (h : ArithmeticEvent a b) :
      CoupledEvent ⟨a,z⟩ ⟨b,z⟩
  | geometry (a : ArithmeticNode)
      (z w : ConstructorNode V H) (h : CertifiedEvent z w) :
      CoupledEvent ⟨a,z⟩ ⟨a,w⟩

/-- Realization of the old all-depth arithmetic sheet coupled with
the genuine geometric constructor graph, not a replacement carrier. -/
def coupledGraph : OmniversalGraph where
  Node := CoupledNode (V := V) (H := H)
  sector := coupledSector
  Event := CoupledEvent

/-- Exact forgetful GST event morphism onto the native CM–NM
geometry carrier, preserving all its three-sector semantics. -/
def geometricProjection :
    OmniversalGraph.EventHom (coupledGraph (V := V) (H := H))
      (certifiedGraph (V := V) (H := H)) where
  toFun s := s.geometry
  sector_eq := by intro s; rfl
  mapEvent := by
    intro a b h
    cases h with
    | arithmetic a b z h =>
        exact CertifiedEvent.remain z
    | geometry a z w h =>
        exact h

/-- Every old horizontal arithmetic event is still a certified
event in the coupled unlimited GST graph. -/
theorem horizontal_geometry_preserved
    (E t p : ℕ) (z : ConstructorNode V H) :
    OmniversalGraph.Reachable (coupledGraph (V := V) (H := H))
      ⟨⟨E,t,p⟩,z⟩ ⟨⟨E,t+1,p⟩,z⟩ := by
  exact OmniversalGraph.reachable_of_event
    (coupledGraph (V := V) (H := H))
    (CoupledEvent.arithmetic ⟨E,t,p⟩ ⟨E,t+1,p⟩ z
      (ArithmeticEvent.horizontal E t p))

/-- Every old vertical depth successor remains an actual event. -/
theorem vertical_geometry_preserved
    (E t p : ℕ) (z : ConstructorNode V H) :
    OmniversalGraph.Reachable (coupledGraph (V := V) (H := H))
      ⟨⟨E,t,p⟩,z⟩ ⟨⟨E,t,p+1⟩,z⟩ := by
  exact OmniversalGraph.reachable_of_event
    (coupledGraph (V := V) (H := H))
    (CoupledEvent.arithmetic ⟨E,t,p⟩ ⟨E,t,p+1⟩ z
      (ArithmeticEvent.vertical E t p))

/-- Meaning of algebraicity for the product graph: the true
geometric state has a native representative. The arithmetic
coordinate carries no miraculous Hodge representation. -/
def GeometricallyAlgebraic (s : CoupledNode (V := V) (H := H)) : Prop :=
  AlgebraicNode s.geometry

def GeometricSeed (s : CoupledNode (V := V) (H := H)) : Prop :=
  AlgebraicSeed s.geometry

/-- Every arithmetic event and every legitimate geometric event
preserves the existence of a REAL algebraic-cycle witness. -/
theorem coupledEvent_algebraic_stable :
    OmniversalGraph.EventStable (coupledGraph (V := V) (H := H))
      (GeometricallyAlgebraic (V := V) (H := H)) := by
  intro a b e ha
  cases e with
  | arithmetic a b z h =>
      exact ha
  | geometry a z w e =>
      exact certifiedEvent_preserves_algebraic e ha

/-- Unlimited GST closure can never assert that a nonalgebraic
Hodge target has become algebraic purely from the existence
of arithmetic/cosmological graph events. -/
theorem coupledClosure_sound
    {s : CoupledNode (V := V) (H := H)}
    (hs : OmniversalGraph.Closure (coupledGraph (V := V) (H := H))
       (GeometricSeed (V := V) (H := H)) s) :
    GeometricallyAlgebraic (V := V) (H := H) s := by
  exact OmniversalGraph.closure_sound
    (coupledGraph (V := V) (H := H))
    (by
      intro s hs
      exact algebraicSeed_sound (V := V) (D := H) s.geometry hs)
    (coupledEvent_algebraic_stable (V := V) (H := H))
    s hs

/-- Equation (5) becomes a rigorously typed union of finite
construction stages, with NO scalar infinity or convergence
postulate, and NO finite truncation of the graph. -/
theorem exact_all_dimension_stage_union
    (Seed : ℕ → CoupledNode (V := V) (H := H) → Prop)
    (s : CoupledNode (V := V) (H := H)) :
    OmniversalGraph.Closure (coupledGraph (V := V) (H := H))
      (fun z => ∃ n, Seed n z) s ↔
      ∃ n, OmniversalGraph.Closure
        (coupledGraph (V := V) (H := H)) (Seed n) s := by
  exact OmniversalGraph.closure_indexed_union_exact
    (coupledGraph (V := V) (H := H)) Seed s

/-- Every genuinely constructed old-geometric proof has the
same arithmetic-sector realization at any fixed physical state. -/
theorem geometric_step_at_any_arithmetic_address
    (a : ArithmeticNode)
    {z w : ConstructorNode V H}
    (e : CertifiedEvent z w) :
    OmniversalGraph.Reachable (coupledGraph (V := V) (H := H))
      ⟨a,z⟩ ⟨a,w⟩ :=
  OmniversalGraph.reachable_of_event
    (coupledGraph (V := V) (H := H))
    (CoupledEvent.geometry a z w e)

#check coupledGraph
#check geometricProjection
#check horizontal_geometry_preserved
#check vertical_geometry_preserved
#check coupledClosure_sound
#check exact_all_dimension_stage_union
#print axioms coupledClosure_sound
#print axioms exact_all_dimension_stage_union

end GSTGraphV2CMNMCoupledUniverse
