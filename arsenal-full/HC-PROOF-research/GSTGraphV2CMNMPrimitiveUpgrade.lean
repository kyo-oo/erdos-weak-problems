import GSTClassicalHodgeOmniversalConstructorGraph
import GSTClassicalHodgeGeometricCycleClassSpine
import GSTCMNumberManipulationDualDetector
import GSTGraphV2ArithmeticOmniversalRealization

/-!
# GST Graph V2 — native CM–NM geometry and primitive event upgrade

This is a CONSERVATIVE EXTENSION of the existing omniversal GST graph,
not a replacement graph. It shares its actual constructor nodes and
three sectors; every old event embeds identically.

The contributor's proposed equations (4) and (5) are interpreted as:
  - A_g: two actual rational CM coefficient channels;
  - G_a: exact Number Manipulation applied to real native geometric
    projective pushforwards, never a postulated reverse cycle class;
  - infinite cosmology: indexed union of finite event closures, NOT
    an undefined real limit of n^x;
  - primitive geometry: genuine codimension-p cycles are admitted by
    the same certified native constructors, without identifying all
    Hodge states with already-algebraic cycles.

The CM–NM graph edge builds an ACTUAL codimension-p rational algebraic
cycle from an existing cycle and two real scheme morphisms, using exact
Gaussian rational arithmetic. Its cohomology is proved by the true
linear cycle-class map. The graph preserves algebraicity and includes
every old GST constructor path.

CRITICAL FIREWALL: Adding these certified edges alone does NOT prove
that arbitrary primitive Hodge classes are algebraic. The upgraded
closure is shown EXACTLY equivalent to the actual existence of a
native algebraic representative. This makes a future genuine geometric
breakthrough observable without manufacturing Hodge surjectivity.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000
noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTGraphV2CMNMPrimitiveUpgrade

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeOmniversalConstructorGraph
open GSTClassicalHodgeProjectivePointTransport
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTGraphV2OmniversalCore
open GSTGraphV2ArithmeticOmniversalRealization
open GSTCMNumberManipulationTrace

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Two canonical Gaussian-rational NM weights, derived from the
contributor's corrected indexed CM denominator. Neither can be
chosen to match an arbitrary Hodge target after the fact. -/
def cmNMRealWeight (x y : CMQ) (m : ℕ) : ℚ :=
  cmIndexedNMTrace x y m

def cmNMImagWeight (x y : CMQ) (m : ℕ) : ℚ :=
  cmImagTrace (cmInv (cmIndexedDenominator x y m))

/-- A GENUINE native algebraic cycle from two actual projective
scheme-morphism pushforwards and the fixed CM–NM weights.
This does not inject a complex Hodge class as an input cycle. -/
noncomputable def cmNMNativeGraphCycle
    (q : ℕ) (f g : V.X ⟶ V.X)
    (x y : CMQ) (m : ℕ) (Z : codimensionCycles V.X q) :
    codimensionCycles V.X q :=
  cmNMRealWeight x y m • smoothProjectiveNativePushforward V f q Z +
    cmNMImagWeight x y m • smoothProjectiveNativePushforward V g q Z

/-- Exact rational Betti cycle-class evaluation of the created
CM–NM native cycle. This is a forward geometric identity, NOT
the existence of a reverse map from arbitrary cohomology. -/
theorem cmNMNativeGraphCycle_cycleClass
    (q : ℕ) (f g : V.X ⟶ V.X)
    (x y : CMQ) (m : ℕ) (Z : codimensionCycles V.X q) :
    H.cycleClass q (cmNMNativeGraphCycle q f g x y m Z) =
      cmNMRealWeight x y m •
        H.cycleClass q (smoothProjectiveNativePushforward V f q Z) +
      cmNMImagWeight x y m •
        H.cycleClass q (smoothProjectiveNativePushforward V g q Z) := by
  simp only [cmNMNativeGraphCycle, map_add, map_smul]

/-- Native CM–NM event that augments the ACTUAL Hodge constructor
graph rather than replacing the ontological graph or inventing
an arbitrary reverse Hodge-to-cycle event. -/
inductive CertifiedEvent :
    ConstructorNode V H → ConstructorNode V H → Prop
  | legacy {a b} :
      ConstructorEvent a b → CertifiedEvent a b
  | remain (a) : CertifiedEvent a a
  | cmNM (q : ℕ) (f g : V.X ⟶ V.X)
      (x y : CMQ) (m : ℕ) (Z : codimensionCycles V.X q) :
      CertifiedEvent (.cycle q Z)
        (.cycle q (cmNMNativeGraphCycle q f g x y m Z))

/-- EXISTING omniversal Hodge geometry, plus exact native NM edges.
Every node, sector and old constructor remains unchanged. -/
def certifiedGraph : OmniversalGraph where
  Node := ConstructorNode V H
  sector := constructorSector
  Event := CertifiedEvent

/-- All old GST constructor events transport into the upgraded graph
with no loss of sectors or paths. -/
def legacyEmbedding :
    OmniversalGraph.EventHom (constructorGraph V H)
      (certifiedGraph (V := V) (H := H)) where
  toFun := id
  sector_eq := by intro a; rfl
  mapEvent := by
    intro a b e
    exact CertifiedEvent.legacy e

/-- Every path constructed by the prior GST graph still exists
after the full CM–NM native-cycle extension. -/
theorem legacy_path_survives
    {a b : ConstructorNode V H}
    (h : OmniversalGraph.Reachable (constructorGraph V H) a b) :
    OmniversalGraph.Reachable (certifiedGraph (V := V) (H := H)) a b := by
  exact OmniversalGraph.EventHom.reachable_map
    (constructorGraph V H) (legacyEmbedding (V := V) (H := H)) h

/-- Every certified CM–NM event produces an actual native cycle.
Crucially, no Hodge node is declared algebraic without an actual
cycle preimage. -/
theorem certifiedEvent_preserves_algebraic :
    OmniversalGraph.EventStable (certifiedGraph (V := V) (H := H))
      (AlgebraicNode (V := V) (D := H)) := by
  intro a b e ha
  cases e with
  | legacy e =>
      exact constructorEvent_preserves_algebraic e ha
  | remain a =>
      exact ha
  | cmNM q f g x y m Z =>
      trivial

/-- Full unbounded ontological graph closure preserves genuine
algebraicity of all states generated from real native cycles. -/
theorem certifiedClosure_sound
    {a : ConstructorNode V H}
    (ha : OmniversalGraph.Closure (certifiedGraph (V := V) (H := H))
      (AlgebraicSeed (V := V) (D := H)) a) :
    AlgebraicNode (V := V) (D := H) a := by
  exact OmniversalGraph.closure_sound
    (certifiedGraph (V := V) (H := H))
    (algebraicSeed_sound (V := V) (D := H))
    (certifiedEvent_preserves_algebraic (V := V) (H := H))
    a ha

/-- A real certified CM–NM geometry event followed by the genuine
cycle-to-Hodge event is an explicit causal history in GST Graph V2. -/
theorem cmNMNative_to_hodge_reachable
    (G : GeometricCycleClassSpine V H)
    (q : ℕ) (f g : V.X ⟶ V.X)
    (x y : CMQ) (m : ℕ) (Z : codimensionCycles V.X q) :
    OmniversalGraph.Reachable (certifiedGraph (V := V) (H := H))
      (.cycle q Z)
      (.hodge q
        ⟨H.cycleClass q (cmNMNativeGraphCycle q f g x y m Z),
         G.algebraic_is_hodge q (cmNMNativeGraphCycle q f g x y m Z)⟩) := by
  apply OmniversalGraph.reachable_trans
    (certifiedGraph (V := V) (H := H))
  · exact OmniversalGraph.reachable_of_event
      (certifiedGraph (V := V) (H := H))
      (CertifiedEvent.cmNM q f g x y m Z)
  · exact OmniversalGraph.reachable_of_event
      (certifiedGraph (V := V) (H := H))
      (CertifiedEvent.legacy
        (ConstructorEvent.cycleHodge q
          (cmNMNativeGraphCycle q f g x y m Z)
          (G.algebraic_is_hodge q (cmNMNativeGraphCycle q f g x y m Z))))

/-- Ontological finite-stage union is the valid meaning of a
limitless cosmology here. This is exact indexed reachability, NOT
an undefined numerical limit as x tends to infinity. -/
theorem certifiedIndexedClosure_exact
    (Seed : ℕ → ConstructorNode V H → Prop)
    (a : ConstructorNode V H) :
    OmniversalGraph.Closure (certifiedGraph (V := V) (H := H))
      (fun s => ∃ n, Seed n s) a ↔
      ∃ n, OmniversalGraph.Closure
        (certifiedGraph (V := V) (H := H)) (Seed n) a := by
  exact OmniversalGraph.closure_indexed_union_exact
    (certifiedGraph (V := V) (H := H)) Seed a

/-- Adding rational CM weights and genuine native scheme operations
does NOT silently produce a primitive Hodge representative:
the upgraded graph reaches a Hodge node iff such a native
representative really exists. One implication is algebraic
soundness, the other follows from the old actual-cycle constructor. -/
theorem certifiedHodgeClosure_iff_native
    (q : ℕ) (alpha : ClassicalHodgeFiber V H q) :
    OmniversalGraph.Closure (certifiedGraph (V := V) (H := H))
       (AlgebraicSeed (V := V) (D := H)) (.hodge q alpha) ↔
       ∃ Z : codimensionCycles V.X q,
         H.cycleClass q Z = alpha.1 := by
  constructor
  · intro hr
    exact certifiedClosure_sound (V := V) (H := H) hr
  · intro hz
    have hOld :
        OmniversalGraph.Closure (constructorGraph V H)
          (AlgebraicSeed (V := V) (D := H)) (.hodge q alpha) :=
      (hodge_constructorClosure_iff_genuine_native_representation
        (V := V) (D := H) q alpha).2 hz
    rcases hOld with ⟨a, ha, hab⟩
    exact ⟨a, ha, legacy_path_survives (V := V) (H := H) hab⟩

#check cmNMNativeGraphCycle
#check cmNMNativeGraphCycle_cycleClass
#check legacyEmbedding
#check certifiedClosure_sound
#check cmNMNative_to_hodge_reachable
#check certifiedIndexedClosure_exact
#check certifiedHodgeClosure_iff_native

#print axioms cmNMNativeGraphCycle_cycleClass
#print axioms certifiedClosure_sound
#print axioms certifiedHodgeClosure_iff_native

end GSTGraphV2CMNMPrimitiveUpgrade
