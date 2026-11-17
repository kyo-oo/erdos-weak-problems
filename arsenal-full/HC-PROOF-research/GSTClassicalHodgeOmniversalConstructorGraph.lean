import GSTClassicalHodgeOmniversalClosure
import GSTClassicalHodgePointNormalForm
import GSTNativeCodimensionCyclePresentation
import GSTClassicalHodgePrincipalCutSuccessorOperator
import GSTClassicalHodgeProjectivePointTransport

/-!
# GST CLASSICAL HODGE — CONCRETE OMNIVERSAL CONSTRUCTOR GRAPH

The abstract closure theorem is useful only if genuine Hodge geometry can be
placed inside the graph without assuming its conclusion.  This file gives the
first concrete realization.

The three GST sectors are used here as an explicit bookkeeping realization:

* `null` carries geometric points and codimension-point states;
* `altMinus` carries native algebraic cycles;
* `gstPlus` carries rational Betti and Hodge states.

This sectoring is not asserted to be the unique interpretation of the historic
three physical sectors.  What is invariant is the typed event semantics.

The primitive events below are all genuine constructors:

* a carrier point with a codimension certificate becomes a codimension point;
* a codimension point gives its native unit cycle;
* a native cycle gives its genuine Betti cycle class;
* whenever that class is certified Hodge, it becomes the corresponding Hodge
  state;
* a Hodge state forgets to its underlying Betti class.

No event sends an arbitrary Hodge class to a cycle.  Therefore total Hodge
reachability remains a real theorem to be proved, not an encoded assumption.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open CategoryTheory

namespace GSTClassicalHodgeOmniversalConstructorGraph

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeProjectivePointTransport
open GSTClassicalHodgeOmniversalClosure
open GSTGraphV2OmniversalCore

variable {V : SmoothProjectiveComplexScheme}
variable {D : HodgeBigradedBettiData V}

/-- Concrete Hodge-construction nodes living over all codimensions at once. -/
inductive ConstructorNode
    (V : SmoothProjectiveComplexScheme)
    (D : HodgeBigradedBettiData V) : Type
  | carrierPoint (x : V.X)
  | codimPoint (q : Nat) (x : CodimensionPoint V.X q)
  | cycle (q : Nat) (Z : codimensionCycles V.X q)
  | betti (q : Nat) (alpha : RationalSingularCohomology D.analytification (2 * q))
  | hodge (q : Nat) (alpha : ClassicalHodgeFiber V D q)

/-- Three-sector realization of the Hodge constructor universe. -/
def constructorSector : ConstructorNode V D → Sector
  | .carrierPoint _ => .null
  | .codimPoint _ _ => .null
  | .cycle _ _ => .altMinus
  | .betti _ _ => .gstPlus
  | .hodge _ _ => .gstPlus

/-- Genuine primitive constructor events. -/
inductive ConstructorEvent :
    ConstructorNode V D → ConstructorNode V D → Prop
  | certifyCodimension (q : Nat) (x : CodimensionPoint V.X q) :
      ConstructorEvent (.carrierPoint x.1) (.codimPoint q x)
  | pointCycle (q : Nat) (x : CodimensionPoint V.X q) :
      ConstructorEvent (.codimPoint q x)
        (.cycle q (codimensionPointCycle V.X q x))
  | cycleClass (q : Nat) (Z : codimensionCycles V.X q) :
      ConstructorEvent (.cycle q Z)
        (.betti q (D.cycleClass q Z))
  | nativePrincipalCut (q : Nat) (Z : codimensionCycles V.X q) :
      ConstructorEvent (.cycle q Z)
        (.cycle (q + 1) (successorNativeOperator V q Z))
  | nativeProjectivePushforward (q : Nat) (f : V.X ⟶ V.X)
      (Z : codimensionCycles V.X q) :
      ConstructorEvent (.cycle q Z)
        (.cycle q (smoothProjectiveNativePushforward V f q Z))
  | cycleHodge (q : Nat) (Z : codimensionCycles V.X q)
      (hHodge : D.cycleClass q Z ∈ rationalHodgeSubspace (D.hodgeBigrading q)) :
      ConstructorEvent (.cycle q Z)
        (.hodge q ⟨D.cycleClass q Z, hHodge⟩)
  | hodgeUnderlying (q : Nat) (alpha : ClassicalHodgeFiber V D q) :
      ConstructorEvent (.hodge q alpha)
        (.betti q alpha.1)

/-- Concrete carrier-agnostic graph of the currently materialized Hodge
constructors. -/
def constructorGraph
    (V : SmoothProjectiveComplexScheme)
    (D : HodgeBigradedBettiData V) : OmniversalGraph where
  Node := ConstructorNode V D
  sector := constructorSector
  Event := ConstructorEvent

/-- Genuine algebraic seeds: actual native cycles are available without any
Hodge conclusion. -/
def AlgebraicSeed : ConstructorNode V D → Prop
  | .cycle _ _ => True
  | _ => False

/-- Semantic algebraicity of arbitrary constructor nodes.  On Betti/Hodge
nodes this literally means existence of a native cycle representative. -/
def AlgebraicNode : ConstructorNode V D → Prop
  | .carrierPoint _ => True
  | .codimPoint _ _ => True
  | .cycle _ _ => True
  | .betti q alpha =>
      ∃ Z : codimensionCycles V.X q, D.cycleClass q Z = alpha
  | .hodge q alpha =>
      ∃ Z : codimensionCycles V.X q, D.cycleClass q Z = alpha.1

/-- Every genuine cycle seed is algebraic. -/
theorem algebraicSeed_sound
    (x : ConstructorNode V D) :
    AlgebraicSeed x → AlgebraicNode x := by
  cases x <;> simp [AlgebraicSeed, AlgebraicNode]

/-- **CONSTRUCTOR EVENTS PRESERVE ALGEBRAICITY.**
This is proved constructor-by-constructor; no Hodge surjectivity is used. -/
theorem constructorEvent_preserves_algebraic :
    OmniversalGraph.EventStable (constructorGraph V D) AlgebraicNode := by
  intro x y e hx
  cases e with
  | certifyCodimension q x =>
      trivial
  | pointCycle q x =>
      trivial
  | cycleClass q Z =>
      exact ⟨Z, rfl⟩
  | nativePrincipalCut q Z =>
      trivial
  | nativeProjectivePushforward q f Z =>
      trivial
  | cycleHodge q Z hHodge =>
      exact ⟨Z, rfl⟩
  | hodgeUnderlying q alpha =>
      exact hx

/-- The abstract exact-Hodge closure semantics instantiated by genuine native
cycle constructors. -/
def constructorHodgeSemantics :
    HodgeClosureSemantics V D (constructorGraph V D) where
  seed := AlgebraicSeed
  algebraic := AlgebraicNode
  hodgeNode := fun q alpha => .hodge q alpha
  seed_algebraic := algebraicSeed_sound
  event_preserves_algebraic := constructorEvent_preserves_algebraic
  hodgeNode_realizes_cycle := by
    intro q alpha h
    exact h

/-- Precise remaining closure theorem for this constructor graph: every Hodge
state is generated from genuine native algebraic-cycle seeds. -/
def ConstructorCompleteClosure : Prop :=
  (constructorHodgeSemantics (V := V) (D := D)).CompleteUnaryClosure

/-- **CONCRETE CONSTRUCTOR CLOSURE ⇒ EXACT HODGE.**
Proving `ConstructorCompleteClosure` after enriching this graph only with
sound geometric events is sufficient for the literal rational Hodge
conjecture. -/
theorem exactHodge_of_constructorCompleteClosure
    (h : ConstructorCompleteClosure (V := V) (D := D)) :
    GSTClassicalHodgeExactClayStatement.EveryHodgeClassIsRationalAlgebraic D := by
  exact
    (constructorHodgeSemantics (V := V) (D := D)).exactHodge_of_completeUnaryClosure h

/-- The same closure proves the literal finite rational combination statement. -/
theorem finiteCombination_of_constructorCompleteClosure
    (h : ConstructorCompleteClosure (V := V) (D := D)) :
    GSTClassicalHodgeExactClayStatement.EveryHodgeClassIsFiniteRationalCombination D := by
  exact
    (constructorHodgeSemantics (V := V) (D := D)).finiteCombination_of_completeUnaryClosure h

/-- Existing point-to-cycle-to-Betti construction is an explicit two-event
causal chain in the omniversal graph. -/
theorem point_cycle_betti_reachable
    (q : Nat) (x : CodimensionPoint V.X q) :
    OmniversalGraph.Reachable (constructorGraph V D)
      (.codimPoint q x)
      (.betti q (D.cycleClass q (codimensionPointCycle V.X q x))) := by
  apply OmniversalGraph.reachable_trans (constructorGraph V D)
  · exact OmniversalGraph.reachable_of_event (constructorGraph V D)
      (ConstructorEvent.pointCycle q x)
  · exact OmniversalGraph.reachable_of_event (constructorGraph V D)
      (ConstructorEvent.cycleClass q (codimensionPointCycle V.X q x))

/-! ## Native geometry as actual GST causal constructors

The original constructor graph certified point -> cycle -> Betti arrows.
It now contains two further REAL geometric operations:

* native principal cuts, which raise codimension by exactly one in the
  algebraic-cycle space, with their existing exact-stratum filtering;
* actual scheme-endomorphism point pushforwards, including residue-degree
  weighting and the codimension-p cut-off.

These are not invented cohomology operators and do not assume a target Hodge
basis representative.  Each arrow is already an independently defined
linear map on real native algebraic cycles.
-/

/-- Every already-constructed native principal cut is an actual one-step
reachable GST event in the enlarged three-sector constructor graph. -/
theorem native_principalCut_reachable
    (q : Nat) (Z : codimensionCycles V.X q) :
    OmniversalGraph.Reachable (constructorGraph V D)
      (.cycle q Z)
      (.cycle (q + 1) (successorNativeOperator V q Z)) :=
  OmniversalGraph.reachable_of_event (constructorGraph V D)
    (ConstructorEvent.nativePrincipalCut q Z)

/-- Every genuine projective endomorphism acts as a certified native-cycle
event, respecting the existing residue-degree and codimension semantics. -/
theorem native_projectivePushforward_reachable
    (q : Nat) (f : V.X ⟶ V.X) (Z : codimensionCycles V.X q) :
    OmniversalGraph.Reachable (constructorGraph V D)
      (.cycle q Z)
      (.cycle q (smoothProjectiveNativePushforward V f q Z)) :=
  OmniversalGraph.reachable_of_event (constructorGraph V D)
    (ConstructorEvent.nativeProjectivePushforward q f Z)

/-- One GST path now implements a genuine projective principal cut followed
by the exact Betti cycle-class construction.  The conclusion is a forward
geometric construction, never a reverse Hodge-class selector. -/
theorem native_principalCut_to_betti_reachable
    (q : Nat) (Z : codimensionCycles V.X q) :
    OmniversalGraph.Reachable (constructorGraph V D)
      (.cycle q Z)
      (.betti (q + 1)
        (D.cycleClass (q + 1) (successorNativeOperator V q Z))) := by
  exact OmniversalGraph.reachable_trans (constructorGraph V D)
    (native_principalCut_reachable q Z)
    (OmniversalGraph.reachable_of_event (constructorGraph V D)
      (ConstructorEvent.cycleClass (q + 1) (successorNativeOperator V q Z)))

/-- All genuine projective native transports also possess an explicit
two-event native -> native -> Betti path, with no assumed naturality bridge. -/
theorem native_projectivePushforward_to_betti_reachable
    (q : Nat) (f : V.X ⟶ V.X) (Z : codimensionCycles V.X q) :
    OmniversalGraph.Reachable (constructorGraph V D)
      (.cycle q Z)
      (.betti q
        (D.cycleClass q (smoothProjectiveNativePushforward V f q Z))) := by
  exact OmniversalGraph.reachable_trans (constructorGraph V D)
    (native_projectivePushforward_reachable q f Z)
    (OmniversalGraph.reachable_of_event (constructorGraph V D)
      (ConstructorEvent.cycleClass q
        (smoothProjectiveNativePushforward V f q Z)))

/-! ## Exact completeness firewall — an invariant of the concrete graph

The enriched constructor graph now incorporates genuine codimension-changing
and scheme-morphism geometric machinery from elsewhere in the GST library.
Nevertheless, its Hodge states are reached from an actual cycle seed
precisely when they have an actual cycle representative.

This is not an impossibility theorem for future NEW geometric constructions;
it is an exact characterization of what the present certified constructor
language achieves.  Adding arbitrary formal connectivity would break its
semantic meaning, and adding more sound native cycle operations alone cannot
manufacture an algebraic representative of a missing Hodge class.
-/

/-- **EXACT CONSTRUCTOR PATH CLASSIFICATION FOR EVERY HODGE STATE.**
Reaching a rational Hodge state from a certified native cycle seed is
equivalent to genuine rational algebraicity.  The reverse implication is
CONSTRUCTIVE: use the given native representative and its one-step
cycle -> Hodge event. -/
theorem hodge_constructorClosure_iff_genuine_native_representation
    (q : Nat) (alpha : ClassicalHodgeFiber V D q) :
    OmniversalGraph.Closure (constructorGraph V D)
      AlgebraicSeed (.hodge q alpha) ↔
    ∃ Z : codimensionCycles V.X q,
      D.cycleClass q Z = alpha.1 := by
  constructor
  · intro hreach
    have halg : AlgebraicNode (ConstructorNode.hodge q alpha) :=
      (constructorHodgeSemantics (V := V) (D := D))
        |>.algebraic_of_unaryClosure hreach
    exact halg
  · rintro ⟨Z, hZ⟩
    have hclass : D.cycleClass q Z ∈
        rationalHodgeSubspace (D.hodgeBigrading q) := by
      rw [hZ]
      exact alpha.2
    have htarget :
        (⟨D.cycleClass q Z, hclass⟩ : ClassicalHodgeFiber V D q) =
          alpha :=
      Subtype.ext hZ
    refine ⟨.cycle q Z, trivial, ?_⟩
    have hstep :=
      OmniversalGraph.reachable_of_event (constructorGraph V D)
        (ConstructorEvent.cycleHodge q Z hclass)
    simpa only [htarget] using hstep

/-- **EXACT CONSTRUCTOR COMPLETENESS CLASSIFICATION.**
For this ACTUAL geometric constructor graph, total GST event reachability
of rational Hodge states is equivalent to the literal classical Hodge
statement.  This theorem is NOT used as a new Hodge premise; it tells us
exactly what remains unconstructed in any proposed GST event completion. -/
theorem constructorCompleteClosure_iff_exactHodge :
    ConstructorCompleteClosure (V := V) (D := D) ↔
      GSTClassicalHodgeExactClayStatement.EveryHodgeClassIsRationalAlgebraic D := by
  constructor
  · exact exactHodge_of_constructorCompleteClosure
  · intro h q alpha
    exact (hodge_constructorClosure_iff_genuine_native_representation
      (V := V) (D := D) q alpha).2 (h q alpha.1 alpha.2)

#check native_principalCut_reachable
#check native_projectivePushforward_reachable
#check native_principalCut_to_betti_reachable
#check native_projectivePushforward_to_betti_reachable
#check hodge_constructorClosure_iff_genuine_native_representation
#check constructorCompleteClosure_iff_exactHodge

#print axioms native_principalCut_to_betti_reachable
#print axioms native_projectivePushforward_to_betti_reachable
#print axioms hodge_constructorClosure_iff_genuine_native_representation
#print axioms constructorCompleteClosure_iff_exactHodge

#check ConstructorNode
#check ConstructorEvent
#check constructorGraph
#check AlgebraicSeed
#check AlgebraicNode
#check constructorEvent_preserves_algebraic
#check constructorHodgeSemantics
#check ConstructorCompleteClosure
#check exactHodge_of_constructorCompleteClosure
#check finiteCombination_of_constructorCompleteClosure
#check point_cycle_betti_reachable

end GSTClassicalHodgeOmniversalConstructorGraph
