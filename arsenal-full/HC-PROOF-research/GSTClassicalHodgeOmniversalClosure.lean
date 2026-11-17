import GSTClassicalHodgeExactClayStatement
import GSTClassicalHodgeFiberedCosmology
import GSTGeometricRealizationStage2D
import GSTGeometricRealizationStage2F
import GSTGraphV2OmniversalCore
import GSTGraphV2OmniversalHyperEvents

/-!
# GST CLASSICAL HODGE — OMNIVERSAL EVENT-CLOSURE CRITERION

This file gives a precise meaning to "complete closure" for the exact rational
Hodge conjecture.

A carrier-agnostic GST graph may contain number-theoretic states, local scheme
states, cycles, cohomology classes, correspondence states, manifold states, or
other geometric/cosmological objects.  To use such a graph for Hodge, one must
supply semantics rather than merely connectivity:

* a node representing each genuine rational Hodge class;
* a seed predicate whose nodes are genuinely algebraic;
* an `algebraic` semantic predicate on arbitrary graph nodes;
* proof that every certified event preserves algebraicity;
* proof that an algebraic terminal Hodge node decodes to an actual native
  codimension-p algebraic cycle with the required cycle class.

Then total event reachability of every Hodge node from the algebraic seeds is
not an analogy: it proves the literal Clay-style target already fixed in
`GSTClassicalHodgeExactClayStatement`.

The higher-arity version covers cup products, intersections, fiber products,
Gysin constructions, correspondence synthesis, and other genuinely multi-input
geometric events.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeOmniversalClosure

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeExactClayStatement
open GSTGraphV2OmniversalCore
open GSTGraphV2OmniversalHyperEvents

universe u v w p

variable {V : SmoothProjectiveComplexScheme}
variable {D : HodgeBigradedBettiData V}
variable {G : OmniversalGraph.{u,v}}

/-- Semantic realization of the exact Hodge problem inside an omniversal event
graph.  Importantly, this structure does NOT assert that every Hodge node is
algebraic or reachable.  Those are the remaining mathematical obligations. -/
structure HodgeClosureSemantics
    (V : SmoothProjectiveComplexScheme)
    (D : HodgeBigradedBettiData V)
    (G : OmniversalGraph.{u,v}) where
  seed : G.Node → Prop
  algebraic : G.Node → Prop
  hodgeNode : ∀ q : Nat, ClassicalHodgeFiber V D q → G.Node
  seed_algebraic : ∀ x, seed x → algebraic x
  event_preserves_algebraic : OmniversalGraph.EventStable G algebraic
  hodgeNode_realizes_cycle :
    ∀ q : Nat, ∀ alpha : ClassicalHodgeFiber V D q,
      algebraic (hodgeNode q alpha) →
        ∃ Z : codimensionCycles V.X q,
          D.cycleClass q Z = alpha.1

namespace HodgeClosureSemantics

variable (S : HodgeClosureSemantics V D G)

/-- Ordinary unary-event complete closure: every genuine Hodge class node is
reachable from a genuine algebraic seed. -/
def CompleteUnaryClosure : Prop :=
  ∀ q : Nat, ∀ alpha : ClassicalHodgeFiber V D q,
    OmniversalGraph.Closure G S.seed (S.hodgeNode q alpha)

/-- Every node in the unary closure of the genuine algebraic seeds is
algebraic by semantic event preservation. -/
theorem algebraic_of_unaryClosure
    {x : G.Node}
    (hx : OmniversalGraph.Closure G S.seed x) :
    S.algebraic x := by
  exact OmniversalGraph.closure_sound G
    S.seed_algebraic S.event_preserves_algebraic x hx

/-- **UNARY COMPLETE-CLOSURE ⇒ EXACT RATIONAL HODGE.**
If every genuine rational Hodge class lies in the certified event closure of
actual algebraic seeds, the exact elementwise rational Hodge conjecture follows. -/
theorem exactHodge_of_completeUnaryClosure
    (hComplete : S.CompleteUnaryClosure) :
    EveryHodgeClassIsRationalAlgebraic D := by
  intro q alpha halpha
  let alphaH : ClassicalHodgeFiber V D q := ⟨alpha, halpha⟩
  have hclosed :
      OmniversalGraph.Closure G S.seed (S.hodgeNode q alphaH) :=
    hComplete q alphaH
  have halg : S.algebraic (S.hodgeNode q alphaH) :=
    S.algebraic_of_unaryClosure hclosed
  obtain ⟨Z, hZ⟩ := S.hodgeNode_realizes_cycle q alphaH halg
  exact ⟨Z, by simpa [alphaH] using hZ⟩

/-- Hence complete unary closure also proves the literal finite-rational-sum
formulation of the Hodge conjecture. -/
theorem finiteCombination_of_completeUnaryClosure
    (hComplete : S.CompleteUnaryClosure) :
    EveryHodgeClassIsFiniteRationalCombination D := by
  exact
    (GSTClassicalHodgeExactClayStatement.rationalAlgebraic_iff_finiteRationalCombination D).1
      (S.exactHodge_of_completeUnaryClosure hComplete)

/-- Higher-arity complete closure for a chosen hyper-event system. -/
def CompleteHyperClosure
    (K : HyperEventSystem.{u,v,w,p} G) : Prop :=
  ∀ q : Nat, ∀ alpha : ClassicalHodgeFiber V D q,
    K.Generated S.seed (S.hodgeNode q alpha)

/-- **HIGHER-ARITY COMPLETE-CLOSURE ⇒ EXACT RATIONAL HODGE.**
This is the form intended for the full constructor geometry: cup products,
intersection, pullback/pushforward, Gysin, correspondence composition, and
other multi-input operations can all be genuine certified hyper-events. -/
theorem exactHodge_of_completeHyperClosure
    (K : HyperEventSystem.{u,v,w,p} G)
    (hStable : K.SemanticallyStable S.algebraic)
    (hComplete : S.CompleteHyperClosure K) :
    EveryHodgeClassIsRationalAlgebraic D := by
  intro q alpha halpha
  let alphaH : ClassicalHodgeFiber V D q := ⟨alpha, halpha⟩
  have hgenerated : K.Generated S.seed (S.hodgeNode q alphaH) :=
    hComplete q alphaH
  have halg : S.algebraic (S.hodgeNode q alphaH) :=
    K.generated_sound S.seed_algebraic hStable hgenerated
  obtain ⟨Z, hZ⟩ := S.hodgeNode_realizes_cycle q alphaH halg
  exact ⟨Z, by simpa [alphaH] using hZ⟩

/-- Literal finite-rational-combination consequence of higher-event closure. -/
theorem finiteCombination_of_completeHyperClosure
    (K : HyperEventSystem.{u,v,w,p} G)
    (hStable : K.SemanticallyStable S.algebraic)
    (hComplete : S.CompleteHyperClosure K) :
    EveryHodgeClassIsFiniteRationalCombination D := by
  exact
    (GSTClassicalHodgeExactClayStatement.rationalAlgebraic_iff_finiteRationalCombination D).1
      (S.exactHodge_of_completeHyperClosure K hStable hComplete)

/-- Contrapositive diagnostic: if the exact Hodge statement fails, then no
sound omniversal realization can have complete unary closure.  This prevents a
mere graph-connectivity claim from masquerading as a proof. -/
theorem not_completeUnaryClosure_of_not_exactHodge
    (hfail : ¬ EveryHodgeClassIsRationalAlgebraic D) :
    ¬ S.CompleteUnaryClosure := by
  intro hComplete
  exact hfail (S.exactHodge_of_completeUnaryClosure hComplete)

/-- Hyper-event version of the same diagnostic. -/
theorem not_completeHyperClosure_of_not_exactHodge
    (K : HyperEventSystem.{u,v,w,p} G)
    (hStable : K.SemanticallyStable S.algebraic)
    (hfail : ¬ EveryHodgeClassIsRationalAlgebraic D) :
    ¬ S.CompleteHyperClosure K := by
  intro hComplete
  exact hfail (S.exactHodge_of_completeHyperClosure K hStable hComplete)

#check HodgeClosureSemantics
#check HodgeClosureSemantics.CompleteUnaryClosure
#check HodgeClosureSemantics.exactHodge_of_completeUnaryClosure
#check HodgeClosureSemantics.CompleteHyperClosure
#check HodgeClosureSemantics.exactHodge_of_completeHyperClosure
#check HodgeClosureSemantics.not_completeUnaryClosure_of_not_exactHodge
#check HodgeClosureSemantics.not_completeHyperClosure_of_not_exactHodge

end HodgeClosureSemantics
end GSTClassicalHodgeOmniversalClosure
