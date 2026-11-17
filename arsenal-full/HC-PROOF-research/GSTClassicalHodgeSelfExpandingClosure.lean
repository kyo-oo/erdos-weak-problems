import GSTGraphV2RecursiveStateCausality
import GSTGeometricRealizationStage2D
import GSTGeometricRealizationStage2F
import GSTClassicalHodgeExactClayStatement
import GSTClassicalHodgeFiberedCosmology

/-!
# GST CLASSICAL HODGE — SELF-EXPANDING COSMIC CLOSURE

This file does not make Hodge geometry a fixed collection of nodes in a fixed
graph.  Instead it interprets the genuine classical objects as states living
inside distinguished worlds of a much larger `SelfExpandingCosmos`.

The ambient cosmos may contain arbitrarily many additional worlds, including
worlds not anticipated by the Hodge formalization.  The cycle, Betti, and Hodge
worlds below are only marked branches inside it.

Two independent closures matter:

1. **world closure** — the relevant geometry worlds themselves must be born
   from the three GST roots through certified world-generation events;
2. **state closure** — every genuine Hodge state must be causally generated
   from genuine algebraic-cycle states through semantic-preserving state flow.

When both are achieved we call the realization `CompleteCosmicClosure`.
The exact rational Hodge statement follows from the state half, while the world
half records the stronger cosmological claim that the geometry was generated
inside GST rather than externally attached to it.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

universe u v w z

namespace GSTClassicalHodgeSelfExpandingClosure

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTGraphV2SelfExpandingCosmology
open GSTGraphV2RecursiveStateCausality

variable {V : SmoothProjectiveComplexScheme}
variable {D : HodgeBigradedBettiData V}

/-- A genuine Hodge interpretation inside an arbitrary recursively expanding
GST cosmos.

No completeness statement is a field.  In particular, this structure does not
assume that all Hodge states are algebraic or reachable. -/
structure HodgeRecursiveRealization
    (V : SmoothProjectiveComplexScheme)
    (D : HodgeBigradedBettiData V)
    (C : SelfExpandingCosmos.{u,v,w,z}) where
  cycleWorld : Nat → C.World
  bettiWorld : Nat → C.World
  hodgeWorld : Nat → C.World

  cycleState :
    ∀ p : Nat, codimensionCycles V.X p → C.State (cycleWorld p)
  bettiState :
    ∀ p : Nat,
      RationalSingularCohomology D.analytification (2 * p) →
        C.State (bettiWorld p)
  hodgeState :
    ∀ p : Nat, ClassicalHodgeFiber V D p → C.State (hodgeWorld p)

  /-- Actual cycle-class formation is one state transition in the evolving
  cosmos. -/
  cycleClassStep :
    ∀ (p : Nat) (Z : codimensionCycles V.X p),
      StateStep C
        ⟨cycleWorld p, cycleState p Z⟩
        ⟨bettiWorld p, bettiState p (D.cycleClass p Z)⟩

  /-- Forgetting the Hodge certificate gives the underlying Betti class as a
  genuine causal transition. -/
  hodgeUnderlyingStep :
    ∀ (p : Nat) (alpha : ClassicalHodgeFiber V D p),
      StateStep C
        ⟨hodgeWorld p, hodgeState p alpha⟩
        ⟨bettiWorld p, bettiState p alpha.1⟩

  /-- Semantic algebraicity on arbitrary states of the much larger cosmos. -/
  algebraic : PackedState C → Prop

  /-- Every genuine native cycle state starts algebraic. -/
  cycleState_algebraic :
    ∀ (p : Nat) (Z : codimensionCycles V.X p),
      algebraic ⟨cycleWorld p, cycleState p Z⟩

  /-- Every permitted state transition preserves algebraicity. -/
  state_preserves_algebraic :
    StateStable C algebraic

  /-- On a genuine Hodge state, semantic algebraicity decodes to an actual
  native cycle with exactly that cycle class. -/
  hodgeState_realizes_cycle :
    ∀ (p : Nat) (alpha : ClassicalHodgeFiber V D p),
      algebraic ⟨hodgeWorld p, hodgeState p alpha⟩ →
      ∃ Z : codimensionCycles V.X p,
        D.cycleClass p Z = alpha.1

namespace HodgeRecursiveRealization

variable {C : SelfExpandingCosmos.{u,v,w,z}}
variable (R : HodgeRecursiveRealization V D C)

/-- Genuine algebraic-cycle states are the only primitive state seeds. -/
def CycleSeed (x : PackedState C) : Prop :=
  ∃ (p : Nat) (Z : codimensionCycles V.X p),
    x = ⟨R.cycleWorld p, R.cycleState p Z⟩

/-- Every cycle seed is semantically algebraic. -/
theorem cycleSeed_sound
    (x : PackedState C) :
    R.CycleSeed x → R.algebraic x := by
  rintro ⟨p,Z,rfl⟩
  exact R.cycleState_algebraic p Z

/-- The marked classical geometry worlds are themselves generated from the
three GST roots.  The ambient cosmos may contain many additional worlds. -/
def GeometryWorldClosure : Prop :=
  (∀ p : Nat, C.Generated (R.cycleWorld p)) ∧
  (∀ p : Nat, C.Generated (R.bettiWorld p)) ∧
  (∀ p : Nat, C.Generated (R.hodgeWorld p))

/-- Every genuine rational Hodge state is generated from genuine algebraic
cycle states by state evolution through the recursively expanding cosmos. -/
def HodgeStateClosure : Prop :=
  ∀ (p : Nat) (alpha : ClassicalHodgeFiber V D p),
    StateClosure C R.CycleSeed
      ⟨R.hodgeWorld p, R.hodgeState p alpha⟩

/-- **COMPLETE COSMIC CLOSURE.**
The geometry itself is generated from the three roots and every genuine Hodge
state is generated from actual algebraic-cycle states. -/
def CompleteCosmicClosure : Prop :=
  R.GeometryWorldClosure ∧ R.HodgeStateClosure

/-- State closure alone propagates algebraicity to every genuine Hodge state. -/
theorem hodgeState_algebraic_of_closure
    (hState : R.HodgeStateClosure)
    (p : Nat) (alpha : ClassicalHodgeFiber V D p) :
    R.algebraic ⟨R.hodgeWorld p, R.hodgeState p alpha⟩ := by
  apply stateClosure_sound C
    (P := R.algebraic)
    (Seed := R.CycleSeed)
    (R.cycleSeed_sound)
    R.state_preserves_algebraic
  exact hState p alpha

/-- **SELF-EXPANDING CLOSURE ⇒ EXACT RATIONAL HODGE.**
The conclusion is the literal Clay-style rational Hodge statement already
formalized in `GSTClassicalHodgeExactClayStatement`. -/
theorem exactHodge_of_hodgeStateClosure
    (hState : R.HodgeStateClosure) :
    GSTClassicalHodgeExactClayStatement.EveryHodgeClassIsRationalAlgebraic D := by
  intro p alpha hHodge
  let a : ClassicalHodgeFiber V D p := ⟨alpha, hHodge⟩
  have hAlg :
      R.algebraic ⟨R.hodgeWorld p, R.hodgeState p a⟩ :=
    R.hodgeState_algebraic_of_closure hState p a
  obtain ⟨Z,hZ⟩ := R.hodgeState_realizes_cycle p a hAlg
  exact ⟨Z, hZ⟩

/-- Full cosmic closure in particular proves the exact rational Hodge target. -/
theorem exactHodge_of_completeCosmicClosure
    (h : R.CompleteCosmicClosure) :
    GSTClassicalHodgeExactClayStatement.EveryHodgeClassIsRationalAlgebraic D := by
  exact R.exactHodge_of_hodgeStateClosure h.2

/-- The finite rational-combination formulation follows as well. -/
theorem finiteCombination_of_completeCosmicClosure
    (h : R.CompleteCosmicClosure) :
    GSTClassicalHodgeExactClayStatement.EveryHodgeClassIsFiniteRationalCombination D := by
  exact
    (GSTClassicalHodgeExactClayStatement.rationalAlgebraic_iff_finiteRationalCombination
      (V := V) (H := D)).1
      (R.exactHodge_of_completeCosmicClosure h)

#check HodgeRecursiveRealization
#check HodgeRecursiveRealization.CycleSeed
#check HodgeRecursiveRealization.GeometryWorldClosure
#check HodgeRecursiveRealization.HodgeStateClosure
#check HodgeRecursiveRealization.CompleteCosmicClosure
#check HodgeRecursiveRealization.exactHodge_of_completeCosmicClosure
#check HodgeRecursiveRealization.finiteCombination_of_completeCosmicClosure

end HodgeRecursiveRealization
end GSTClassicalHodgeSelfExpandingClosure
