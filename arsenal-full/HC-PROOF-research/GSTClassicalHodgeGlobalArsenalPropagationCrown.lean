import GSTClassicalHodgeCrossWeightNativePropagation
import GSTClassicalHodgeAlgebraicArsenalSaturation
import GSTClassicalHodgeArsenalOrbitSaturation

/-!
# GST CLASSICAL HODGE — GLOBAL ARSENAL PROPAGATION CROWN

The full limitless strategy has two orthogonal engines.

* Cross-weight Lefschetz propagation transports one native algebraic seed
  through the Hodge weights.
* Rank-free GST matrix-unit saturation expands one nonzero algebraic seed in a
  fixed weight to the entire genuine rational `(p,p)` fiber.

This module composes them.  It is deliberately basis-free at the final target:
the result constructs a native codimension-p algebraic cycle for every actual
rational Hodge class.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeArsenalOrbitSaturation
open GSTClassicalHodgeAlgebraicArsenalSaturation
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeAtomicDefectDuality

namespace GSTClassicalHodgeGlobalArsenalPropagationCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Native realization of the complete rank-free GST matrix-unit arsenal in
one weight, expressed only by the property needed for algebraic saturation:
every one-step orbit of the distinguished seed remains algebraic. -/
structure WeightArsenalRealization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (seed : ClassicalHodgeFiber V H p) where
  orbit_algebraic :
    ∀ i j : ClassicalHodgeBasisIndex V H p,
      hodgeMatrixUnit i j seed ∈ AlgebraicHodgeSubspace V H p

/-- Complete limitless global data: one propagated nonzero seed in every
weight and native realization of its complete rank-free GST orbit. -/
structure GlobalArsenalPropagation
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) where
  propagation : SeedPropagationFamily V H
  zero_seed_algebraic :
    propagation.seed 0 ∈ AlgebraicHodgeSubspace V H 0
  arsenal : ∀ p : Nat,
    WeightArsenalRealization V H p (propagation.seed p)

namespace GlobalArsenalPropagation

/-- Every propagated seed is algebraic. -/
theorem seed_algebraic
    (G : GlobalArsenalPropagation V H) :
    ∀ p : Nat,
      G.propagation.seed p ∈ AlgebraicHodgeSubspace V H p :=
  G.propagation.algebraic_of_zero_seed G.zero_seed_algebraic

/-- Every weight receives the one-seed algebraic saturation package. -/
noncomputable def algebraicArsenalSeed
    (G : GlobalArsenalPropagation V H)
    (p : Nat) : AlgebraicArsenalSeed V H p where
  seed := G.propagation.seed p
  seed_ne_zero := G.propagation.seed_ne_zero p
  seed_algebraic := G.seed_algebraic p
  orbit_algebraic := G.arsenal p |>.orbit_algebraic

/-- The algebraic Hodge subspace is the whole genuine Hodge fiber in every
weight. -/
theorem algebraicHodgeSubspace_eq_top
    (G : GlobalArsenalPropagation V H)
    (p : Nat) :
    AlgebraicHodgeSubspace V H p = ⊤ :=
  (G.algebraicArsenalSeed p).algebraicHodgeSubspace_eq_top

/-- Every genuine Hodge class has an actual native codimension-p cycle. -/
theorem every_hodge_class_has_native_cycle
    (G : GlobalArsenalPropagation V H)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 :=
  (G.algebraicArsenalSeed p).every_hodge_class_has_native_cycle alpha

/-- **GLOBAL LIMITLESS HODGE CROWN.**  The propagated one-seed/full-arsenal
mechanism closes the exact Stage-2G rational Hodge statement. -/
theorem bigradedBettiHodge
    (G : GlobalArsenalPropagation V H) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  exact G.every_hodge_class_has_native_cycle p alphaH

/-- The complete atomic defect vanishes weight by weight. -/
theorem atomicDefect_zero
    (G : GlobalArsenalPropagation V H) :
    ∀ p : Nat, atomicDefectLinearMap V H p = 0 := by
  intro p
  exact (G.algebraicArsenalSeed p).atomicDefect_eq_zero

end GlobalArsenalPropagation

#check WeightArsenalRealization
#check GlobalArsenalPropagation
#check GlobalArsenalPropagation.seed_algebraic
#check GlobalArsenalPropagation.algebraicArsenalSeed
#check GlobalArsenalPropagation.algebraicHodgeSubspace_eq_top
#check GlobalArsenalPropagation.every_hodge_class_has_native_cycle
#check GlobalArsenalPropagation.bigradedBettiHodge
#check GlobalArsenalPropagation.atomicDefect_zero

#print axioms GlobalArsenalPropagation.algebraicHodgeSubspace_eq_top
#print axioms GlobalArsenalPropagation.every_hodge_class_has_native_cycle
#print axioms GlobalArsenalPropagation.bigradedBettiHodge
#print axioms GlobalArsenalPropagation.atomicDefect_zero

end GSTClassicalHodgeGlobalArsenalPropagationCrown
