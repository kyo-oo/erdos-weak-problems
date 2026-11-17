import GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
import GSTClassicalHodgeAtomicSpan
import GSTClassicalHodgeExactClayStatement
open GSTClassicalHodgeAtomicSpan

/-!
# GST CLASSICAL HODGE — CYCLIC REALIZED-CORRESPONDENCE ATTACK

This file removes the remaining all-pairs matrix-unit packaging from the final
geometric attack.

Fix one genuine nonzero algebraic Hodge seed in a weight p.  A target Hodge
class is called reachable when ONE finite rational word of ACTUAL realized
closed correspondences carries the seed class to that target class.

Every realized word preserves the genuine cycle-class range.  Consequently,
if the single seed is cyclic for the realized correspondence algebra, the whole
Hodge fiber is algebraic.  No basis cycle, matrix-unit descent, arbitrary
ambient extension, or Hodge-surjectivity hypothesis is used in the proof.

Thus the remaining geometric problem can be attacked as one representation
statement about the actual correspondence algebra: construct a cyclic algebraic
Hodge seed.
-/

set_option maxHeartbeats 80000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCyclicRealizedCorrespondenceAttack

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- One target Hodge class lies in the genuine realized-correspondence orbit of
one fixed source Hodge class. -/
def RealizedWordReaches
    (seed alpha : ClassicalHodgeFiber V H p) : Prop :=
  ∃ W : RealizedCorrespondenceWord V H p,
    (realizedWordPair W).cohomologyOperator seed.1 = alpha.1

/-- A genuine algebraic Hodge seed is cyclic when its actual realized closed-
correspondence orbit reaches every Hodge class in the weight. -/
def IsCyclicAlgebraicSeed
    (seed : ClassicalHodgeFiber V H p) : Prop :=
  seed ∈ AlgebraicHodgeSubspace V H p ∧
  ∀ alpha : ClassicalHodgeFiber V H p, RealizedWordReaches seed alpha

/-- **REALIZED ORBITS PRESERVE ALGEBRAICITY.**
Every Hodge target reached from an algebraic seed by an actual correspondence
word is itself algebraic. -/
theorem algebraic_of_realizedWordReaches
    (seed alpha : ClassicalHodgeFiber V H p)
    (hseed : seed ∈ AlgebraicHodgeSubspace V H p)
    (hreach : RealizedWordReaches seed alpha) :
    alpha ∈ AlgebraicHodgeSubspace V H p := by
  rcases hreach with ⟨W, hW⟩
  rw [mem_AlgebraicHodgeSubspace_iff] at hseed
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at hseed
  rcases hseed with ⟨Z, hZ⟩
  have hseedRange : seed.1 ∈ LinearMap.range (H.cycleClass p) :=
    ⟨Z, hZ⟩
  have hout := realizedWord_range_stable W seed.1 hseedRange
  rw [hW] at hout
  rw [mem_AlgebraicHodgeSubspace_iff]
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
  exact hout

/-- A single cyclic algebraic seed saturates the entire genuine Hodge fiber. -/
theorem algebraicHodgeSubspace_eq_top_of_cyclicSeed
    (seed : ClassicalHodgeFiber V H p)
    (hcyc : IsCyclicAlgebraicSeed seed) :
    AlgebraicHodgeSubspace V H p = ⊤ := by
  apply top_unique
  intro alpha _
  exact algebraic_of_realizedWordReaches seed alpha hcyc.1 (hcyc.2 alpha)

/-- Weightwise cyclicity of genuine realized correspondences proves the exact
Stage-2G Hodge statement. -/
theorem bigradedBettiHodge_of_cyclicRealizedCorrespondenceSeeds
    (seed : ∀ q : Nat, ClassicalHodgeFiber V H q)
    (hcyc : ∀ q : Nat, IsCyclicAlgebraicSeed (seed q)) :
    BigradedBettiHodgeStatement V H := by
  intro q alpha halpha
  let a : ClassicalHodgeFiber V H q := ⟨alpha, halpha⟩
  have htop := algebraicHodgeSubspace_eq_top_of_cyclicSeed
    (seed q) (hcyc q)
  have ha : a ∈ AlgebraicHodgeSubspace V H q := by
    rw [htop]
    trivial
  rw [mem_AlgebraicHodgeSubspace_iff] at ha
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H q] at ha
  rcases ha with ⟨Z, hZ⟩
  exact ⟨Z, hZ⟩

/-- Literal rational Hodge-conjecture form from one cyclic genuine algebraic
seed in every weight. -/
theorem exactHodge_of_cyclicRealizedCorrespondenceSeeds
    (seed : ∀ q : Nat, ClassicalHodgeFiber V H q)
    (hcyc : ∀ q : Nat, IsCyclicAlgebraicSeed (seed q)) :
    EveryHodgeClassIsRationalAlgebraic H := by
  rw [everyHodgeClassIsRationalAlgebraic_iff_stage2G]
  exact bigradedBettiHodge_of_cyclicRealizedCorrespondenceSeeds seed hcyc

/-- Literal finite rational-combination wording of the conjecture. -/
theorem finiteCombination_of_cyclicRealizedCorrespondenceSeeds
    (seed : ∀ q : Nat, ClassicalHodgeFiber V H q)
    (hcyc : ∀ q : Nat, IsCyclicAlgebraicSeed (seed q)) :
    EveryHodgeClassIsFiniteRationalCombination H := by
  rw [← rationalAlgebraic_iff_finiteRationalCombination]
  exact exactHodge_of_cyclicRealizedCorrespondenceSeeds seed hcyc

#check RealizedWordReaches
#check IsCyclicAlgebraicSeed
#check algebraic_of_realizedWordReaches
#check algebraicHodgeSubspace_eq_top_of_cyclicSeed
#check bigradedBettiHodge_of_cyclicRealizedCorrespondenceSeeds
#check exactHodge_of_cyclicRealizedCorrespondenceSeeds
#check finiteCombination_of_cyclicRealizedCorrespondenceSeeds

#print axioms algebraic_of_realizedWordReaches
#print axioms algebraicHodgeSubspace_eq_top_of_cyclicSeed
#print axioms exactHodge_of_cyclicRealizedCorrespondenceSeeds
#print axioms finiteCombination_of_cyclicRealizedCorrespondenceSeeds

end GSTClassicalHodgeCyclicRealizedCorrespondenceAttack
