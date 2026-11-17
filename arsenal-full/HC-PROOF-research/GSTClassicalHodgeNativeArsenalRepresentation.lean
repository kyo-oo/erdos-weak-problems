import GSTClassicalHodgeGlobalArsenalPropagationCrown
import GSTClassicalHodgeCycleOperatorNaturality
import GSTClassicalHodgeProjectiveCorrespondenceAlgebra

/-!
# GST CLASSICAL HODGE — NATIVE ARSENAL REPRESENTATION

The previous global crown only needs one fact from the geometric side in each
weight: every GST matrix-unit image of the propagated algebraic seed remains
algebraic.  This module derives that fact from a much more structural object:
a native cycle-class representation of the rank-free matrix-unit algebra.

For every pair of genuine Hodge basis indices `(i,j)`, a native cycle operator
acts on actual codimension-p algebraic cycles and a cohomological operator
acts on rational singular cohomology, with an exact commuting cycle-class
square.  On the genuine Hodge fiber the cohomological action is required to be
exactly the matrix unit `E_{i,j}`.

Once such a representation exists, the actual cycle-class range — hence the
algebraic Hodge subspace — is invariant by construction.  No separate
`orbit_algebraic` assumption remains.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGlobalArsenalPropagationCrown

namespace GSTClassicalHodgeNativeArsenalRepresentation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Native realization of every rank-free Hodge matrix unit. -/
structure NativeArsenalRepresentation
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) where
  operator :
    ClassicalHodgeBasisIndex V H p →
    ClassicalHodgeBasisIndex V H p →
      CycleClassOperatorPair V H p
  hodge_action :
    ∀ i j : ClassicalHodgeBasisIndex V H p,
      ∀ alpha : ClassicalHodgeFiber V H p,
        (operator i j).cohomologyOperator alpha.1 =
          (hodgeMatrixUnit i j alpha).1

namespace NativeArsenalRepresentation

/-- Every represented matrix unit preserves the full native cycle-class range. -/
theorem range_stable
    (R : NativeArsenalRepresentation V H p)
    (i j : ClassicalHodgeBasisIndex V H p) :
    ∀ x,
      x ∈ LinearMap.range (H.cycleClass p) →
        (R.operator i j).cohomologyOperator x ∈
          LinearMap.range (H.cycleClass p) :=
  (R.operator i j).cycleClass_range_stable

/-- Hence every represented matrix unit preserves the actual atomic span. -/
theorem atomic_stable
    (R : NativeArsenalRepresentation V H p)
    (i j : ClassicalHodgeBasisIndex V H p) :
    ∀ x,
      x ∈ pointCycleClassSpan p (H.cycleClass p) →
        (R.operator i j).cohomologyOperator x ∈
          pointCycleClassSpan p (H.cycleClass p) :=
  (R.operator i j).atomicSpan_stable

/-- **ARSENAL INVARIANCE IS DERIVED.** The algebraic Hodge subspace is stable
under every rank-free GST matrix unit. -/
theorem algebraicHodgeSubspace_invariant
    (R : NativeArsenalRepresentation V H p) :
    RankFreeArsenalInvariant (AlgebraicHodgeSubspace V H p) := by
  intro i j alpha halpha
  have hatomic : alpha.1 ∈ pointCycleClassSpan p (H.cycleClass p) := halpha
  have hstable := R.atomic_stable i j alpha.1 hatomic
  have hact := R.hodge_action i j alpha
  change (hodgeMatrixUnit i j alpha).1 ∈
    pointCycleClassSpan p (H.cycleClass p)
  rw [← hact]
  exact hstable

/-- One algebraic seed automatically satisfies the entire one-step orbit law
needed by `AlgebraicArsenalSeed`. -/
noncomputable def toAlgebraicArsenalSeed
    (R : NativeArsenalRepresentation V H p)
    (seed : ClassicalHodgeFiber V H p)
    (hseed0 : seed ≠ 0)
    (hseedAlg : seed ∈ AlgebraicHodgeSubspace V H p) :
    GSTClassicalHodgeAlgebraicArsenalSaturation.AlgebraicArsenalSeed V H p where
  seed := seed
  seed_ne_zero := hseed0
  seed_algebraic := hseedAlg
  orbit_algebraic := by
    intro i j
    exact R.algebraicHodgeSubspace_invariant i j seed hseedAlg

/-- A nonzero algebraic seed plus native representation of the full arsenal
forces the complete Hodge fiber to be algebraic. -/
theorem algebraicHodgeSubspace_eq_top
    (R : NativeArsenalRepresentation V H p)
    (seed : ClassicalHodgeFiber V H p)
    (hseed0 : seed ≠ 0)
    (hseedAlg : seed ∈ AlgebraicHodgeSubspace V H p) :
    AlgebraicHodgeSubspace V H p = ⊤ :=
  (R.toAlgebraicArsenalSeed seed hseed0 hseedAlg).algebraicHodgeSubspace_eq_top

end NativeArsenalRepresentation

/-- Global native arsenal representation, one exact representation in every
Hodge weight. -/
structure GlobalNativeArsenalRepresentation
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) where
  weight : ∀ p : Nat, NativeArsenalRepresentation V H p

/-- Cross-weight seed propagation plus a global native arsenal representation
closes the exact Stage-2G statement.  The separate orbit-algebraicity field of
the previous crown is now completely derived. -/
noncomputable def globalArsenalPropagationOfNativeRepresentation
    (F : GSTClassicalHodgeCrossWeightNativePropagation.SeedPropagationFamily V H)
    (h0 : F.seed 0 ∈ AlgebraicHodgeSubspace V H 0)
    (R : GlobalNativeArsenalRepresentation V H) :
    GlobalArsenalPropagation V H where
  propagation := F
  zero_seed_algebraic := h0
  arsenal := fun p => {
    orbit_algebraic := by
      intro i j
      have hseed := F.algebraic_of_zero_seed h0 p
      exact (R.weight p).algebraicHodgeSubspace_invariant i j (F.seed p) hseed
  }

/-- **NATIVE-ARSENAL CLASSICAL HODGE CROWN.** -/
theorem bigradedBettiHodge_of_nativeArsenal
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (F : GSTClassicalHodgeCrossWeightNativePropagation.SeedPropagationFamily V H)
    (h0 : F.seed 0 ∈ AlgebraicHodgeSubspace V H 0)
    (R : GlobalNativeArsenalRepresentation V H) :
    BigradedBettiHodgeStatement V H :=
  (globalArsenalPropagationOfNativeRepresentation F h0 R).bigradedBettiHodge

#check NativeArsenalRepresentation
#check NativeArsenalRepresentation.range_stable
#check NativeArsenalRepresentation.atomic_stable
#check NativeArsenalRepresentation.algebraicHodgeSubspace_invariant
#check NativeArsenalRepresentation.toAlgebraicArsenalSeed
#check GlobalNativeArsenalRepresentation
#check globalArsenalPropagationOfNativeRepresentation
#check bigradedBettiHodge_of_nativeArsenal

#print axioms NativeArsenalRepresentation.algebraicHodgeSubspace_invariant
#print axioms NativeArsenalRepresentation.algebraicHodgeSubspace_eq_top
#print axioms bigradedBettiHodge_of_nativeArsenal

end GSTClassicalHodgeNativeArsenalRepresentation
