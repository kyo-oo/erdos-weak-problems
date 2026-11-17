import GSTClassicalHodgeAlgebraicArsenalSaturation
import GSTPureHodgeLefschetzKernel
import GSTLefschetzPoincareReciprocity
import GSTClassicalHodgeCycleOperatorNaturality

/-!
# GST CLASSICAL HODGE — CROSS-WEIGHT NATIVE PROPAGATION

Within one weight the full limitless matrix-unit arsenal saturates every
multiplicity direction from one nonzero algebraic seed.  This module supplies
the complementary graded mechanism: move an algebraic seed from codimension
`p` to codimension `q` through a native cycle operator whose cohomological
action is the GST Lefschetz propagation.

The universal pure-Hodge kernel proves that the forward diagonal coefficient
at time `2(q-p)` is the central binomial coefficient
`choose (2(q-p)) (q-p)`, hence nonzero.  Over `Q` it is invertible.  Therefore
a native graded transport realizing that Lefschetz step carries a nonzero
pure seed to a nonzero algebraic seed in the target weight; no independent
seed must be postulated there.
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
open GSTClassicalHodgeAlgebraicArsenalSaturation
open GSTPureHodgeLefschetzKernel

namespace GSTClassicalHodgeCrossWeightNativePropagation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- A native graded operator between two codimensions together with its exact
cycle-class naturality square. -/
structure GradedCycleClassOperatorPair
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p q : Nat) where
  cycleOperator :
    codimensionCycles V.X p →ₗ[ℚ] codimensionCycles V.X q
  cohomologyOperator :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * q)
  cycleClass_natural :
    ∀ Z : codimensionCycles V.X p,
      H.cycleClass q (cycleOperator Z) =
        cohomologyOperator (H.cycleClass p Z)

namespace GradedCycleClassOperatorPair

variable {p q : Nat}

/-- A source native cycle is transported to an actual target native cycle. -/
theorem image_has_native_class
    (T : GradedCycleClassOperatorPair V H p q)
    (Z : codimensionCycles V.X p) :
    ∃ W : codimensionCycles V.X q,
      H.cycleClass q W = T.cohomologyOperator (H.cycleClass p Z) :=
  ⟨T.cycleOperator Z, T.cycleClass_natural Z⟩

/-- Transport of an algebraic Hodge class remains algebraic whenever the
cohomological image lies in the target Hodge fiber. -/
theorem maps_algebraic_hodge
    (T : GradedCycleClassOperatorPair V H p q)
    (alpha : ClassicalHodgeFiber V H p)
    (halg : alpha ∈ AlgebraicHodgeSubspace V H p)
    (hq : T.cohomologyOperator alpha.1 ∈
      rationalHodgeSubspace (H.hodgeBigrading q)) :
    (⟨T.cohomologyOperator alpha.1, hq⟩ : ClassicalHodgeFiber V H q) ∈
      AlgebraicHodgeSubspace V H q := by
  have hrange : alpha.1 ∈ LinearMap.range (H.cycleClass p) := by
    have hatomic : alpha.1 ∈ pointCycleClassSpan p (H.cycleClass p) := halg
    rwa [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at hatomic
  rcases hrange with ⟨Z, hZ⟩
  have htarget :
      T.cohomologyOperator alpha.1 ∈ LinearMap.range (H.cycleClass q) := by
    refine ⟨T.cycleOperator Z, ?_⟩
    rw [T.cycleClass_natural, hZ]
  rw [smoothProjective_cycleClass_range_eq_atomic_span V H q] at htarget
  exact htarget

end GradedCycleClassOperatorPair

/-- Central-binomial scalar of a limitless forward pure-Hodge jump. -/
def limitlessLefschetzScalar (p q : Nat) : ℚ :=
  ((2 * (q - p)).choose (q - p) : Nat)

/-- The limitless forward scalar is nonzero over `Q`. -/
theorem limitlessLefschetzScalar_ne_zero
    (p q : Nat) : limitlessLefschetzScalar p q ≠ 0 := by
  unfold limitlessLefschetzScalar
  exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (by omega))

/-- A graded native transport realizes the exact limitless pure-Hodge jump on
one chosen source/target Hodge state.  The target is required to be nonzero;
the central-binomial normalization records the GST Lefschetz kernel. -/
structure PureLefschetzSeedTransport
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p q : Nat) where
  hpq : p ≤ q
  pair : GradedCycleClassOperatorPair V H p q
  source : ClassicalHodgeFiber V H p
  target : ClassicalHodgeFiber V H q
  source_ne_zero : source ≠ 0
  target_ne_zero : target ≠ 0
  transport_formula :
    pair.cohomologyOperator source.1 =
      limitlessLefschetzScalar p q • target.1

namespace PureLefschetzSeedTransport

variable {p q : Nat}

/-- A native source representative yields a native target representative by
applying the graded operator and dividing by the nonzero GST coefficient. -/
noncomputable def targetCycle
    (T : PureLefschetzSeedTransport V H p q)
    (Z : codimensionCycles V.X p) :
    codimensionCycles V.X q :=
  (limitlessLefschetzScalar p q)⁻¹ • T.pair.cycleOperator Z

/-- Exact target-cycle formula. -/
theorem targetCycle_spec
    (T : PureLefschetzSeedTransport V H p q)
    (Z : codimensionCycles V.X p)
    (hZ : H.cycleClass p Z = T.source.1) :
    H.cycleClass q (T.targetCycle Z) = T.target.1 := by
  unfold targetCycle
  rw [LinearMap.map_smul, T.pair.cycleClass_natural, hZ,
    T.transport_formula]
  simp [limitlessLefschetzScalar_ne_zero]

/-- Algebraicity propagates from the source seed to the target seed. -/
theorem target_algebraic_of_source_algebraic
    (T : PureLefschetzSeedTransport V H p q)
    (hsource : T.source ∈ AlgebraicHodgeSubspace V H p) :
    T.target ∈ AlgebraicHodgeSubspace V H q := by
  have hrange : T.source.1 ∈ LinearMap.range (H.cycleClass p) := by
    have hatomic : T.source.1 ∈ pointCycleClassSpan p (H.cycleClass p) := hsource
    rwa [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at hatomic
  rcases hrange with ⟨Z, hZ⟩
  have htargetRange : T.target.1 ∈ LinearMap.range (H.cycleClass q) :=
    ⟨T.targetCycle Z, T.targetCycle_spec Z hZ⟩
  rw [smoothProjective_cycleClass_range_eq_atomic_span V H q] at htargetRange
  exact htargetRange

end PureLefschetzSeedTransport

/-- A chain of graded native pure-Hodge transports propagates one algebraic
seed through all listed weights. -/
structure SeedPropagationFamily
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) where
  seed : ∀ p : Nat, ClassicalHodgeFiber V H p
  seed_ne_zero : ∀ p, seed p ≠ 0
  step : ∀ p : Nat, PureLefschetzSeedTransport V H p (p + 1)
  step_source : ∀ p, (step p).source = seed p
  step_target : ∀ p, (step p).target = seed (p + 1)

namespace SeedPropagationFamily

/-- Once one seed is algebraic, every later seed is algebraic by induction. -/
theorem algebraic_of_zero_seed
    (F : SeedPropagationFamily V H)
    (h0 : F.seed 0 ∈ AlgebraicHodgeSubspace V H 0) :
    ∀ p : Nat, F.seed p ∈ AlgebraicHodgeSubspace V H p := by
  intro p
  induction p with
  | zero => exact h0
  | succ p ih =>
      have h := (F.step p).target_algebraic_of_source_algebraic
        (by simpa [F.step_source p] using ih)
      simpa [F.step_target p] using h

#check algebraic_of_zero_seed

end SeedPropagationFamily

#check GradedCycleClassOperatorPair
#check PureLefschetzSeedTransport
#check PureLefschetzSeedTransport.targetCycle
#check PureLefschetzSeedTransport.targetCycle_spec
#check PureLefschetzSeedTransport.target_algebraic_of_source_algebraic
#check SeedPropagationFamily

#print axioms PureLefschetzSeedTransport.targetCycle_spec
#print axioms PureLefschetzSeedTransport.target_algebraic_of_source_algebraic
#print axioms SeedPropagationFamily.algebraic_of_zero_seed

end GSTClassicalHodgeCrossWeightNativePropagation
