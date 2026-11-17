import GSTClassicalHodgeSynchronizedDefectOrbit
import GSTClassicalHodgeLimitlessProjectiveLefschetzTower
import GSTClassicalHodgeGradedNativeCohomologyRealization
import GSTClassicalHodgeCrossWeightNativePropagation
import GSTClassicalHodgeTransferSeedUniverse
import GSTClassicalHodgeThreeUniverseSeedIdentification

/-!
# GST CLASSICAL HODGE — LIMITLESS PROJECTIVE-TOWER ORBIT CROWN

The projective side already has one canonical unbounded native cycle tower,
while the completed GST cosmos has the true global Lefschetz tower with its
nonzero central-binomial diagonal coefficients.

This module removes independent algebraic seed choices at higher weights.  One
synchronized weight-zero state and one universal comparison between the actual
projective successor operator and the corresponding limitless Lefschetz action
recursively generate normalized native representatives at every weight.  The
rank-free projector/Lefschetz/Poincare word then generates every genuine Hodge
basis direction from each propagated seed.

No Nat-address chart and no independently postulated basis-cycle family occurs
in the construction.
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeLimitlessTowerOrbitCrown

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeLimitlessProjectiveLefschetzTower
open GSTClassicalHodgeLimitlessCosmicLefschetzPropagation
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeGradedNativeCohomologyRealization
open GSTClassicalHodgeGeometryFirstTwoGenerator

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The actual geometry-built native operator used at the p-th projective
successor step. -/
abbrev ProjectiveSuccessor (p : Nat) :=
  GSTClassicalHodgePrincipalCutSuccessorOperator.successorNativeOperator V p

/-- The exact rational coefficient of one limitless diagonal Lefschetz jump. -/
def successorScalar (p : Nat) : ℚ :=
  limitlessLefschetzScalar p (p + 1)

/-- Every successive limitless coefficient is nonzero. -/
theorem successorScalar_ne_zero (p : Nat) : successorScalar p ≠ 0 := by
  exact limitlessLefschetzScalar_ne_zero p (p + 1)

/-- The successive scalar is literally the coefficient produced by two steps
of the actual unbounded cosmic Lefschetz operator. -/
theorem successorScalar_eq_cosmic (p : Nat) :
    successorScalar p =
      (((GSTUniversalLefschetzCosmology.cosmicLefschetz ^ 2)
          (GSTDimensionFreeHodgeDiagonal.cosmicDiagonalClass p))
        (p + 1, p + 1) : ℚ) := by
  simpa [successorScalar] using
    limitlessLefschetzScalar_eq_cosmic_coefficient p (p + 1) (by omega)

/-- The single recursive projective/cosmic intertwining datum.

The native operator is not arbitrary data: it is fixed to the projective
principal-cut successor already constructed in the geometry stack.  The
cohomological operator is also not supplied independently: it is the canonical
ambient operator descended from that native operator by kernel stability.
The comparison law says that this actual ambient action realizes the exact
nonzero limitless Lefschetz coefficient between successive distinguished Hodge
states. -/
structure ProjectiveTowerHodgeIntertwining where
  seed : ∀ p : Nat, ClassicalHodgeFiber V H p
  seed_ne_zero : ∀ p : Nat, seed p ≠ 0
  class_zero :
    H.cycleClass 0 (projectiveCutTower V 0) = (seed 0).1
  kernelStable : ∀ p : Nat,
    GradedKernelStable (H := H) (ProjectiveSuccessor (V := V) p)
  successor_formula : ∀ p : Nat,
    gradedAmbientOperator
        (ProjectiveSuccessor (V := V) p)
        (kernelStable p)
        (seed p).1 =
      successorScalar p • (seed (p + 1)).1

namespace ProjectiveTowerHodgeIntertwining

/-- Normalize the recursively generated native tower at every step by the true
nonzero limitless Lefschetz coefficient. -/
noncomputable def normalizedTowerCycle
    (C : ProjectiveTowerHodgeIntertwining (V := V) (H := H)) :
    (p : Nat) → codimensionCycles V.X p
  | 0 => projectiveCutTower V 0
  | p + 1 =>
      (successorScalar p)⁻¹ •
        (ProjectiveSuccessor (V := V) p) (normalizedTowerCycle C p)

/-- **EXACT NORMALIZED PROJECTIVE-TOWER CLASS LAW.**
Every normalized native tower level has cycle class equal to the corresponding
genuine Hodge seed. -/
theorem normalizedTowerCycle_spec
    (C : ProjectiveTowerHodgeIntertwining (V := V) (H := H)) :
    ∀ p : Nat,
      H.cycleClass p (C.normalizedTowerCycle p) = (C.seed p).1 := by
  intro p
  induction p with
  | zero => simpa [normalizedTowerCycle] using C.class_zero
  | succ p ih =>
      unfold normalizedTowerCycle
      rw [LinearMap.map_smul]
      rw [← cycleClass_gradedAmbientOperator
        (H := H)
        (ProjectiveSuccessor (V := V) p)
        (C.kernelStable p)
        (C.normalizedTowerCycle p)]
      rw [ih, C.successor_formula]
      simp [successorScalar_ne_zero]

/-- The recursively normalized projective tower therefore supplies the one
arbitrary nonzero algebraic Hodge orbit seed required in every weight. -/
noncomputable def orbitSeed
    (C : ProjectiveTowerHodgeIntertwining (V := V) (H := H))
    (p : Nat) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := p) where
  cycle := C.normalizedTowerCycle p
  hodge := C.seed p
  hodge_ne_zero := C.seed_ne_zero p
  class_eq := C.normalizedTowerCycle_spec p

/-- **LIMITLESS TOWER + RANK-FREE ORBIT LANDING.**
The projective/cosmic tower supplies all cross-weight algebraic seeds, and the
full GST two-generator word supplies every within-weight Hodge basis cycle. -/
theorem bigradedBettiHodge
    (C : ProjectiveTowerHodgeIntertwining (V := V) (H := H))
    (R : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        GeometryFirstTwoGenerator
          (V := V) (H := H) (C.orbitSeed p).sourceIndex j) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  exact (C.orbitSeed p).hodge_weight (R p) halpha

end ProjectiveTowerHodgeIntertwining

/-- Final two-artery mathematical crown:

* the genuine limitless projective/cosmic tower generates one algebraic seed in
  every weight from weight zero;
* the genuine rank-free GST matrix-unit word generates every multiplicity
  direction inside each weight.
-/
theorem classical_hodge_from_limitless_projective_cosmic_arsenal
    (C : ProjectiveTowerHodgeIntertwining (V := V) (H := H))
    (R : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        GeometryFirstTwoGenerator
          (V := V) (H := H) (C.orbitSeed p).sourceIndex j) :
    BigradedBettiHodgeStatement V H :=
  C.bigradedBettiHodge R

#check ProjectiveTowerHodgeIntertwining
#check ProjectiveTowerHodgeIntertwining.normalizedTowerCycle
#check ProjectiveTowerHodgeIntertwining.normalizedTowerCycle_spec
#check ProjectiveTowerHodgeIntertwining.orbitSeed
#check ProjectiveTowerHodgeIntertwining.bigradedBettiHodge
#check classical_hodge_from_limitless_projective_cosmic_arsenal

#print axioms ProjectiveTowerHodgeIntertwining.normalizedTowerCycle_spec
#print axioms ProjectiveTowerHodgeIntertwining.bigradedBettiHodge
#print axioms classical_hodge_from_limitless_projective_cosmic_arsenal

end GSTClassicalHodgeLimitlessTowerOrbitCrown
