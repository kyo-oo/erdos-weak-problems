import GSTClassicalHodgeStage2GSemanticRigidity
import GSTClassicalHodgeFiberedCosmology
import GSTClassicalHodgeLimitlessCosmicMatrixUnits
import GSTClassicalHodgeCanonicalCosmicRealizationEquivalence
import GSTClassicalHodgeThreeUniverseSeedIdentification

/-!
# GST CLASSICAL HODGE — LIMITLESS SEMANTIC SEPARATION

The limitless GST Hodge engine is built from the genuine rational Hodge
subspace, its unrestricted basis, finite-support coordinates, recoordination,
Lefschetz/Poincare words and the cosmic matrix-unit algebra.  None of those
constructions should silently depend on the still-arbitrary `cycleClass` field
of `HodgeBigradedBettiData`.

This module makes that separation formal.  Replacing the cycle-class map by the
zero map leaves the analytification, Hodge bigrading, rational Hodge subspace,
Hodge fiber and every purely Hodge/cosmic coordinate construction unchanged.
Nevertheless a nonzero Hodge class is not in the range of the zero cycle-class
map.  Consequently the final classical landing must externalize the already
complete limitless operator algebra through the genuine geometric cycle-class
construction; additional internal coordinate algebra alone cannot distinguish
the two semantic packages.

This is a target-localization theorem.  It does not weaken any GST theorem and
it introduces no new mathematical hypothesis.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeLimitlessSemanticSeparation

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeStage2GSemanticRigidity
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeLimitlessCosmicMatrixUnits
open GSTClassicalHodgeCanonicalCosmicRealizationEquivalence

variable {V : SmoothProjectiveComplexScheme}

/-- Zeroing the unconstrained cycle-class field does not change the rational
Hodge subspace. -/
theorem rationalHodgeSubspace_zeroCycleClassData
    (H : HodgeBigradedBettiData V) (p : Nat) :
    rationalHodgeSubspace ((zeroCycleClassData H).hodgeBigrading p) =
      rationalHodgeSubspace (H.hodgeBigrading p) :=
  rfl

/-- Hence the genuine Hodge fiber type is definitionally the same after the
cycle-class field is erased. -/
theorem classicalHodgeFiber_zeroCycleClassData
    (H : HodgeBigradedBettiData V) (p : Nat) :
    ClassicalHodgeFiber V (zeroCycleClassData H) p =
      ClassicalHodgeFiber V H p :=
  rfl

/-- The unrestricted basis-index type used by the rank-free limitless engine is
also unchanged. -/
theorem classicalHodgeBasisIndex_zeroCycleClassData
    (H : HodgeBigradedBettiData V) (p : Nat) :
    ClassicalHodgeBasisIndex V (zeroCycleClassData H) p =
      ClassicalHodgeBasisIndex V H p :=
  rfl

/-- Every finite-support coordinate computation on the Hodge fiber therefore
sees identical input data before and after the cycle-class map is erased. -/
theorem fiberedWeightCoordinates_zeroCycleClassData
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    fiberedWeightCoordinates V (zeroCycleClassData H) p alpha =
      fiberedWeightCoordinates V H p alpha := by
  rfl

/-- The base-weight limitless projection is equally insensitive to the
cycle-class field. -/
theorem forgetMultiplicity_zeroCycleClassData
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    forgetMultiplicityToGST
        (fiberedWeightCoordinates V (zeroCycleClassData H) p alpha) =
      forgetMultiplicityToGST (fiberedWeightCoordinates V H p alpha) := by
  rfl

/-- The purely Hodge-side rank-free matrix unit is unchanged as a function on
the common Hodge fiber. -/
theorem hodgeMatrixUnit_zeroCycleClassData
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (i j : ClassicalHodgeBasisIndex V H p)
    (alpha : ClassicalHodgeFiber V H p) :
    GSTClassicalHodgeRankFreeArsenalIrreducibility.hodgeMatrixUnit
        (V := V) (H := zeroCycleClassData H) i j alpha =
      GSTClassicalHodgeRankFreeArsenalIrreducibility.hodgeMatrixUnit
        (V := V) (H := H) i j alpha := by
  rfl

/-- Consequently the canonical ambient cosmic action, restricted to the Hodge
fiber, has the same matrix-unit value under both semantic packages. -/
theorem canonicalCosmicAmbient_on_hodge_zeroCycleClassData
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (i j : ClassicalHodgeBasisIndex V H p)
    (alpha : ClassicalHodgeFiber V H p) :
    canonicalCosmicAmbient (V := V) (H := zeroCycleClassData H) i j alpha.1 =
      (GSTClassicalHodgeRankFreeArsenalIrreducibility.hodgeMatrixUnit
        (V := V) (H := H) i j alpha).1 := by
  rw [canonicalCosmicAmbient_on_hodge (V := V) (H := zeroCycleClassData H) i j alpha,
    GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy.hodgeMatrixUnit_eq_lift_limitless_cosmic]
  rfl

/-- **LIMITLESS SEMANTIC-SEPARATION CROWN.**
A nonzero rational Hodge class is seen by exactly the same unrestricted Hodge
fiber and limitless coordinate universe after zeroing the arbitrary cycle-class
field, while it cannot lie in the resulting cycle-class range. -/
theorem limitless_semantic_separation_crown
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p))
    (halpha0 : alpha ≠ 0) :
    alpha ∈ rationalHodgeSubspace ((zeroCycleClassData H).hodgeBigrading p)
      ∧ alpha ∉ LinearMap.range ((zeroCycleClassData H).cycleClass p) := by
  exact ⟨halpha,
    nonzero_hodge_not_in_zero_cycleClass_range H p alpha halpha0⟩

/-- Therefore any final theorem whose only new ingredients are constructions
that factor through the Hodge bigrading/cosmic-coordinate side cannot determine
the classical cycle-class range.  The missing operation must involve the actual
geometric cycle-class semantics.  This is expressed constructively by the fact
that the same Hodge datum admits a zero-cycle-class package with false target. -/
theorem final_externalization_must_use_cycleClass_semantics
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (hH : rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥) :
    ∃ H0 : HodgeBigradedBettiData V,
      H0 = zeroCycleClassData H ∧
      ¬ BigradedBettiHodgeStatement V H0 :=
  exists_semantic_countermodel_of_nontrivial_hodge H p hH

#check rationalHodgeSubspace_zeroCycleClassData
#check classicalHodgeFiber_zeroCycleClassData
#check fiberedWeightCoordinates_zeroCycleClassData
#check forgetMultiplicity_zeroCycleClassData
#check hodgeMatrixUnit_zeroCycleClassData
#check canonicalCosmicAmbient_on_hodge_zeroCycleClassData
#check limitless_semantic_separation_crown
#check final_externalization_must_use_cycleClass_semantics

#print axioms limitless_semantic_separation_crown
#print axioms final_externalization_must_use_cycleClass_semantics

end GSTClassicalHodgeLimitlessSemanticSeparation
