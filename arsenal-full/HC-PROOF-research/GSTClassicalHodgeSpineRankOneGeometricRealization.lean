import GSTClassicalHodgeLimitlessSpinePropagation
import GSTClassicalHodgeRankFreeArsenalIrreducibility

/-!
# A genuine GST native-cycle construction in rank-one Hodge fibers

This is an actual construction: for a fixed Hodge weight with rational
Hodge-fiber dimension one, the pre-existing recursive projective native spine
generates all Hodge classes whenever its genuine cycle class is nonzero.

Unlike the full-plane or CM-GST program supply statements, there is no
assumption that the *target* class has an algebraic preimage. The witness
is explicitly a rational scalar multiple of the recursively manufactured
native projective cycle `spineNativeTower G p`.

The dimension-one restriction matters: a nonzero algebraic spine alone cannot
span an arbitrary higher-dimensional Hodge fiber. No claim is made here to
have established the general rational Hodge conjecture.
-/

set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation

namespace GSTClassicalHodgeSpineRankOneGeometricRealization

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The *actual recursively generated* GST projective cycle spans any rank-one
rational Hodge fiber in which its cycle class is nonzero. Its scalar is
extracted from the rank-one coordinate identity, not from an assumed
algebraic target-cycle witness. -/
theorem explicit_spine_native_cycle_of_rank_one
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hnz : spineHodgeSeed G p ≠ 0)
    (hrank : Module.finrank ℚ (ClassicalHodgeFiber V H p) = 1)
    (alpha : ClassicalHodgeFiber V H p) :
    ∃ c : ℚ,
      H.cycleClass p (c • spineNativeTower G p) = alpha.1 := by
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' (spineHodgeSeed G p) hnz).mp hrank alpha
  refine ⟨c, ?_⟩
  rw [map_smul, spineNativeTower_cycleClass G p]
  exact congrArg Subtype.val hc

/-- The full rational Hodge conclusion at ONE weight, from a concrete
projective-spine class and a checkable rank-one cohomological condition. -/
theorem every_rank_one_hodge_class_is_native
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hnz : spineHodgeSeed G p ≠ 0)
    (hrank : Module.finrank ℚ (ClassicalHodgeFiber V H p) = 1)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha := by
  obtain ⟨c, hc⟩ :=
    explicit_spine_native_cycle_of_rank_one G p hnz hrank ⟨alpha, halpha⟩
  exact ⟨c • spineNativeTower G p, hc⟩

/-- In GST, a conserved native/Betti charge already proves that the
recursively generated geometric spine is nonzero. Combining that *derived*
nonvanishing with rank-one Hodge geometry gives the exact native algebraic
cycle for every Hodge state in that weight. No orbit-cyclicity, CM period,
matrix determinant, or Hodge-surjectivity premise is used. -/
theorem every_rank_one_hodge_class_of_conserved_charge
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (p : Nat)
    (hrank : Module.finrank ℚ (ClassicalHodgeFiber V H p) = 1)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha :=
  every_rank_one_hodge_class_is_native
    G p (D.spineHodgeSeed_ne_zero p) hrank alpha halpha

/-- An EFFECTIVE charge-normalization formula, not an existentially selected
coefficient. The native representative of any rational Hodge class in a
rank-one fiber is obtained by evaluating the conserved GST charge and
dividing by the nonzero charge of the *actual native projective spine*.
This derives the coefficient using intrinsic projective-geometric data. -/
theorem charged_normalized_spine_cycle_spec
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (p : Nat)
    (hrank : Module.finrank ℚ (ClassicalHodgeFiber V H p) = 1)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    H.cycleClass p
      ((D.cohomologyRead p alpha /
        D.nativeRead p (spineNativeTower G p)) • spineNativeTower G p) =
      alpha := by
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero'
      (spineHodgeSeed G p) (D.spineHodgeSeed_ne_zero p)).mp
      hrank ⟨alpha, halpha⟩
  have hcoeffstate : c • (spineHodgeSeed G p).1 = alpha :=
    congrArg Subtype.val hc
  have hread :
      D.cohomologyRead p alpha =
        c * D.nativeRead p (spineNativeTower G p) := by
    calc
      D.cohomologyRead p alpha =
          D.cohomologyRead p (c • (spineHodgeSeed G p).1) := by
            rw [hcoeffstate]
      _ = c * D.cohomologyRead p
          (H.cycleClass p (spineNativeTower G p)) := by
            rw [map_smul, spineNativeTower_cycleClass G p, smul_eq_mul]
      _ = c * D.nativeRead p (spineNativeTower G p) := by
            rw [D.cycleClass_read p (spineNativeTower G p)]
  have hnormalized :
      D.cohomologyRead p alpha /
        D.nativeRead p (spineNativeTower G p) = c := by
    rw [hread]
    exact mul_div_cancel_right₀ c (D.nativeRead_spineNativeTower_ne_zero p)
  rw [hnormalized, map_smul, spineNativeTower_cycleClass G p]
  exact hcoeffstate

/-- The resulting native cycle is an explicitly written rational multiple,
with no target-cycle selection and no period-determinant or orbit assumption. -/
noncomputable def chargedNormalizedSpineCycle
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p)) :
    codimensionCycles V.X p :=
  (D.cohomologyRead p alpha /
    D.nativeRead p (spineNativeTower G p)) • spineNativeTower G p

theorem chargedNormalizedSpineCycle_correct
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (p : Nat)
    (hrank : Module.finrank ℚ (ClassicalHodgeFiber V H p) = 1)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    H.cycleClass p (chargedNormalizedSpineCycle G D p alpha) = alpha :=
  charged_normalized_spine_cycle_spec G D p hrank alpha halpha

#check explicit_spine_native_cycle_of_rank_one
#check every_rank_one_hodge_class_is_native
#check every_rank_one_hodge_class_of_conserved_charge
#check chargedNormalizedSpineCycle_correct

#print axioms explicit_spine_native_cycle_of_rank_one
#print axioms every_rank_one_hodge_class_of_conserved_charge
#print axioms chargedNormalizedSpineCycle_correct

end GSTClassicalHodgeSpineRankOneGeometricRealization
