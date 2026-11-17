import GSTUniversalSurfaceGraphAugmentation

/-!
# GST surface automorphism graph cycles: exact H1 obstruction and primitive rank

For any smooth polarized projective surface S, the graph of g ∈ Aut(S,h)
is an algebraic codimension-two cycle on the original S×S.

The graph Lefschetz class on S×S is determined by:
  (1) the common polarization h (constant term);
  (2) the action g* on H¹(S,ℚ) (odd-cohomology term).

On a regular surface, H¹=0 and condition (2) vanishes, recovering the
K3 graph orbit augmentation theorem. On irregular surfaces one must
annihilate BOTH the coefficient sum and the weighted H¹-action.

The following Lean theorem implements the full two-moment geometric
criterion, and a separate primitive Kunneth readout proves that
algebraic Lefschetz correction preserves measured graph endomorphisms.
These are genuine rational algebraic cycle constructions, with analytic
H¹/Kunneth comparisons kept in explicit geometric measurement inputs.
-/

set_option maxHeartbeats 20000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGeometricMatrixRankLanding
open GSTUniversalLefschetzCurveCycles
open GSTUniversalCodimensionTwoPrimitiveExtraction
open GSTUniversalSurfaceGraphAugmentation

namespace GSTSurfaceGraphH1Obstruction

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Every algebraic graph orbit combination with augmentation
and odd Betti action moments both equal to zero is primitive.
This applies to arbitrary smooth projective surfaces, and
specializes to the K3 case when the H¹ moment space is zero. -/
theorem graph_orbit_primitive_of_two_moment_cancellation
    {ι W : Type*} [Fintype ι] [AddCommGroup W] [Module ℚ W]
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G 4)
    (graphs : ι → codimensionCycles V.X 2)
    (common : ClassicalHodgeFiber V H 3)
    (oddAction : ι → W)
    (oddLefschetz : W →ₗ[ℚ] ClassicalHodgeFiber V H 3)
    (hGraph : ∀ i : ι,
      P.primitiveTest (nativeToHodgeFiberLinear G (graphs i)) =
        common + oddLefschetz (oddAction i))
    (a : ι → ℚ)
    (hAug : (∑ i : ι, a i) = 0)
    (hOdd : (∑ i : ι, a i • oddAction i) = 0) :
    P.primitiveTest
      (nativeToHodgeFiberLinear G
        (nativeGraphOrbitCombination graphs a)) = 0 := by
  calc
    P.primitiveTest
        (nativeToHodgeFiberLinear G
          (nativeGraphOrbitCombination graphs a)) =
      ∑ i : ι, a i •
        P.primitiveTest (nativeToHodgeFiberLinear G (graphs i)) := by
          simp [nativeGraphOrbitCombination, map_sum, map_smul]
    _ = ∑ i : ι, a i • (common + oddLefschetz (oddAction i)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hGraph i]
    _ = (∑ i : ι, a i) • common +
        oddLefschetz (∑ i : ι, a i • oddAction i) := by
          simp_rw [smul_add]
          rw [Finset.sum_add_distrib, Finset.sum_smul]
          simp only [map_sum, map_smul]
    _ = 0 := by simp [hAug, hOdd]

/-- Exact converse: when the canonical Kunneth decomposition separates
the common even-degree hyperplane term from the odd H1-action term,
the TWO group-ring moments characterize primitive graph combinations.

On genuine projective surface products, this separation follows from
the even/odd Kunneth summands, ample-square positivity and the
nondegenerate H1 cup-h polarization pairing. -/
theorem graph_orbit_primitive_iff_two_moment_cancellation
    {ι W : Type*} [Fintype ι] [AddCommGroup W] [Module ℚ W]
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G 4)
    (graphs : ι → codimensionCycles V.X 2)
    (common : ClassicalHodgeFiber V H 3)
    (oddAction : ι → W)
    (oddLefschetz : W →ₗ[ℚ] ClassicalHodgeFiber V H 3)
    (hGraph : ∀ i : ι,
      P.primitiveTest (nativeToHodgeFiberLinear G (graphs i)) =
        common + oddLefschetz (oddAction i))
    (hKunnethSeparate :
      ∀ (q : ℚ) (w : W),
        q • common + oddLefschetz w = 0 →
        q = 0 ∧ w = 0)
    (a : ι → ℚ) :
    (P.primitiveTest
        (nativeToHodgeFiberLinear G
          (nativeGraphOrbitCombination graphs a)) = 0) ↔
      (∑ i : ι, a i) = 0 ∧
      (∑ i : ι, a i • oddAction i) = 0 := by
  constructor
  · intro hPrimitive
    have hFormula :
        P.primitiveTest
          (nativeToHodgeFiberLinear G
            (nativeGraphOrbitCombination graphs a)) =
        (∑ i : ι, a i) • common +
          oddLefschetz (∑ i : ι, a i • oddAction i) := by
      calc
        P.primitiveTest
            (nativeToHodgeFiberLinear G
              (nativeGraphOrbitCombination graphs a)) =
          ∑ i : ι, a i •
            P.primitiveTest
              (nativeToHodgeFiberLinear G (graphs i)) := by
                simp [nativeGraphOrbitCombination, map_sum, map_smul]
        _ = ∑ i : ι, a i •
            (common + oddLefschetz (oddAction i)) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hGraph i]
        _ = (∑ i : ι, a i) • common +
              oddLefschetz (∑ i : ι, a i • oddAction i) := by
                simp_rw [smul_add]
                rw [Finset.sum_add_distrib, Finset.sum_smul]
                simp only [map_sum, map_smul]
    exact hKunnethSeparate _ _ (hFormula.symm.trans hPrimitive)
  · rintro ⟨hAug, hOdd⟩
    exact graph_orbit_primitive_of_two_moment_cancellation
      G P graphs common oddAction oddLefschetz hGraph a hAug hOdd

#check graph_orbit_primitive_iff_two_moment_cancellation
#print axioms graph_orbit_primitive_iff_two_moment_cancellation

/-- The universal GST primitiveizer retains every rational
transcendental Kunneth measurement that annihilates the
genuine native algebraic Lefschetz-correction image. -/
theorem primitiveization_preserves_transcendental_measure
    {W : Type*} [AddCommGroup W] [Module ℚ W]
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G 4)
    (h11 : DivisorsRepresentHodge11 H)
    (probe : ClassicalHodgeFiber V H 2 →ₗ[ℚ] W)
    (hKillsLefschetz :
      ∀ alpha : ClassicalHodgeFiber V H 2,
        probe (nativeToHodgeFiberLinear G
          (algebraicLefschetzCorrection G P h11 alpha)) = 0)
    (Z : codimensionCycles V.X 2) :
    probe (nativeToHodgeFiberLinear G
      (primitiveizeNativeMiddleCycle G P h11 Z)) =
    probe (nativeToHodgeFiberLinear G Z) := by
  change probe (nativeToHodgeFiberLinear G
      (Z - algebraicLefschetzCorrection G P h11
        (nativeToHodgeFiberLinear G Z))) =
    probe (nativeToHodgeFiberLinear G Z)
  rw [map_sub, map_sub, hKillsLefschetz]
  simp

/-- The transcendental rank of an algebraic graph orbit survives
the universal native GST primitiveization: measurements are exactly
the finite rational group-action coefficients. -/
theorem primitive_graph_orbit_transcendental_rank_certificate
    {ι W : Type*} [Fintype ι] [AddCommGroup W] [Module ℚ W]
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G 4)
    (h11 : DivisorsRepresentHodge11 H)
    (graphs : ι → codimensionCycles V.X 2)
    (probe : ClassicalHodgeFiber V H 2 →ₗ[ℚ] W)
    (hKillsLefschetz :
      ∀ alpha : ClassicalHodgeFiber V H 2,
        probe (nativeToHodgeFiberLinear G
          (algebraicLefschetzCorrection G P h11 alpha)) = 0)
    (repr : ι → W)
    (hProbe : ∀ i : ι,
      probe (nativeToHodgeFiberLinear G (graphs i)) = repr i)
    (a : ι → ℚ) :
    probe (nativeToHodgeFiberLinear G
      (primitiveizeNativeMiddleCycle G P h11
        (nativeGraphOrbitCombination graphs a))) =
      ∑ i : ι, a i • repr i := by
  rw [primitiveization_preserves_transcendental_measure
    G P h11 probe hKillsLefschetz]
  simp [nativeGraphOrbitCombination, map_sum, map_smul, hProbe]

#check graph_orbit_primitive_of_two_moment_cancellation
#check primitiveization_preserves_transcendental_measure
#check primitive_graph_orbit_transcendental_rank_certificate
#print axioms graph_orbit_primitive_of_two_moment_cancellation
#print axioms primitive_graph_orbit_transcendental_rank_certificate

end GSTSurfaceGraphH1Obstruction
