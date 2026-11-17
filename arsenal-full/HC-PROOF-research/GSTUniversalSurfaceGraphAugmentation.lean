import GSTUniversalCodimensionTwoPrimitiveExtraction

/-!
# GST universal finite graph augmentation: native primitive cycles

Let S be a smooth projective complex surface and g an algebraic
automorphism preserving a polarization h. On X=S×S its graph Γ_g is
a genuine algebraic codimension-two cycle.

For surfaces with H¹(S,ℚ)=0 (including K3 surfaces), the class
    (pr₁*h+pr₂*h) cup cl(Γ_g)
is independent of the polarized automorphism g. Every rational
augmentation-zero sum Σ_g a_g Γ_g is then primitive.

For irregular surfaces with H¹(S,ℚ)≠0, the graph Lefschetz image
also detects g's action on H¹(S,ℚ). The full geometric construction
therefore uses the additional H¹-moment cancellation developed in
GSTSurfaceGraphH1Obstruction.lean.

The Lean theorem here implements exactly the verified shared-Lefschetz
hypothesis, without treating polarization preservation alone as the
general shared-Lefschetz theorem.

The Lean theorem implements the exact native rational cycle sum and
proves its primitive-test vanishing from the geometric shared-Lefschetz
identity. This isolates the canonical graph/Gysin implementation from
the algebraic construction and its kernel verification.
-/

set_option maxHeartbeats 12000000
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

namespace GSTUniversalSurfaceGraphAugmentation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Native algebraic group-ring graph combination over any finite
index set of real irreducible surface correspondences. -/
def nativeGraphOrbitCombination
    {ι : Type*} [Fintype ι]
    (graphs : ι → codimensionCycles V.X 2)
    (a : ι → ℚ) : codimensionCycles V.X 2 :=
  ∑ i : ι, a i • graphs i

/-- FINITE-GROUP AUGMENTATION CONSTRUCTION.
For a polarized algebraic automorphism orbit with a verified
shared Lefschetz image (for example on a K3 self-product), every
augmentation-zero orbit combination is an ACTUAL primitive
algebraic codimension-two cycle. -/
theorem all_augmentation_zero_graph_cycles_primitive
    {ι : Type*} [Fintype ι]
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G 4)
    (graphs : ι → codimensionCycles V.X 2)
    (common : ClassicalHodgeFiber V H (4-1))
    (hShared : ∀ i : ι,
      P.primitiveTest (nativeToHodgeFiberLinear G (graphs i)) =
        common)
    (a : ι → ℚ)
    (hAug : (∑ i : ι, a i) = 0) :
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
    _ = ∑ i : ι, a i • common := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hShared i]
    _ = (∑ i : ι, a i) • common := by
          rw [Finset.sum_smul]
    _ = 0 := by simp [hAug]

#check nativeGraphOrbitCombination
#check all_augmentation_zero_graph_cycles_primitive
#print axioms all_augmentation_zero_graph_cycles_primitive

end GSTUniversalSurfaceGraphAugmentation
