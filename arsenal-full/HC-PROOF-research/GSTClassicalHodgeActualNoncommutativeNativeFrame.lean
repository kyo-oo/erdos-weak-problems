import GSTClassicalHodgeNativeGeometricPowerOrbit

/-!
# Noncommutative GST finite native-cycle frames from actual geometry

The one-generator polynomial orbit need not span a higher-rank Hodge fiber.
This construction handles arbitrary finite families of DISTINCT genuine
realized correspondence expressions, and their noncommutative commutators.

Every polynomial/word and commutator acts on the ACTUAL recursive projective
native spine. A target-cycle lift is never requested. Naturality gives the
exact Betti realization and the algebraic Hodge-type certificate for each
constructed vector, even when no independence certificate is available.

A separately verifiable full-rank matrix of *these* genuine constructions
suffices to represent arbitrary classes; its existence for arbitrary
varieties is not assumed or established by this file.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 900000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
open GSTClassicalHodgeGeometricMatrixRankLanding

namespace GSTClassicalHodgeActualNoncommutativeNativeFrame

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}
variable {ι : Type*}

/-- One genuine noncommutative geometric word evaluated on the projective
spine, without supplying any arbitrary native operator or cycle preimage. -/
noncomputable def nativeWord
    (G : GeometricCycleClassSpine V H)
    (E : RealizedCorrespondenceExpr V H p) :
    codimensionCycles V.X p :=
  E.cycleOperator (spineNativeTower G p)

/-- Its entire Betti-side image is fixed by geometric realization. -/
noncomputable def bettiWord
    (G : GeometricCycleClassSpine V H)
    (E : RealizedCorrespondenceExpr V H p) :
    RationalSingularCohomology H.analytification (2 * p) :=
  E.cohomologyOperator (spineHodgeSeed G p).1

theorem nativeWord_cycleClass
    (G : GeometricCycleClassSpine V H)
    (E : RealizedCorrespondenceExpr V H p) :
    H.cycleClass p (nativeWord G E) = bettiWord G E := by
  unfold nativeWord bettiWord
  rw [E.cycleClass_natural, spineNativeTower_cycleClass]

/-- FINITE MULTI-GENERATOR CONSTRUCTION: unlike a polynomial in just one
operator, the words may contain arbitrary ordered compositions of unrelated
finite-closed geometric correspondences. -/
noncomputable def nativeFiniteWordFrame
    (G : GeometricCycleClassSpine V H)
    (word : ι → RealizedCorrespondenceExpr V H p)
    (coeff : ι →₀ ℚ) : codimensionCycles V.X p :=
  coeff.sum (fun i q => q • nativeWord G (word i))

noncomputable def bettiFiniteWordFrame
    (G : GeometricCycleClassSpine V H)
    (word : ι → RealizedCorrespondenceExpr V H p)
    (coeff : ι →₀ ℚ) :
    RationalSingularCohomology H.analytification (2 * p) :=
  coeff.sum (fun i q => q • bettiWord G (word i))

theorem nativeFiniteWordFrame_cycleClass
    (G : GeometricCycleClassSpine V H)
    (word : ι → RealizedCorrespondenceExpr V H p)
    (coeff : ι →₀ ℚ) :
    H.cycleClass p (nativeFiniteWordFrame G word coeff) =
      bettiFiniteWordFrame G word coeff := by
  simp only [nativeFiniteWordFrame, bettiFiniteWordFrame, Finsupp.sum,
    map_sum, map_smul, nativeWord_cycleClass]

theorem bettiFiniteWordFrame_has_native_cycle
    (G : GeometricCycleClassSpine V H)
    (word : ι → RealizedCorrespondenceExpr V H p)
    (coeff : ι →₀ ℚ) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = bettiFiniteWordFrame G word coeff :=
  ⟨nativeFiniteWordFrame G word coeff,
    nativeFiniteWordFrame_cycleClass G word coeff⟩

theorem bettiFiniteWordFrame_is_hodge
    (G : GeometricCycleClassSpine V H)
    (word : ι → RealizedCorrespondenceExpr V H p)
    (coeff : ι →₀ ℚ) :
    bettiFiniteWordFrame G word coeff ∈
      rationalHodgeSubspace (H.hodgeBigrading p) := by
  rw [← nativeFiniteWordFrame_cycleClass G word coeff]
  exact G.algebraic_is_hodge p _

/-- A specific additional native class from the noncommutative defect
E ∘ F - F ∘ E. This is a genuine algebraic cycle, and it may reveal
directions inaccessible to one-generator polynomial iterations. -/
noncomputable def nativeGeometricCommutator
    (G : GeometricCycleClassSpine V H)
    (E F : RealizedCorrespondenceExpr V H p) :
    codimensionCycles V.X p :=
  E.cycleOperator (F.cycleOperator (spineNativeTower G p)) -
    F.cycleOperator (E.cycleOperator (spineNativeTower G p))

noncomputable def bettiGeometricCommutator
    (G : GeometricCycleClassSpine V H)
    (E F : RealizedCorrespondenceExpr V H p) :
    RationalSingularCohomology H.analytification (2 * p) :=
  E.cohomologyOperator (F.cohomologyOperator (spineHodgeSeed G p).1) -
    F.cohomologyOperator (E.cohomologyOperator (spineHodgeSeed G p).1)

/-- Exact Betti realization of the explicit noncommutative GST cycle. -/
theorem nativeGeometricCommutator_cycleClass
    (G : GeometricCycleClassSpine V H)
    (E F : RealizedCorrespondenceExpr V H p) :
    H.cycleClass p (nativeGeometricCommutator G E F) =
      bettiGeometricCommutator G E F := by
  unfold nativeGeometricCommutator bettiGeometricCommutator
  rw [map_sub, E.cycleClass_natural, F.cycleClass_natural,
    F.cycleClass_natural, E.cycleClass_natural,
    spineNativeTower_cycleClass]

theorem bettiGeometricCommutator_is_hodge
    (G : GeometricCycleClassSpine V H)
    (E F : RealizedCorrespondenceExpr V H p) :
    bettiGeometricCommutator G E F ∈
      rationalHodgeSubspace (H.hodgeBigrading p) := by
  rw [← nativeGeometricCommutator_cycleClass G E F]
  exact G.algebraic_is_hodge p _

/-- Test actual constructed noncommutative words by a rational coordinate
matrix in the genuine finite Hodge fiber; no Hodge-basis cycle preimages. -/
noncomputable def geometricWordFrameMatrix
    (G : GeometricCycleClassSpine V H)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (words :
      Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)) →
        RealizedCorrespondenceExpr V H p) :
    Matrix (Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)))
      (Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p))) ℚ :=
  nativeHodgeMatrix G (fun j => nativeWord G (words j))

/-- Finite-dimensional full recovery from ACTUAL noncommutative geometric
words. This depends only on the explicit numerical determinant of the
constructed family, which still requires an independent geometric proof. -/
theorem native_cycle_of_nonzero_geometric_word_frame
    (G : GeometricCycleClassSpine V H)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (words :
      Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)) →
        RealizedCorrespondenceExpr V H p)
    (hdet : (geometricWordFrameMatrix G words).det ≠ 0)
    (alpha : ClassicalHodgeFiber V H p) :
    H.cycleClass p
      (nativeCycleByMatrixInversion G (fun j => nativeWord G (words j))
        (geometricWordFrameMatrix G words)⁻¹ alpha) = alpha.1 :=
  hodge_cycle_of_nonzero_geometric_determinant
    G (fun j => nativeWord G (words j)) hdet alpha

#check nativeFiniteWordFrame
#check nativeFiniteWordFrame_cycleClass
#check nativeGeometricCommutator
#check nativeGeometricCommutator_cycleClass
#check native_cycle_of_nonzero_geometric_word_frame

#print axioms nativeFiniteWordFrame_cycleClass
#print axioms nativeGeometricCommutator_cycleClass
#print axioms native_cycle_of_nonzero_geometric_word_frame

end GSTClassicalHodgeActualNoncommutativeNativeFrame
