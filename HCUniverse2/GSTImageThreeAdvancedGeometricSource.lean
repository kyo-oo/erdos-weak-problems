import HCUniverse2.GSTImageThreeOriginalXCurvatureLanding
import HCUniverse2.GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
import Mathlib

/-!
# Image 3 — actual original-X closed-correspondence curvature compiler

The source is the owner's original U, J, M, and [J,M].
An arbitrary commuting pair is NOT an algebraic correspondence.
This layer takes five ACTUAL finite closed correspondences on X x X:
U,J,M, a geometric witness JM for J∘M, and a geometric witness MJ for M∘J.

Assuming the two witnesses induce those compositions on the ORIGINAL native
cycles AND the supplied rational Betti data, the FIVE-ATOM RATIONAL WORD
 U + J + a M + b JM - b MJ
is a genuine geometric correspondence expression whose action agrees exactly
with the original Image-3 geometricCurvatureF.  No Hodge cyclicity, unknown
algebraic Hodge basis, or target-to-cycle inverse is assumed or manufactured.

The missing independent GEOMETRIC task is constructing the five witnesses
with the specified compositional actions for arbitrary original X,p, then
proving their canonical Hodge landing is rank-preserving.
-/

set_option maxHeartbeats 6000000
noncomputable section

namespace GSTImageThreeAdvancedGeometricSource

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTImageThreeOriginalXCurvatureLanding

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Five genuine geometric inputs, with both ordered composition witnesses. -/
structure ClosedCurvatureGeometry
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) (p : Nat) where
  U : RealizedFiniteClosedCorrespondence V H p
  J : RealizedFiniteClosedCorrespondence V H p
  M : RealizedFiniteClosedCorrespondence V H p
  JM : RealizedFiniteClosedCorrespondence V H p
  MJ : RealizedFiniteClosedCorrespondence V H p
  JM_native :
    JM.operatorPair.cycleOperator =
      J.operatorPair.cycleOperator.comp M.operatorPair.cycleOperator
  MJ_native :
    MJ.operatorPair.cycleOperator =
      M.operatorPair.cycleOperator.comp J.operatorPair.cycleOperator
  JM_betti :
    JM.operatorPair.cohomologyOperator =
      J.operatorPair.cohomologyOperator.comp M.operatorPair.cohomologyOperator
  MJ_betti :
    MJ.operatorPair.cohomologyOperator =
      M.operatorPair.cohomologyOperator.comp J.operatorPair.cohomologyOperator

/-- A literal rational sum of FIVE actual finite closed geometric correspondences. -/
def closedCurvatureWord
    (G : ClosedCurvatureGeometry V H p) (a b : ℚ) :
    RealizedCorrespondenceWord V H p :=
  [(1,G.U),(1,G.J),(a,G.M),(b,G.JM),(-b,G.MJ)]

/-- The word's original-X native action is precisely the owner's
two-parameter F = U+J+aM+b[J,M], not a synthetic Hodge endomorphism. -/
theorem closedCurvatureWord_cycle
    (G : ClosedCurvatureGeometry V H p) (a b : ℚ) :
    (realizedWordPair (closedCurvatureWord G a b)).cycleOperator =
      (geometricCurvatureF G.U.operatorPair G.J.operatorPair G.M.operatorPair a b).cycleOperator := by
  apply LinearMap.ext
  intro z
  have hJM :
      G.JM.geometry.nativeOperator p z =
        G.J.geometry.nativeOperator p (G.M.geometry.nativeOperator p z) := by
    have h := LinearMap.congr_fun G.JM_native z
    simpa only [RealizedFiniteClosedCorrespondence.operatorPair_cycle,
      LinearMap.comp_apply] using h
  have hMJ :
      G.MJ.geometry.nativeOperator p z =
        G.M.geometry.nativeOperator p (G.J.geometry.nativeOperator p z) := by
    have h := LinearMap.congr_fun G.MJ_native z
    simpa only [RealizedFiniteClosedCorrespondence.operatorPair_cycle,
      LinearMap.comp_apply] using h
  simp [closedCurvatureWord, realizedWordPair,
    CycleClassOperatorPair.add, CycleClassOperatorPair.smul,
    CycleClassOperatorPair.zero, geometricCurvatureF, cmSourcePair,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.sub_apply, hJM, hMJ, neg_smul, smul_sub] <;> abel_nf

/-- Independent matching rational Betti equation for the SAME geometric word. -/
theorem closedCurvatureWord_betti
    (G : ClosedCurvatureGeometry V H p) (a b : ℚ) :
    (realizedWordPair (closedCurvatureWord G a b)).cohomologyOperator =
      (geometricCurvatureF G.U.operatorPair G.J.operatorPair G.M.operatorPair a b).cohomologyOperator := by
  apply LinearMap.ext
  intro alpha
  have hJM :
      G.JM.cohomologyOperator alpha =
        G.J.cohomologyOperator (G.M.cohomologyOperator alpha) := by
    have h := LinearMap.congr_fun G.JM_betti alpha
    simpa only [RealizedFiniteClosedCorrespondence.operatorPair_cohomology,
      LinearMap.comp_apply] using h
  have hMJ :
      G.MJ.cohomologyOperator alpha =
        G.M.cohomologyOperator (G.J.cohomologyOperator alpha) := by
    have h := LinearMap.congr_fun G.MJ_betti alpha
    simpa only [RealizedFiniteClosedCorrespondence.operatorPair_cohomology,
      LinearMap.comp_apply] using h
  simp [closedCurvatureWord, realizedWordPair,
    CycleClassOperatorPair.add, CycleClassOperatorPair.smul,
    CycleClassOperatorPair.zero, geometricCurvatureF, cmSourcePair,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.sub_apply, hJM, hMJ, neg_smul, smul_sub] <;> abel_nf

/-- True original-X cycle class naturality for the five-atom geometric F. -/
theorem closedCurvatureWord_class
    (G : ClosedCurvatureGeometry V H p) (a b : ℚ)
    (z : codimensionCycles V.X p) :
    H.cycleClass p ((realizedWordPair (closedCurvatureWord G a b)).cycleOperator z) =
      (realizedWordPair (closedCurvatureWord G a b)).cohomologyOperator
        (H.cycleClass p z) :=
  (realizedWordPair (closedCurvatureWord G a b)).cycleClass_cycleOperator z

/-- Any actual five-atom algebraic F preserves the entire original cycle-class
image; finite information-space rank alone cannot enlarge that image. -/
theorem closedCurvatureWord_algebraic_range_stable
    (G : ClosedCurvatureGeometry V H p) (a b : ℚ) :
    ∀ alpha,
      alpha ∈ LinearMap.range (H.cycleClass p) →
      (realizedWordPair (closedCurvatureWord G a b)).cohomologyOperator alpha
        ∈ LinearMap.range (H.cycleClass p) :=
  realizedWord_range_stable (closedCurvatureWord G a b)

#check ClosedCurvatureGeometry
#check closedCurvatureWord
#check closedCurvatureWord_cycle
#check closedCurvatureWord_betti
#check closedCurvatureWord_class
#check closedCurvatureWord_algebraic_range_stable
#print axioms closedCurvatureWord_cycle
#print axioms closedCurvatureWord_betti
#print axioms closedCurvatureWord_class

end GSTImageThreeAdvancedGeometricSource
