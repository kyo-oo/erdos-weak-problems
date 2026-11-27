import HCUniverse2.GSTCardinalWorldHodgeStarPart1
import Mathlib

/-!
# Original GST CM curvature / Hodge Star on EVERY complementary Hodge degree

From owner's image three:
  N-cohomology + Hodge cohomology + original complex J + true SURVIVE M
  + original [J,M] + Hodge Star, with original-X quantifiers retained.

Geometry in:
research/derivations/GST_owner_all_degree_HodgeStar_CM_graded_Ncohomology_20261111.tex

A genuine Hodge Star sends H^{2p} -> H^{2d-2p}, not generally back to
H^{2p}. The correct ALL-DEGREE carrier is a graded double P x Q with
D : P ≃ₗ[ℚ] Q, interpreted as the polarized rational Hodge-Star map
between complementary rational (p,p) Hodge fibers (when that map is
independently constructed via the rational Lefschetz decomposition).

On P x Q, define the exact SOURCE mechanism:
  Star(x,y) = (D^{-1} y, D x)
  J(x,y)    = (D^{-1} y, -D x)
  M(x,y)    = (0, 2y)
  [J,M]     = 2 Star.
This is the owner's original CM/SURVIVE fixed-pair algebra in EVERY degree.

This file proves the purely typed algebra and directly matches the
original user's 12-cell fixed-pair curvature. It does NOT assume that
Star is a genuine algebraic Chow correspondence on arbitrary X.
-/

set_option maxHeartbeats 5000000
noncomputable section

namespace GSTAllDegreeHodgeStarCMFold

open GSTImageThreeCurvatureResonance
open GSTGraphV2CMWaveFusion

universe u v
variable {P : Type u} [AddCommGroup P] [Module ℚ P]
variable {Q : Type v} [AddCommGroup Q] [Module ℚ Q]

/-- The true across-complementary-degree Hodge-Star template. -/
def gradedStar (D : P ≃ₗ[ℚ] Q) (x : P × Q) : P × Q :=
  (D.symm x.2, D x.1)

/-- Original GST CM operator, now typed on complementary degrees. -/
def gradedCM (D : P ≃ₗ[ℚ] Q) (x : P × Q) : P × Q :=
  (D.symm x.2, -(D x.1))

/-- The original SURVIVE source of strength two on maximum-coordinates. -/
def gradedSurvive (_D : P ≃ₗ[ℚ] Q) (x : P × Q) : P × Q :=
  (0, (2 : ℚ) • x.2)

/-- Original actual commutator, not a separately imposed curvature axiom. -/
def gradedCurvature (D : P ≃ₗ[ℚ] Q) (x : P × Q) : P × Q :=
  gradedCM D (gradedSurvive D x) -
    gradedSurvive D (gradedCM D x)

/-- Hodge Star is an involution on the correct GRADED paired degrees. -/
theorem gradedStar_square (D : P ≃ₗ[ℚ] Q) (x : P × Q) :
    gradedStar D (gradedStar D x) = x := by
  rcases x with ⟨a, b⟩
  simp [gradedStar]

/-- The original GST complex CM structure squares to MINUS identity,
distinct from the Hodge Star squaring to plus identity. -/
theorem gradedCM_square (D : P ≃ₗ[ℚ] Q) (x : P × Q) :
    gradedCM D (gradedCM D x) = -x := by
  rcases x with ⟨a, b⟩
  simp [gradedCM, map_neg]

/-- All-degree GST original CM curvature source:
  [J,M] = 2 HodgeStar
on paired complementary degree rational source modules. -/
theorem gradedCurvature_equals_twoStar (D : P ≃ₗ[ℚ] Q)
    (x : P × Q) :
    gradedCurvature D x = (2 : ℚ) • gradedStar D x := by
  rcases x with ⟨a, b⟩
  apply Prod.ext
  · simp [gradedCurvature, gradedCM, gradedSurvive,
      gradedStar, map_smul]
  · simp [gradedCurvature, gradedCM, gradedSurvive,
      gradedStar, map_smul]

/-- The actual GST full ORIGINAL null/maximum fixed-pair strength-one
wave is the scalar matrix templating all complementary-degree folds.
Its curvature gate is the user's physical Navigation charge b=0 or 1. -/
def scalarOriginalFold (b : ℚ) (x : ℚ × ℚ) : ℚ × ℚ :=
  (x.1 + (1 + 2*b)*x.2,
   (2*b-1)*x.1 + 3*x.2)

/-- This matrix is literally the owner's original 12-cell fixed-pair
factor, not an independently invented source matrix. -/
theorem scalarOriginalFold_is_true_wave (b : ℚ) (u : WaveSignal) :
    fixedPair (curvatureFold 1 b u) =
      scalarOriginalFold b (fixedPair u) := by
  simpa [scalarOriginalFold, fixedPair] using
    (fixedPair_curvatureFold 1 b u)

/-- Exact quadratic Hodge-Star/CM folding law: for any b this source has
a degree-two minimal-polynomial upper bound, so a single orbit stays
inside span{v,Fv} even if the Hodge degrees have huge cardinal indexes. -/
theorem scalarOriginalFold_quadratic (b : ℚ) (x : ℚ × ℚ) :
    scalarOriginalFold b (scalarOriginalFold b x) =
      (4 * (scalarOriginalFold b x).1 -
         4 * (1-b*b) * x.1,
       4 * (scalarOriginalFold b x).2 -
         4 * (1-b*b) * x.2) := by
  rcases x with ⟨a, c⟩
  apply Prod.ext <;> dsimp [scalarOriginalFold] <;> ring

#check gradedStar_square
#check gradedCM_square
#check gradedCurvature_equals_twoStar
#check scalarOriginalFold_is_true_wave
#check scalarOriginalFold_quadratic

#print axioms gradedStar_square
#print axioms gradedCM_square
#print axioms gradedCurvature_equals_twoStar
#print axioms scalarOriginalFold_quadratic

end GSTAllDegreeHodgeStarCMFold
