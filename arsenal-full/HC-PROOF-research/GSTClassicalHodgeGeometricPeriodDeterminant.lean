import GSTClassicalHodgeGeometricMatrixRankLanding
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# FROM GEOMETRIC INTERSECTION PERIODS TO FULL HODGE RANK

The previous theorem accepted a nonsingular Hodge-COORDINATE matrix
of genuine native GST program outputs. This upgrade gives an independent
way to establish that criterion from geometric numerical PERIODS.

Take a rational Hodge fiber W of dimension n, n genuine native
algebraic-cycle classes Z_j, and n rational linear period detectors t_i.
Construct the directly TESTABLE intersection/period matrix

       A_ij = t_i( cycleClass(Z_j) ).

The chosen basis-coordinate matrix is M_kj = coord_k(cycleClass Z_j).
The detector matrix in the Hodge basis is P_ik = t_i(b_k).
By exact rational linearity, A = P * M, so

       det(A) = det(P) * det(M).

Therefore NONZERO DET(A) forces NONZERO DET(M). Consequently the
already-proved GST geometric matrix inversion constructs actual rational
algebraic cycles for EVERY rational Hodge class.

This is a major practical improvement: the user need not calculate
coordinates against each abstract Hodge basis direction. They can
compute intersection numbers/periods of INDEPENDENT, ACTUAL geometric
correspondence cycles, using GST's projective topology and Gysin calculus.

It remains a genuine geometric task to construct n programs with nonzero
intersection determinant on arbitrary V. We DO NOT postulate its
existence, and a single positive projective-degree trace cannot in
general certify a full rank-n matrix.

NEEDS CI RUN LATER.
-/

set_option maxHeartbeats 35000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit.GradedCorrespondenceProgram
open GSTClassicalHodgeCodimensionZeroFundamentalCycle
open GSTClassicalHodgeGeometricMatrixRankLanding

namespace GSTClassicalHodgeGeometricPeriodDeterminant

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Geometric period matrix of n supplied vectors against n linear
detectors. Entries can be integration and intersection numbers. -/
def periodMatrix (z : ι → W) (detector : ι → W →ₗ[ℚ] ℚ) :
    Matrix ι ι ℚ :=
  fun i j => detector i (z j)

/-- The matrix of the same rational detectors on a chosen Hodge basis. -/
def detectorBasisMatrix
    (b : Module.Basis ι ℚ W)
    (detector : ι → W →ₗ[ℚ] ℚ) :
    Matrix ι ι ℚ :=
  fun i j => detector i (b j)

/-- Fundamental matrix identity for ANY rational vector space and finite
basis. Every geometric period factorizes through rational basis
coordinates; this is independent of the Hodge conjecture. -/
theorem periodMatrix_eq_detector_mul_coordinate
    (b : Module.Basis ι ℚ W)
    (z : ι → W)
    (detector : ι → W →ₗ[ℚ] ℚ) :
    periodMatrix z detector =
      detectorBasisMatrix b detector *
        geometricCoordinateMatrix b z := by
  classical
  ext i j
  change detector i (z j) =
    ∑ k : ι, detector i (b k) * (b.repr (z j)) k
  conv_lhs => rw [← b.sum_repr (z j)]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  exact mul_comm _ _

/-- NONZERO PERIOD DETERMINANT -> NONZERO COORDINATE DETERMINANT.
The proof is independent of any numerical nondegeneracy assumption on
the detector family: nonzero det(A) itself forces what is needed. -/
theorem coordinate_det_ne_zero_of_period_det_ne_zero
    (b : Module.Basis ι ℚ W)
    (z : ι → W)
    (detector : ι → W →ₗ[ℚ] ℚ)
    (hPeriod :
      (periodMatrix z detector).det ≠ 0) :
    (geometricCoordinateMatrix b z).det ≠ 0 := by
  intro hZero
  have hFactor := periodMatrix_eq_detector_mul_coordinate b z detector
  apply hPeriod
  rw [hFactor, Matrix.det_mul, hZero, mul_zero]

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- NUMERICALLY TESTABLE GST PERIOD MATRIX: the selected columns are
actual algebraic-cycle outputs of existing GST graded programs from the
projective origin. Detectors are rational linear intersection/Gysin
functionals on the genuine Hodge fiber. -/
noncomputable def nativeGSTPeriodMatrix
    (G : GeometricCycleClassSpine V H)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (programs :
      Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)) →
        GradedCorrespondenceProgram V H 0 p)
    (detectors :
      Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)) →
        ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ) :
    Matrix
      (Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)))
      (Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p))) ℚ :=
  periodMatrix
    (fun j => geometricHodgeClass G
      ((programs j).cycleEval G (codimensionZeroFundamentalCycle V)))
    detectors

/-- THE ACTUAL MATRIX RANK CAN BE PROVED FROM INDEPENDENTLY COMPUTED
GEOMETRIC PERIODS, without matching program outputs to basis directions.
The normal-form change of basis is handled by Mathlib determinant algebra. -/
theorem nativeGSTHodgeMatrix_det_ne_zero_of_period_det_ne_zero
    (G : GeometricCycleClassSpine V H)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (programs :
      Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)) →
        GradedCorrespondenceProgram V H 0 p)
    (detectors :
      Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)) →
        ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (hPeriod : (nativeGSTPeriodMatrix G programs detectors).det ≠ 0) :
    (nativeGSTProgramHodgeMatrix G programs).det ≠ 0 := by
  exact coordinate_det_ne_zero_of_period_det_ne_zero
    (Module.finBasis ℚ (ClassicalHodgeFiber V H p))
    (fun j => geometricHodgeClass G
      ((programs j).cycleEval G (codimensionZeroFundamentalCycle V)))
    detectors hPeriod

/-- Actual algebraic cycle from a nonzero period determinant.
No target-sheet period equations appear in the input: only the
determinant of the independently constructed program/detector matrix. -/
theorem native_cycle_of_nonzero_GST_period_determinant
    (G : GeometricCycleClassSpine V H)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (programs :
      Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)) →
        GradedCorrespondenceProgram V H 0 p)
    (detectors :
      Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)) →
        ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (hPeriod : (nativeGSTPeriodMatrix G programs detectors).det ≠ 0)
    (alpha : ClassicalHodgeFiber V H p) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 := by
  let cycles := fun j =>
    (programs j).cycleEval G (codimensionZeroFundamentalCycle V)
  have hDet := nativeGSTHodgeMatrix_det_ne_zero_of_period_det_ne_zero
    G programs detectors hPeriod
  exact ⟨nativeCycleByMatrixInversion G cycles
    (nativeHodgeMatrix G cycles)⁻¹ alpha,
    hodge_cycle_of_nonzero_geometric_determinant G cycles hDet alpha⟩

/-! ## Geometry-first triangular period certificate

The existing GSTClassicalHodgeLefschetzTomography proves an intrinsic
unit-triangular readout on abstract Hodge-support addresses. To
complete the GEOMETRIC attack, construct the same shape using ACTUAL
GST correspondence-output cycles and genuine period detectors.

The determinant then follows from triangularity and nonzero diagonal
intersection numbers. This replaces an opaque determinant computation
with explicit off-diagonal vanishing and diagonal positivity claims. -/

/-- Upper triangular rational geometric periods with nonzero diagonal
have nonzero determinant, so they reconstruct EVERY Hodge class in
the corresponding weight as an actual native algebraic cycle. -/
theorem native_cycle_of_triangular_GST_periods
    (G : GeometricCycleClassSpine V H)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (programs :
      Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)) →
        GradedCorrespondenceProgram V H 0 p)
    (detectors :
      Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)) →
        ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (hTriangular :
      (nativeGSTPeriodMatrix G programs detectors).IsUpperTriangular)
    (hDiagonal :
      ∀ i : Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)),
        nativeGSTPeriodMatrix G programs detectors i i ≠ 0)
    (alpha : ClassicalHodgeFiber V H p) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 := by
  have hDet : (nativeGSTPeriodMatrix G programs detectors).det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular hTriangular]
    apply (Finset.prod_ne_zero_iff).2
    intro i hi
    exact hDiagonal i
  exact native_cycle_of_nonzero_GST_period_determinant
    G programs detectors hDet alpha

/-! ## The exact full-conjecture geometric target

A complete universal proof can now be reduced to the following very
concrete geometric theorem, for each arbitrary smooth projective
variety V and all codimensions p:

  construct n = dim_Q(Hdg^p(V)) genuine GST native geometric programs;
  construct n rational geometric period detectors;
  prove their pairing matrix is upper triangular with every
  diagonal entry nonzero.

This is a UNIVERSAL ALL-WEIGHTS target, not a finite-case theorem. The
programs and detectors are independent of an arbitrary Hodge target
class alpha. Once they exist, the proof of the FULL rational Hodge
conjecture is given below by the explicit matrix inversion construction.

An intrinsic GST Lefschetz tomography matrix is NOT sufficient here:
the lower inputs must be actual native-cycle operators and genuine
Betti geometric periods. That distinction is enforced in this type.
The existential geometry itself is not assumed as an axiom. -/

/-- Universal genuine GST triangular period generation, with actual
graded correspondence programs starting from the projective origin. -/
def UniversalGSTTriangularPeriodGeneration
    (G : GeometricCycleClassSpine V H)
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H) : Prop :=
  ∀ q : Nat,
    letI : FiniteDimensional ℚ (ClassicalHodgeFiber V H q) := F.finite q
    ∃ programs :
      Fin (Module.finrank ℚ (ClassicalHodgeFiber V H q)) →
        GradedCorrespondenceProgram V H 0 q,
    ∃ detectors :
      Fin (Module.finrank ℚ (ClassicalHodgeFiber V H q)) →
        ClassicalHodgeFiber V H q →ₗ[ℚ] ℚ,
      (nativeGSTPeriodMatrix G programs detectors).IsUpperTriangular ∧
      ∀ i : Fin (Module.finrank ℚ (ClassicalHodgeFiber V H q)),
        nativeGSTPeriodMatrix G programs detectors i i ≠ 0

/-- The genuine ALL-VARIETIES rational Hodge target, derived explicitly
from the actual native-cycle geometric period matrix and its triangular
geometry. No basis-cycle witness or target-specific algebraic preimage
is supplied as a hypothesis. -/
theorem full_rational_hodge_of_universal_GST_triangular_geometry
    (G : GeometricCycleClassSpine V H)
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (h : UniversalGSTTriangularPeriodGeneration G F) :
    BigradedBettiHodgeStatement V H := by
  intro q alpha halpha
  letI : FiniteDimensional ℚ (ClassicalHodgeFiber V H q) := F.finite q
  obtain ⟨programs, detectors, hTri, hDiag⟩ := h q
  exact native_cycle_of_triangular_GST_periods
    G programs detectors hTri hDiag ⟨alpha, halpha⟩

#check periodMatrix_eq_detector_mul_coordinate
#check coordinate_det_ne_zero_of_period_det_ne_zero
#check native_cycle_of_nonzero_GST_period_determinant
#print axioms native_cycle_of_nonzero_GST_period_determinant

end GSTClassicalHodgeGeometricPeriodDeterminant
