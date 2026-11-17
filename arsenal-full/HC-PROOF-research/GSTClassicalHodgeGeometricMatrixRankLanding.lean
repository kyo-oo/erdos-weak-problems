import GSTClassicalHodgeGeometricCycleClassSpine
import GSTClassicalHodgeGradedCorrespondenceProgramOrbit
import GSTClassicalHodgeCodimensionZeroFundamentalCycle
import GSTClassicalHodgeFiberedCosmology
import GSTHodgeChannelFinale
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# UNIVERSAL GST HODGE ATTACK: GEOMETRIC FULL-RANK MATRIX

Instead of constructing one correspondence with EXACT output equal to EACH
chosen Hodge basis direction, we can construct independently defined
native algebraic-cycle classes and prove that their matrix of rational
Hodge coordinates has full rank.

THE MATHEMATICAL ADVANCE IS AN EXPLICIT RECONSTRUCTION FORMULA.
For a rational Hodge fiber W of dimension n, take n actual native cycles
Z_j and let

       M_ij = ith Hodge coordinate of cycleClass(Z_j).

If the RATIONAL matrix M admits a right inverse B, an arbitrary rational
Hodge state alpha is represented by the ACTUAL native cycle

       sum_j (B * repr(alpha))_j Z_j.

Thus no per-basis exact cycle-class equation is needed as a premise: the
geometry only needs to prove a NUMERICAL full-rank criterion.

This is an alternate attack on the UNIVERSAL, all-varieties theorem.
It is not a proof that every smooth projective variety supplies such
independent cycles. That geometric full-rank theorem is precisely what
must be derived from GST projective/correspondence and intersection theory.
No per-target cycle or preimage is included in the full-rank criterion.

The second theorem specializes each Z_j to the native output of one ACTUAL
existing GST graded correspondence program from its universal projective
origin. This makes full rank a concrete target for the repo's geometric
operator engine, not an unrelated linear-algebraic abstraction.

NEEDS CI RUN LATER.
-/

set_option maxHeartbeats 50000000
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
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit.GradedCorrespondenceProgram
open GSTClassicalHodgeCodimensionZeroFundamentalCycle

namespace GSTClassicalHodgeGeometricMatrixRankLanding

/-! ## General mathematical reconstruction from an invertible coordinate
matrix, requiring no algebraic geometry and no assumed basis witnesses. -/

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The rational coordinate matrix of independently selected geometric
vectors in an ARBITRARY FINITE basis index type (not just Fin n).
The abstract period-detector factorization specializes to precisely
this same index type. -/
noncomputable def geometricCoordinateMatrix
    (b : Module.Basis ι ℚ W)
    (z : ι → W) : Matrix ι ι ℚ :=
  fun i j => (b.repr (z j)) i

/-- FULL RANK -> UNIVERSAL EXACT RECONSTRUCTION.

The only hypothesis is numerical invertibility M * B = I.
For every x, we build the coefficients explicitly as B * repr(x),
and PROVE their combination of supplied geometric vectors equals x. -/
theorem geometric_matrix_right_inverse_reconstructs
    (b : Module.Basis ι ℚ W)
    (z : ι → W)
    (B : Matrix ι ι ℚ)
    (hInv : geometricCoordinateMatrix b z * B = 1)
    (x : W) :
    ∑ j : ι,
      (B.mulVec (fun i => (b.repr x) i)) j • z j = x := by
  classical
  apply b.repr.injective
  ext i
  let target : ι → ℚ := fun k => (b.repr x) k
  let coeff : ι → ℚ := B.mulVec target
  let M : Matrix ι ι ℚ := geometricCoordinateMatrix b z
  have htarget : M.mulVec coeff = target := by
    calc
      M.mulVec coeff = (M * B).mulVec target := by
        simp only [coeff, Matrix.mulVec_mulVec]
      _ = target := by simpa [M, hInv]
  calc
    (b.repr (∑ j : ι, (B.mulVec target) j • z j)) i =
      ∑ j : ι, (B.mulVec target) j * (b.repr (z j)) i := by
        simp [map_sum, map_smul, Finsupp.sum_apply, smul_eq_mul]
    _ = M.mulVec coeff i := by
      simp [M, coeff, geometricCoordinateMatrix, Matrix.mulVec,
        dotProduct, mul_comm]
    _ = target i := congrFun htarget i
    _ = (b.repr x) i := rfl

/-! ## Geometric specialization to actual algebraic cycles. -/

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Genuine cycle-class map, now regarded in the rational Hodge fiber.
Its output is geometric: no formal Hodge matrix-unit maps are inserted. -/
noncomputable def geometricHodgeClass
    (G : GeometricCycleClassSpine V H)
    (Z : codimensionCycles V.X p) :
    ClassicalHodgeFiber V H p :=
  ⟨H.cycleClass p Z, G.algebraic_is_hodge p Z⟩

/-- Native rational codimension-p cycles -> the complete rational Hodge
fiber, with linearity inherited from the actual cycle-class map. -/
noncomputable def nativeToHodgeFiberLinear
    (G : GeometricCycleClassSpine V H) :
    codimensionCycles V.X p →ₗ[ℚ] ClassicalHodgeFiber V H p where
  toFun := geometricHodgeClass G
  map_add' := by
    intro Z W
    apply Subtype.ext
    simp [geometricHodgeClass]
  map_smul' := by
    intro a Z
    apply Subtype.ext
    simp [geometricHodgeClass]

/-- Finite-dimensional matrix of actual native cycle classes, expressed in
the canonical rational Hodge basis. This is the numerical object whose rank
must be forced by the GST projective and correspondence geometry. -/
noncomputable def nativeHodgeMatrix
    (G : GeometricCycleClassSpine V H)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (cycles : Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)) →
      codimensionCycles V.X p) :
    Matrix (Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)))
      (Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p))) ℚ :=
  geometricCoordinateMatrix
    (Module.finBasis ℚ (ClassicalHodgeFiber V H p))
    (fun j => geometricHodgeClass G (cycles j))

/-- The actual native-cycle reconstruction dictated by a right inverse
of the geometric coordinate matrix. Completely explicit and rational. -/
noncomputable def nativeCycleByMatrixInversion
    (G : GeometricCycleClassSpine V H)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (cycles : Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)) →
      codimensionCycles V.X p)
    (inverse : Matrix
      (Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)))
      (Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p))) ℚ)
    (alpha : ClassicalHodgeFiber V H p) :
    codimensionCycles V.X p :=
  ∑ j : Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)),
    (inverse.mulVec
      (fun i => ((Module.finBasis ℚ
        (ClassicalHodgeFiber V H p)).repr alpha) i)) j • cycles j

/-- **DIRECT MATRIX-RANK TO ACTUAL CYCLE PROOF.**
Independent algebraic cycles + nondegenerate coordinate matrix give a
concrete rational algebraic cycle representing every Hodge class. -/
theorem geometric_full_rank_produces_all_hodge_cycles
    (G : GeometricCycleClassSpine V H)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (cycles : Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)) →
      codimensionCycles V.X p)
    (inverse : Matrix
      (Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)))
      (Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p))) ℚ)
    (hFullRank : nativeHodgeMatrix G cycles * inverse = 1)
    (alpha : ClassicalHodgeFiber V H p) :
    H.cycleClass p (nativeCycleByMatrixInversion G cycles inverse alpha) =
      alpha.1 := by
  let b := Module.finBasis ℚ (ClassicalHodgeFiber V H p)
  have hrepr :=
    geometric_matrix_right_inverse_reconstructs b
      (fun j => geometricHodgeClass G (cycles j))
      inverse hFullRank alpha
  have hcycle :
      nativeToHodgeFiberLinear G
        (nativeCycleByMatrixInversion G cycles inverse alpha) = alpha := by
    change nativeToHodgeFiberLinear G
        (∑ j : Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)),
          (inverse.mulVec (fun i => (b.repr alpha) i)) j • cycles j) = alpha
    rw [map_sum]
    simp only [map_smul]
    change
      (∑ j : Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)),
        (inverse.mulVec (fun i => (b.repr alpha) i)) j •
          geometricHodgeClass G (cycles j)) = alpha
    exact hrepr
  exact congrArg Subtype.val hcycle

/-! ## Direct tie-in to EXISTING graded GST geometric program outputs. -/

/-- Genuine GST origin-to-p programs generate a concrete Hodge-coordinate
matrix. ALL its columns are independently computable native program outputs,
never chosen as preimages of target Hodge basis vectors. -/
noncomputable def nativeGSTProgramHodgeMatrix
    (G : GeometricCycleClassSpine V H)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (programs :
      Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)) →
        GradedCorrespondenceProgram V H 0 p) :
    Matrix
      (Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)))
      (Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p))) ℚ :=
  nativeHodgeMatrix G
    (fun j => (programs j).cycleEval G (codimensionZeroFundamentalCycle V))

/-- **NUMERICAL GST FULL-RANK LANDING.**
A right inverse for the actual correspondence-output matrix is enough
to derive EVERY rational Hodge class in that weight, using only genuine
native algebraic cycles from the canonical GST geometric origin. -/
theorem all_hodge_cycles_of_full_rank_GST_program_matrix
    (G : GeometricCycleClassSpine V H)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (programs :
      Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)) →
        GradedCorrespondenceProgram V H 0 p)
    (inverse : Matrix
      (Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)))
      (Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p))) ℚ)
    (hMatrix : nativeGSTProgramHodgeMatrix G programs * inverse = 1)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  let a : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  exact ⟨nativeCycleByMatrixInversion G
    (fun j => (programs j).cycleEval G (codimensionZeroFundamentalCycle V))
    inverse a,
    geometric_full_rank_produces_all_hodge_cycles G
      (fun j => (programs j).cycleEval G
        (codimensionZeroFundamentalCycle V))
      inverse hMatrix a⟩

/-! ## Determinant-based universal geometric target

For the mathematical attack, it is stronger and more useful to demand
a NONZERO rational determinant of the matrix of genuine GST program
outputs, instead of furnishing an inverse matrix as extra data.
NonsingularInverse constructs the inverse automatically, and the
reconstruction above computes the rational algebraic cycle. -/

/-- Numerical nonvanishing of the ACTUAL native Hodge-coordinate
matrix canonically gives exact algebraic realization at this weight. -/
theorem hodge_cycle_of_nonzero_geometric_determinant
    (G : GeometricCycleClassSpine V H)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (cycles : Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)) →
      codimensionCycles V.X p)
    (hdet : (nativeHodgeMatrix G cycles).det ≠ 0)
    (alpha : ClassicalHodgeFiber V H p) :
    H.cycleClass p
        (nativeCycleByMatrixInversion G cycles
          (nativeHodgeMatrix G cycles)⁻¹ alpha) = alpha.1 := by
  classical
  have hunit : IsUnit (nativeHodgeMatrix G cycles).det :=
    isUnit_iff_ne_zero.mpr hdet
  exact geometric_full_rank_produces_all_hodge_cycles
    G cycles (nativeHodgeMatrix G cycles)⁻¹
    (Matrix.mul_nonsing_inv (nativeHodgeMatrix G cycles) hunit) alpha

/-- UNIVERSAL geometric determinant-generation hypothesis: for each
codimension, there are actual GST native correspondence programs from
the canonical projective origin with linearly independent rational Hodge
cycle classes spanning the entire Hodge fiber.

Unlike assuming a target Hodge cycle already exists, the data are
concrete program SYNTAX and ONE scalar determinant inequality.
It remains to prove such programs exist for arbitrary V; this is the
substantive geometric challenge to be attacked with new GST operators. -/
def UniversalGSTGeometricDeterminantGeneration
    (G : GeometricCycleClassSpine V H)
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H) : Prop :=
  ∀ q : Nat,
    letI : FiniteDimensional ℚ (ClassicalHodgeFiber V H q) := F.finite q
    ∃ programs :
      Fin (Module.finrank ℚ (ClassicalHodgeFiber V H q)) →
        GradedCorrespondenceProgram V H 0 q,
      (nativeGSTProgramHodgeMatrix G programs).det ≠ 0

/-- **FULL RATIONAL HODGE STATEMENT FROM GEOMETRIC DETERMINANTS.**

Every codimension on the ORIGINAL arbitrary smooth projective complex
carrier is handled simultaneously. The proof explicitly constructs
a native rational codimension-q algebraic cycle for EVERY rational
(q,q) Hodge class, using ONLY genuine GST program output cycles.

One geometric nonzero determinant per Hodge weight replaces exact
target-sheet matching for every basis vector. It is an independently
testable, scalar, intersection-geometric target for the entire proof. -/
theorem exact_hodge_of_universal_GST_geometric_determinants
    (G : GeometricCycleClassSpine V H)
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (h : UniversalGSTGeometricDeterminantGeneration G F) :
    BigradedBettiHodgeStatement V H := by
  intro q alpha halpha
  letI : FiniteDimensional ℚ (ClassicalHodgeFiber V H q) := F.finite q
  obtain ⟨programs, hdet⟩ := h q
  let cycles : Fin (Module.finrank ℚ (ClassicalHodgeFiber V H q)) →
      codimensionCycles V.X q :=
    fun i => (programs i).cycleEval G (codimensionZeroFundamentalCycle V)
  let a : ClassicalHodgeFiber V H q := ⟨alpha, halpha⟩
  refine ⟨nativeCycleByMatrixInversion G cycles
      (nativeHodgeMatrix G cycles)⁻¹ a, ?_⟩
  exact hodge_cycle_of_nonzero_geometric_determinant G cycles hdet a

#check geometric_matrix_right_inverse_reconstructs
#check geometric_full_rank_produces_all_hodge_cycles
#check all_hodge_cycles_of_full_rank_GST_program_matrix
#print axioms all_hodge_cycles_of_full_rank_GST_program_matrix

end GSTClassicalHodgeGeometricMatrixRankLanding
