import GSTMathboxCorrectedZetaInfinite
import GSTClassicalHodgeGeometricMatrixRankLanding
import GSTClassicalHodgeCodimensionZeroFundamentalCycle

/-!
# Research GST: fixed non-free zeta measurement from actual degree-zero geometry

The author's corrected indexed zeta equation has exact sum -1 at
x=y=2 (proved, not assumed). A previous audit proved that an ARBITRARY
free real multiplier called zetaAtS adds no independent geometric
information: it can be chosen to match a preexisting nonzero class.

The improvement here is to FIX the scalar -1/2, the standard
analytic-continuation special value zeta(0), rather than freely choose
a multiplier, and build the native SOURCE cycle from genuine geometry:
the canonical sum of codimension-zero fundamental components on V.

A legitimate Betti degree-normalization equation (class of fundamental
cycle measured as 1) is required to connect that cycle to Q-valued
Hodge cohomology. The current HodgeBigradedBettiData record stores an
arbitrary rational-linear cycleClass, so this normalization cannot be
derived from its present fields (the zero-cycleClass countermodel).

Under the explicitly stated geometric degree-normalization input,
the fixed scalar expression is realized by the canonical geometric
cycle and the canonical half-degree readout; nonzero source follows.
This is a concrete universal *codimension-zero construction*, not a
replacement for the still-missing p>0 geometric source mechanism.
-/

set_option maxHeartbeats 20000000
noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGeometricMatrixRankLanding
open GSTClassicalHodgeCodimensionZeroFundamentalCycle
open GSTMathboxCorrectedZetaGeometry
open GSTMathboxCorrectedZetaInfinite

namespace GSTResearchFixedZetaGeometricSource

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Degree normalization of a TRUE rational cycle-class map on the
canonical fundamental component cycle. It is not a surjectivity,
Hodge-basis, arbitrary-target preimage, or complex period axiom. -/
def FundamentalDegreeNormalization
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∃ degreeRead : ClassicalHodgeFiber V H 0 →ₗ[ℚ] ℚ,
    degreeRead (geometricHodgeClass G
      (codimensionZeroFundamentalCycle V)) = 1

/-- A fixed rational coefficient (-1/2), representing the known special
zeta value at s=0, gives the EXACT corrected indexed zeta scalar 1/2.
There is no adjustable zeta multiplier in this statement. -/
theorem fixed_zetazero_corrected_scalar :
    (-1/2 : ℝ) * (∑' m : ℕ, indexedKernel 2 2 m) = 1/2 := by
  rw [corrected_series_two_tsum]
  norm_num

/-- Construction of a nonzero native Hodge source from the CANONICAL
codimension-zero fundamental cycle and independently normalized degree
readout. The resulting corrected-series measurement is FIXED to 1/2,
rather than a free real number selected to fit a target class. -/
theorem actual_codimension_zero_source_of_degree_normalization
    (G : GeometricCycleClassSpine V H)
    (hnorm : FundamentalDegreeNormalization G) :
    ∃ (Z : codimensionCycles V.X 0)
      (read : ClassicalHodgeFiber V H 0 →ₗ[ℚ] ℚ),
      Z = codimensionZeroFundamentalCycle V ∧
      ((read (geometricHodgeClass G Z) : ℚ) : ℝ) =
        (-1/2 : ℝ) * (∑' m : ℕ, indexedKernel 2 2 m) ∧
      geometricHodgeClass G Z ≠ 0 := by
  obtain ⟨degreeRead, hdegree⟩ := hnorm
  let halfDegree : ClassicalHodgeFiber V H 0 →ₗ[ℚ] ℚ :=
    (1/2 : ℚ) • degreeRead
  refine ⟨codimensionZeroFundamentalCycle V, halfDegree,
    rfl, ?_, ?_⟩
  · have hhalf :
        halfDegree (geometricHodgeClass G
          (codimensionZeroFundamentalCycle V)) = 1/2 := by
      simp [halfDegree, hdegree]
    rw [fixed_zetazero_corrected_scalar]
    simpa using congrArg (fun q : ℚ => (q : ℝ)) hhalf
  · intro hz
    have hd :
        degreeRead (geometricHodgeClass G
          (codimensionZeroFundamentalCycle V)) = 0 := by
      rw [hz]
      exact map_zero degreeRead
    rw [hdegree] at hd
    norm_num at hd

#check FundamentalDegreeNormalization
#check fixed_zetazero_corrected_scalar
#check actual_codimension_zero_source_of_degree_normalization
#print axioms fixed_zetazero_corrected_scalar
#print axioms actual_codimension_zero_source_of_degree_normalization

end GSTResearchFixedZetaGeometricSource
