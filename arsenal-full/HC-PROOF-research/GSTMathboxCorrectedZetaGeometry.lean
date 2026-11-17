import GSTClassicalHodgeGeometricMatrixRankLanding
import Mathlib

/-!
# Mathbox: corrected indexed GST zeta / geometric-coordinate equation (3)

User correction 2026-10-14:
  L(t(s)) s = zeta(s) * Σ [n → R] 1 / (x^n - y^(n+1)) ⊕ H × Q.

The denominator NOW DEPENDS ON n. This repairs the earlier *constant*
summand defect, but does not make arbitrary inputs convergent or legal.
The index set "n → R" and the direct-sum/product algebra operation still
require definitions. We choose NATURAL n >= 1 as an explicitly scoped
interpretation, never relabeling it as the user's unspecified R.

Mathematical contributions:
1. The EXACT indexed real denominator, no substituted toy kernel.
2. An explicit pole at (x,y,n)=(4,2,1).
3. A diagonal x=y=2 identity reducing every term to a negative geometric
   term; thus every nonempty partial sum is strictly negative.
4. The corrected finite zeta-weighted expression is nonzero for any
   nonzero scalar zeta value, not merely a claimed nonzero input.
5. A bridge to a GENUINELY ALGEBRAIC geometric direction: if the exact
   real indexed expression is identified with a rational linear detector
   evaluated on an ACTUAL native rational algebraic cycle, the cycle
   cannot be in the old algebraic span. This is arbitrary-rank, but the
   independent geometric comparison identity is an explicit input.

No infinite sum, zeta transcendental coefficient, or unspecified
"H × Q" operation is silently promoted into a rational cycle class.
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

namespace GSTMathboxCorrectedZetaGeometry

/-- Exact corrected equation (3) denominator for original index n>=1,
using Lean index m=n-1, so the denominator is x^(m+1)-y^(m+2). -/
def indexedDenominator (x y : ℝ) (m : ℕ) : ℝ :=
  x ^ (m + 1) - y ^ (m + 2)

/-- Whether the user's reciprocal is mathematically defined at this index. -/
def legalIndex (x y : ℝ) (m : ℕ) : Prop :=
  indexedDenominator x y m ≠ 0

/-- A finite-length corrected series, with index n from 1 to N inclusive.
Every term is exactly one of the user's corrected reciprocals. -/
def indexedKernel (x y : ℝ) (m : ℕ) : ℝ :=
  (indexedDenominator x y m)⁻¹

def correctedPartialSum (x y : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.range N, indexedKernel x y m

/-- Corrected finite zeta-weighted expression at a fixed spectral value.
The scalar zeta value is explicit; we make no silent irrational-to-Q cast. -/
def correctedZetaPartial (zetaAtS x y : ℝ) (N : ℕ) : ℝ :=
  zetaAtS * correctedPartialSum x y N

/-- Corrected equation (3) STILL has genuine poles, e.g. 4^1=2^2.
Lean's totalized inverse sends zero to zero, so the legalIndex predicate
must be checked before treating a term as an actual reciprocal. -/
theorem exact_pole_at_four_two :
    indexedDenominator 4 2 0 = 0 ∧ ¬ legalIndex 4 2 0 := by
  constructor
  · norm_num [indexedDenominator]
  · norm_num [legalIndex, indexedDenominator]

/-- For x=y=2 the indexed denominator simplifies EXACTLY to -2^(m+1). -/
theorem equal_base_two_denominator (m : ℕ) :
    indexedDenominator 2 2 m = -(2 : ℝ) ^ (m+1) := by
  unfold indexedDenominator
  rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
  ring

/-- The diagonal x=y=2 terms are a negative geometric sequence. -/
theorem equal_base_two_kernel_neg (m : ℕ) :
    indexedKernel 2 2 m < 0 := by
  have hp : 0 < (2 : ℝ) ^ (m + 1) := pow_pos (by norm_num) _
  have hi : 0 < ((2 : ℝ) ^ (m + 1))⁻¹ := inv_pos.mpr hp
  unfold indexedKernel
  rw [equal_base_two_denominator]
  simpa using (neg_neg_of_pos hi)

/-- Hence the *corrected* series has a nonzero partial sum at
every finite positive cutoff, unlike the false constant-sum diagnosis
of the old, unindexed formula. -/
theorem equal_base_two_partialSum_neg
    (N : ℕ) (hN : 0 < N) :
    correctedPartialSum 2 2 N < 0 := by
  cases N with
  | zero => omega
  | succ N =>
    unfold correctedPartialSum
    rw [Finset.sum_range_succ]
    have hn : (∑ m ∈ Finset.range N, indexedKernel 2 2 m) ≤ 0 :=
      Finset.sum_nonpos (fun m _ => le_of_lt (equal_base_two_kernel_neg m))
    exact add_neg_of_nonpos_of_neg hn (equal_base_two_kernel_neg N)

/-- Nonzero zeta scalar and a nonempty partial sum force nonvanishing.
This is a REAL scalar fact, not an unsupported rational Hodge class. -/
theorem correctedZetaPartial_ne_zero
    (zetaAtS : ℝ) (N : ℕ)
    (hZeta : zetaAtS ≠ 0) (hN : 0 < N) :
    correctedZetaPartial zetaAtS 2 2 N ≠ 0 := by
  unfold correctedZetaPartial
  exact mul_ne_zero hZeta (ne_of_lt (equal_base_two_partialSum_neg N hN))

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : ℕ}
variable {ι : Type*}

/-- A precise source-to-target dictionary for the user's FIXED equation:
if the numerical finite series equals a rational Hodge coordinate of a
genuinely constructed native algebraic cycle, then it detects a new
direction in the actual algebraic cycle-class image. Does not assume a
representative for an arbitrary target Hodge class. -/
theorem corrected_zeta_detector_adds_native_direction
    (G : GeometricCycleClassSpine V H)
    (old : ι → codimensionCycles V.X p)
    (fresh : codimensionCycles V.X p)
    (read : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (hOld : ∀ i : ι, read (geometricHodgeClass G (old i)) = 0)
    (zetaAtS : ℝ) (N : ℕ)
    (hZeta : zetaAtS ≠ 0) (hN : 0 < N)
    (hActual :
      ((read (geometricHodgeClass G fresh) : ℚ) : ℝ) =
        correctedZetaPartial zetaAtS 2 2 N) :
    geometricHodgeClass G fresh ∉
      Submodule.span ℚ
        (Set.range (fun i : ι => geometricHodgeClass G (old i))) := by
  have hscalar : correctedZetaPartial zetaAtS 2 2 N ≠ 0 :=
    correctedZetaPartial_ne_zero zetaAtS N hZeta hN
  have hFresh : read (geometricHodgeClass G fresh) ≠ 0 := by
    intro hz
    apply hscalar
    rw [← hActual, hz]
    norm_num
  intro hspan
  have hker :
      Submodule.span ℚ
        (Set.range (fun i : ι => geometricHodgeClass G (old i))) ≤
      LinearMap.ker read := by
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    exact LinearMap.mem_ker.mpr (hOld i)
  exact hFresh (LinearMap.mem_ker.mp (hker hspan))

#check indexedDenominator
#check legalIndex
#check exact_pole_at_four_two
#check equal_base_two_denominator
#check equal_base_two_kernel_neg
#check equal_base_two_partialSum_neg
#check correctedZetaPartial_ne_zero
#check corrected_zeta_detector_adds_native_direction

#print axioms equal_base_two_partialSum_neg
#print axioms correctedZetaPartial_ne_zero
#print axioms corrected_zeta_detector_adds_native_direction

end GSTMathboxCorrectedZetaGeometry
