import HCUniverse2.GSTOriginalXAllWeightsLefschetzResidual
import HCUniverse2.GSTHypothesisPart1ChowAlgebraTransfer
import Mathlib

/-!
# GST original-X wave correspondence: rational Chow matrix compiler

The companion genuine ORIGINAL-X geometric derivation gives real Chow
cycles Z_i in CH^p(X)_Q, dual cycles Y_i in CH^(d-p)(X)_Q and
real self-correspondence matrix units
 E_(i,j)=pr1^*Y_i . pr2^*Z_j in CH^d(X x X)_Q.
They satisfy their matrix-unit composition identities in the Chow
ring and have exact canonical Betti cup/push-pull naturality.

Consequently every rational operator matrix A on the divisor-Lefschetz
source span has a GENUINE Chow representative
 Gamma_A = sum_(i,j) A_(j,i) E_(i,j).
For Picard rank >=12, this realizes the owner's original 12-cell
U,J,M,[J,M] matrices on an ACTUAL original-X algebraic cycle sector.

This file proves THE RATIONAL MODULE portion of the correspondence
compiler (the genuine algebraic source cycles are inputs with certified
intersection pairing):
  * arbitrary rational matrices have matching native and Betti operators;
  * native and Betti classes agree on EVERY native cycle;
  * the native action on each actual source cycle is the stated matrix
    column, with NO assumed inverse of cycleClass.

The full refined Chow product/push-pull statement is proved in the
geometric TeX derivation; this generic rational linear algebra module
must not be confused with a scheme-theoretic Chow API constructor.
-/

set_option maxHeartbeats 6000000
noncomputable section

open scoped BigOperators
open GSTHypothesisPart1ChowAlgebraTransfer
open GSTOriginalXDivisorCurveCyclicChowFold

namespace GSTOriginalXWaveChowMatrixCompiler

universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {A : Type v} [AddCommGroup A] [Module ℚ A]
variable {B : Type w} [AddCommGroup B] [Module ℚ B]
variable (F : IntersectionChowFrame ι A B)

/-- The genuine product-Chow matrix-unit formula at rational native level.
The geometric meaning is (A_(j,i) pr1^*Y_i . pr2^*Z_j) summed in Chow. -/
noncomputable def nativeMatrixFold (T : Matrix ι ι ℚ) : Module.End ℚ A :=
  ∑ i : ι, ∑ j : ι,
    T j i • nativeRankOne (F.nativeIntersection i) (F.source j)

/-- Canonical Betti action of the SAME Chow correspondence matrix. -/
noncomputable def bettiMatrixFold (T : Matrix ι ι ℚ) : Module.End ℚ B :=
  ∑ i : ι, ∑ j : ι,
    T j i • nativeRankOne
      (F.bettiIntersection i) (F.cycleClass (F.source j))

/-- One arbitrary rational GST wave matrix gives the exact native-Betti
commuting square. The source is an actual Chow matrix-unit expression
in the companion original-X geometric theorem. -/
theorem nativeMatrixFold_class (T : Matrix ι ι ℚ) (z : A) :
    F.cycleClass (nativeMatrixFold F T z) =
      bettiMatrixFold F T (F.cycleClass z) := by
  simp only [nativeMatrixFold, bettiMatrixFold, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp [nativeRankOne, F.intersection_natural i z]

/-- At EACH original-X algebraic source Z_k the full geometric
correspondence acts by the column k of the rational source matrix. -/
theorem nativeMatrixFold_source (T : Matrix ι ι ℚ) (k : ι) :
    nativeMatrixFold F T (F.source k) =
      ∑ j : ι, T j k • F.source j := by
  calc
    nativeMatrixFold F T (F.source k) =
        ∑ i : ι, ∑ j : ι,
          T j i • (F.nativeIntersection i (F.source k) • F.source j) := by
            simp only [nativeMatrixFold, LinearMap.sum_apply, LinearMap.smul_apply]
            rfl
    _ = ∑ i : ι,
          (if i = k then ∑ j : ι, T j i • F.source j else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [F.intersection_delta]
          split_ifs with h
          · simp [h]
          · simp
    _ = ∑ j : ι, T j k • F.source j := by simp

/-- The original-X canonical Betti action agrees with that column on
the ACTUAL divisor-Lefschetz source classes. -/
theorem bettiMatrixFold_source (T : Matrix ι ι ℚ) (k : ι) :
    bettiMatrixFold F T (F.cycleClass (F.source k)) =
      ∑ j : ι, T j k • F.cycleClass (F.source j) := by
  rw [← nativeMatrixFold_class F T (F.source k), nativeMatrixFold_source F T k]
  simp only [map_sum, map_smul]

/-- All true ORIGINAL-X rational matrix source actions preserve the
range of the actual native-to-Betti cycle-class map. -/
theorem matrixFold_preserves_algebraic_range
    (T : Matrix ι ι ℚ) (beta : B)
    (hbeta : beta ∈ LinearMap.range F.cycleClass) :
    bettiMatrixFold F T beta ∈ LinearMap.range F.cycleClass := by
  rcases hbeta with ⟨z, rfl⟩
  exact ⟨nativeMatrixFold F T z,
    nativeMatrixFold_class F T z⟩

#check nativeMatrixFold
#check bettiMatrixFold
#check nativeMatrixFold_class
#check nativeMatrixFold_source
#check bettiMatrixFold_source
#check matrixFold_preserves_algebraic_range

#print axioms nativeMatrixFold_class
#print axioms nativeMatrixFold_source
#print axioms matrixFold_preserves_algebraic_range

end GSTOriginalXWaveChowMatrixCompiler
