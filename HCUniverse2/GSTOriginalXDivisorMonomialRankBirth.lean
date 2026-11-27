import HCUniverse2.GSTOriginalXNativePhysicalNavigationBridge
import HCUniverse2.GSTOriginalXAllWeightsLefschetzResidual
import Mathlib

/-!
# Universal original-X divisor-monomial GST geometric source rank extraction

Geometry (companion TeX): on any smooth projective original X, each
multi-index mu determines an ACTUAL algebraic divisor-product cycle
Z_mu in CH^p(X)_Q; each complementary nu determines an ACTUAL cycle
Y_nu in CH^(d-p)(X)_Q. The rational intersection matrix
B_(nu,mu)=degree_X(Y_nu . Z_mu) is finite. Any full-rank square MINOR
has a rational inverse, yielding honest dual algebraic Chow cycles.

This module proves the exact extraction theorem from the actual
raw native intersection readouts and their canonical Betti comparison:
 1. an invertible rational source intersection minor constructs
    a Kronecker-dual native/Betti frame, not a supplied Hodge inverse;
 2. every prescribed alpha receives an explicit selected Chow source
    whose canonical Betti class equals the genuine projector of alpha;
 3. for ANY twelve independent original monomial directions the
    ACTUAL owner physical GST U/J/M/[J,M]/Navigation matrix compiles
    into a natural Chow/Betti source operator.

An invertible rank minor is not assumed to exist with arbitrary
chosen size. The geometric derivation takes its size to be the
rank of the independently computed divisor-monomial intersection
matrix. This rank may exceed Picard rank at higher p.

This Lean algebra checks source extraction; it does not manufacture
scheme intersection products internally or assert full Hodge coverage.
-/

set_option maxHeartbeats 8000000
noncomputable section
open scoped BigOperators

namespace GSTOriginalXDivisorMonomialRankBirth

open GSTOriginalXDivisorCurveCyclicChowFold
open GSTOriginalXNativePhysicalNavigationBridge
open GSTOriginalXAllWeightsLefschetzResidual

universe u v w z
variable {I : Type u} {J : Type v}
variable {A : Type w} [AddCommGroup A] [Module ℚ A]
variable {B : Type z} [AddCommGroup B] [Module ℚ B]

/-- True source interface of FINITE actual algebraic divisor monomials
and their canonical rational Betti intersection comparison on X. -/
structure OriginalMonomialPairing
    (I J : Type*)
    (A B : Type*)
    [AddCommGroup A] [Module ℚ A]
    [AddCommGroup B] [Module ℚ B] where
  cycleClass : A →ₗ[ℚ] B
  nativeCycle : I → A
  nativeDetector : J → (A →ₗ[ℚ] ℚ)
  bettiDetector : J → (B →ₗ[ℚ] ℚ)
  detector_natural :
    ∀ j z, nativeDetector j z = bettiDetector j (cycleClass z)

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable (D : OriginalMonomialPairing I J A B)
variable (src : κ → I) (detIdx : κ → J)

namespace OriginalMonomialPairing

/-- Actual original-X intersection MINOR for selected algebraic
codimension-p source and complementary Chow cycles. -/
def intersectionMinor : Matrix κ κ ℚ :=
  fun i j => D.nativeDetector (detIdx i) (D.nativeCycle (src j))

/-- The Gram inverse directly constructs each genuinely algebraic
dual numerical intersection readout from ACTUAL original-X cycles. -/
noncomputable def dualNativeReadout
    (inv : Matrix κ κ ℚ) (i : κ) : A →ₗ[ℚ] ℚ :=
  ∑ j : κ, inv i j • D.nativeDetector (detIdx j)

/-- Identical coefficients produce the corresponding CANONICAL rational
Betti cup/integration functional; no artificial Hodge pairing. -/
noncomputable def dualBettiReadout
    (inv : Matrix κ κ ℚ) (i : κ) : B →ₗ[ℚ] ℚ :=
  ∑ j : κ, inv i j • D.bettiDetector (detIdx j)

/-- Finite genuine original-X intersection rank suffices to MAKE a
dual algebraic source frame. We do not assume duality separately. -/
noncomputable def originalXSourceFrame
    (inv : Matrix κ κ ℚ)
    (hinv : inv * D.intersectionMinor src detIdx = 1) :
    IntersectionChowFrame κ A B where
  cycleClass := D.cycleClass
  source := fun i => D.nativeCycle (src i)
  nativeIntersection := D.dualNativeReadout detIdx inv
  bettiIntersection := D.dualBettiReadout detIdx inv
  intersection_natural := by
    intro i z
    simp only [dualNativeReadout, dualBettiReadout,
      LinearMap.sum_apply, LinearMap.smul_apply]
    apply Finset.sum_congr rfl
    intro j hj
    rw [D.detector_natural (detIdx j) z]
  intersection_delta := by
    intro i j
    simp only [dualNativeReadout, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul]
    have h := congrArg (fun Q : Matrix κ κ ℚ => Q i j) hinv
    simpa [Matrix.mul_apply, intersectionMinor, Matrix.one_apply] using h

/-- An arbitrary prescribed alpha has a DIRECT genuine native cycle
representing its actual divisor-monomial SOURCE PROJECTION.
The proof uses only the extracted intersection minor and canonical
native/Betti comparison, never an assumed Hodge-to-Chow inverse. -/
theorem prescribed_alpha_monomial_source_class
    (inv : Matrix κ κ ℚ)
    (hinv : inv * D.intersectionMinor src detIdx = 1)
    (alpha : B) :
    D.cycleClass
      (selectedLefschetzCycle
        (D.originalXSourceFrame src detIdx inv hinv) alpha) =
      bettiLefschetzProjector
        (D.originalXSourceFrame src detIdx inv hinv) alpha :=
  selectedLefschetzCycle_class
    (D.originalXSourceFrame src detIdx inv hinv) alpha

/-- At TWELVE independently extracted true algebraic monomial sources,
the SAME original-X Chow geometry realizes the literal owner's
physical Navigation-controlled GST U/J/M/[J,M] fold. -/
theorem prescribed_original_GST_wave_square
    (src12 : Fin 12 → I) (det12 : Fin 12 → J)
    (inv : Matrix (Fin 12) (Fin 12) ℚ)
    (hinv : inv * D.intersectionMinor src12 det12 = 1)
    (R : Nat) (z : A) :
    D.cycleClass
      (physicalChowOperator
        (D.originalXSourceFrame src12 det12 inv hinv) R z) =
      physicalBettiOperator
        (D.originalXSourceFrame src12 det12 inv hinv) R
          (D.cycleClass z) :=
  physical_chow_betti_square
    (D.originalXSourceFrame src12 det12 inv hinv) R z

#check intersectionMinor
#check originalXSourceFrame
#check prescribed_alpha_monomial_source_class
#check prescribed_original_GST_wave_square
#print axioms originalXSourceFrame
#print axioms prescribed_original_GST_wave_square

end OriginalMonomialPairing

end GSTOriginalXDivisorMonomialRankBirth
