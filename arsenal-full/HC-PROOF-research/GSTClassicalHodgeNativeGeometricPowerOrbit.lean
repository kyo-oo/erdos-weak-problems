import GSTClassicalHodgeActualGeometricIdentityClosure
import GSTClassicalHodgeLimitlessSpinePropagation
import GSTClassicalHodgeGeometricMatrixRankLanding

/-!
# Finite polynomial orbit of ACTUAL GST geometric correspondences

This file constructs native algebraic cycles in arbitrary codimension and
arbitrary rational Hodge-fiber rank. It requires only:
(1) the existing genuine geometric cycle-class spine;
(2) one realized correspondence expression, built from finite closed geometry.

The native output is the explicit finite rational sum of genuine powers
of the operator applied to the already constructed projective spine cycle.
It never requests a cycle-class preimage of the target.

The full-rank result uses a separately checkable determinant of these
*constructed* cycles. We DO NOT assert that the determinant is nonzero for
every variety, or that one correspondence must generate the entire Hodge
fiber. In some varieties this construction may be highly degenerate.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 800000

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
open GSTClassicalHodgeGeometricCorrespondencePolynomialCalculus
open GSTClassicalHodgeActualGeometricIdentityClosure
open GSTClassicalHodgeGeometricMatrixRankLanding

namespace GSTClassicalHodgeNativeGeometricPowerOrbit

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The n-th ACTUAL native geometric correspondence image of the GST spine. -/
noncomputable def nativePowerOrbit
    (G : GeometricCycleClassSpine V H)
    (E : RealizedCorrespondenceExpr V H p)
    (n : Nat) : codimensionCycles V.X p :=
  (geometricPow E n).cycleOperator (spineNativeTower G p)

/-- The corresponding geometric Betti expression, with no arbitrary
cohomology endomorphism injected. -/
noncomputable def bettiPowerOrbit
    (G : GeometricCycleClassSpine V H)
    (E : RealizedCorrespondenceExpr V H p)
    (n : Nat) :
    RationalSingularCohomology H.analytification (2 * p) :=
  (geometricPow E n).cohomologyOperator (spineHodgeSeed G p).1

/-- The actual diagonal provides the degree-zero polynomial coefficient:
its action on native cycles is exactly the identity. -/
theorem nativePowerOrbit_zero
    (G : GeometricCycleClassSpine V H)
    (E : RealizedCorrespondenceExpr V H p) :
    nativePowerOrbit G E 0 = spineNativeTower G p := by
  change (diagonalExpr (V := V) (H := H) (p := p)).cycleOperator
    (spineNativeTower G p) = spineNativeTower G p
  rw [diagonalExpr_native_eq_id]
  rfl

/-- Higher orbit terms are built by actual ordered geometric composition. -/
theorem nativePowerOrbit_succ
    (G : GeometricCycleClassSpine V H)
    (E : RealizedCorrespondenceExpr V H p)
    (n : Nat) :
    nativePowerOrbit G E (n + 1) =
      E.cycleOperator (nativePowerOrbit G E n) := rfl

/-- Exact geometric Betti/nativity equality at EVERY natural power. -/
theorem nativePowerOrbit_cycleClass
    (G : GeometricCycleClassSpine V H)
    (E : RealizedCorrespondenceExpr V H p)
    (n : Nat) :
    H.cycleClass p (nativePowerOrbit G E n) =
      bettiPowerOrbit G E n := by
  unfold nativePowerOrbit bettiPowerOrbit
  rw [geometricPow_cycleClass_natural, spineNativeTower_cycleClass]

/-- An arbitrarily high-degree but FINITELY SUPPORTED rational polynomial
in a genuine realized correspondence, evaluated on an ACTUAL native cycle. -/
noncomputable def nativePolynomialOrbit
    (G : GeometricCycleClassSpine V H)
    (E : RealizedCorrespondenceExpr V H p)
    (coeff : Nat →₀ ℚ) : codimensionCycles V.X p :=
  coeff.sum (fun n q => q • nativePowerOrbit G E n)

/-- The independent Betti-side polynomial evaluation of the same
genuine correspondence, with the geometric spine as initial state. -/
noncomputable def bettiPolynomialOrbit
    (G : GeometricCycleClassSpine V H)
    (E : RealizedCorrespondenceExpr V H p)
    (coeff : Nat →₀ ℚ) :
    RationalSingularCohomology H.analytification (2 * p) :=
  coeff.sum (fun n q => q • bettiPowerOrbit G E n)

/-- The entire noncommutative geometric engine preserves the exact
native-cycle/Betti commuting square under arbitrary finite polynomial sums. -/
theorem nativePolynomialOrbit_cycleClass
    (G : GeometricCycleClassSpine V H)
    (E : RealizedCorrespondenceExpr V H p)
    (coeff : Nat →₀ ℚ) :
    H.cycleClass p (nativePolynomialOrbit G E coeff) =
      bettiPolynomialOrbit G E coeff := by
  simp only [nativePolynomialOrbit, bettiPolynomialOrbit, Finsupp.sum,
    map_sum, map_smul, nativePowerOrbit_cycleClass]

/-- This is genuine, unconditional (relative to the actual geometric
spine) algebraicity for every polynomial-generated Betti vector,
with the explicit native cycle on the left. -/
theorem bettiPolynomialOrbit_has_native_cycle
    (G : GeometricCycleClassSpine V H)
    (E : RealizedCorrespondenceExpr V H p)
    (coeff : Nat →₀ ℚ) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = bettiPolynomialOrbit G E coeff :=
  ⟨nativePolynomialOrbit G E coeff,
    nativePolynomialOrbit_cycleClass G E coeff⟩

/-- All newly constructed geometric polynomial classes have true Hodge type.
This needs no Hodge target-lifting hypothesis or rank assumption. -/
theorem bettiPolynomialOrbit_is_hodge
    (G : GeometricCycleClassSpine V H)
    (E : RealizedCorrespondenceExpr V H p)
    (coeff : Nat →₀ ℚ) :
    bettiPolynomialOrbit G E coeff ∈
      rationalHodgeSubspace (H.hodgeBigrading p) := by
  rw [← nativePolynomialOrbit_cycleClass G E coeff]
  exact G.algebraic_is_hodge p _

/-- In a finite Hodge fiber, form the concrete coordinate matrix of the
first finrank-many actual geometric iterates from ONE correspondence. -/
noncomputable def geometricPowerHodgeMatrix
    (G : GeometricCycleClassSpine V H)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (E : RealizedCorrespondenceExpr V H p) :
    Matrix
      (Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)))
      (Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p))) ℚ :=
  nativeHodgeMatrix G (fun j => nativePowerOrbit G E j.val)

/-- Construct the exact native algebraic representative by inverting the
matrix of *actually generated* powers. The only extra requirement is the
numerical nonvanishing of that particular geometric matrix, never a
per-target algebraic preimage or an abstract full Hodge generator. -/
theorem actual_power_matrix_native_cycle
    (G : GeometricCycleClassSpine V H)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (E : RealizedCorrespondenceExpr V H p)
    (hdet : (geometricPowerHodgeMatrix G E).det ≠ 0)
    (alpha : ClassicalHodgeFiber V H p) :
    H.cycleClass p
      (nativeCycleByMatrixInversion G
        (fun j => nativePowerOrbit G E j.val)
        (geometricPowerHodgeMatrix G E)⁻¹ alpha) = alpha.1 :=
  hodge_cycle_of_nonzero_geometric_determinant G
    (fun j => nativePowerOrbit G E j.val) hdet alpha

#check nativePowerOrbit
#check nativePowerOrbit_zero
#check nativePowerOrbit_cycleClass
#check nativePolynomialOrbit
#check nativePolynomialOrbit_cycleClass
#check bettiPolynomialOrbit_has_native_cycle
#check bettiPolynomialOrbit_is_hodge
#check actual_power_matrix_native_cycle

#print axioms nativePowerOrbit_cycleClass
#print axioms nativePolynomialOrbit_cycleClass
#print axioms actual_power_matrix_native_cycle

end GSTClassicalHodgeNativeGeometricPowerOrbit
