import GSTClassicalHodgeExplicitArsenalGeneration
import GSTClassicalHodgeUniversalTwoSlotNativeClosure

/-!
# GST CLASSICAL HODGE — TWO-SLOT LEFSCHETZ COLLAPSE

The general finite-window matrix-unit construction uses

  P_target ∘ L^(2 gap) ∘ P_source.

In the universal two-slot window there are only two pure diagonal states,
`sourceSlot = 0` and `targetSlot = 1`.  A two-step Lefschetz path can only move
from the first diagonal state to the second.  Therefore `L^2` itself already
has rank one: it is the central-binomial forward scalar times `E_01`.

This removes both spectral projectors from the least-bad Hodge attack.  The
only nontrivial GST primitive that must acquire classical native naturality is
the actual rationalized two-step world Lefschetz operator.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

namespace GSTClassicalHodgeTwoSlotLefschetzCollapse

open GSTWorldCosmology
open GSTTruncatedWorldCohomologyRing
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgeExplicitArsenalGeneration
open GSTClassicalHodgePrimitiveArsenalRationalization
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeUniversalTwoSlotNativeClosure

/-- In the two-slot pure diagonal, bare `L^2` is exactly the nonzero forward
scalar times the unique forward matrix unit. -/
theorem diagonalLefschetzQ_two_two_eq_scaled_matrixUnit :
    diagonalLefschetzQ 2 2 =
      (forwardScalar sourceSlot targetSlot : ℚ) •
        pureMatrixUnit sourceSlot targetSlot := by
  apply LinearMap.ext
  intro a
  rw [rationalPureWindow_eq_sum_basis a]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro r _
  fin_cases r
  · have hraw :
        diagonalLefschetzQ 2 2 (rationalPureBasis sourceSlot) =
          (forwardScalar sourceSlot targetSlot : ℚ) •
            rationalPureBasis targetSlot := by
      funext q
      fin_cases q
      · simp [diagonalLefschetzQ, rationalPureBasis, sourceSlot, targetSlot]
        exact_mod_cast GSTUniversalLefschetzCausalGeometry.positive_time_no_return
          (GSTGlobalPureHodgeCosmology.pureDiagonalState
            (Fin.castLE (show 2 ≤ min 2 2 by omega) sourceSlot)) (by norm_num)
      · simp [diagonalLefschetzQ, rationalPureBasis, sourceSlot, targetSlot]
        exact_mod_cast gst_forward_scalar_receipt sourceSlot targetSlot
          (by simp [sourceSlot, targetSlot])
    change a sourceSlot • diagonalLefschetzQ 2 2
      (rationalPureBasis sourceSlot) = _
    rw [hraw]
    simp [pureMatrixUnit_basis_source, smul_smul, mul_comm,
      rationalPureBasis, sourceSlot, targetSlot]
  · have hzero :
        diagonalLefschetzQ 2 2 (rationalPureBasis targetSlot) = 0 := by
      funext q
      fin_cases q
      · simp [diagonalLefschetzQ, rationalPureBasis, sourceSlot, targetSlot]
        exact_mod_cast GSTUniversalLefschetzKernel.worldAct_L_pow_basis_outside_future_zero
          (GSTGlobalPureHodgeCosmology.pureDiagonalState
            (Fin.castLE (show 2 ≤ min 2 2 by omega) targetSlot))
          (GSTGlobalPureHodgeCosmology.pureDiagonalState
            (Fin.castLE (show 2 ≤ min 2 2 by omega) sourceSlot))
          (by simp [GSTUniversalLefschetzKernel.worldForward,
            GSTGlobalPureHodgeCosmology.pureDiagonalState,
            GSTDimensionFreeHodgeDiagonal.diagonalState,
            sourceSlot, targetSlot])
      · simp [diagonalLefschetzQ, rationalPureBasis, sourceSlot, targetSlot]
        exact_mod_cast GSTUniversalLefschetzCausalGeometry.positive_time_no_return
          (GSTGlobalPureHodgeCosmology.pureDiagonalState
            (Fin.castLE (show 2 ≤ min 2 2 by omega) targetSlot)) (by norm_num)
    change a targetSlot • diagonalLefschetzQ 2 2
      (rationalPureBasis targetSlot) = _
    rw [hzero, smul_zero]
    simp [rationalPureBasis, sourceSlot, targetSlot]

/-- The forward scalar in the universal two-slot window is nonzero. -/
theorem twoSlot_forwardScalar_ne_zero :
    (forwardScalar sourceSlot targetSlot : ℚ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (forwardScalar_pos sourceSlot targetSlot))

/-- Lifted to any ordered pair of genuine Hodge basis directions, the bare
GST `L^2` primitive is already the same nonzero scalar times the rank-free
matrix unit. -/
theorem lifted_twoSlotLefschetz_eq_scaled_hodgeMatrixUnit
    {V : GSTProjectiveOverC.SmoothProjectiveComplexScheme}
    {H : GSTGeometricRealizationStage2G.HodgeBigradedBettiData V}
    {p : Nat}
    (i j : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeBasisIndex V H p) :
    GSTClassicalHodgeRankFreePrimitiveGeneration.liftFiniteHodgeOperator
        (pairBasisIndex i j) (diagonalLefschetzQ 2 2) =
      (forwardScalar sourceSlot targetSlot : ℚ) •
        GSTClassicalHodgeRankFreeArsenalIrreducibility.hodgeMatrixUnit i j := by
  rw [diagonalLefschetzQ_two_two_eq_scaled_matrixUnit]
  have hsmul : liftFiniteHodgeOperator (pairBasisIndex i j)
      ((forwardScalar sourceSlot targetSlot : ℚ) •
        pureMatrixUnit sourceSlot targetSlot) =
    (forwardScalar sourceSlot targetSlot : ℚ) •
      liftFiniteHodgeOperator (pairBasisIndex i j)
        (pureMatrixUnit sourceSlot targetSlot) := by
    apply LinearMap.ext
    intro x
    show (finiteHodgeWrite (pairBasisIndex i j))
        (((forwardScalar sourceSlot targetSlot : ℚ) •
          pureMatrixUnit sourceSlot targetSlot)
        (finiteHodgeRead (pairBasisIndex i j) x)) =
      (forwardScalar sourceSlot targetSlot : ℚ) •
        (finiteHodgeWrite (pairBasisIndex i j))
        (pureMatrixUnit sourceSlot targetSlot
          (finiteHodgeRead (pairBasisIndex i j) x))
    simp [LinearMap.smul_apply, LinearMap.map_smul]
  rw [hsmul, liftFiniteHodgeOperator_matrixUnit]
  simp only [pairBasisIndex_source, pairBasisIndex_target]

#check diagonalLefschetzQ_two_two_eq_scaled_matrixUnit
#check twoSlot_forwardScalar_ne_zero
#check lifted_twoSlotLefschetz_eq_scaled_hodgeMatrixUnit

#print axioms diagonalLefschetzQ_two_two_eq_scaled_matrixUnit
#print axioms lifted_twoSlotLefschetz_eq_scaled_hodgeMatrixUnit

end GSTClassicalHodgeTwoSlotLefschetzCollapse
