import GSTClassicalHodgeAugmentedTargetWindow

/-!
# GST CLASSICAL HODGE — AUGMENTED TARGET MATRIX UNITS

A nonzero Hodge class has finite support, but a desired target basis direction
need not already be live.  The augmented-target window adjoins that target to
the exact finite support.  The total GST matrix-unit word then transports one
chosen live source coefficient to that arbitrary target.  After denominator
normalization and genuine-basis readback this is exactly the unrestricted
rank-free Hodge matrix unit.

Thus arbitrary-target matrix units are not postulated at the limitless level:
they are finite GST calculations on the support-plus-target observation.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeLocalCyclicCriterion
open GSTClassicalHodgeFiniteSupportArsenalConjugation
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeAugmentedTargetWindow
open GSTClassicalHodgeTotalSheetMatrixUnit

namespace GSTClassicalHodgeAugmentedTargetMatrixUnit

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Reading the exact total GST transfer from one live source to the adjoined
arbitrary target gives precisely the source integral coefficient times that
target Hodge basis vector. -/
theorem readAugmentedSquare_totalMatrixUnit
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p)
    (i : HodgeSupportIndex alpha) :
    readAugmentedSquare alpha j
      (totalSheetMatrixUnit
        (liveSourceSlot alpha j i)
        (targetSlot alpha j)
        (augmentedIntegralSquare alpha j).world) =
      ((augmentedIntegralSquare alpha j).world
        (liveSourceSlot alpha j i, liveSourceSlot alpha j i) : ℚ) •
        classicalHodgeBasis V H p j := by
  rw [totalSheetMatrixUnit_exact
    (liveSourceSlot alpha j i)
    (targetSlot alpha j)
    (augmentedIntegralSquare alpha j).world
    (augmentedIntegralSquare alpha j).world_pure]
  exact readAugmentedSquare_target alpha j _

/-- Normalize the finite GST transfer by the denominator-clearing scale. -/
noncomputable def augmentedConcreteHodgeMatrixUnit
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p)
    (i : HodgeSupportIndex alpha) :
    ClassicalHodgeFiber V H p :=
  ((augmentedIntegralSquare alpha j).scale : ℚ)⁻¹ •
    readAugmentedSquare alpha j
      (totalSheetMatrixUnit
        (liveSourceSlot alpha j i)
        (targetSlot alpha j)
        (augmentedIntegralSquare alpha j).world)

/-- **ARBITRARY-TARGET GST CONJUGATION.**  The normalized support-plus-target
GST word is exactly the unrestricted rank-free matrix unit from the chosen
live source basis direction to the arbitrary requested target direction. -/
theorem augmentedConcreteHodgeMatrixUnit_eq
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p)
    (i : HodgeSupportIndex alpha) :
    augmentedConcreteHodgeMatrixUnit alpha j i =
      hodgeMatrixUnit i.1 j alpha := by
  unfold augmentedConcreteHodgeMatrixUnit
  rw [readAugmentedSquare_totalMatrixUnit]
  rw [augmentedIntegralSquare_diagonal]
  rw [augmentedCoordinate_liveSource]
  have hscale : ((augmentedIntegralSquare alpha j).scale : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (augmentedIntegralSquare alpha j).scale_pos
  rw [smul_smul]
  simp [hscale]
  unfold hodgeCoordinate
  rfl

/-- Every nonzero Hodge class admits a live source whose concrete augmented
GST word reaches any prescribed target with a nonzero coefficient. -/
theorem exists_nonzero_augmented_target_transport
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (j : ClassicalHodgeBasisIndex V H p) :
    ∃ i : HodgeSupportIndex alpha,
      augmentedConcreteHodgeMatrixUnit alpha j i =
        hodgeMatrixUnit i.1 j alpha ∧
      hodgeCoordinate i.1 alpha ≠ 0 := by
  obtain ⟨k, hk⟩ := exists_nonzero_hodgeCoordinate halpha
  have hmem : k ∈ ((classicalHodgeBasis V H p).repr alpha).support := by
    apply Finsupp.mem_support_iff.mpr
    simpa [hodgeCoordinate] using hk
  let i : HodgeSupportIndex alpha := ⟨k, hmem⟩
  refine ⟨i, augmentedConcreteHodgeMatrixUnit_eq alpha j i, ?_⟩
  simpa [i] using hk

/-- Consequently the concrete augmented GST transport itself is nonzero for
one live source and every requested target. -/
theorem exists_nonzero_augmentedConcreteHodgeMatrixUnit
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (j : ClassicalHodgeBasisIndex V H p) :
    ∃ i : HodgeSupportIndex alpha,
      augmentedConcreteHodgeMatrixUnit alpha j i ≠ 0 := by
  obtain ⟨i, hiEq, hi⟩ :=
    exists_nonzero_augmented_target_transport alpha halpha j
  refine ⟨i, ?_⟩
  rw [hiEq, hodgeMatrixUnit_apply]
  exact smul_ne_zero hi (by
    exact (classicalHodgeBasis V H p).ne_zero j)

#check readAugmentedSquare_totalMatrixUnit
#check augmentedConcreteHodgeMatrixUnit
#check augmentedConcreteHodgeMatrixUnit_eq
#check exists_nonzero_augmented_target_transport
#check exists_nonzero_augmentedConcreteHodgeMatrixUnit

#print axioms augmentedConcreteHodgeMatrixUnit_eq
#print axioms exists_nonzero_augmented_target_transport
#print axioms exists_nonzero_augmentedConcreteHodgeMatrixUnit

end GSTClassicalHodgeAugmentedTargetMatrixUnit
