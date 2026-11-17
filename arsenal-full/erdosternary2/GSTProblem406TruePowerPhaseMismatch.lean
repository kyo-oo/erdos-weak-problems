import GSTGraphV2PerfectPowerBlockProbe
import GSTGraphV2UnifiedVerticalTelescope
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Why local U-positivity alone cannot close the pure-power 3-step collision

This is an EXACT, ORIGINAL FOUR-POWER experiment, not a synthetic source.
At K=8, the child 4^8 has a Happy cell at p=4, and 4^11 has
NO Happy cells at rows p=3 or 4, yet:
  child phase prefix at b=3, H=2 = +2,
  parent phase prefix at b=3, H=2 = -4,
  exact unified U derivative at p=4 = +518.

All of these are direct consequences of the actual GST graph.
They are CONSISTENT. Therefore local source phase>0, local
right phase<=0, and positive GST U derivative do not contradict
each other, even on literal 4^K. The right parent later has a
real Happy at p=10, so this does not refute the full theorem.
-/

namespace GSTProblem406TruePowerPhaseMismatch

open GSTCanonicalSevenAxisBridge
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2UnifiedPowerRectangle
open GSTGraphV2CoupledUFlux

/-- Every observation is the literal canonical physical 4^8→4^11
rectangle. No hypotheses, no axioms, no samples of other K. -/
theorem k8_exact_phase_mismatch_and_u_defect :
    HappyCell
      (graph (4^8) 0 4).seven.carry
      (graph (4^8) 0 4).seven.digit ∧
    (∀ j : Fin 2, ¬ HappyCell
      (graph (4^8) 3 (3+j.val)).seven.carry
      (graph (4^8) 3 (3+j.val)).seven.digit) ∧
    graphPhaseWindow (4^8) 0 3 2 = 2 ∧
    graphPhaseWindow (4^8) 3 3 2 = -4 ∧
    3*potentialWith gstUChargeExact (4^3)
      (unifiedState (4^8) 3 5).core -
    potentialWith gstUChargeExact (4^3)
      (unifiedState (4^8) 3 4).core = 518 := by
  unfold HappyCell
  decide

/-- Falsifies the tempting but mathematically invalid *local*
physical phase comparison used to turn a negative parent into a
contradiction. An all-depth assertion requires additional,
nonlocal, genuinely source-specific arithmetic information. -/
theorem no_universal_local_pure_power_phase_monotonicity :
    ¬ (∀ (K q : Nat),
        HappyCell
          (graph (4^K) 0 (3+q)).seven.carry
          (graph (4^K) 0 (3+q)).seven.digit →
        (∀ j : Nat, j < q+1 → ¬ HappyCell
          (graph (4^K) 3 (3+j)).seven.carry
          (graph (4^K) 3 (3+j)).seven.digit) →
        graphPhaseWindow (4^K) 0 3 (q+1) ≤
          graphPhaseWindow (4^K) 3 3 (q+1)) := by
  intro h
  have data := k8_exact_phase_mismatch_and_u_defect
  have hr : ∀ j : Nat, j < 1+1 → ¬ HappyCell
      (graph (4^8) 3 (3+j)).seven.carry
      (graph (4^8) 3 (3+j)).seven.digit := by
    intro j hj
    exact data.2.1 ⟨j, by omega⟩
  have hbound := h 8 1 (by simpa using data.1) hr
  change graphPhaseWindow (4^8) 0 3 2 ≤
    graphPhaseWindow (4^8) 3 3 2 at hbound
  have hl : graphPhaseWindow (4^8) 0 3 2 = 2 := data.2.2.1
  have hx : graphPhaseWindow (4^8) 3 3 2 = -4 := data.2.2.2.1
  rw [hl, hx] at hbound
  omega

#print axioms k8_exact_phase_mismatch_and_u_defect
#print axioms no_universal_local_pure_power_phase_monotonicity

end GSTProblem406TruePowerPhaseMismatch
