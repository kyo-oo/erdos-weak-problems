import GSTGraphV2PerfectPowerBlockProbe
import GSTGraphV2UnifiedVerticalTelescope
import GSTFinalPurePowerResidueTransplant

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2PowerThreeWaveObservation

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTGraphV2CoupledUFlux
open GSTGraphV2InfiniteControl
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2UnifiedPowerRectangle
open GSTGraphV2UnifiedVerticalTelescope
open GSTFinalPurePowerResidueTransplant
open GSTU2DEventTransport

/-- Exact Graph-V2 observation produced by a Happy cell on a power sheet and
an all-depth bad boundary three x4 waves to its right.  The information is not
discarded or turned into a one-step contradiction: it reappears as a strictly
positive coupled-U derivative while the exact width-three strip equation and
both phase signs remain live. -/
theorem power_three_wave_observation
    (K q : Nat)
    (hChild : HappyCell
      (graph (4^K) 0 (3+q)).seven.carry
      (graph (4^K) 0 (3+q)).seven.digit)
    (hRightBad : ∀ j, ¬ HappyCell
      (graph (4^K) 3 (3+j)).seven.carry
      (graph (4^K) 3 (3+j)).seven.digit) :
    0 < graphPhaseWindow (4^K) 0 3 (q+1) ∧
      graphPhaseWindow (4^K) 3 3 (q+1) ≤ 0 ∧
      64 * (graph (4^K) 0 (3+q)).seven.digit +
          wideCarry 64 (4^K) (3+q) =
        (graph (4^K) 3 (3+q)).seven.digit +
          3 * wideCarry 64 (4^K) ((3+q)+1) ∧
      0 <
        3 * potentialWith gstUChargeExact (4^3)
            (unifiedState (4^K) 3 ((3+q)+1)).core -
          potentialWith gstUChargeExact (4^3)
            (unifiedState (4^K) 3 (3+q)).core := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply graph_phase_window_positive_of_happy
    simpa [Nat.add_assoc] using hChild
  · apply graph_phase_window_nonpositive_of_bad
    intro j hj
    simpa [Nat.add_assoc] using hRightBad j
  · have h := exactPowerRectangle_conservation 1 2 K q
    norm_num [graph, cell, GSTCanonicalSevenAxisBridge.vertex,
      Nat.add_assoc, Nat.pow_add] at h ⊢
    simpa [Nat.mul_comm] using h
  · have hEq := unified_equationIII_graph_closed (4^K) 3 (3+q)
    have hChildNeg :
        gstUJumpExact
          (graph (4^K) 0 (3+q)).seven.carry
          (graph (4^K) 0 (3+q)).seven.digit < 0 := by
      rcases hChild with ⟨hd2, h0 | h3⟩
      · rw [hd2, h0]
        norm_num [gstUJumpExact, jumpWith, gstUChargeExact,
          gstStepCarryExact]
      · rw [hd2, h3]
        norm_num [gstUJumpExact, jumpWith, gstUChargeExact,
          gstStepCarryExact]
    have hRightNonneg :
        0 ≤ gstUJumpExact
          (graph (4^K) 3 (3+q)).seven.carry
          (graph (4^K) 3 (3+q)).seven.digit := by
      have hC := graph_carry_lt_four (4^K) 3 (3+q)
      have hd := graph_digit_lt_three (4^K) 3 (3+q)
      have hbad := hRightBad q
      have hCc : (graph (4^K) 3 (3+q)).seven.carry = 0 ∨
          (graph (4^K) 3 (3+q)).seven.carry = 1 ∨
          (graph (4^K) 3 (3+q)).seven.carry = 2 ∨
          (graph (4^K) 3 (3+q)).seven.carry = 3 := by omega
      have hdc : (graph (4^K) 3 (3+q)).seven.digit = 0 ∨
          (graph (4^K) 3 (3+q)).seven.digit = 1 ∨
          (graph (4^K) 3 (3+q)).seven.digit = 2 := by omega
      rcases hCc with hC0 | hC1 | hC2 | hC3
      · rcases hdc with hd0 | hd1 | hd2
        · rw [hC0, hd0]
          norm_num [gstUJumpExact, jumpWith, gstUChargeExact,
            gstStepCarryExact]
        · rw [hC0, hd1]
          norm_num [gstUJumpExact, jumpWith, gstUChargeExact,
            gstStepCarryExact]
        · exfalso
          apply hbad
          exact ⟨hd2, Or.inl hC0⟩
      · rcases hdc with hd0 | hd1 | hd2
        · rw [hC1, hd0]
          norm_num [gstUJumpExact, jumpWith, gstUChargeExact,
            gstStepCarryExact]
        · rw [hC1, hd1]
          norm_num [gstUJumpExact, jumpWith, gstUChargeExact,
            gstStepCarryExact]
        · rw [hC1, hd2]
          norm_num [gstUJumpExact, jumpWith, gstUChargeExact,
            gstStepCarryExact]
      · rcases hdc with hd0 | hd1 | hd2
        · rw [hC2, hd0]
          norm_num [gstUJumpExact, jumpWith, gstUChargeExact,
            gstStepCarryExact]
        · rw [hC2, hd1]
          norm_num [gstUJumpExact, jumpWith, gstUChargeExact,
            gstStepCarryExact]
        · rw [hC2, hd2]
          norm_num [gstUJumpExact, jumpWith, gstUChargeExact,
            gstStepCarryExact]
      · rcases hdc with hd0 | hd1 | hd2
        · rw [hC3, hd0]
          norm_num [gstUJumpExact, jumpWith, gstUChargeExact,
            gstStepCarryExact]
        · rw [hC3, hd1]
          norm_num [gstUJumpExact, jumpWith, gstUChargeExact,
            gstStepCarryExact]
        · exfalso
          apply hbad
          exact ⟨hd2, Or.inr hC3⟩
    rw [← hEq]
    norm_num
    nlinarith

#check power_three_wave_observation
#print axioms power_three_wave_observation

end GSTGraphV2PowerThreeWaveObservation
