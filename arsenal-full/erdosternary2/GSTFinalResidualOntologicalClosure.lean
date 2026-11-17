import GSTGraphV2ProductionLaws
import GSTU2DSharpCrossingBlock
import GSTGraphV2PerfectPowerBlockProbe
import GSTGraphV2InfiniteControllerBridge
import GSTGraphV2PhysicalSignedKernelTelescopeScratch
import GSTCanonicalFirstGateStandalone

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2HandwrittenOmegaUBlock
open GSTGraphV2HandwrittenExponentialCascade
open GSTGraphV2HandwrittenExponentialLTE
open GSTGraphV2HandwrittenAnchoredCocycle
open GSTGraphV2ProductionLaws
open GSTU2DCanonicalPhaseDensity
open GSTU2DPureDivergence83
open GSTU2DExactCrossingCharge

namespace GSTFinalResidualOntologicalClosure

/-- The recursive 8×3 observation prefix is exactly its literal weighted sum. -/
theorem weightedRectanglePrefix83_eq_sum
    (C d : Nat → Nat → Nat) (N K : Nat) :
    weightedRectanglePrefix83 C d N K =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          reverseDensity83 (fun t => C t p) (fun t => d t p) N) := by
  induction K with
  | zero => simp [weightedRectanglePrefix83]
  | succ K ih =>
      rw [weightedRectanglePrefix83, Finset.sum_range_succ, ih]

/-- The recursive sharp crossing prefix is exactly its literal weighted sum. -/
theorem weightedCrossPrefix_eq_sum
    (C d : Nat → Nat → Nat) (N K : Nat) :
    GSTU2DExactCrossingCharge.weightedCrossPrefix C d N K =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          GSTU2DExactCrossingCharge.reverseCrossCode
            (fun t => C t p) (fun t => d t p) N) := by
  induction K with
  | zero => simp [GSTU2DExactCrossingCharge.weightedCrossPrefix]
  | succ K ih =>
      rw [GSTU2DExactCrossingCharge.weightedCrossPrefix,
        Finset.sum_range_succ, ih]

/-- Final hard-family Graph-V2 collision.  This is the only mathematical seam:
level one, origin trit one, one Happy child gate, and an allegedly all-bad
width-three parent boundary. -/
theorem residual_level_one_origin_one_ontological
    (k m q : Nat) (hk : 1 ≤ k) (hm : 1 ≤ m) (hm1 : m % 3 = 1)
    (hChild : HappyCell
      (GSTGraphV2InfiniteControl.graph
        (GSTGraphV2Production.residualEnergy 1 k m) 0 (k+2+q)).seven.carry
      (GSTGraphV2InfiniteControl.graph
        (GSTGraphV2Production.residualEnergy 1 k m) 0 (k+2+q)).seven.digit)
    (hRightBad : ∀ j, ¬ HappyCell
      (GSTGraphV2InfiniteControl.graph
        (GSTGraphV2Production.residualEnergy 1 k m) 3 (k+2+j)).seven.carry
      (GSTGraphV2InfiniteControl.graph
        (GSTGraphV2Production.residualEnergy 1 k m) 3 (k+2+j)).seven.digit) :
    False := by
  let E := GSTGraphV2Production.residualEnergy 1 k m
  let b := k + 2

  have hBaseCarryZero :
      (GSTGraphV2InfiniteControl.graph E 0 b).seven.carry = 0 := by
    have hmod : E % 3^b = 1 := by
      have h := pow4_scaled_mod_next (k+1) m
      simpa [E, b, GSTGraphV2Production.residualEnergy,
        GSTGraphV2HandwrittenOmegaUBlock.residualEnergy,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have hc : carry4 E b = 0 := by
      unfold carry4
      rw [hmod]
      apply Nat.div_eq_of_lt
      have hb9 : 9 ≤ 3^b := by
        rw [show (9 : Nat) = 3^2 by decide]
        exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by dsimp [b]; omega)
      omega
    simpa [GSTGraphV2InfiniteControl.graph,
      GSTGraphV2InfiniteControl.cell,
      GSTCanonicalSevenAxisBridge.vertex] using hc

  have hOriginTrit : originTrit m = 1 := by
    simpa [originTrit] using hm1

  have hOriginFactor :
      E = 4^(3^(k+1)) * 4^(3^(k+2) * originTail m) := by
    have h := residual_energy_u_mul_div_exact 1 k m
    rw [hOriginTrit] at h
    simpa [E, GSTGraphV2Production.residualEnergy,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

  have hOriginStep :=
    residual_level_one_origin_one_energy_step k m (b+q) hm1

  have hController :
      GSTV2.InfiniteBadCoupledControl
        (4^3)
        (GSTGraphV2InfiniteControllerBridge.graphCoupledState E 3 b) := by
    apply GSTGraphV2InfiniteControllerBridge.graph_infinite_bad_control
      E 3 b hBaseCarryZero
    intro j
    simpa [E, b, Nat.add_assoc] using hRightBad j

  have hLatent :
      GSTV2.LatentGateTransfer
        (4^3)
        (GSTGraphV2InfiniteControllerBridge.graphCoupledState E 3 b) q := by
    apply GSTGraphV2InfiniteControllerBridge.graph_child_happy_latent_transfer
      E 3 b q hBaseCarryZero
    · intro j
      simpa [E, b, Nat.add_assoc] using hRightBad j
    · simpa [E, b, Nat.add_assoc] using hChild

  have hLatentNextCarry :
      (GSTV2.coupledOrbit (4^3)
          (GSTGraphV2InfiniteControllerBridge.graphCoupledState E 3 b)
          (q+1)).childCarry = 2 ∨
      (GSTV2.coupledOrbit (4^3)
          (GSTGraphV2InfiniteControllerBridge.graphCoupledState E 3 b)
          (q+1)).childCarry = 3 :=
    hLatent.nextCarryTwoOrThree

  have hLatentNextNonzero :
      (GSTV2.coupledOrbit (4^3)
          (GSTGraphV2InfiniteControllerBridge.graphCoupledState E 3 b)
          (q+1)).childCarry ≠ 0 :=
    hLatent.nextCarryNonzero

  have hGateNeutral :=
    residual_gate_neutral_tail 1 k m q (by decide) hk
  have hGateLeftPhased :=
    residual_gate_left_is_phased_tail 1 k m q

  have hPhaseLeftPositive :
      0 < GSTGraphV2PerfectPowerBlock.graphPhaseWindow E 0 b (q+1) := by
    apply GSTGraphV2PerfectPowerBlock.graph_phase_window_positive_of_happy
    simpa [E, b, Nat.add_assoc] using hChild

  have hPhaseRightNonpositive :
      GSTGraphV2PerfectPowerBlock.graphPhaseWindow E 3 b (q+1) ≤ 0 := by
    apply GSTGraphV2PerfectPowerBlock.graph_phase_window_nonpositive_of_bad
    intro j hj
    simpa [E, b, Nat.add_assoc] using hRightBad j

  have hPhaseLeftExact :=
    GSTGraphV2PerfectPowerBlock.graph_phase_window_exact E 0 b (q+1)
  have hPhaseRightExact :=
    GSTGraphV2PerfectPowerBlock.graph_phase_window_exact E 3 b (q+1)
  have hPhaseLeftBoundary :=
    GSTGraphV2PerfectPowerBlock.graph_phase_digit_window_boundary_exact E 0 b (q+1)
  have hPhaseRightBoundary :=
    GSTGraphV2PerfectPowerBlock.graph_phase_digit_window_boundary_exact E 3 b (q+1)

  have hPositive83 :
      0 < weightedRectanglePrefix83
        (fun t p => (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.carry)
        (fun t p => (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.digit)
        3 (q+1) := by
    apply weightedRectanglePrefix83_positive_of_top_leading_happy
    · decide
    · intro t p ht hp
      exact graph_carry_lt_four E t (b+p)
    · intro t p ht hp
      exact graph_digit_lt_three E t (b+p)
    · simpa [E, b, Nat.add_assoc] using hChild

  have hPositive83Sum :
      0 < Finset.sum (Finset.range (q+1)) (fun p =>
        (((3^p : Nat) : Int)) *
          reverseDensity83
            (fun t => (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.carry)
            (fun t => (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.digit) 3) := by
    rw [← weightedRectanglePrefix83_eq_sum]
    exact hPositive83

  have hExact83 := density83_rectangle_exact
    (fun t p => (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.carry)
    (fun t p => (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.digit)
    3 (q+1)
    (by
      intro t p ht hp
      exact ⟨graph_carry_lt_four E t (b+p),
        graph_digit_lt_three E t (b+p),
        (graph_cell_exact E t (b+p)).1,
        by simpa [Nat.add_assoc] using (graph_cell_exact E t (b+p)).2⟩)

  have hCrossPositive :
      0 < GSTU2DExactCrossingCharge.weightedCrossPrefix
        (fun t p => (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.carry)
        (fun t p => (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.digit)
        3 (q+1) := by
    apply GSTU2DExactCrossingCharge.weightedCrossPrefix_positive_of_top_leading_happy
    · decide
    · intro t p ht hp
      exact graph_carry_lt_four E t (b+p)
    · intro t p ht hp
      exact graph_digit_lt_three E t (b+p)
    · intro t p ht hp
      exact (graph_cell_exact E t (b+p)).1
    · simpa [E, b, Nat.add_assoc] using hChild

  have hCrossPositiveSum :
      0 < Finset.sum (Finset.range (q+1)) (fun p =>
        (((3^p : Nat) : Int)) *
          GSTU2DExactCrossingCharge.reverseCrossCode
            (fun t => (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.carry)
            (fun t => (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.digit) 3) := by
    rw [← weightedCrossPrefix_eq_sum]
    exact hCrossPositive

  have hCrossExact := GSTU2DExactCrossingCharge.reverseCrossRectangle_exact
    (fun t p => (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.carry)
    (fun t p => (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.digit)
    3 (q+1)
    (by
      intro t p ht hp
      exact ⟨graph_carry_lt_four E t (b+p),
        graph_digit_lt_three E t (b+p),
        (graph_cell_exact E t (b+p)).1,
        by simpa [Nat.add_assoc] using (graph_cell_exact E t (b+p)).2⟩)

  have hBinaryWidth : 2 * 3^1 = 6 := by decide

  have hChildOutputTwo :
      outDigit
        (GSTGraphV2InfiniteControl.graph E 0 (b+q)).seven.carry
        (GSTGraphV2InfiniteControl.graph E 0 (b+q)).seven.digit = 2 :=
    (happyCell_positive_and_preserves_big2 _ _ hChild).2

  have hGraphOneDigitTwo :
      (GSTGraphV2InfiniteControl.graph E 1 (b+q)).seven.digit = 2 := by
    have hstep := (graph_cell_exact E 0 (b+q)).1
    rw [← hstep]
    exact hChildOutputTwo

  have hPhysicalLeftChord :
      GSTPhysicalKernel.binaryColumnDigit E (b+q) 0 = 2 ∧
      GSTPhysicalKernel.binaryColumnDigit E (b+q) 2 = 2 := by
    constructor
    · simpa [GSTPhysicalKernel.binaryColumnDigit,
        GSTGraphV2InfiniteControl.graph, GSTGraphV2InfiniteControl.cell,
        GSTCanonicalSevenAxisBridge.vertex, GSTCanonicalSevenAxisBridge.digit3]
        using hChild.1
    · simpa [GSTPhysicalKernel.binaryColumnDigit,
        GSTGraphV2InfiniteControl.graph, GSTGraphV2InfiniteControl.cell,
        GSTCanonicalSevenAxisBridge.vertex, GSTCanonicalSevenAxisBridge.digit3]
        using hGraphOneDigitTwo

  have hPhysicalRightNoChord : ∀ j,
      ¬ (GSTPhysicalKernel.binaryColumnDigit E (b+j) 6 = 2 ∧
         GSTPhysicalKernel.binaryColumnDigit E (b+j) 8 = 2) := by
    intro j hpair
    have hd3 :
        (GSTGraphV2InfiniteControl.graph E 3 (b+j)).seven.digit = 2 := by
      simpa [GSTPhysicalKernel.binaryColumnDigit,
        GSTGraphV2InfiniteControl.graph, GSTGraphV2InfiniteControl.cell,
        GSTCanonicalSevenAxisBridge.vertex, GSTCanonicalSevenAxisBridge.digit3]
        using hpair.1
    have hd4 :
        (GSTGraphV2InfiniteControl.graph E 4 (b+j)).seven.digit = 2 := by
      simpa [GSTPhysicalKernel.binaryColumnDigit,
        GSTGraphV2InfiniteControl.graph, GSTGraphV2InfiniteControl.cell,
        GSTCanonicalSevenAxisBridge.vertex, GSTCanonicalSevenAxisBridge.digit3]
        using hpair.2
    have hout :
        outDigit
          (GSTGraphV2InfiniteControl.graph E 3 (b+j)).seven.carry
          (GSTGraphV2InfiniteControl.graph E 3 (b+j)).seven.digit = 2 := by
      have hstep := (graph_cell_exact E 3 (b+j)).1
      rw [hstep, hd4]
    have hout2 :
        outDigit
          (GSTGraphV2InfiniteControl.graph E 3 (b+j)).seven.carry 2 = 2 := by
      simpa [hd3] using hout
    have hevent :
        GSTCanonicalSevenAxisBridge.event
          (GSTGraphV2InfiniteControl.graph E 3 (b+j)).seven.carry
          (GSTGraphV2InfiniteControl.graph E 3 (b+j)).seven.digit = 8 := by
      simp [GSTCanonicalSevenAxisBridge.event, hd3, hout2]
    have hhappy : HappyCell
        (GSTGraphV2InfiniteControl.graph E 3 (b+j)).seven.carry
        (GSTGraphV2InfiniteControl.graph E 3 (b+j)).seven.digit :=
      (GSTCanonicalSevenAxisBridge.happy_iff_event_eight _ _
        (graph_carry_lt_four E 3 (b+j))
        (graph_digit_lt_three E 3 (b+j))).2 hevent
    have hbadj : ¬ HappyCell
        (GSTGraphV2InfiniteControl.graph E 3 (b+j)).seven.carry
        (GSTGraphV2InfiniteControl.graph E 3 (b+j)).seven.digit := by
      simpa [E, b, Nat.add_assoc] using hRightBad j
    exact hbadj hhappy

  trace_state
  omega

end GSTFinalResidualOntologicalClosure
