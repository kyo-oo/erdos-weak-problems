import GSTFinalResidualBinaryBoundaryBridge
import GSTGraphV2ProductionLaws

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2HandwrittenOmegaUBlock
open GSTGraphV2ProductionLaws
open GSTInfiniteV2
open GSTGraphV2HandwrittenExponentialLTE

namespace GSTFinalResidualCollision

/-- The literal binary columns of one arithmetic row form the infinite bridge
path consumed by the already-green BIG-N theorems. -/
theorem physical_binary_path (R p : Nat) :
    GSTInfiniteBridgePathS
      (fun r => GSTPhysicalKernel.binaryColumnCarry R p r)
      (fun r => GSTPhysicalKernel.binaryColumnDigit R p r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    exact GSTPhysicalKernel.binaryColumnCarry_lt_two R p r
  · intro r
    exact GSTPhysicalKernel.binaryColumnDigit_lt_three R p r
  · intro r
    exact GSTPhysicalKernel.microOutput_eq_next_binaryColumnDigit R p r

/-- Production compositor for the sole unbounded residual family.

The proof surface is deliberately narrow: all geometry, controller transport,
earliest-gate extraction and binary/right-boundary identification are consumed
from already kernel-checked green modules. -/
theorem residual_level_one_origin_one_collision
    (k m q : Nat) (hk : 1 ≤ k) (hm : 1 ≤ m) (hm1 : m % 3 = 1)
    (hChild : HappyCell
      (graph (GSTGraphV2Production.residualEnergy 1 k m) 0 (k+2+q)).seven.carry
      (graph (GSTGraphV2Production.residualEnergy 1 k m) 0 (k+2+q)).seven.digit)
    (hRightBad : ∀ j, ¬ HappyCell
      (graph (GSTGraphV2Production.residualEnergy 1 k m) 3 (k+2+j)).seven.carry
      (graph (GSTGraphV2Production.residualEnergy 1 k m) 3 (k+2+j)).seven.digit) :
    False := by
  let E := GSTGraphV2Production.residualEnergy 1 k m
  let b := k + 2
  let T := E / 3^b

  have hb : 3 ≤ b := by
    dsimp [b]
    omega

  have hmod : E % 3^b = 1 := by
    have h := pow4_scaled_mod_next (k+1) m
    simpa [E, b, GSTGraphV2Production.residualEnergy,
      GSTGraphV2HandwrittenOmegaUBlock.residualEnergy,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

  have hEdecomp : E = 1 + 3^b*T := by
    have hsplit := Nat.mod_add_div E (3^b)
    dsimp [T]
    rw [hmod] at hsplit
    omega

  have hBaseCarryZero : (graph E 0 b).seven.carry = 0 := by
    have hc : carry4 E b = 0 := by
      unfold carry4
      rw [hmod]
      apply Nat.div_eq_of_lt
      have hb9 : 9 ≤ 3^b := by
        rw [show (9 : Nat) = 3^2 by decide]
        exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
      omega
    simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hc

  have hChild' : HappyCell
      (graph E 0 (b+q)).seven.carry
      (graph E 0 (b+q)).seven.digit := by
    simpa [E, b, Nat.add_assoc] using hChild

  have hRightBad' : ∀ j, ¬ HappyCell
      (graph E 3 (b+j)).seven.carry
      (graph E 3 (b+j)).seven.digit := by
    intro j
    simpa [E, b, Nat.add_assoc] using hRightBad j

  obtain ⟨q0, hNull | hPlus⟩ :=
    GSTFinalResidualEarliestGateBridge.graph_exposed_tail_first_seedzero_chord
      E 3 b q hBaseCarryZero hChild'

  · have hFirstTail : GSTFirstBig1AtS
        (fun r => GSTPhysicalKernel.binaryColumnDigit T q0 r) 1 := by
      simpa [T] using hNull.2.2
    have hFirstFull0 :=
      GSTFinalResidualBinaryBoundaryBridge.prefixed_first_big1_transfer_le_three
        T b q0 1 hb (by decide) hFirstTail
    have hFirstFull : GSTFirstBig1AtS
        (fun r => GSTPhysicalKernel.binaryColumnDigit E (b+q0) r) 1 := by
      rw [← hEdecomp] at hFirstFull0
      exact hFirstFull0
    have hD0 : GSTPhysicalKernel.binaryColumnDigit E (b+q0) 0 = 2 := by
      rw [hEdecomp]
      calc
        GSTPhysicalKernel.binaryColumnDigit (1 + 3^b*T) (b+q0) 0 =
            GSTPhysicalKernel.binaryColumnDigit T q0 0 :=
          GSTFinalResidualBinaryBoundaryBridge.prefixed_binary_column_digit_exact
            T b q0 0 (by
              have h27 : 27 ≤ 3^b := by
                rw [show (27 : Nat) = 3^3 by decide]
                exact Nat.pow_le_pow_of_le (by decide : 1 < 3) hb
              norm_num
              omega)
        _ = 2 := by
          simpa [GSTPhysicalKernel.binaryColumnDigit, GSTInfiniteV2.gstDigitS]
            using hNull.1
    have hPath := physical_binary_path E (b+q0)
    have hBoundary := GSTInfiniteV2.gst_first_big1_boundary_is_destroyS
      (fun r => GSTPhysicalKernel.binaryColumnCarry E (b+q0) r)
      (fun r => GSTPhysicalKernel.binaryColumnDigit E (b+q0) r)
      hPath (by omega) 1 (by decide) hFirstFull
    have hNoRightChord :
        ¬ (GSTPhysicalKernel.binaryColumnDigit E (b+q0) 6 = 2 ∧
           GSTPhysicalKernel.binaryColumnDigit E (b+q0) 8 = 2) :=
      (GSTFinalResidualBinaryBoundaryBridge.level_one_right_bad_iff_no_binary_6_8
        E (b+q0)).1 (hRightBad' q0)
    trace_state
    omega

  · have hFirstTail : GSTFirstBig1AtS
        (fun r => GSTPhysicalKernel.binaryColumnDigit T q0 r) 3 := by
      simpa [T] using hPlus.2.2
    have hFirstFull0 :=
      GSTFinalResidualBinaryBoundaryBridge.prefixed_first_big1_transfer_le_three
        T b q0 3 hb (by decide) hFirstTail
    have hFirstFull : GSTFirstBig1AtS
        (fun r => GSTPhysicalKernel.binaryColumnDigit E (b+q0) r) 3 := by
      rw [← hEdecomp] at hFirstFull0
      exact hFirstFull0
    have hD0 : GSTPhysicalKernel.binaryColumnDigit E (b+q0) 0 = 2 := by
      rw [hEdecomp]
      calc
        GSTPhysicalKernel.binaryColumnDigit (1 + 3^b*T) (b+q0) 0 =
            GSTPhysicalKernel.binaryColumnDigit T q0 0 :=
          GSTFinalResidualBinaryBoundaryBridge.prefixed_binary_column_digit_exact
            T b q0 0 (by
              have h27 : 27 ≤ 3^b := by
                rw [show (27 : Nat) = 3^3 by decide]
                exact Nat.pow_le_pow_of_le (by decide : 1 < 3) hb
              norm_num
              omega)
        _ = 2 := by
          simpa [GSTPhysicalKernel.binaryColumnDigit, GSTInfiniteV2.gstDigitS]
            using hPlus.1
    have hPath := physical_binary_path E (b+q0)
    have hSurvive0 := GSTInfiniteV2.gst_before_first_big1_edges_surviveS
      (fun r => GSTPhysicalKernel.binaryColumnCarry E (b+q0) r)
      (fun r => GSTPhysicalKernel.binaryColumnDigit E (b+q0) r)
      hPath (by omega) 3 (by decide) hFirstFull 0 (by decide)
    have hSurvive1 := GSTInfiniteV2.gst_before_first_big1_edges_surviveS
      (fun r => GSTPhysicalKernel.binaryColumnCarry E (b+q0) r)
      (fun r => GSTPhysicalKernel.binaryColumnDigit E (b+q0) r)
      hPath (by omega) 3 (by decide) hFirstFull 1 (by decide)
    have hBoundary := GSTInfiniteV2.gst_first_big1_boundary_is_destroyS
      (fun r => GSTPhysicalKernel.binaryColumnCarry E (b+q0) r)
      (fun r => GSTPhysicalKernel.binaryColumnDigit E (b+q0) r)
      hPath (by omega) 3 (by decide) hFirstFull
    have hNoRightChord :
        ¬ (GSTPhysicalKernel.binaryColumnDigit E (b+q0) 6 = 2 ∧
           GSTPhysicalKernel.binaryColumnDigit E (b+q0) 8 = 2) :=
      (GSTFinalResidualBinaryBoundaryBridge.level_one_right_bad_iff_no_binary_6_8
        E (b+q0)).1 (hRightBad' q0)
    trace_state
    omega

end GSTFinalResidualCollision
