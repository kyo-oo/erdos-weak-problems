import GSTGraphV2InfiniteControllerBridge
import GSTCanonicalFirstGateStandalone

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTInfiniteV2

namespace GSTFinalResidualEarliestGateBridge

/-- Strong production-facing bridge.  Besides locating the earliest seed-zero
Happy gate on the exposed residual tail, retain the complete bad lower prefix
and the sharp carry-three residue bound.  These are the vertical boundary data
needed by the final all-depth compositor. -/
theorem graph_exposed_tail_first_seedzero_control
    (E N b q : Nat)
    (hBaseCarryZero : (graph E 0 b).seven.carry = 0)
    (hChild : HappyCell
      (graph E 0 (b+q)).seven.carry
      (graph E 0 (b+q)).seven.digit) :
    let T := E / 3^b
    ∃ q0,
      GSTInfiniteV2.gstDigitS T q0 = 2 ∧
      (GSTInfiniteV2.gstCarryS T q0 = 0 ∨
       GSTInfiniteV2.gstCarryS T q0 = 3) ∧
      (∀ j, j < q0 →
        GSTInfiniteV2.GSTBadPairS
          (GSTInfiniteV2.gstAffineCarryS 0 T j)
          (GSTInfiniteV2.gstDigitS T j)) ∧
      (GSTInfiniteV2.gstCarryS T q0 = 3 →
        8 * (T % 3^q0) < 7 * 3^q0) := by
  dsimp only
  let st := GSTGraphV2InfiniteControllerBridge.graphCoupledState E N b
  let T := E / 3^b

  have hC0 : st.childCarry = 0 := by
    simpa [st, GSTGraphV2InfiniteControllerBridge.graphCoupledState] using
      hBaseCarryZero

  have hChildController :
      GSTV2.Happy
        (GSTV2.coupledOrbit (4^N) st q).childCarry
        ((GSTV2.coupledOrbit (4^N) st q).childTail % 3) := by
    simpa [st] using
      GSTGraphV2InfiniteControllerBridge.graph_child_happy_to_controller
        E N b q hChild

  have hDigitExact :=
    GSTV2.coupledOrbit_childDigit_exact (4^N) st q
  have hCarryExact :=
    GSTV2.coupledOrbit_childCarry_exact (4^N) st hC0 q

  have hTailDigit : GSTInfiniteV2.gstDigitS T q = 2 := by
    have hD : GSTV2.digit st.childTail q = 2 :=
      hDigitExact.symm.trans hChildController.1
    simpa [T, st, GSTGraphV2InfiniteControllerBridge.graphCoupledState,
      GSTV2.digit, GSTInfiniteV2.gstDigitS] using hD

  have hTailCarry :
      GSTInfiniteV2.gstCarryS T q = 0 ∨
      GSTInfiniteV2.gstCarryS T q = 3 := by
    have hC :
        GSTV2.naturalCarry st.childTail q = 0 ∨
        GSTV2.naturalCarry st.childTail q = 3 := by
      rcases hChildController.2 with h0 | h3
      · exact Or.inl (hCarryExact.symm.trans h0)
      · exact Or.inr (hCarryExact.symm.trans h3)
    simpa [T, st, GSTGraphV2InfiniteControllerBridge.graphCoupledState,
      GSTV2.naturalCarry, GSTInfiniteV2.gstCarryS] using hC

  exact gpt56_first_seedzero_gate_u_control T
    ⟨q, hTailDigit, hTailCarry⟩

/-- A physical Happy cell above a genuine zero-carry cut is exactly a Happy
cell of the exposed seed-zero tail.  Taking the earliest such tail gate then
produces the kernelized short physical chord: NULL has first BIG1 at binary
column one, GST+ at binary column three. -/
theorem graph_exposed_tail_first_seedzero_chord
    (E N b q : Nat)
    (hBaseCarryZero : (graph E 0 b).seven.carry = 0)
    (hChild : HappyCell
      (graph E 0 (b+q)).seven.carry
      (graph E 0 (b+q)).seven.digit) :
    let T := E / 3^b
    ∃ q0,
      (GSTInfiniteV2.gstDigitS T q0 = 2 ∧
        GSTInfiniteV2.gstCarryS T q0 = 0 ∧
        GSTFirstBig1AtS
          (fun r => GSTPhysicalKernel.binaryColumnDigit T q0 r) 1) ∨
      (GSTInfiniteV2.gstDigitS T q0 = 2 ∧
        GSTInfiniteV2.gstCarryS T q0 = 3 ∧
        GSTFirstBig1AtS
          (fun r => GSTPhysicalKernel.binaryColumnDigit T q0 r) 3) := by
  dsimp only
  let st := GSTGraphV2InfiniteControllerBridge.graphCoupledState E N b
  let T := E / 3^b

  have hC0 : st.childCarry = 0 := by
    simpa [st, GSTGraphV2InfiniteControllerBridge.graphCoupledState] using
      hBaseCarryZero

  have hChildController :
      GSTV2.Happy
        (GSTV2.coupledOrbit (4^N) st q).childCarry
        ((GSTV2.coupledOrbit (4^N) st q).childTail % 3) := by
    simpa [st] using
      GSTGraphV2InfiniteControllerBridge.graph_child_happy_to_controller
        E N b q hChild

  have hDigitExact :=
    GSTV2.coupledOrbit_childDigit_exact (4^N) st q
  have hCarryExact :=
    GSTV2.coupledOrbit_childCarry_exact (4^N) st hC0 q

  have hTailDigit : GSTInfiniteV2.gstDigitS T q = 2 := by
    have hD : GSTV2.digit st.childTail q = 2 :=
      hDigitExact.symm.trans hChildController.1
    simpa [T, st, GSTGraphV2InfiniteControllerBridge.graphCoupledState,
      GSTV2.digit, GSTInfiniteV2.gstDigitS] using hD

  have hTailCarry :
      GSTInfiniteV2.gstCarryS T q = 0 ∨
      GSTInfiniteV2.gstCarryS T q = 3 := by
    have hC :
        GSTV2.naturalCarry st.childTail q = 0 ∨
        GSTV2.naturalCarry st.childTail q = 3 := by
      rcases hChildController.2 with h0 | h3
      · exact Or.inl (hCarryExact.symm.trans h0)
      · exact Or.inr (hCarryExact.symm.trans h3)
    simpa [T, st, GSTGraphV2InfiniteControllerBridge.graphCoupledState,
      GSTV2.naturalCarry, GSTInfiniteV2.gstCarryS] using hC

  exact gpt56_first_seedzero_gate_exact_binary_chord T
    ⟨q, hTailDigit, hTailCarry⟩

#check graph_exposed_tail_first_seedzero_control
#check graph_exposed_tail_first_seedzero_chord
#print axioms graph_exposed_tail_first_seedzero_control
#print axioms graph_exposed_tail_first_seedzero_chord

end GSTFinalResidualEarliestGateBridge
