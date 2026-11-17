import GSTInfiniteGateTransport
import GSTInfiniteCoupledLedger
import GSTGraphV2UnifiedVerticalTelescope
import GSTU2DEventTransport

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2InfiniteControllerBridge

open GSTGraphV2InfiniteControl
open GSTGraphV2UnifiedPowerRectangle
open GSTGraphV2UnifiedVerticalTelescope

/-- The transplanted all-Nat controller state read directly from one physical
width-`N` rectangle of the canonical infinite Graph-V2 sheet. -/
def graphCoupledState (E N p : Nat) : GSTV2.CoupledState :=
  {
    parentSeed := (graph E N p).seven.carry
    parentOffset := carryWord E p 0 N
    childResidue := carryWord E p 1 N
    childCarry := (graph E 0 p).seven.carry
    childTail := E / 3^p
  }

private theorem coupled_state_eq_of_fields
    (a b : GSTV2.CoupledState)
    (hParentSeed : a.parentSeed = b.parentSeed)
    (hParentOffset : a.parentOffset = b.parentOffset)
    (hChildResidue : a.childResidue = b.childResidue)
    (hChildCarry : a.childCarry = b.childCarry)
    (hChildTail : a.childTail = b.childTail) : a = b := by
  cases a
  cases b
  simp_all

/-- The child digit stored in the transplanted state is the actual left-edge
Graph-V2 ternary digit. -/
theorem graphCoupledState_childDigit_exact (E N p : Nat) :
    (graphCoupledState E N p).childTail % 3 =
      (graph E 0 p).seven.digit := by
  simp [graphCoupledState, graph, cell,
    GSTCanonicalSevenAxisBridge.vertex,
    GSTCanonicalSevenAxisBridge.digit3]

/-- The parent digit emitted by the transplanted state is the actual right-edge
Graph-V2 digit. -/
theorem graphCoupledState_parentDigit_exact (E N p : Nat) :
    ((graphCoupledState E N p).parentOffset +
        4^N * ((graphCoupledState E N p).childTail % 3)) % 3 =
      (graph E N p).seven.digit := by
  rw [graphCoupledState_childDigit_exact]
  simpa [graphCoupledState] using carryWord_digit_transport E p 0 N

/-- Every physical rectangle supplies the exact two-endpoint invariant needed
by the all-Nat controller. -/
theorem graphCoupledState_invariant (E N p : Nat) :
    GSTV2.CoupledInvariant (4^N) (graphCoupledState E N p) := by
  constructor
  · have h := unifiedState_physicalInvariant E N p
    simpa [GSTV2.CoupledInvariant, graphCoupledState,
      GSTGraphV2CoupledUPhysicalBridge.PhysicalInvariant,
      GSTGraphV2UnifiedPowerRectangle.unifiedState] using h
  · simpa [graphCoupledState,
      GSTGraphV2UnifiedPowerRectangle.unifiedState] using
      (unifiedState_residue_lt E N p)

/-- One transplanted controller step is literally one vertical ternary step of
the same physical Graph-V2 rectangle. -/
theorem graphCoupledState_step_exact (E N p : Nat) :
    GSTV2.coupledStep (4^N) (graphCoupledState E N p) =
      graphCoupledState E N (p+1) := by
  apply coupled_state_eq_of_fields
  · dsimp [GSTV2.coupledStep]
    rw [graphCoupledState_parentDigit_exact]
    have h := (graph_cell_exact E N p).2
    simpa [graphCoupledState, GSTV2.cellNextCarry, GSTV2.cellMass,
      GST2DMixedEmergence.nextCarry] using h
  · dsimp [GSTV2.coupledStep]
    have h := unifiedState_parentOffset_step_exact E N p
    simpa [graphCoupledState,
      GSTGraphV2UnifiedPowerRectangle.unifiedState,
      GSTGraphV2CoupledUFlux.childDigit] using h
  · dsimp [GSTV2.coupledStep]
    have hout :
        GSTV2.cellOutput
            (graphCoupledState E N p).childCarry
            ((graphCoupledState E N p).childTail % 3) =
          (graph E 1 p).seven.digit := by
      rw [graphCoupledState_childDigit_exact]
      have h := (graph_cell_exact E 0 p).1
      simpa [graphCoupledState, GSTV2.cellOutput, GSTV2.cellMass,
        GST2DMixedEmergence.outDigit] using h
    rw [hout]
    change
      (carryWord E p 1 N + 4^N * (graph E 1 p).seven.digit) / 3 =
        carryWord E (p+1) 1 N
    have hbal := carryWord_vertical_balance E p 1 N
    have hdlt := graph_digit_lt_three E (1+N) p
    have h3 : 0 < (3 : Nat) := by decide
    rw [hbal, Nat.add_mul_div_left _ _ h3,
      Nat.div_eq_of_lt hdlt, Nat.zero_add]
  · dsimp [GSTV2.coupledStep]
    rw [graphCoupledState_childDigit_exact]
    have h := (graph_cell_exact E 0 p).2
    simpa [graphCoupledState, GSTV2.cellNextCarry, GSTV2.cellMass,
      GST2DMixedEmergence.nextCarry] using h
  · dsimp [GSTV2.coupledStep, graphCoupledState]
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ]

/-- **All-depth rectangle/controller identification.**  Observation depth `K`
is arbitrary: the transplanted controller orbit and the original infinite
Graph-V2 sheet are the same state at row `b+K`. -/
theorem graphCoupledOrbit_exact (E N b : Nat) : ∀ K,
    GSTV2.coupledOrbit (4^N) (graphCoupledState E N b) K =
      graphCoupledState E N (b+K) := by
  intro K
  induction K with
  | zero => simp [GSTV2.coupledOrbit]
  | succ K ih =>
      rw [GSTV2.coupledOrbit, ih, graphCoupledState_step_exact]
      have hidx : b + K + 1 = b + (K+1) := by omega
      exact congrArg (graphCoupledState E N) hidx

/-- A complete bad right edge on the Graph-V2 sheet becomes the transplanted
controller's exact all-Nat seeded bad language. -/
theorem graph_right_bad_to_seededBadTrace
    (E N b : Nat)
    (hRightBad : ∀ j,
      ¬ GSTU2DEventTransport.HappyCell
        (graph E N (b+j)).seven.carry
        (graph E N (b+j)).seven.digit) :
    GSTV2.SeededBadTrace
      (graphCoupledState E N b).parentSeed
      ((graphCoupledState E N b).parentWord (4^N)) := by
  intro K hHappy
  have hbad := hRightBad K
  have hseed := GSTV2.coupledOrbit_parentSeed_exact
    (4^N) (graphCoupledState E N b) K
  have hdigit := GSTV2.coupledOrbit_parentDigit_exact
    (4^N) (graphCoupledState E N b) K
  have horbit := graphCoupledOrbit_exact E N b K
  rw [horbit] at hseed hdigit
  apply hbad
  have hCarry :
      (graph E N (b+K)).seven.carry =
        GSTV2.affineCarry
          (graphCoupledState E N b).parentSeed
          ((graphCoupledState E N b).parentWord (4^N)) K := by
    simpa [graphCoupledState] using hseed
  have hLocalDigit := graphCoupledState_parentDigit_exact E N (b+K)
  have hDigit :
      (graph E N (b+K)).seven.digit =
        GSTV2.digit ((graphCoupledState E N b).parentWord (4^N)) K := by
    calc
      (graph E N (b+K)).seven.digit =
          ((graphCoupledState E N (b+K)).parentOffset +
            4^N * ((graphCoupledState E N (b+K)).childTail % 3)) % 3 :=
        hLocalDigit.symm
      _ = GSTV2.digit
          ((graphCoupledState E N b).parentWord (4^N)) K := hdigit
  rcases hHappy with ⟨hd2, hC⟩
  refine ⟨hDigit.trans hd2, ?_⟩
  rcases hC with h0 | h3
  · exact Or.inl (hCarry.trans h0)
  · exact Or.inr (hCarry.trans h3)

/-- If the left boundary begins with the true zero carry, a bad right edge
constructs the full transplanted all-Nat bad coupled controller. -/
theorem graph_infinite_bad_control
    (E N b : Nat)
    (hChildCarryZero : (graph E 0 b).seven.carry = 0)
    (hRightBad : ∀ j,
      ¬ GSTU2DEventTransport.HappyCell
        (graph E N (b+j)).seven.carry
        (graph E N (b+j)).seven.digit) :
    GSTV2.InfiniteBadCoupledControl
      (4^N) (graphCoupledState E N b) := by
  apply GSTV2.infinite_bad_coupled_control
  · positivity
  · exact graphCoupledState_invariant E N b
  · simpa [graphCoupledState] using hChildCarryZero
  · exact graph_right_bad_to_seededBadTrace E N b hRightBad

/-- A left-edge Graph-V2 Happy cell is exactly a child Happy event at the same
all-Nat controller depth. -/
theorem graph_child_happy_to_controller
    (E N b q : Nat)
    (hChild : GSTU2DEventTransport.HappyCell
      (graph E 0 (b+q)).seven.carry
      (graph E 0 (b+q)).seven.digit) :
    GSTV2.Happy
      (GSTV2.coupledOrbit (4^N) (graphCoupledState E N b) q).childCarry
      ((GSTV2.coupledOrbit (4^N)
        (graphCoupledState E N b) q).childTail % 3) := by
  have horbit := graphCoupledOrbit_exact E N b q
  rw [horbit]
  have hDigit := graphCoupledState_childDigit_exact E N (b+q)
  rcases hChild with ⟨hd2, hC⟩
  refine ⟨hDigit.trans hd2, ?_⟩
  simpa [graphCoupledState] using hC

/-- The Graph-V2 child gate therefore yields the transplanted latent-gate
packet while all-depth right-edge badness continues. -/
theorem graph_child_happy_latent_transfer
    (E N b q : Nat)
    (hChildCarryZero : (graph E 0 b).seven.carry = 0)
    (hRightBad : ∀ j,
      ¬ GSTU2DEventTransport.HappyCell
        (graph E N (b+j)).seven.carry
        (graph E N (b+j)).seven.digit)
    (hChild : GSTU2DEventTransport.HappyCell
      (graph E 0 (b+q)).seven.carry
      (graph E 0 (b+q)).seven.digit) :
    GSTV2.LatentGateTransfer (4^N) (graphCoupledState E N b) q := by
  exact GSTV2.coupled_happy_transports_information
    (4^N) (graphCoupledState E N b) q
    (graph_infinite_bad_control E N b hChildCarryZero hRightBad)
    (graph_child_happy_to_controller E N b q hChild)

end GSTGraphV2InfiniteControllerBridge
