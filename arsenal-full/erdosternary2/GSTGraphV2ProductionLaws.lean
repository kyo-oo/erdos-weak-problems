import GSTGraphV2Production
import GSTGraphV2HandwrittenExponentialLTE

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2ProductionLaws

open GSTCanonicalSevenAxisBridge
open GSTU2DEventTransport
open GSTGraphV2Production
open GSTGraphV2HandwrittenOmegaUBlock
open GSTGraphV2HandwrittenExponentialCascade
open GSTGraphV2HandwrittenExponentialLTE

/-- The horizontal edge of the production lattice is the exact x4 digit edge. -/
theorem horizontal_digit_exact (E t p : Nat) :
    GST2DMixedEmergence.outDigit
        (GSTGraphV2Production.cell E t p).seven.carry
        (GSTGraphV2Production.cell E t p).seven.digit =
      (GSTGraphV2Production.cell E (t+1) p).seven.digit := by
  simpa [GSTGraphV2Production.cell] using
    (GSTGraphV2InfiniteControl.graph_cell_exact E t p).1

/-- The vertical edge of the production lattice is the exact ternary carry edge. -/
theorem vertical_carry_exact (E t p : Nat) :
    GST2DMixedEmergence.nextCarry
        (GSTGraphV2Production.cell E t p).seven.carry
        (GSTGraphV2Production.cell E t p).seven.digit =
      (GSTGraphV2Production.cell E t (p+1)).seven.carry := by
  simpa [GSTGraphV2Production.cell] using
    (GSTGraphV2InfiniteControl.graph_cell_exact E t p).2

/-- Equation I is literally one coordinate identity of each production cell. -/
theorem navigation_nullspace_flux_exact (E t p : Nat) :
    4 * ((GSTGraphV2Production.cell E t p).absoluteEnergy % 3^p) =
      (GSTGraphV2Production.cell E t p).navigationNullspace +
        3^p * (GSTGraphV2Production.cell E t p).seven.carry := by
  simpa [GSTGraphV2Production.cell] using
    GSTGraphV2HandwrittenExponentialCascade.graph_navigation_nullspace_flux_exact
      E t p

/-- The full perfect-power cell and the re-phased U-tail cell are the same
physical arithmetic state in carry and information coordinates. -/
theorem origin_frame_phased_state_exact
    (t n K x p : Nat) :
    (originFrame t n K x p).full.seven.carry =
        (originFrame t n K x p).phasedTail.seven.carry ∧
      (originFrame t n K x p).full.seven.digit =
        (originFrame t n K x p).phasedTail.seven.digit := by
  have h :=
    GSTGraphV2HandwrittenExponentialCascade.graph_u_block_observables_exact
      t n K x p
  constructor
  · simpa [GSTGraphV2Production.originFrame,
      GSTGraphV2Production.originCoordinates,
      GSTGraphV2Production.cell] using h.1
  · simpa [GSTGraphV2Production.originFrame,
      GSTGraphV2Production.originCoordinates,
      GSTGraphV2Production.cell] using h.2.1

/-- At the canonical production cut, the unphased higher-level U tail is the
exact neutral NULL/zero-information state. -/
theorem canonical_cut_neutral_tail
    (s n q : Nat) (hs : 1 ≤ s) :
    let F := canonicalCutFrame s n q
    F.uFrame.neutralTail.seven.carry = 0 ∧
      F.uFrame.neutralTail.seven.digit = 0 ∧
      F.uFrame.neutralTail.seven.space = .null := by
  dsimp only
  have h := canonical_child_u_cut_neutral s n q hs
  simpa [GSTGraphV2Production.canonicalCutFrame,
    GSTGraphV2Production.canonicalCutRow,
    GSTGraphV2Production.originFrame,
    GSTGraphV2Production.originCoordinates,
    GSTGraphV2Production.cell] using h

/-- At every generalized residual gate row, the unphased tail is likewise the
exact neutral state. This is the absolute Graph-V2 form of consuming j+1
origin trits before re-applying the finite phase. -/
theorem residual_gate_neutral_tail
    (s k m j : Nat) (hs : 1 ≤ s) (hk : 1 ≤ k) :
    let F := residualGateFrame s k m j
    F.originFrame.neutralTail.seven.carry = 0 ∧
      F.originFrame.neutralTail.seven.digit = 0 ∧
      F.originFrame.neutralTail.seven.space = .null := by
  dsimp only
  have hcut : 2 ≤ (s+k) + (j+1) := by omega
  have h := uTailEnergy_cut_neutral (s+k) m (j+1) hcut
  simpa [GSTGraphV2Production.residualGateFrame,
    GSTGraphV2Production.residualGateRow,
    GSTGraphV2Production.originFrame,
    GSTGraphV2Production.originCoordinates,
    GSTGraphV2Production.cell,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- The left endpoint of the generalized residual rectangle at a gate row is
exactly the re-phased U-tail state. No surrogate child graph is introduced. -/
theorem residual_gate_left_is_phased_tail
    (s k m j : Nat) :
    let F := residualGateFrame s k m j
    F.residual.block.left.seven.carry =
        F.originFrame.phasedTail.seven.carry ∧
      F.residual.block.left.seven.digit =
        F.originFrame.phasedTail.seven.digit := by
  dsimp only
  have h :=
    GSTGraphV2HandwrittenExponentialCascade.graph_u_block_observables_exact
      (s+k) m (j+1) 0 (residualGateRow s k j)
  constructor
  · simpa [GSTGraphV2Production.residualGateFrame,
      GSTGraphV2Production.residualGateRow,
      GSTGraphV2Production.residualFrame,
      GSTGraphV2Production.residualRectangle,
      GSTGraphV2Production.rectangle,
      GSTGraphV2Production.residualEnergy,
      GSTGraphV2HandwrittenOmegaUBlock.residualEnergy,
      GSTGraphV2Production.originFrame,
      GSTGraphV2Production.originCoordinates,
      GSTGraphV2Production.cell] using h.1
  · simpa [GSTGraphV2Production.residualGateFrame,
      GSTGraphV2Production.residualGateRow,
      GSTGraphV2Production.residualFrame,
      GSTGraphV2Production.residualRectangle,
      GSTGraphV2Production.rectangle,
      GSTGraphV2Production.residualEnergy,
      GSTGraphV2HandwrittenOmegaUBlock.residualEnergy,
      GSTGraphV2Production.originFrame,
      GSTGraphV2Production.originCoordinates,
      GSTGraphV2Production.cell] using h.2.1

/-- The right endpoint of every residual production rectangle is exactly the
absolute parent perfect-power sheet, in all observables needed by the proof. -/
theorem residual_right_absolute_state_exact
    (s k m p : Nat) :
    let F := residualFrame s k m p
    F.block.right.seven.carry =
        (GSTGraphV2Production.cell 1 F.parentExponent p).seven.carry ∧
      F.block.right.seven.digit =
        (GSTGraphV2Production.cell 1 F.parentExponent p).seven.digit ∧
      F.block.right.eventCode =
        (GSTGraphV2Production.cell 1 F.parentExponent p).eventCode ∧
      F.block.right.uCharge =
        (GSTGraphV2Production.cell 1 F.parentExponent p).uCharge ∧
      F.block.right.mixedCharge =
        (GSTGraphV2Production.cell 1 F.parentExponent p).mixedCharge ∧
      F.block.right.crossingCharge =
        (GSTGraphV2Production.cell 1 F.parentExponent p).crossingCharge ∧
      F.block.right.survive =
        (GSTGraphV2Production.cell 1 F.parentExponent p).survive := by
  dsimp only
  have h := residual_parent_observables_exact s k m p
  simpa [GSTGraphV2Production.residualFrame,
    GSTGraphV2Production.residualRectangle,
    GSTGraphV2Production.rectangle,
    GSTGraphV2Production.residualEnergy,
    GSTGraphV2HandwrittenOmegaUBlock.residualEnergy,
    GSTGraphV2Production.cell] using h

/-- In the sole unbounded classifier level `s=1`, the parent block is exactly
three horizontal x4 edges. -/
theorem residual_level_one_width (k m p : Nat) :
    (residualFrame 1 k m p).parentWidth = 3 := by
  norm_num [GSTGraphV2Production.residualFrame,
    GSTGraphV2HandwrittenOmegaUBlock.residualWidth]

/-- The sole unbounded level therefore has the exact absolute exponent
`3 + 3^(k+1)*m` at its right endpoint. -/
theorem residual_level_one_parent_exponent (k m p : Nat) :
    (residualFrame 1 k m p).parentExponent =
      3 + 3^(k+1) * m := by
  dsimp [GSTGraphV2Production.residualFrame,
    GSTGraphV2HandwrittenOmegaUBlock.residualParentExponent]
  rw [Nat.pow_add]
  ring

/-- On the hard residue-one branch, one natural-origin trit is consumed exactly:
the residual child energy factors into the trit-one phase and the strictly
deeper tail energy retained in the production frame. -/
theorem residual_level_one_origin_one_energy_step
    (k m p : Nat) (hm1 : m % 3 = 1) :
    (residualFrame 1 k m p).childEnergy =
      4^(3^(k+1)) * (residualFrame 1 k m p).nextTailEnergy := by
  have h := residual_energy_u_mul_div_exact 1 k m
  simpa [GSTGraphV2Production.residualFrame,
    GSTGraphV2Production.residualEnergy,
    GSTGraphV2HandwrittenOmegaUBlock.residualEnergy,
    GSTGraphV2HandwrittenOmegaUBlock.originTrit,
    GSTGraphV2HandwrittenOmegaUBlock.originTail,
    hm1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

#check horizontal_digit_exact
#check vertical_carry_exact
#check navigation_nullspace_flux_exact
#check origin_frame_phased_state_exact
#check canonical_cut_neutral_tail
#check residual_gate_neutral_tail
#check residual_gate_left_is_phased_tail
#check residual_right_absolute_state_exact
#check residual_level_one_width
#check residual_level_one_parent_exponent
#check residual_level_one_origin_one_energy_step

#print axioms horizontal_digit_exact
#print axioms origin_frame_phased_state_exact
#print axioms canonical_cut_neutral_tail
#print axioms residual_gate_neutral_tail
#print axioms residual_gate_left_is_phased_tail
#print axioms residual_right_absolute_state_exact
#print axioms residual_level_one_origin_one_energy_step

end GSTGraphV2ProductionLaws
