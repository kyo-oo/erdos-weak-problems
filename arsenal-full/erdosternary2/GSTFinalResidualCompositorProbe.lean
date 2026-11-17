import GSTGraphV2ProductionLaws
import GSTU2DSharpCrossingBlock
import GSTGraphV2PerfectPowerBlockProbe
import GSTGraphV2InfiniteControllerBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

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

namespace GSTFinalResidualCompositorProbe

/-- Exact lower-window strengthening of the existing LTE cut theorem.  A
perfect-power U tail is neutral at every positive row below its defining cut,
not only at the top cut. -/
theorem uTailEnergy_below_cut_neutral
    (t n K p : Nat) (hp2 : 2 ≤ p) (hp : p ≤ t+K) :
    (GSTGraphV2InfiniteControl.graph
        (uTailEnergy t n K) 0 p).seven.carry = 0 ∧
    (GSTGraphV2InfiniteControl.graph
        (uTailEnergy t n K) 0 p).seven.digit = 0 ∧
    (GSTGraphV2InfiniteControl.graph
        (uTailEnergy t n K) 0 p).seven.space = .null := by
  let r := t + K
  let u := originSuffix n K
  let R := uTailEnergy t n K
  have hR : R = 4^(3^r * u) := by
    rfl
  have hnext : R % 3^(r+1) = 1 := by
    rw [hR]
    exact pow4_scaled_mod_next r u
  have hpPow : 1 < 3^p := by
    have h9 : 9 ≤ 3^p := by
      rw [show (9 : Nat) = 3^2 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) hp2
    omega
  have hcur : R % 3^p = 1 := by
    have hdvd : 3^p ∣ 3^(r+1) :=
      Nat.pow_dvd_pow 3 (by omega)
    have hmod := Nat.mod_mod_of_dvd R hdvd
    rw [hnext, Nat.mod_eq_of_lt hpPow] at hmod
    exact hmod.symm
  have hp1Pow : 1 < 3^(p+1) := by
    have h3 : 3^1 ≤ 3^(p+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    norm_num at h3 ⊢
  have hnextAtP : R % 3^(p+1) = 1 := by
    have hdvd : 3^(p+1) ∣ 3^(r+1) :=
      Nat.pow_dvd_pow 3 (by omega)
    have hmod := Nat.mod_mod_of_dvd R hdvd
    rw [hnext, Nat.mod_eq_of_lt hp1Pow] at hmod
    exact hmod.symm
  have hc : carry4 R p = 0 := by
    unfold carry4
    rw [hcur]
    apply Nat.div_eq_of_lt
    have h9 : 9 ≤ 3^p := by
      rw [show (9 : Nat) = 3^2 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) hp2
    omega
  have hd : digit3 R p = 0 := by
    have hsplit :
        R % (3^p * 3) = R % 3^p + 3^p * (R / 3^p % 3) := by
      rw [Nat.mod_mul]
    rw [← Nat.pow_succ, hnextAtP, hcur] at hsplit
    have hprod : 3^p * (R / 3^p % 3) = 0 := by omega
    have hd0 : R / 3^p % 3 = 0 := by
      rcases Nat.mul_eq_zero.mp hprod with hp0 | hd0
      · exact False.elim ((Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 3))) hp0)
      · exact hd0
    exact hd0
  constructor
  · simpa [GSTGraphV2InfiniteControl.graph, GSTGraphV2InfiniteControl.cell,
      GSTCanonicalSevenAxisBridge.vertex, R] using hc
  constructor
  · simpa [GSTGraphV2InfiniteControl.graph, GSTGraphV2InfiniteControl.cell,
      GSTCanonicalSevenAxisBridge.vertex, R] using hd
  · simp [GSTGraphV2InfiniteControl.graph, GSTGraphV2InfiniteControl.cell,
      GSTCanonicalSevenAxisBridge.vertex,
      GSTCanonicalSevenAxisBridge.spaceOfCarry, R, hc]

/-! -----------------------------------------------------------------------
TRANSPLANTED PERFECT-POWER PHASE BLOCK

These declarations are copied into the final residual compositor itself so the
hard seam consumes the exact shifted perfect-power window directly.  They are
not left as a detached candidate theorem or external TODO.
------------------------------------------------------------------------ -/

/-- Shifted phase pressure beginning at the live production cut. -/
def transplantedGraphPhaseWindow (E t b K : Nat) : Int :=
  weightedPhaseColumnPrefix
    (fun j => (graph E t (b+j)).seven.carry)
    (fun j => (graph E t (b+j)).seven.digit) K

/-- Transplanted Happy-to-positive shifted window. -/
theorem transplanted_graph_phase_window_positive_of_happy
    (E t b q : Nat)
    (hHappy : HappyCell
      (graph E t (b+q)).seven.carry
      (graph E t (b+q)).seven.digit) :
    0 < transplantedGraphPhaseWindow E t b (q+1) := by
  unfold transplantedGraphPhaseWindow
  apply weightedPhaseColumnPrefix_positive_of_top_happy
  · intro p hp
    exact graph_carry_lt_four E t (b+p)
  · intro p hp
    exact graph_digit_lt_three E t (b+p)
  · exact hHappy

/-- Transplanted complete-badness-to-nonpositive shifted window. -/
theorem transplanted_graph_phase_window_nonpositive_of_bad
    (E t b K : Nat)
    (hBad : ∀ j, j < K → ¬ HappyCell
      (graph E t (b+j)).seven.carry
      (graph E t (b+j)).seven.digit) :
    transplantedGraphPhaseWindow E t b K ≤ 0 := by
  unfold transplantedGraphPhaseWindow
  induction K with
  | zero => simp [weightedPhaseColumnPrefix]
  | succ K ih =>
      have ih' := ih (fun j hj => hBad j (by omega))
      have hlocal :
          phaseDensity
              (graph E t (b+K)).seven.carry
              (graph E t (b+K)).seven.digit ≤ 0 :=
        phaseDensity_nonpositive_of_not_happy
          (graph E t (b+K)).seven.carry
          (graph E t (b+K)).seven.digit
          (graph_carry_lt_four E t (b+K))
          (graph_digit_lt_three E t (b+K))
          (hBad K (by omega))
      have hw : (0 : Int) ≤ (((3^K : Nat) : Int)) := by positivity
      rw [weightedPhaseColumnPrefix]
      exact add_nonpos ih' (mul_nonpos_of_nonneg_of_nonpos hw hlocal)

/-- Transplanted exact ternary digit shift through the production prefix. -/
theorem transplanted_digit3_add_shift (R b q : Nat) :
    digit3 R (b+q) = digit3 (R / 3^b) q := by
  unfold digit3
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]

/-- Transplanted exact residue identity for the shifted graph digits. -/
theorem transplanted_graph_digit_window_exact (E t b K : Nat) :
    Finset.sum (Finset.range K) (fun j =>
      (((3^j : Nat) : Int)) *
        (((graph E t (b+j)).seven.digit : Nat) : Int)) =
      ((((4^t * E) / 3^b) % 3^K : Nat) : Int) := by
  simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex,
    transplanted_digit3_add_shift] using
    GSTGraphV2PerfectPowerBlock.digit3_weighted_prefix_int
      ((4^t * E) / 3^b) K

/-- Transplanted exact divergence equation on the shifted production window. -/
theorem transplanted_graph_phase_window_exact (E t b K : Nat) :
    transplantedGraphPhaseWindow E t b K =
      Finset.sum (Finset.range K) (fun j =>
        (((3^j : Nat) : Int)) *
          (phaseDigitPotential (graph E (t+1) (b+j)).seven.digit -
           phaseDigitPotential (graph E t (b+j)).seven.digit)) +
      phaseCarryPotential (graph E t b).seven.carry -
        (((3^K : Nat) : Int)) *
          phaseCarryPotential (graph E t (b+K)).seven.carry +
      Finset.sum (Finset.range K) (fun j =>
        (((3^j : Nat) : Int)) *
          surviveI
            (graph E t (b+j)).seven.carry
            (graph E t (b+j)).seven.digit) := by
  unfold transplantedGraphPhaseWindow
  rw [GSTGraphV2PerfectPowerBlock.weightedPhaseColumnPrefix_eq_sum]
  have h := phaseColumn_exact
    (fun j => (graph E t (b+j)).seven.carry)
    (fun j => (graph E t (b+j)).seven.digit)
    (fun j => (graph E (t+1) (b+j)).seven.digit) K
    (by
      intro j hj
      exact ⟨graph_carry_lt_four E t (b+j),
        graph_digit_lt_three E t (b+j),
        (graph_cell_exact E t (b+j)).1,
        by simpa [Nat.add_assoc] using (graph_cell_exact E t (b+j)).2⟩)
  simpa [Nat.add_zero] using h

/-- Transplanted exact phase digit boundary: literal exposed residues, no
terminal row and no finite-support replacement. -/
theorem transplanted_graph_phase_digit_window_boundary_exact
    (E t b K : Nat) :
    Finset.sum (Finset.range K) (fun j =>
      (((3^j : Nat) : Int)) *
        (phaseDigitPotential (graph E (t+1) (b+j)).seven.digit -
         phaseDigitPotential (graph E t (b+j)).seven.digit)) =
      ((((4^(t+1) * E) / 3^b) % 3^K : Nat) : Int) -
      ((((4^t * E) / 3^b) % 3^K : Nat) : Int) := by
  calc
    Finset.sum (Finset.range K) (fun j =>
      (((3^j : Nat) : Int)) *
        (phaseDigitPotential (graph E (t+1) (b+j)).seven.digit -
         phaseDigitPotential (graph E t (b+j)).seven.digit)) =
      Finset.sum (Finset.range K) (fun j =>
        (((3^j : Nat) : Int)) * (((graph E (t+1) (b+j)).seven.digit : Nat) : Int) -
        (((3^j : Nat) : Int)) * (((graph E t (b+j)).seven.digit : Nat) : Int)) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [phaseDigitPotential]
          ring
    _ =
      Finset.sum (Finset.range K) (fun j =>
        (((3^j : Nat) : Int)) * (((graph E (t+1) (b+j)).seven.digit : Nat) : Int)) -
      Finset.sum (Finset.range K) (fun j =>
        (((3^j : Nat) : Int)) * (((graph E t (b+j)).seven.digit : Nat) : Int)) := by
          rw [Finset.sum_sub_distrib]
    _ = _ := by
      rw [transplanted_graph_digit_window_exact,
        transplanted_graph_digit_window_exact]

/-- Hard unbounded residual family only: level one, origin trit one.  This probe
contains no legacy Omega termination and no generic perfect-power collision. -/
theorem residual_level_one_origin_one_probe
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
  let T := uTailEnergy (1+k) m (q+1)
  let P := uPhaseShift (1+k) m (q+1)

  have hWidth := residual_level_one_width k m (b+q)
  have hParentExponent := residual_level_one_parent_exponent k m (b+q)
  have hEnergyStep := residual_level_one_origin_one_energy_step k m (b+q) hm1
  have hNeutral := residual_gate_neutral_tail 1 k m q (by decide) hk
  have hLeftPhased := residual_gate_left_is_phased_tail 1 k m q
  have hRightAbsolute := residual_right_absolute_state_exact 1 k m (b+q)

  /- Direct all-Nat controller transplant for the exact hard width-3 strip. -/
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

  have hControllerBad :=
    GSTGraphV2InfiniteControllerBridge.graph_infinite_bad_control
      E 3 b hBaseCarryZero (by
        intro j
        simpa [E, b, Nat.add_assoc] using hRightBad j)

  have hLatentGate :=
    GSTGraphV2InfiniteControllerBridge.graph_child_happy_latent_transfer
      E 3 b q hBaseCarryZero
      (by
        intro j
        simpa [E, b, Nat.add_assoc] using hRightBad j)
      (by simpa [E, b, Nat.add_assoc] using hChild)

  have hControllerLedger :=
    GSTV2.infinite_coupled_ledger
      (4^3)
      (GSTGraphV2InfiniteControllerBridge.graphCoupledState E 3 b)
      (by positivity)
      (GSTGraphV2InfiniteControllerBridge.graphCoupledState_invariant E 3 b)

  have hLedgerAtGate := hControllerLedger.pastSynchronized q
  have hBadSuffixAfterGate := hLatentGate.nextParentBadSuffix

  have hNeutralWindow : ∀ p, p ≤ q →
      (GSTGraphV2InfiniteControl.graph T 0 (b+p)).seven.carry = 0 ∧
      (GSTGraphV2InfiniteControl.graph T 0 (b+p)).seven.digit = 0 ∧
      (GSTGraphV2InfiniteControl.graph T 0 (b+p)).seven.space = .null := by
    intro p hpq
    have h := uTailEnergy_below_cut_neutral
      (1+k) m (q+1) (b+p) (by dsimp [b]; omega) (by dsimp [b]; omega)
    simpa [T, b, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

  have hRephaseWindow : ∀ p, p ≤ q →
      (GSTGraphV2InfiniteControl.graph E 0 (b+p)).seven.carry =
        (GSTGraphV2InfiniteControl.graph T P (b+p)).seven.carry ∧
      (GSTGraphV2InfiniteControl.graph E 0 (b+p)).seven.digit =
        (GSTGraphV2InfiniteControl.graph T P (b+p)).seven.digit := by
    intro p hpq
    have h := graph_u_block_observables_exact
      (1+k) m (q+1) 0 (b+p)
    constructor
    · simpa [E, T, P, GSTGraphV2Production.residualEnergy,
        GSTGraphV2HandwrittenOmegaUBlock.residualEnergy,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.1
    · simpa [E, T, P, GSTGraphV2Production.residualEnergy,
        GSTGraphV2HandwrittenOmegaUBlock.residualEnergy,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.2.1

  have hRephaseRightWindow : ∀ p, p ≤ q →
      (GSTGraphV2InfiniteControl.graph E 3 (b+p)).seven.carry =
        (GSTGraphV2InfiniteControl.graph T (P+3) (b+p)).seven.carry ∧
      (GSTGraphV2InfiniteControl.graph E 3 (b+p)).seven.digit =
        (GSTGraphV2InfiniteControl.graph T (P+3) (b+p)).seven.digit := by
    intro p hpq
    have h := graph_u_block_observables_exact
      (1+k) m (q+1) 3 (b+p)
    constructor
    · simpa [E, T, P, GSTGraphV2Production.residualEnergy,
        GSTGraphV2HandwrittenOmegaUBlock.residualEnergy,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.1
    · simpa [E, T, P, GSTGraphV2Production.residualEnergy,
        GSTGraphV2HandwrittenOmegaUBlock.residualEnergy,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.2.1

  /- The transplanted phase block is consumed here, inside the hard proof. -/
  have hPhaseLeftPositive :
      0 < transplantedGraphPhaseWindow E 0 b (q+1) := by
    apply transplanted_graph_phase_window_positive_of_happy
    simpa [E, b, Nat.add_assoc] using hChild

  have hPhaseRightNonpositive :
      transplantedGraphPhaseWindow E 3 b (q+1) ≤ 0 := by
    apply transplanted_graph_phase_window_nonpositive_of_bad
    intro j hj
    simpa [E, b, Nat.add_assoc] using hRightBad j

  have hPhaseLeftExact :=
    transplanted_graph_phase_window_exact E 0 b (q+1)
  have hPhaseRightExact :=
    transplanted_graph_phase_window_exact E 3 b (q+1)
  have hPhaseLeftBoundary :=
    transplanted_graph_phase_digit_window_boundary_exact E 0 b (q+1)
  have hPhaseRightBoundary :=
    transplanted_graph_phase_digit_window_boundary_exact E 3 b (q+1)

  have hPositive83 :
      0 < weightedRectanglePrefix83
        (fun t p =>
          (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.carry)
        (fun t p =>
          (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.digit)
        3 (q+1) := by
    apply weightedRectanglePrefix83_positive_of_top_leading_happy
    · decide
    · intro t p ht hp
      exact graph_carry_lt_four E t (b+p)
    · intro t p ht hp
      exact graph_digit_lt_three E t (b+p)
    · simpa [E, b, Nat.add_assoc] using hChild

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
        (fun t p =>
          (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.carry)
        (fun t p =>
          (GSTGraphV2InfiniteControl.graph E t (b+p)).seven.digit)
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

  trace_state
  omega

end GSTFinalResidualCompositorProbe