import GSTGraphV2ProductionLaws
import GSTGraphV2InfiniteControllerBridge
import GSTFinalResidualEarliestGateBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

open GSTCanonicalSevenAxisBridge
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2HandwrittenOmegaUBlock
open GSTGraphV2ProductionLaws

namespace GSTFinalResidualInfiniteLedgerProbe

/-- The hard residual congruence `m ≡ 1 (mod 3)` survives the exact LTE cut:
the exposed tail has first ternary digit one.  This is the missing arithmetic
link between the production residual family and the all-Nat controller. -/
theorem residual_level_one_origin_one_tail_mod_three
    (k m : Nat) (hm1 : m % 3 = 1) :
    (GSTGraphV2Production.residualEnergy 1 k m / 3^(k+2)) % 3 = 1 := by
  let E := GSTGraphV2Production.residualEnergy 1 k m
  let D := 3^(k+2)
  let A := 4^(3^(k+1))
  let P := 4^(3^(k+2) * (m/3))
  let c := GSTGraphV2HandwrittenExponentialLTE.lteCoeff (k+1)

  have hstep0 :=
    GSTGraphV2ProductionLaws.residual_level_one_origin_one_energy_step k m 0 hm1
  have hstep : E = A * P := by
    simpa [E, A, P, GSTGraphV2Production.residualFrame,
      GSTGraphV2Production.residualEnergy,
      GSTGraphV2HandwrittenOmegaUBlock.residualEnergy,
      GSTGraphV2HandwrittenOmegaUBlock.originTail,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep0

  have hDgt1 : 1 < D := by
    dsimp [D]
    have h9 : 9 ≤ 3^(k+2) := by
      rw [show (9 : Nat) = 3^2 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega
  have hDpos : 0 < D := by omega

  have hPmod : P % (D * 3) = 1 := by
    have h := GSTGraphV2HandwrittenExponentialLTE.pow4_scaled_mod_next
      (k+2) (m/3)
    simpa [P, D, Nat.pow_succ] using h

  have hAexact : A = 1 + D * c := by
    have h := GSTGraphV2HandwrittenExponentialLTE.pow4_three_power_lte_exact (k+1)
    simpa [A, D, c, Nat.add_assoc] using h

  have hcmod : c % 3 = 1 := by
    dsimp [c]
    exact GSTGraphV2HandwrittenExponentialLTE.lteCoeff_mod3_one (k+1)

  have hAmodD : A % D = 1 := by
    have h := GSTGraphV2HandwrittenExponentialLTE.pow4_scaled_mod_next (k+1) 1
    simpa [A, D, Nat.add_assoc] using h

  have hAdivD : A / D = c := by
    rw [hAexact]
    rw [Nat.add_mul_div_left _ _ hDpos]
    rw [Nat.div_eq_of_lt hDgt1, Nat.zero_add]

  have hAmod : A % (D * 3) = 1 + D := by
    calc
      A % (D * 3) = A % D + D * (A / D % 3) := by rw [Nat.mod_mul]
      _ = 1 + D := by rw [hAmodD, hAdivD, hcmod]; ring

  have hsmall : 1 + D < D * 3 := by omega
  have hEmod : E % (D * 3) = 1 + D := by
    calc
      E % (D * 3) = (A * P) % (D * 3) := by rw [hstep]
      _ = ((A % (D * 3)) * (P % (D * 3))) % (D * 3) := by
        rw [Nat.mul_mod]
      _ = (1 + D) % (D * 3) := by rw [hAmod, hPmod]; simp
      _ = 1 + D := Nat.mod_eq_of_lt hsmall

  have hEmodD : E % D = 1 := by
    have h := GSTGraphV2HandwrittenExponentialLTE.pow4_scaled_mod_next (k+1) m
    simpa [E, D, GSTGraphV2Production.residualEnergy,
      GSTGraphV2HandwrittenOmegaUBlock.residualEnergy,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

  have hsplit : E % (D * 3) = E % D + D * (E / D % 3) := by
    rw [Nat.mod_mul]
  rw [hEmod, hEmodD] at hsplit
  have hmul : D * 1 = D * (E / D % 3) := by
    simpa using Nat.add_left_cancel hsplit
  have hone : 1 = E / D % 3 := Nat.mul_left_cancel hDpos hmul
  simpa [E, D] using hone.symm

/-- Focused all-Nat hard-family compositor probe.

No global-last gate, finite support horizon, residual termination, or terminal
NULL principle occurs here.  The child event is reindexed to the earliest
seed-zero Happy gate, retaining its complete bad lower prefix; the same
physical width-three rectangle is then read through the exact coupled
Past/Future ledger at that gate. -/
theorem residual_level_one_origin_one_infinite_ledger
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
  let st := GSTGraphV2InfiniteControllerBridge.graphCoupledState E 3 b

  have hBaseCarryZero : (graph E 0 b).seven.carry = 0 := by
    have hmod : E % 3^b = 1 := by
      have h := GSTGraphV2HandwrittenExponentialLTE.pow4_scaled_mod_next (k+1) m
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

  have hControl : GSTV2.InfiniteBadCoupledControl (4^3) st := by
    dsimp [st]
    exact GSTGraphV2InfiniteControllerBridge.graph_infinite_bad_control
      E 3 b hBaseCarryZero hRightBad'

  have hEarliest :=
    GSTFinalResidualEarliestGateBridge.graph_exposed_tail_first_seedzero_control
      E 3 b q hBaseCarryZero hChild'
  dsimp only at hEarliest
  obtain ⟨q0, hGateDigit, hGateCarry, hBadPrefix, hCarryThreeBound⟩ := hEarliest

  have hTailOriginOne : (E / 3^b) % 3 = 1 := by
    simpa [E, b] using residual_level_one_origin_one_tail_mod_three k m hm1

  have hq0 : 1 ≤ q0 := by
    by_contra hq
    have hqz : q0 = 0 := by omega
    subst q0
    have hd0 : (E / 3^b) % 3 = 2 := by
      simpa [GSTInfiniteV2.gstDigitS] using hGateDigit
    omega

  have hInvariant : GSTV2.CoupledInvariant (4^3) st := by
    dsimp [st]
    exact GSTGraphV2InfiniteControllerBridge.graphCoupledState_invariant E 3 b

  have hLedger : GSTV2.InfiniteCoupledLedger (4^3) st :=
    GSTV2.infinite_coupled_ledger (4^3) st (by positivity) hInvariant

  have hLedgerAt := hLedger.pastSynchronized (q0+1)
  have hOrbitAt :=
    GSTGraphV2InfiniteControllerBridge.graphCoupledOrbit_exact E 3 b (q0+1)
  dsimp [st] at hLedgerAt hOrbitAt
  rw [hOrbitAt] at hLedgerAt

  have hParentBadAt := hControl.parentBadSuffix (q0+1)
  have hChildCarryAt := hControl.childCarryExact q0

  trace_state
  omega

end GSTFinalResidualInfiniteLedgerProbe