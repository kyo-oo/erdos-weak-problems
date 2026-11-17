import GSTGraphV2InfiniteControllerBridge
import GSTPerfectPowerTailNavigation
import GSTGraphV2HandwrittenOmegaUBlock
import GSTU2DSharpCrossingBlock

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFinalPrefixOneStep6Infinite

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTU2DExactCrossingCharge
open GSTGraphV2InfiniteControl
open GSTGraphV2InfiniteControllerBridge
open GSTGraphV2HandwrittenOmegaUBlock
open GSTPerfectPowerTailNavigation

private def infE (s n : Nat) : Nat := residualEnergy s 1 n
private def infN (s : Nat) : Nat := residualWidth s
private def infB (s : Nat) : Nat := s + 2

/-- The canonical child starts the all-depth controller with the true zero carry. -/
theorem infinite_base_carry_zero
    (s n : Nat) (hs : 1 ≤ s) :
    (graph (infE s n) 0 (infB s)).seven.carry = 0 := by
  let E := infE s n
  let b := infB s
  let T := canonicalTail (s+1) n
  have hE : E = 1 + 3^b * T := by
    have h := canonical_tail_decomposition (s+1) n
    simpa [E, b, T, infE, infB, residualEnergy, Nat.add_assoc] using h
  have hb : 1 < 3^b := by
    have h9 : 9 ≤ 3^b := by
      rw [show (9 : Nat) = 3^2 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by dsimp [b, infB]; omega)
    omega
  have hmod : E % 3^b = 1 := by
    rw [hE]
    have hmul : (3^b * T) % 3^b = 0 :=
      Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right _ _)
    calc
      (1 + 3^b * T) % 3^b = (1 % 3^b + (3^b * T) % 3^b) % 3^b := Nat.add_mod _ _ _
      _ = (1 % 3^b) % 3^b := by rw [hmul, Nat.add_zero]
      _ = 1 % 3^b := Nat.mod_mod_of_dvd _ (dvd_refl (3^b))
      _ = 1 := Nat.mod_eq_of_lt hb
  have hc : carry4 E b = 0 := by
    unfold carry4
    rw [hmod]
    apply Nat.div_eq_of_lt
    have hb27 : 27 ≤ 3^b := by
      rw [show (27 : Nat) = 3^3 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by dsimp [b, infB]; omega)
    omega
  simpa [E, b, infE, infB, graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hc

/-- All-depth parent badness is packaged once as one InfiniteBadCoupledControl. -/
theorem canonical_infinite_bad_control
    (s n : Nat) (hs : 1 ≤ s)
    (hRightBad : ∀ j,
      ¬ HappyCell
        (graph (infE s n) (infN s) (infB s + j)).seven.carry
        (graph (infE s n) (infN s) (infB s + j)).seven.digit) :
    GSTV2.InfiniteBadCoupledControl
      (4^(infN s)) (graphCoupledState (infE s n) (infN s) (infB s)) := by
  apply graph_infinite_bad_control
  · exact infinite_base_carry_zero s n hs
  · intro j
    exact hRightBad j

/-- The same canonical physical rectangle carries the stronger all-depth Past/Future ledger. -/
theorem canonical_infinite_ledger
    (s n : Nat) :
    GSTV2.InfiniteCoupledLedger
      (4^(infN s)) (graphCoupledState (infE s n) (infN s) (infB s)) := by
  apply GSTV2.infinite_coupled_ledger
  · positivity
  · exact graphCoupledState_invariant (infE s n) (infN s) (infB s)

/-- Atomic all-depth synchronization: controller orbit equals the physical graph state at every K. -/
theorem canonical_controller_graph_all_depth
    (s n : Nat) : ∀ K,
    GSTV2.coupledOrbit (4^(infN s))
        (graphCoupledState (infE s n) (infN s) (infB s)) K =
      graphCoupledState (infE s n) (infN s) (infB s + K) := by
  intro K
  exact graphCoupledOrbit_exact (infE s n) (infN s) (infB s) K

/-- Atomic all-depth synchronization law: no terminal height and no bounded horizon. -/
theorem canonical_past_future_synchronized_all_depth
    (s n : Nat) : ∀ K,
    let initial := graphCoupledState (infE s n) (infN s) (infB s)
    initial.parentPast (4^(infN s)) K +
        3^K * (GSTV2.coupledOrbit (4^(infN s)) initial K).childResidue =
      initial.childResidue + (4^(infN s)) * initial.childPast K := by
  intro K
  exact (canonical_infinite_ledger s n).pastSynchronized K

/-- The exact Step-6 linear combination of crossing and mixed charge has no
microscopic SURVIVE source. -/
theorem cross_mixed_survive_cancel
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    2 * crossDensity C d - 3 * mixedDensity C d =
      2 *
        (digitPotential (outDigit C d) - 4 * digitPotential d +
          carryPotentialX C - 3 * carryPotentialX (nextCarry C d)) -
      3 *
        (infoPotential (outDigit C d) - infoPotential d +
          7 * carryPotential C - 21 * carryPotential (nextCarry C d)) := by
  rw [crossDensity, mixed_cell_emergence C d hC hd]
  ring

/-- Horizontal potential left after the exact `2·cross - 3·mixed` source
cancellation. -/
def controllerDigitPotential (d : Nat) : Int :=
  2 * digitPotential d - 3 * infoPotential d

/-- Vertical carry potential left after the same cancellation. -/
def controllerCarryPotential (C : Nat) : Int :=
  2 * carryPotentialX C - 21 * carryPotential C

/-- The cancelled local charge is a genuine two-direction controller
divergence plus one retained BIG1 packet.  The packet is explicit rather than
silently discarded. -/
theorem cross_mixed_controller_divergence
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    2 * crossDensity C d - 3 * mixedDensity C d =
      controllerDigitPotential (outDigit C d) -
        4 * controllerDigitPotential d +
      controllerCarryPotential C -
        3 * controllerCarryPotential (nextCarry C d) -
      9 * infoPotential d := by
  rw [cross_mixed_survive_cancel C d hC hd]
  unfold controllerDigitPotential controllerCarryPotential
  ring

/-- Reverse-base-four mixed charge, in the same physical orientation as
`reverseCrossCode`. -/
def reverseMixedCode (C d : Nat → Nat) : Nat → Int
  | 0 => 0
  | N+1 => 4 * reverseMixedCode C d N + mixedDensity (C N) (d N)

/-- Reverse-base-four retained BIG1 packet. -/
def reverseInfoCode (d : Nat → Nat) : Nat → Int
  | 0 => 0
  | N+1 => 4 * reverseInfoCode d N + infoPotential (d N)

/-- Reverse-base-four controller carry potential. -/
def reverseControllerCarryCode (C : Nat → Nat) : Nat → Int
  | 0 => 0
  | N+1 =>
      4 * reverseControllerCarryCode C N + controllerCarryPotential (C N)

/-- Exact row telescope of the source-cancelled Step-6 charge.  No SURVIVE
term remains: only endpoint information, the vertical controller derivative,
and the explicitly retained BIG1 packet survive. -/
theorem reverse_cross_mixed_controller_exact
    (C Cnext d : Nat → Nat) : ∀ N : Nat,
    (∀ t, t < N → C t < 4) →
    (∀ t, t < N → d t < 3) →
    (∀ t, t < N → outDigit (C t) (d t) = d (t+1)) →
    (∀ t, t < N → nextCarry (C t) (d t) = Cnext t) →
    2 * reverseCrossCode C d N - 3 * reverseMixedCode C d N =
      controllerDigitPotential (d N) -
        (((4^N : Nat) : Int)) * controllerDigitPotential (d 0) +
      reverseControllerCarryCode C N -
        3 * reverseControllerCarryCode Cnext N -
      9 * reverseInfoCode d N := by
  intro N
  induction N with
  | zero =>
      intro hC hd hout hnext
      simp [reverseCrossCode, reverseMixedCode, reverseInfoCode,
        reverseControllerCarryCode]
  | succ N ih =>
      intro hC hd hout hnext
      have ih' := ih
        (fun t ht => hC t (by omega))
        (fun t ht => hd t (by omega))
        (fun t ht => hout t (by omega))
        (fun t ht => hnext t (by omega))
      have hlocal := cross_mixed_controller_divergence
        (C N) (d N) (hC N (by omega)) (hd N (by omega))
      have houtN := hout N (by omega)
      have hnextN := hnext N (by omega)
      rw [reverseCrossCode, reverseMixedCode, reverseInfoCode,
        reverseControllerCarryCode, reverseControllerCarryCode]
      calc
        2 * (4 * reverseCrossCode C d N + crossDensity (C N) (d N)) -
            3 * (4 * reverseMixedCode C d N + mixedDensity (C N) (d N)) =
          4 * (2 * reverseCrossCode C d N - 3 * reverseMixedCode C d N) +
            (2 * crossDensity (C N) (d N) - 3 * mixedDensity (C N) (d N)) := by
              ring
        _ = _ := by
          rw [ih', hlocal, houtN, hnextN, Nat.pow_succ]
          push_cast
          ring

/-- Base-three weighted mixed prefix, aligned exactly with
`weightedCrossPrefix`. -/
def weightedMixedPrefix
    (C d : Nat → Nat → Nat) (N : Nat) : Nat → Int
  | 0 => 0
  | K+1 =>
      weightedMixedPrefix C d N K +
        (((3^K : Nat) : Int)) *
          reverseMixedCode (fun t => C t K) (fun t => d t K) N

/-- Full finite rectangle telescope of the all-depth Step-6 cancelled charge.
The vertical controller derivative cancels exactly under the physical `3^p`
weights.  No terminal row, support horizon, or SURVIVE source is used. -/
theorem weighted_cross_mixed_controller_exact
    (C d : Nat → Nat → Nat) (N : Nat) : ∀ K : Nat,
    (∀ t p, t < N → p < K →
      C t p < 4 ∧ d t p < 3 ∧
      outDigit (C t p) (d t p) = d (t+1) p ∧
      nextCarry (C t p) (d t p) = C t (p+1)) →
    2 * weightedCrossPrefix C d N K -
        3 * weightedMixedPrefix C d N K =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (controllerDigitPotential (d N p) -
            (((4^N : Nat) : Int)) * controllerDigitPotential (d 0 p) -
            9 * reverseInfoCode (fun t => d t p) N)) +
      reverseControllerCarryCode (fun t => C t 0) N -
        (((3^K : Nat) : Int)) *
          reverseControllerCarryCode (fun t => C t K) N := by
  intro K
  induction K with
  | zero =>
      intro hcell
      simp [weightedCrossPrefix, weightedMixedPrefix,
        reverseControllerCarryCode]
  | succ K ih =>
      intro hcell
      have hprefix : ∀ t p, t < N → p < K →
          C t p < 4 ∧ d t p < 3 ∧
          outDigit (C t p) (d t p) = d (t+1) p ∧
          nextCarry (C t p) (d t p) = C t (p+1) := by
        intro t p ht hp
        exact hcell t p ht (by omega)
      have ih' := ih hprefix
      have hrow := reverse_cross_mixed_controller_exact
        (fun t => C t K) (fun t => C t (K+1)) (fun t => d t K) N
        (fun t ht => (hcell t K ht (by omega)).1)
        (fun t ht => (hcell t K ht (by omega)).2.1)
        (fun t ht => (hcell t K ht (by omega)).2.2.1)
        (fun t ht => (hcell t K ht (by omega)).2.2.2)
      rw [weightedCrossPrefix, weightedMixedPrefix, Finset.sum_range_succ]
      calc
        2 * (weightedCrossPrefix C d N K +
              (((3^K : Nat) : Int)) *
                reverseCrossCode (fun t => C t K) (fun t => d t K) N) -
            3 * (weightedMixedPrefix C d N K +
              (((3^K : Nat) : Int)) *
                reverseMixedCode (fun t => C t K) (fun t => d t K) N) =
          (2 * weightedCrossPrefix C d N K - 3 * weightedMixedPrefix C d N K) +
            (((3^K : Nat) : Int)) *
              (2 * reverseCrossCode (fun t => C t K) (fun t => d t K) N -
                3 * reverseMixedCode (fun t => C t K) (fun t => d t K) N) := by
              ring
        _ = _ := by
          rw [ih', hrow, Nat.pow_succ]
          push_cast
          ring

#check infinite_base_carry_zero
#check canonical_infinite_bad_control
#check canonical_infinite_ledger
#check canonical_controller_graph_all_depth
#check canonical_past_future_synchronized_all_depth
#check cross_mixed_survive_cancel
#check cross_mixed_controller_divergence
#check reverse_cross_mixed_controller_exact
#check weighted_cross_mixed_controller_exact
#print axioms infinite_base_carry_zero
#print axioms canonical_infinite_bad_control
#print axioms canonical_infinite_ledger
#print axioms canonical_controller_graph_all_depth
#print axioms canonical_past_future_synchronized_all_depth
#print axioms cross_mixed_survive_cancel
#print axioms cross_mixed_controller_divergence
#print axioms reverse_cross_mixed_controller_exact
#print axioms weighted_cross_mixed_controller_exact

end GSTFinalPrefixOneStep6Infinite