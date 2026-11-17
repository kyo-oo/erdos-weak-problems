import GSTFinalPrefixOneStep6Boundary

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GPT56Step6SignClosure

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2InfiniteControllerBridge
open GSTU2DExactCrossingCharge
open GSTPerfectPowerTailNavigation
open GSTGraphV2HandwrittenOmegaUBlock
open GSTFinalPrefixOneStep6Infinite
open GSTFinalPrefixOneStep6Boundary

private def signC (s n : Nat) : Nat → Nat → Nat :=
  fun t p => (graph (residualEnergy s 1 n) t (s + 2 + p)).seven.carry

private def signD (s n : Nat) : Nat → Nat → Nat :=
  fun t p => (graph (residualEnergy s 1 n) t (s + 2 + p)).seven.digit

/-- Isolated all-depth Step-6 sign seam. -/
theorem step6_sign_closure
    (s n q : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hRightBad : ∀ j,
      ¬ HappyCell
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.carry
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.digit) :
    weightedCrossPrefix (signC s n) (signD s n)
      (residualWidth s) (q+1) ≤ 0 := by
  let E := residualEnergy s 1 n
  let N := residualWidth s
  let b := s + 2

  -- Keep the controller construction on the public canonical graph state.
  -- This avoids leaking the private infE/infN/infB implementation aliases
  -- from GSTFinalPrefixOneStep6Infinite into a downstream theorem statement.
  have hBaseCarryZero : (graph E 0 b).seven.carry = 0 := by
    let T := canonicalTail (s+1) n
    have hE : E = 1 + 3^b * T := by
      have h := canonical_tail_decomposition (s+1) n
      simpa [E, b, T, residualEnergy, Nat.add_assoc] using h
    have hb : 1 < 3^b := by
      have h9 : 9 ≤ 3^b := by
        rw [show (9 : Nat) = 3^2 by decide]
        exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by dsimp [b]; omega)
      omega
    have hmod : E % 3^b = 1 := by
      rw [hE]
      have hmul : (3^b * T) % 3^b = 0 :=
        Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right _ _)
      calc
        (1 + 3^b * T) % 3^b =
            (1 % 3^b + (3^b * T) % 3^b) % 3^b := Nat.add_mod _ _ _
        _ = (1 % 3^b) % 3^b := by rw [hmul, Nat.add_zero]
        _ = 1 % 3^b := Nat.mod_mod_of_dvd _ (dvd_refl (3^b))
        _ = 1 := Nat.mod_eq_of_lt hb
    have hc : carry4 E b = 0 := by
      unfold carry4
      rw [hmod]
      apply Nat.div_eq_of_lt
      have hb27 : 27 ≤ 3^b := by
        rw [show (27 : Nat) = 3^3 by decide]
        exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by dsimp [b]; omega)
      omega
    simpa [E, b, graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hc

  have hController :
      GSTV2.InfiniteBadCoupledControl (4^N) (graphCoupledState E N b) := by
    apply graph_infinite_bad_control E N b hBaseCarryZero
    intro j
    simpa [E, N, b, Nat.add_assoc] using hRightBad j

  have hLedger :
      GSTV2.InfiniteCoupledLedger (4^N) (graphCoupledState E N b) := by
    apply GSTV2.infinite_coupled_ledger
    · positivity
    · exact graphCoupledState_invariant E N b

  have hAllDepth : ∀ K,
      GSTV2.coupledOrbit (4^N) (graphCoupledState E N b) K =
        graphCoupledState E N (b+K) := by
    intro K
    exact graphCoupledOrbit_exact E N b K

  have hPastFuture : ∀ K,
      let initial := graphCoupledState E N b
      initial.parentPast (4^N) K +
          3^K * (GSTV2.coupledOrbit (4^N) initial K).childResidue =
        initial.childResidue + (4^N) * initial.childPast K := by
    intro K
    exact hLedger.pastSynchronized K

  have hCancelled := canonical_controller_boundary_identification
    s n (q+1) hs hn hRightBad
  have hRight := right_boundary_weighted_sum_nonpositive
    s n (q+1) hRightBad
  dsimp [signC, signD, E, N, b] at hCancelled hRight ⊢
  trace_state
  omega

#check step6_sign_closure
#print axioms step6_sign_closure

end GPT56Step6SignClosure
