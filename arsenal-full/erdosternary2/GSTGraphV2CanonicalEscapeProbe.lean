import GSTGraphV2CanonicalInfiniteCycle
import GSTGraphV2CanonicalDescentOntology
import GSTGraphV2CanonicalRenormalization
import GSTGraphV2CanonicalPhaseSteering
import GSTGraphV2CanonicalSheetTranslation

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2CanonicalEscapeProbe

open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2SeededPrefix
open GSTGraphV2CanonicalEscape
open GSTGraphV2CanonicalInfiniteCycle
open GSTGraphV2CanonicalDescentOntology
open GSTGraphV2CanonicalRenormalization
open GSTGraphV2CanonicalPhaseSteering
open GSTGraphV2CanonicalSheetTranslation
open GSTGraphV2InfiniteControllerBridge
open GSTV2

/-- RED probe for the exact remaining canonical escape implication. Every
available live Graph-V2 packet is exposed at an arbitrary origin cutoff K.
The probe now also carries exact phase steering and canonical sheet-translation
laws, so the residual is tested inside the actual renormalized spacetime.
This checkpoint intentionally remains RED until the regeneration seam closes. -/
theorem canonical_bad_parent_forces_unbounded_origin_support_probe
    (s n q : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hChild : HappyCell
      (graph (canonicalEnergy s n) 0 (s+2+q)).seven.carry
      (graph (canonicalEnergy s n) 0 (s+2+q)).seven.digit)
    (hRightBad : ∀ j, ¬ HappyCell
      (graph (canonicalEnergy s n) (canonicalWidth s) (s+2+j)).seven.carry
      (graph (canonicalEnergy s n) (canonicalWidth s) (s+2+j)).seven.digit) :
    ∀ K : Nat, ∃ r : Nat,
      K ≤ r ∧ (n / 3^r) % 3 ≠ 0 := by
  let E := canonicalEnergy s n
  let N := canonicalWidth s
  let b := s + 2
  let initial := graphCoupledState E N b

  have hChildSeed :
      SeedHappy 0 0 (canonicalChildTail s n) q := by
    apply (canonical_left_seed_adapter s n q hs).mp
    simpa [E, b, canonicalEnergy, Nat.add_assoc] using hChild

  have hRightSeed : ∀ j,
      ¬ SeedHappy 1 1 (canonicalParentTail s n) j := by
    intro j hSeed
    apply hRightBad j
    have hGraph := (canonical_right_seed_adapter s n j hs).mpr hSeed
    simpa [E, N, b, canonicalEnergy, canonicalWidth, Nat.add_assoc] using hGraph

  have hCut :=
    canonical_graphCoupledState_cut_packet s n hs

  have hPhaseDigit := canonical_right_digit_cut_phase s n hs
  have hPhaseZero := fun h0 : n % 3 = 0 =>
    canonical_right_phase_zero_next_seed s n hs h0
  have hPhaseOne := fun h1 : n % 3 = 1 =>
    canonical_right_phase_one_next_seed s n hs h1
  have hPhaseTwo := fun h2 : n % 3 = 2 =>
    canonical_right_phase_two_next_seed s n hs h2

  have hControl :
      InfiniteBadCoupledControl (4^N) initial := by
    dsimp [initial]
    apply graph_infinite_bad_control
    · simpa [E, b, canonicalEnergy] using canonical_base_carry_zero s n hs
    · intro j
      simpa [E, N, b, Nat.add_assoc] using hRightBad j

  have hGate :
      LatentGateTransfer (4^N) initial q := by
    dsimp [initial]
    apply graph_child_happy_latent_transfer
    · simpa [E, b, canonicalEnergy] using canonical_base_carry_zero s n hs
    · intro j
      simpa [E, N, b, Nat.add_assoc] using hRightBad j
    · simpa [E, b, Nat.add_assoc] using hChild

  have hLedger :
      InfiniteCoupledLedger (4^N) initial := by
    apply infinite_coupled_ledger
    · positivity
    · dsimp [initial]
      exact graphCoupledState_invariant E N b

  have hOrbit : ∀ j,
      coupledOrbit (4^N) initial j =
        graphCoupledState E N (b+j) := by
    dsimp [initial]
    exact graphCoupledOrbit_exact E N b

  have hKnownPrefix :
      n % 3^(q+1) ≠ 0 :=
    canonical_origin_packet_nonzero
      s n q hs hChildSeed hRightSeed

  intro K

  have hSplit :
      n = n % 3^K + 3^K * (n / 3^K) := by
    simpa using (Nat.mod_add_div n (3^K)).symm

  have hRenormalized :=
    canonicalTail_power_block_recurrence
      (s+1) (n % 3^K) (n / 3^K) K
  rw [← hSplit] at hRenormalized

  have hCanonicalChildTailK :=
    canonical_controller_childTail_cut_exact s n K

  have hControllerChildTailK := hControl.coupled.childTailExact K
  have hLedgerK := hLedger.pastSynchronized K
  have hInvariantK := hControl.coupled.invariantAll K
  have hBadSuffixK := hControl.parentBadSuffix K
  have hOrbitK := hOrbit K

  dsimp [E, N, b, initial] at hCut hControl hGate hLedgerK
    hInvariantK hBadSuffixK hOrbitK hRenormalized
  trace_state
  omega

#check canonical_bad_parent_forces_unbounded_origin_support_probe

end GSTGraphV2CanonicalEscapeProbe