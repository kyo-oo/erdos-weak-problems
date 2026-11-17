import GSTGraphV2FourPowerRelocation
import GSTInfiniteFourPowerNavigation
import GSTGraphV2FourPowerForcingBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2FourPowerRelocationClosure

open GSTCanonicalTailStateIso
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2FourPowerForcingBridge
open GSTFourPowerOntologicalAdapter

/-- Universal Graph-V2 relocation.  The repaired four-power navigation theorem
is stronger than the requested induction edge: for every exponent at least
8 it constructs a physical Happy row directly, so at `K+1` it supplies the
required relocated witness independently of the source row. -/
theorem four_power_happy_propagates :
    GSTGraphV2FourPowerRelocation.FourPowerHappyPropagation := by
  intro K p hK hp hHappy
  obtain ⟨q, hq3, hqHappy⟩ :=
    GSTInfiniteFourPowerNavigation.four_power_happy_ge_three (K+1) (by omega)
  refine ⟨q, by omega, ?_⟩
  simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hqHappy

/-- Exact arithmetic base at exponent five, reusing the already-kernelized
consecutive-digit overlap witness. -/
theorem four_power_happy_base_5 :
    ∃ p : Nat, 1 ≤ p ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^5) p)
        (GSTCanonicalTailStateIso.digit3 (4^5) p) := by
  obtain ⟨p, hp, hd, hn⟩ :=
    GSTGraphV2FourPowerRelocation.four_power_digit_overlap_base_5
  exact ⟨p, hp,
    (GSTGraphV2FourPowerRelocation.four_power_happy_iff_consecutive_digit_two 5 p).2
      ⟨hd, hn⟩⟩

/-- Exact arithmetic base at exponent six. -/
theorem four_power_happy_base_6 :
    ∃ p : Nat, 1 ≤ p ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^6) p)
        (GSTCanonicalTailStateIso.digit3 (4^6) p) := by
  obtain ⟨p, hp, hd, hn⟩ :=
    GSTGraphV2FourPowerRelocation.four_power_digit_overlap_base_6
  exact ⟨p, hp,
    (GSTGraphV2FourPowerRelocation.four_power_happy_iff_consecutive_digit_two 6 p).2
      ⟨hd, hn⟩⟩

/-- Exact arithmetic induction base at exponent eight. -/
theorem four_power_happy_base_8 :
    ∃ p : Nat, 1 ≤ p ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^8) p)
        (GSTCanonicalTailStateIso.digit3 (4^8) p) := by
  obtain ⟨p, hp, hd, hn⟩ :=
    GSTGraphV2FourPowerRelocation.four_power_digit_overlap_base_8
  exact ⟨p, hp,
    (GSTGraphV2FourPowerRelocation.four_power_happy_iff_consecutive_digit_two 8 p).2
      ⟨hd, hn⟩⟩

/-- All exponents from eight onward have a physical Happy witness.  This is
exactly the induction domain required by `FourPowerGraphForcing`; the repaired
three-step navigation theorem supplies the witness with the stronger bound
`3 ≤ p`. -/
theorem four_power_happy_all_from_eight
    (K : Nat) (hK : 8 ≤ K) :
    ∃ p : Nat, 1 ≤ p ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p) := by
  obtain ⟨p, hp3, hHappy⟩ :=
    GSTInfiniteFourPowerNavigation.four_power_happy_ge_three K hK
  refine ⟨p, by omega, ?_⟩
  simpa [GSTCanonicalTailStateIso.HappyCell,
    GSTCanonicalTailStateIso.carry4,
    GSTCanonicalTailStateIso.digit3] using hHappy

/-- Full exception-aware Graph-V2 four-power forcing theorem. -/
theorem four_power_graph_forcing :
    GSTGraphV2FourPowerForcingBridge.FourPowerGraphForcing := by
  intro K hK5 hK7
  by_cases hK8 : 8 ≤ K
  · exact four_power_happy_all_from_eight K hK8
  · have hCases : K = 5 ∨ K = 6 ∨ K = 7 := by omega
    rcases hCases with rfl | rfl | rfl
    · exact four_power_happy_base_5
    · exact four_power_happy_base_6
    · exact (hK7 rfl).elim

/-- Production creation master obtained only through the already-green exact
Graph-V2 equivalence; the quarantined historical chain is not used. -/
theorem four_power_creation_master :
    GSTFourPowerOntologicalAdapter.FourPowerCreationMaster :=
  GSTGraphV2FourPowerForcingBridge.graph_forcing_to_creation_master
    four_power_graph_forcing

#check four_power_happy_propagates
#check four_power_graph_forcing
#check four_power_creation_master
#print axioms GSTInfiniteFourPowerNavigation.power_three_step_collision
#print axioms GSTInfiniteFourPowerNavigation.four_power_happy_ge_three
#print axioms four_power_happy_propagates
#print axioms four_power_happy_base_5
#print axioms four_power_happy_base_6
#print axioms four_power_happy_base_8
#print axioms four_power_happy_all_from_eight
#print axioms four_power_graph_forcing
#print axioms four_power_creation_master

end GSTGraphV2FourPowerRelocationClosure
