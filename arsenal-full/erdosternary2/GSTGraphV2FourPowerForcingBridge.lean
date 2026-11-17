import GSTFourPowerOntologicalAdapter
import GSTFourPowerDirectHappyBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2FourPowerForcingBridge

open GSTCanonicalTailStateIso
open GSTFourPowerOntologicalAdapter
open GSTFourPowerDirectExistence
open GSTFourPowerDirectHappyBridge

/-- Literal Graph-V2 form of the remaining four-power forcing law.  This is
the exact physical target: every relevant power sheet contains a Happy cell
above row zero. -/
def FourPowerGraphForcing : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 →
    ∃ p : Nat, 1 ≤ p ∧
      HappyCell (carry4 (4^K) p) (digit3 (4^K) p)

/-- The fresh direct arithmetic existence theorem produces the literal
Graph-V2 physical forcing law without any navigation or N-wave dependency. -/
theorem direct_existence_to_graph_forcing
    (hDirect : FourPowerDirectExistence) :
    FourPowerGraphForcing := by
  intro K hK h7
  exact directExistence_to_physical_happy_forcing hDirect K hK h7

/-- A physical Happy cell gives the historical creation certificate directly;
the information is retained in the carry-zero/carry-three realization. -/
theorem graph_forcing_to_creation_master
    (hGraph : FourPowerGraphForcing) :
    FourPowerCreationMaster := by
  intro K hK5 hK7
  obtain ⟨p, hp, hd, hC⟩ := hGraph K hK5 hK7
  refine ⟨p, hp, ?_, ?_⟩
  · simpa [digit3] using hd
  · left
    change carry4 (4^K) p % 3 = 0
    rcases hC with h0 | h3
    · simp [h0]
    · simp [h3]

/-- Conversely, the creation master produces a physical Graph-V2 Happy cell.
This records equivalence with the historical certificate layer, but the fresh
production proof itself enters through `direct_existence_to_graph_forcing`. -/
theorem creation_master_to_graph_forcing
    (hMaster : FourPowerCreationMaster) :
    FourPowerGraphForcing := by
  intro K hK5 hK7
  obtain ⟨p, hd, hC⟩ :=
    creation_certificate_to_navigation (4^K) (hMaster K hK5 hK7)
  have hp : 1 ≤ p := by
    cases p with
    | zero =>
        simp [digit3, Nat.pow_mod] at hd
    | succ p => omega
  exact ⟨p, hp, hd, hC⟩

theorem graph_forcing_iff_creation_master :
    FourPowerGraphForcing ↔ FourPowerCreationMaster := by
  exact ⟨graph_forcing_to_creation_master,
    creation_master_to_graph_forcing⟩

#check direct_existence_to_graph_forcing
#check GSTFourPowerDirectHappyBridge.four_power_happy_propagates
#check graph_forcing_to_creation_master
#check creation_master_to_graph_forcing
#print axioms direct_existence_to_graph_forcing
#print axioms GSTFourPowerDirectHappyBridge.four_power_happy_propagates
#print axioms graph_forcing_iff_creation_master

end GSTGraphV2FourPowerForcingBridge
