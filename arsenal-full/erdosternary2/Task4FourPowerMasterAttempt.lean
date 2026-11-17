import GSTGraphV2FourPowerForcingBridge
import GSTInfiniteFourPowerNavigation

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Task4FourPowerMasterAttempt

open GSTCanonicalTailStateIso
open GSTGraphV2FourPowerForcingBridge
open GSTFourPowerOntologicalAdapter

/-- Task 4: construct the exact Graph-V2 forcing proposition.  For K >= 8
use the repaired universal four-power existence theorem; handle 5 and 6 by
exact arithmetic and discharge 7 from the explicit exception hypothesis. -/
theorem four_power_graph_forcing_attempt : FourPowerGraphForcing := by
  intro K hK5 hK7
  by_cases hK8 : 8 ≤ K
  · obtain ⟨p, hp3, hHappy⟩ :=
      GSTInfiniteFourPowerNavigation.four_power_happy_ge_three K hK8
    exact ⟨p, by omega, hHappy⟩
  · have hCases : K = 5 ∨ K = 6 ∨ K = 7 := by omega
    rcases hCases with rfl | rfl | rfl
    · refine ⟨2, by decide, ?_⟩
      norm_num [HappyCell, carry4, digit3]
    · refine ⟨2, by decide, ?_⟩
      norm_num [HappyCell, carry4, digit3]
    · exact (hK7 rfl).elim

/-- Task 4 production master via the already-green exact equivalence. -/
theorem four_power_creation_master_attempt : FourPowerCreationMaster :=
  graph_forcing_to_creation_master four_power_graph_forcing_attempt

#check four_power_graph_forcing_attempt
#check four_power_creation_master_attempt
#print axioms four_power_graph_forcing_attempt
#print axioms four_power_creation_master_attempt

end Task4FourPowerMasterAttempt
