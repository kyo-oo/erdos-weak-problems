import GSTGraphV2FourPowerRelocation
import GSTInfiniteFourPowerNavigation

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Task33FourPowerPropagationAttempt

open GSTCanonicalTailStateIso
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl

/-- Compiler-driven Task 3.3 adapter.  The repaired universal four-power
existence theorem is stronger than the requested propagation edge: at K+1 it
constructs a physical Happy witness independently of the supplied source row. -/
theorem four_power_happy_propagates_attempt :
    GSTGraphV2FourPowerRelocation.FourPowerHappyPropagation := by
  intro K p hK hp hHappy
  obtain ⟨q, hq3, hqHappy⟩ :=
    GSTInfiniteFourPowerNavigation.four_power_happy_ge_three (K+1) (by omega)
  refine ⟨q, by omega, ?_⟩
  simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hqHappy

#check four_power_happy_propagates_attempt
#print axioms four_power_happy_propagates_attempt

end Task33FourPowerPropagationAttempt
