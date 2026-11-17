import GSTGraphV2InfiniteControl
import GSTU2DEventTransport

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Nonlocal GST Happy-Gate transport: exact delay certificate

The first Happy gate for 4^8 is row four, but the first for 4^11
is row ten. The exponent-three transform may delay a witness.

This refutes any attempt to prove an immediate (<= child index)
same-position Gate transport by a short potential telescope.
It does not refute delayed universal Gate existence.
-/

namespace GSTInfiniteDelayAudit

open GSTCanonicalSevenAxisBridge
open GSTU2DEventTransport

theorem child_eight_gate_at_four :
    HappyCell (carry4 (4^8) 4) (digit3 (4^8) 4) := by
  norm_num [HappyCell, carry4, digit3]

theorem parent_eleven_no_gate_through_nine :
    ∀ p : Nat, 3 ≤ p → p < 10 →
      ¬ HappyCell (carry4 (4^11) p) (digit3 (4^11) p) := by
  intro p hp hp10
  interval_cases p <;> norm_num [HappyCell, carry4, digit3]

theorem parent_eleven_first_gate_at_ten :
    HappyCell (carry4 (4^11) 10) (digit3 (4^11) 10) := by
  norm_num [HappyCell, carry4, digit3]

theorem cannot_force_gate_by_child_row :
    ∃ K p : Nat,
      8 ≤ K ∧ 3 ≤ p ∧
      HappyCell (carry4 (4^K) p) (digit3 (4^K) p) ∧
      (∀ j, 3 ≤ j → j ≤ p →
        ¬ HappyCell (carry4 (4^(K+3)) j) (digit3 (4^(K+3)) j)) := by
  refine ⟨8, 4, by decide, by decide, child_eight_gate_at_four, ?_⟩
  intro j hj hjp
  have hlt : j < 10 := by omega
  exact parent_eleven_no_gate_through_nine j hj hlt

#print axioms child_eight_gate_at_four
#print axioms parent_eleven_no_gate_through_nine
#print axioms parent_eleven_first_gate_at_ten
#print axioms cannot_force_gate_by_child_row

end GSTInfiniteDelayAudit
