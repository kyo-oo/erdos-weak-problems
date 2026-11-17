import Task33FreshPowerPropagation
import GSTGraphV2FourPowerResidueObstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Task33FreshDirectRelocation

open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2FourPowerRelocation

/-- Fresh positive Task 3.3 branch.  For the two target exponent residue
classes detected by the exact LTE period at row two, the relocated witness is
constructed literally as `q = 2`.  The source Happy witness is retained in
the statement so this theorem is an honest conditional fragment of the exact
propagation edge, rather than a failure/obstruction reformulation. -/
theorem fresh_direct_relocated_q_two_of_target_mod9_five_six
    (K p : Nat)
    (hK : 8 ≤ K)
    (hp : 1 ≤ p)
    (hSource :
      HappyCell
        (graph 1 K p).seven.carry
        (graph 1 K p).seven.digit)
    (hres : (K+1) % 9 = 5 ∨ (K+1) % 9 = 6) :
    ∃ q : Nat, 1 ≤ q ∧
      HappyCell
        (graph 1 (K+1) q).seven.carry
        (graph 1 (K+1) q).seven.digit := by
  refine ⟨2, by norm_num, ?_⟩
  have hov :=
    GSTGraphV2FourPowerResidueObstruction.row_two_overlap_of_mod9_five_or_six
      (K+1) hres
  exact
    (GSTGraphV2FourPowerRelocation.graph_happy_iff_consecutive_digit_two
      1 (K+1) 2).2 (by
        simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hov)

#check fresh_direct_relocated_q_two_of_target_mod9_five_six
#print axioms fresh_direct_relocated_q_two_of_target_mod9_five_six

end Task33FreshDirectRelocation
