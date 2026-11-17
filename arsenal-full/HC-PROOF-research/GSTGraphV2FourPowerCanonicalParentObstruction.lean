import GSTGraphV2FourPowerResidueObstruction
import GSTGraphV2CanonicalEscape
import GSTGraphV2CanonicalPhaseWaveProbe
import GSTGraphV2PerfectPowerAncestry

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2FourPowerCanonicalParentObstruction

open GSTCanonicalSevenAxisBridge
open GSTGraphV2InfiniteControl
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2PerfectPowerAncestry
open GSTGraphV2CanonicalEscape
open GSTGraphV2CanonicalPhaseWaveProbe
open GSTGraphV2SeededPrefix
open GSTU2DEventTransport

/-- Global no-Happy on the literal unit-energy power column at exponent
`3^(s+1)*n + 3^s` transports exactly to the all-depth seeded bad trace on the
canonical parent tail. -/
theorem pure_power_right_edge_no_happy_to_parent_bad
    (s n : Nat) (hs : 1 ≤ s)
    (hNo : ¬ ∃ q : Nat, 1 ≤ q ∧
      HappyCell (graph 1 (3^(s+1) * n + 3^s) q).seven.carry
        (graph 1 (3^(s+1) * n + 3^s) q).seven.digit) :
    ∀ j : Nat, ¬ SeedHappy 1 1 (canonicalParentTail s n) j := by
  intro j hSeed
  apply hNo
  refine ⟨s + 2 + j, by omega, ?_⟩
  have hCanonical :
      HappyCell
        (graph (4^(3^(s+1) * n)) (3^s) (s + 2 + j)).seven.carry
        (graph (4^(3^(s+1) * n)) (3^s) (s + 2 + j)).seven.digit :=
    (canonical_right_seed_adapter s n j hs).2 hSeed
  exact (power_origin_happy_iff (3^(s+1) * n) (3^s) (s + 2 + j)).1 hCanonical

/-- Consequently, on every canonical right-edge exponent, global physical
badness forces the exact phase-wave residue obstruction on the origin tail. -/
theorem pure_power_right_edge_bad_forbids_origin_mod9_three_four
    (s n : Nat) (hs : 2 ≤ s)
    (hNo : ¬ ∃ q : Nat, 1 ≤ q ∧
      HappyCell (graph 1 (3^(s+1) * n + 3^s) q).seven.carry
        (graph 1 (3^(s+1) * n + 3^s) q).seven.digit) :
    n % 9 ≠ 3 ∧ n % 9 ≠ 4 := by
  apply canonical_parent_bad_forbids_mod9_three_four s n hs
  exact pure_power_right_edge_no_happy_to_parent_bad s n (by omega) hNo


/-! ## Exact surviving origin phase sector -/

/-- Under global right-edge badness, the origin phase is forced into the exact
seven-class complement of residues three and four modulo nine. -/
theorem pure_power_right_edge_bad_origin_mod9_survivor
    (s n : Nat) (hs : 2 ≤ s)
    (hNo : ¬ ∃ q : Nat, 1 ≤ q ∧
      HappyCell (graph 1 (3^(s+1) * n + 3^s) q).seven.carry
        (graph 1 (3^(s+1) * n + 3^s) q).seven.digit) :
    n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨
    n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by
  have hobs :=
    pure_power_right_edge_bad_forbids_origin_mod9_three_four s n hs hNo
  have hr : n % 9 < 9 := Nat.mod_lt _ (by norm_num)
  omega


#check pure_power_right_edge_no_happy_to_parent_bad
#check pure_power_right_edge_bad_forbids_origin_mod9_three_four
#check pure_power_right_edge_bad_origin_mod9_survivor
#print axioms pure_power_right_edge_no_happy_to_parent_bad
#print axioms pure_power_right_edge_bad_forbids_origin_mod9_three_four
#print axioms pure_power_right_edge_bad_origin_mod9_survivor

end GSTGraphV2FourPowerCanonicalParentObstruction
