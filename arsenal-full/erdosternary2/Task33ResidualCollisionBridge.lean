import GSTFinalResidualChildConnector
import GSTFinalResidualCollision

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Task33ResidualCollisionBridge

open GSTCanonicalSevenAxisBridge
open GSTGraphV2InfiniteControl
open GSTU2DEventTransport
open GSTGraphV2HandwrittenOmegaUBlock

/-- The finite level-one residual collision closes directly from an absolute
all-bad parent sheet.  This is the monolith-free hard origin-trit-one branch:
no Omega-state or infinite-trace definition is used. -/
theorem residual_level_one_origin_one_parent_bad_impossible
    (k m : Nat) (hk : 1 ≤ k) (hm : 1 ≤ m) (hm1 : m % 3 = 1)
    (hchild : GSTNavigationWitness (gstNavigationConstant (1+k) m))
    (hNoParent : ¬ ∃ p : Nat, 1 ≤ p ∧
      HappyCell
        (graph 1 (residualParentExponent 1 k m) p).seven.carry
        (graph 1 (residualParentExponent 1 k m) p).seven.digit) :
    False := by
  obtain ⟨q, hChild⟩ :=
    GSTFinalResidualChildConnector.residual_child_witness_to_left_happy
      1 k m (by decide) hk hchild

  have hRightBad : ∀ j, ¬ HappyCell
      (graph (residualEnergy 1 k m) 3 (k+2+j)).seven.carry
      (graph (residualEnergy 1 k m) 3 (k+2+j)).seven.digit := by
    intro j hRight
    apply hNoParent
    refine ⟨k+2+j, by omega, ?_⟩
    have hResidual : HappyCell
        (graph (residualEnergy 1 k m) (residualWidth 1) (k+2+j)).seven.carry
        (graph (residualEnergy 1 k m) (residualWidth 1) (k+2+j)).seven.digit := by
      simpa [residualWidth] using hRight
    exact (residual_parent_happy_iff 1 k m (k+2+j)).1 hResidual

  apply GSTFinalResidualCollision.residual_level_one_origin_one_collision
    k m q hk hm hm1
  · simpa [GSTGraphV2Production.residualEnergy,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hChild
  · intro j
    simpa [GSTGraphV2Production.residualEnergy,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hRightBad j

#check residual_level_one_origin_one_parent_bad_impossible
#print axioms residual_level_one_origin_one_parent_bad_impossible

end Task33ResidualCollisionBridge
