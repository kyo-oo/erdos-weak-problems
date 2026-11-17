import GSTFourPowerAffinePeelClassifier

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineTwoTritClassifier

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineExponentPeel
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerAffinePeelClassifier

/-- After exponent branch `0`, the next exponent trit chooses exactly between
    channels `0` and `1`; trit `2` is already a common-two success. -/
theorem noCommonTwo_three_mul_second_iff (q : Nat) :
    (¬ CommonTwo (3*q)) ↔
      (q % 3 = 0 ∧ BadChannel 0 (tail3 (peel0 (affineOrbit q)))) ∨
      (q % 3 = 1 ∧ BadChannel 1 (tail3 (peel0 (affineOrbit q)))) := by
  rw [noCommonTwo_three_mul_iff, badChannel_zero_iff,
    lowDigit_peel0_affineOrbit]

/-- After exponent branch `1`, all three second trits survive, selecting
    channels `0`, `1`, and `3`. -/
theorem noCommonTwo_three_mul_add_one_second_iff (q : Nat) :
    (¬ CommonTwo (3*q+1)) ↔
      (q % 3 = 0 ∧ BadChannel 0 (tail3 (peel1 (affineOrbit q)))) ∨
      (q % 3 = 1 ∧ BadChannel 1 (tail3 (peel1 (affineOrbit q)))) ∨
      (q % 3 = 2 ∧ BadChannel 3 (tail3 (peel1 (affineOrbit q)))) := by
  rw [noCommonTwo_three_mul_add_one_iff, badChannel_one_iff,
    lowDigit_peel1_affineOrbit]

/-- After exponent branch `2`, the twisted second read `(q+1) mod 3` chooses
    channels `1` or `2`; twisted trit `2` is immediate success. -/
theorem noCommonTwo_three_mul_add_two_second_iff (q : Nat) :
    (¬ CommonTwo (3*q+2)) ↔
      ((q + 1) % 3 = 0 ∧ BadChannel 1 (tail3 (peel2 (affineOrbit q)))) ∨
      ((q + 1) % 3 = 1 ∧ BadChannel 2 (tail3 (peel2 (affineOrbit q)))) := by
  rw [noCommonTwo_three_mul_add_two_iff, badChannel_three_iff,
    lowDigit_peel2_affineOrbit]

/-- Structural recovery of the `K mod 9 = 6` killing class from the affine
    transducer itself, with no residue-table lookup. -/
theorem commonTwo_three_mul_of_q_mod_three_two
    (q : Nat) (hq : q % 3 = 2) : CommonTwo (3*q) := by
  by_contra hNo
  rcases (noCommonTwo_three_mul_second_iff q).1 hNo with h0 | h1
  · omega
  · omega

/-- Structural recovery of the `K mod 9 = 5` killing class. -/
theorem commonTwo_three_mul_add_two_of_q_mod_three_one
    (q : Nat) (hq : q % 3 = 1) : CommonTwo (3*q+2) := by
  by_contra hNo
  rcases (noCommonTwo_three_mul_add_two_second_iff q).1 hNo with h0 | h1
  · have hmod : (q + 1) % 3 = 2 := by
      omega
    omega
  · have hmod : (q + 1) % 3 = 2 := by
      omega
    omega

#check noCommonTwo_three_mul_second_iff
#check noCommonTwo_three_mul_add_one_second_iff
#check noCommonTwo_three_mul_add_two_second_iff
#check commonTwo_three_mul_of_q_mod_three_two
#check commonTwo_three_mul_add_two_of_q_mod_three_one
#print axioms noCommonTwo_three_mul_second_iff
#print axioms noCommonTwo_three_mul_add_one_second_iff
#print axioms noCommonTwo_three_mul_add_two_second_iff

end GSTFourPowerAffineTwoTritClassifier
