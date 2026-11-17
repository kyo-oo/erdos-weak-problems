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


/-! ## Structural mod-nine classification from the affine automaton -/

/-- Residue six modulo nine is killed structurally by the branch
`K = 3*q`, `q mod 3 = 2`; no power table is used. -/
theorem commonTwo_of_mod9_six_structural
    (K : Nat) (hK : K % 9 = 6) :
    CommonTwo K := by
  have hs := Nat.mod_add_div K 9
  have hshape9 : K = 6 + 9 * (K / 9) := by
    rw [hK] at hs
    omega
  let q := K / 3
  have hqShape : q = 2 + 3 * (K / 9) := by
    dsimp [q]
    rw [hshape9]
    omega
  have hshape : K = 3 * q := by
    rw [hshape9, hqShape]
    ring
  have hq : q % 3 = 2 := by
    rw [hqShape]
    simp
  rw [hshape]
  exact commonTwo_three_mul_of_q_mod_three_two q hq

/-- Residue five modulo nine is killed structurally by the branch
`K = 3*q+2`, `q mod 3 = 1`. -/
theorem commonTwo_of_mod9_five_structural
    (K : Nat) (hK : K % 9 = 5) :
    CommonTwo K := by
  have hs := Nat.mod_add_div K 9
  have hshape9 : K = 5 + 9 * (K / 9) := by
    rw [hK] at hs
    omega
  let q := K / 3
  have hqShape : q = 1 + 3 * (K / 9) := by
    dsimp [q]
    rw [hshape9]
    omega
  have hshape : K = 3 * q + 2 := by
    rw [hshape9, hqShape]
    ring
  have hq : q % 3 = 1 := by
    rw [hqShape]
    simp
  rw [hshape]
  exact commonTwo_three_mul_add_two_of_q_mod_three_one q hq

/-- The two killing classes are therefore an intrinsic theorem of the affine
transducer, independent of the direct residue classifier. -/
theorem commonTwo_of_mod9_five_or_six_structural
    (K : Nat) (hK : K % 9 = 5 ∨ K % 9 = 6) :
    CommonTwo K := by
  rcases hK with h5 | h6
  · exact commonTwo_of_mod9_five_structural K h5
  · exact commonTwo_of_mod9_six_structural K h6

/-- Any affine-transducer counterexample excludes both structural killing
classes. -/
theorem noCommonTwo_forbids_mod9_five_six_structural
    (K : Nat) (hNo : ¬ CommonTwo K) :
    K % 9 ≠ 5 ∧ K % 9 ≠ 6 := by
  constructor
  · intro h5
    exact hNo (commonTwo_of_mod9_five_structural K h5)
  · intro h6
    exact hNo (commonTwo_of_mod9_six_structural K h6)


#check noCommonTwo_three_mul_second_iff
#check noCommonTwo_three_mul_add_one_second_iff
#check noCommonTwo_three_mul_add_two_second_iff
#check commonTwo_three_mul_of_q_mod_three_two
#check commonTwo_three_mul_add_two_of_q_mod_three_one
#check commonTwo_of_mod9_five_structural
#check commonTwo_of_mod9_six_structural
#check commonTwo_of_mod9_five_or_six_structural
#check noCommonTwo_forbids_mod9_five_six_structural
#print axioms noCommonTwo_three_mul_second_iff
#print axioms noCommonTwo_three_mul_add_one_second_iff
#print axioms noCommonTwo_three_mul_add_two_second_iff
#print axioms commonTwo_of_mod9_five_or_six_structural

end GSTFourPowerAffineTwoTritClassifier
