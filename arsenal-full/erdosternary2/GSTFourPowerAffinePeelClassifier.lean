import GSTFourPowerAffineClassifierBridge
import GSTFourPowerAffineExponentPeel

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffinePeelClassifier

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineExponentPeel
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge

/-- After exponent trit `0`, the affine coordinate tail is exactly `peel0`. -/
theorem tail3_affineOrbit_three_mul (q : Nat) :
    tail3 (affineOrbit (3*q)) = peel0 (affineOrbit q) := by
  unfold tail3
  rw [affineOrbit_three_mul]
  omega

/-- After exponent trit `1`, the affine coordinate tail is exactly `peel1`. -/
theorem tail3_affineOrbit_three_mul_add_one (q : Nat) :
    tail3 (affineOrbit (3*q+1)) = peel1 (affineOrbit q) := by
  unfold tail3
  rw [affineOrbit_three_mul_add_one]
  omega

/-- After exponent trit `2`, the affine coordinate tail is exactly `peel2`. -/
theorem tail3_affineOrbit_three_mul_add_two (q : Nat) :
    tail3 (affineOrbit (3*q+2)) = peel2 (affineOrbit q) := by
  unfold tail3
  rw [affineOrbit_three_mul_add_two]
  omega

/-- Exact first exponent-trit classifier, branch `0`. -/
theorem noCommonTwo_three_mul_iff (q : Nat) :
    (¬ CommonTwo (3*q)) ↔
      BadChannel 0 (peel0 (affineOrbit q)) := by
  rw [noCommonTwo_low_trit_branch]
  simp [tail3_affineOrbit_three_mul]

/-- Exact first exponent-trit classifier, branch `1`. -/
theorem noCommonTwo_three_mul_add_one_iff (q : Nat) :
    (¬ CommonTwo (3*q+1)) ↔
      BadChannel 1 (peel1 (affineOrbit q)) := by
  have hmod : (3*q+1) % 3 = 1 := by omega
  rw [noCommonTwo_low_trit_branch]
  rw [tail3_affineOrbit_three_mul_add_one]
  simp [hmod]

/-- Exact first exponent-trit classifier, branch `2`. -/
theorem noCommonTwo_three_mul_add_two_iff (q : Nat) :
    (¬ CommonTwo (3*q+2)) ↔
      BadChannel 3 (peel2 (affineOrbit q)) := by
  have hmod : (3*q+2) % 3 = 2 := by omega
  rw [noCommonTwo_low_trit_branch]
  rw [tail3_affineOrbit_three_mul_add_two]
  simp [hmod]

/-- The low ternary digit of the `0` peel is inherited from its input. -/
theorem peel0_mod_three (x : Nat) : peel0 x % 3 = x % 3 := by
  simp [peel0, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]

/-- The low ternary digit of the `1` peel is also inherited from its input. -/
theorem peel1_mod_three (x : Nat) : peel1 x % 3 = x % 3 := by
  rw [peel1_eq_four_peel0]
  simp [Nat.mul_mod, peel0_mod_three]

/-- The low ternary digit of the `2` peel is the successor of the input trit. -/
theorem peel2_mod_three (x : Nat) : peel2 x % 3 = (x + 1) % 3 := by
  rw [peel2_eq_four_peel1_add_one]
  simp [Nat.add_mod, Nat.mul_mod, peel1_mod_three]

/-- Therefore the second automaton read after exponent branch `0` is exactly
    the next ternary exponent trit. -/
theorem lowDigit_peel0_affineOrbit (q : Nat) :
    lowDigit (peel0 (affineOrbit q)) = q % 3 := by
  unfold lowDigit
  rw [peel0_mod_three, affineOrbit_mod_three]

/-- The same is true after exponent branch `1`. -/
theorem lowDigit_peel1_affineOrbit (q : Nat) :
    lowDigit (peel1 (affineOrbit q)) = q % 3 := by
  unfold lowDigit
  rw [peel1_mod_three, affineOrbit_mod_three]

/-- Branch `2` twists the next automaton read by one. -/
theorem lowDigit_peel2_affineOrbit (q : Nat) :
    lowDigit (peel2 (affineOrbit q)) = (q + 1) % 3 := by
  unfold lowDigit
  rw [peel2_mod_three]
  calc
    (affineOrbit q + 1) % 3 = (affineOrbit q % 3 + 1 % 3) % 3 := Nat.add_mod _ _ _
    _ = (q % 3 + 1 % 3) % 3 := by rw [affineOrbit_mod_three]
    _ = (q + 1) % 3 := (Nat.add_mod q 1 3).symm

#check tail3_affineOrbit_three_mul
#check tail3_affineOrbit_three_mul_add_one
#check tail3_affineOrbit_three_mul_add_two
#check noCommonTwo_three_mul_iff
#check noCommonTwo_three_mul_add_one_iff
#check noCommonTwo_three_mul_add_two_iff
#check lowDigit_peel0_affineOrbit
#check lowDigit_peel1_affineOrbit
#check lowDigit_peel2_affineOrbit
#print axioms noCommonTwo_three_mul_iff
#print axioms noCommonTwo_three_mul_add_one_iff
#print axioms noCommonTwo_three_mul_add_two_iff

end GSTFourPowerAffinePeelClassifier
