import GSTFourPowerAffinePeelClassifier

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineRenormalizedOrbit

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineExponentPeel
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffinePeelClassifier

/-- One exact ternary-scale renormalization of the affine orbit.  Concretely
    this is `(4^(3q)-1)/9`, but the polynomial form avoids division. -/
def renormOrbit (q : Nat) : Nat := peel0 (affineOrbit q)

/-- Exponent class `3q` is exactly three times the renormalized orbit. -/
theorem affineOrbit_three_mul_eq_three_renorm (q : Nat) :
    affineOrbit (3*q) = 3 * renormOrbit q := by
  simpa [renormOrbit] using affineOrbit_three_mul q

/-- The `3q+1` tail is the first x4 edge from the renormalized orbit. -/
theorem peel1_eq_four_renorm (q : Nat) :
    peel1 (affineOrbit q) = 4 * renormOrbit q := by
  simpa [renormOrbit] using peel1_eq_four_peel0 (affineOrbit q)

/-- The `3q+2` tail is the second affine edge. -/
theorem peel2_eq_sixteen_renorm_add_one (q : Nat) :
    peel2 (affineOrbit q) = 16 * renormOrbit q + 1 := by
  rw [peel2_eq_four_peel1_add_one, peel1_eq_four_renorm]
  ring

/-- Star-crusher scale law: after consuming one ternary exponent digit, the
    normalized orbit advances by one base-64 affine step. -/
theorem renormOrbit_succ (q : Nat) :
    renormOrbit (q+1) = 64 * renormOrbit q + 7 := by
  unfold renormOrbit
  rw [affineOrbit_succ, peel0_affine_succ]
  rw [peel2_eq_four_peel1_add_one, peel1_eq_four_peel0]
  ring

/-- Exact classifier for the `0` exponent-trit edge in renormalized form. -/
theorem noCommonTwo_three_mul_renorm_iff (q : Nat) :
    (¬ CommonTwo (3*q)) ↔ BadChannel 0 (renormOrbit q) := by
  simpa [renormOrbit] using noCommonTwo_three_mul_iff q

/-- Exact classifier for the `1` exponent-trit edge in renormalized form. -/
theorem noCommonTwo_three_mul_add_one_renorm_iff (q : Nat) :
    (¬ CommonTwo (3*q+1)) ↔ BadChannel 1 (4 * renormOrbit q) := by
  rw [noCommonTwo_three_mul_add_one_iff, peel1_eq_four_renorm]

/-- Exact classifier for the `2` exponent-trit edge in renormalized form. -/
theorem noCommonTwo_three_mul_add_two_renorm_iff (q : Nat) :
    (¬ CommonTwo (3*q+2)) ↔
      BadChannel 3 (16 * renormOrbit q + 1) := by
  rw [noCommonTwo_three_mul_add_two_iff, peel2_eq_sixteen_renorm_add_one]

/-- The three branches therefore form one contiguous affine chain:
    `Y -> 4Y -> 16Y+1 -> 64Y+7 = Y_next`. -/
theorem renorm_chain_closes (q : Nat) :
    4 * (16 * renormOrbit q + 1) + 3 = renormOrbit (q+1) := by
  rw [renormOrbit_succ]
  ring

#check renormOrbit_succ
#check noCommonTwo_three_mul_renorm_iff
#check noCommonTwo_three_mul_add_one_renorm_iff
#check noCommonTwo_three_mul_add_two_renorm_iff
#check renorm_chain_closes
#print axioms renormOrbit_succ
#print axioms noCommonTwo_three_mul_renorm_iff

end GSTFourPowerAffineRenormalizedOrbit
