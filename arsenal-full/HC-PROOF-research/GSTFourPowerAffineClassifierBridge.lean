import GSTFourPowerAffineChannelAutomaton

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineClassifierBridge

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton

/-- The least ternary digit of the affine orbit is exactly the least ternary
    trit of the exponent. -/
theorem affineOrbit_mod_three (K : Nat) :
    affineOrbit K % 3 = K % 3 := by
  induction K with
  | zero => rfl
  | succ K ih =>
      rw [affineOrbit_succ]
      omega

/-- Exact identification of the direct common-two target with channel `1` on
    the affine orbit. -/
theorem commonTwo_iff_channel_one (K : Nat) :
    CommonTwo K ↔
      PairCommonTwo (affineOrbit K) (4 * affineOrbit K + 1) := by
  rw [commonTwo_iff_affineCommonTwo]
  unfold AffineCommonTwo
  rw [affineOrbit_forward]
  rfl

/-- Therefore a direct counterexample is literally bad state `B₁` of the
    four-state channel automaton. -/
theorem noCommonTwo_iff_badChannel_one (K : Nat) :
    (¬ CommonTwo K) ↔ BadChannel 1 (affineOrbit K) := by
  unfold BadChannel
  exact not_congr (commonTwo_iff_channel_one K)

/-- The low digit read by the channel automaton is the actual low exponent
    trit. -/
theorem lowDigit_affineOrbit (K : Nat) :
    lowDigit (affineOrbit K) = K % 3 := by
  exact affineOrbit_mod_three K

/-- One exact counterexample step, expressed entirely in exponent language.
    No inherited Happy witness occurs anywhere: the lowest trit of `K` chooses
    the next channel state on the exact quotient of the affine coordinate. -/
theorem noCommonTwo_low_trit_branch (K : Nat) :
    (¬ CommonTwo K) ↔
      (K % 3 = 0 ∧ BadChannel 0 (tail3 (affineOrbit K))) ∨
      (K % 3 = 1 ∧ BadChannel 1 (tail3 (affineOrbit K))) ∨
      (K % 3 = 2 ∧ BadChannel 3 (tail3 (affineOrbit K))) := by
  rw [noCommonTwo_iff_badChannel_one, badChannel_one_iff]
  rw [lowDigit_affineOrbit]

/-- A counterexample with exponent trit `0` enters channel zero. -/
theorem noCommonTwo_mod_three_zero
    {K : Nat} (hNo : ¬ CommonTwo K) (hK : K % 3 = 0) :
    BadChannel 0 (tail3 (affineOrbit K)) := by
  rcases (noCommonTwo_low_trit_branch K).1 hNo with h0 | h1 | h2
  · exact h0.2
  · omega
  · omega

/-- A counterexample with exponent trit `1` stays in channel one. -/
theorem noCommonTwo_mod_three_one
    {K : Nat} (hNo : ¬ CommonTwo K) (hK : K % 3 = 1) :
    BadChannel 1 (tail3 (affineOrbit K)) := by
  rcases (noCommonTwo_low_trit_branch K).1 hNo with h0 | h1 | h2
  · omega
  · exact h1.2
  · omega

/-- A counterexample with exponent trit `2` enters the terminal-risk channel
    three, where a subsequent source digit `2` is immediately forbidden. -/
theorem noCommonTwo_mod_three_two
    {K : Nat} (hNo : ¬ CommonTwo K) (hK : K % 3 = 2) :
    BadChannel 3 (tail3 (affineOrbit K)) := by
  rcases (noCommonTwo_low_trit_branch K).1 hNo with h0 | h1 | h2
  · omega
  · omega
  · exact h2.2


/-! ## Branch-free counterexample transition -/

/-- Total next-channel map selected by the low ternary exponent phase. -/
def counterexampleNextChannel (r : Nat) : Nat :=
  if r % 3 = 0 then 0 else if r % 3 = 1 then 1 else 3

/-- The transition map has the exact three-phase spectrum. -/
theorem counterexampleNextChannel_spectrum :
    counterexampleNextChannel 0 = 0 ∧
    counterexampleNextChannel 1 = 1 ∧
    counterexampleNextChannel 2 = 3 := by
  decide

/-- **TOTAL COUNTEREXAMPLE TRANSITION.**  Any direct counterexample determines
one exact next automaton channel from its low exponent trit, with no external
case split in the theorem statement. -/
theorem noCommonTwo_next_channel
    (K : Nat) (hNo : ¬ CommonTwo K) :
    BadChannel (counterexampleNextChannel (K % 3))
      (tail3 (affineOrbit K)) := by
  have hlt : K % 3 < 3 := Nat.mod_lt K (by decide)
  have hcases : K % 3 = 0 ∨ K % 3 = 1 ∨ K % 3 = 2 := by
    omega
  rcases hcases with h0 | h1 | h2
  · rw [h0]
    norm_num [counterexampleNextChannel]
    exact noCommonTwo_mod_three_zero hNo h0
  · rw [h1]
    norm_num [counterexampleNextChannel]
    exact noCommonTwo_mod_three_one hNo h1
  · rw [h2]
    norm_num [counterexampleNextChannel]
    exact noCommonTwo_mod_three_two hNo h2

/-- The next counterexample channel always remains physical. -/
theorem counterexampleNextChannel_lt_four (K : Nat) :
    counterexampleNextChannel (K % 3) < 4 := by
  have hlt : K % 3 < 3 := Nat.mod_lt K (by decide)
  interval_cases h : K % 3 <;>
    norm_num [counterexampleNextChannel, h]


#check commonTwo_iff_channel_one
#check noCommonTwo_iff_badChannel_one
#check noCommonTwo_low_trit_branch
#check noCommonTwo_mod_three_zero
#check noCommonTwo_mod_three_one
#check noCommonTwo_mod_three_two
#check counterexampleNextChannel_spectrum
#check noCommonTwo_next_channel
#check counterexampleNextChannel_lt_four
#print axioms noCommonTwo_low_trit_branch
#print axioms noCommonTwo_next_channel

end GSTFourPowerAffineClassifierBridge
