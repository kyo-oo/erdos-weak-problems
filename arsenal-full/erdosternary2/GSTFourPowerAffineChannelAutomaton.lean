import GSTFourPowerAffineBadState

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineChannelAutomaton

open GSTFourPowerDirectResidue
open GSTFourPowerAffineBadState

/-- Least ternary digit of a channel source. -/
def lowDigit (x : Nat) : Nat := x % 3

/-- One-digit ternary tail. -/
def tail3 (x : Nat) : Nat := x / 3

/-- Low output digit of the affine channel `x ↦ 4x+c`. -/
def channelOut (c a : Nat) : Nat := (4*a + c) % 3

/-- Carry/channel state passed to the next ternary digit. -/
def channelNext (c a : Nat) : Nat := (4*a + c) / 3

/-- The low pair is already a common two. -/
def lowSuccess (c x : Nat) : Prop :=
  lowDigit x = 2 ∧ channelOut c (lowDigit x) = 2

/-- Global badness of one affine channel. -/
def BadChannel (c x : Nat) : Prop :=
  ¬ PairCommonTwo x (4*x + c)

lemma lowDigit_lt_three (x : Nat) : lowDigit x < 3 := by
  exact Nat.mod_lt _ (by decide)

/-- Exact one-trit decomposition. -/
theorem split_three (x : Nat) :
    x = lowDigit x + 3 * tail3 x := by
  simpa [lowDigit, tail3] using (Nat.mod_add_div x 3).symm

/-- Exact one-trit decomposition of the affine target.  This proof deliberately
    rewrites only the outer source `x`; it does not rewrite the `lowDigit x`
    occurrences that define the finite channel state. -/
theorem split_channel (c x : Nat) :
    4*x + c =
      channelOut c (lowDigit x) +
        3 * (4 * tail3 x + channelNext c (lowDigit x)) := by
  have hx : x = lowDigit x + 3 * tail3 x := split_three x
  have hz := (Nat.mod_add_div (4 * lowDigit x + c) 3).symm
  unfold channelOut channelNext
  calc
    4*x + c = 4 * (lowDigit x + 3 * tail3 x) + c := by
      exact congrArg (fun y : Nat => 4 * y + c) hx
    _ = (4 * lowDigit x + c) + 12 * tail3 x := by ring
    _ = ((4 * lowDigit x + c) % 3) +
          3 * ((4 * lowDigit x + c) / 3) + 12 * tail3 x := by
          omega
    _ = ((4 * lowDigit x + c) % 3) +
          3 * (4 * tail3 x + (4 * lowDigit x + c) / 3) := by ring

/-- Removing one ternary digit from the source shifts every higher digit
    literally onto the quotient. -/
theorem digit3_succ_tail (x j : Nat) :
    digit3 x (j+1) = digit3 (tail3 x) j := by
  have h := GSTCanonicalTailStateIso.prefix_slice_digit_exact
    1 (lowDigit x) (tail3 x) j (by simpa using lowDigit_lt_three x)
  calc
    digit3 x (j+1) =
        digit3 (lowDigit x + 3 * tail3 x) (1+j) := by
          have hx := split_three x
          rw [← hx]
          congr 1 <;> omega
    _ = digit3 (tail3 x) j := by
      simpa [GSTCanonicalTailStateIso.digit3,
        GSTFourPowerDirectResidue.digit3] using h

/-- Removing one ternary digit from `4x+c` exposes the next finite channel. -/
theorem digit3_succ_channel (c x j : Nat) :
    digit3 (4*x+c) (j+1) =
      digit3 (4 * tail3 x + channelNext c (lowDigit x)) j := by
  have hout : channelOut c (lowDigit x) < 3 := by
    unfold channelOut
    exact Nat.mod_lt _ (by decide)
  have h := GSTCanonicalTailStateIso.prefix_slice_digit_exact
    1 (channelOut c (lowDigit x))
      (4 * tail3 x + channelNext c (lowDigit x)) j
      (by simpa using hout)
  calc
    digit3 (4*x+c) (j+1) =
        digit3
          (channelOut c (lowDigit x) +
            3 * (4 * tail3 x + channelNext c (lowDigit x)))
          (1+j) := by
            have hx := split_channel c x
            rw [← hx]
            congr 1 <;> omega
    _ = digit3 (4 * tail3 x + channelNext c (lowDigit x)) j := by
      simpa [GSTCanonicalTailStateIso.digit3,
        GSTFourPowerDirectResidue.digit3] using h

@[simp] theorem digit3_zero_source (x : Nat) :
    digit3 x 0 = lowDigit x := by
  simp [GSTFourPowerDirectResidue.digit3, lowDigit]

/-- The discarded target trit is exactly the finite channel output. -/
@[simp] theorem digit3_zero_channel (c x : Nat) :
    digit3 (4*x+c) 0 = channelOut c (lowDigit x) := by
  simp [GSTFourPowerDirectResidue.digit3, channelOut, lowDigit,
    Nat.add_mod, Nat.mul_mod]

/-- Master affine-channel recursion. Every common-two witness is either the
    discarded low digit itself, or a witness in the unique next channel. -/
theorem pairCommonTwo_channel_iff (c x : Nat) :
    PairCommonTwo x (4*x+c) ↔
      lowSuccess c x ∨
        PairCommonTwo (tail3 x)
          (4 * tail3 x + channelNext c (lowDigit x)) := by
  constructor
  · rintro ⟨j, hx, hy⟩
    cases j with
    | zero =>
        left
        constructor
        · rw [digit3_zero_source] at hx
          exact hx
        · rw [digit3_zero_channel] at hy
          exact hy
    | succ j =>
        right
        refine ⟨j, ?_, ?_⟩
        · rw [← digit3_succ_tail x j]
          exact hx
        · rw [← digit3_succ_channel c x j]
          exact hy
  · intro h
    rcases h with hlow | htail
    · rcases hlow with ⟨hx, hy⟩
      refine ⟨0, ?_, ?_⟩
      · rw [digit3_zero_source]
        exact hx
      · rw [digit3_zero_channel]
        exact hy
    · rcases htail with ⟨j, hx, hy⟩
      refine ⟨j+1, ?_, ?_⟩
      · rw [digit3_succ_tail x j]
        exact hx
      · rw [digit3_succ_channel c x j]
        exact hy

/-- Complement form of the master recursion. -/
theorem badChannel_iff (c x : Nat) :
    BadChannel c x ↔
      ¬ lowSuccess c x ∧
        BadChannel (channelNext c (lowDigit x)) (tail3 x) := by
  unfold BadChannel
  rw [pairCommonTwo_channel_iff]
  simp

/-- State `0`: trit `2` is an immediate success; only `0,1` survive. -/
theorem badChannel_zero_iff (x : Nat) :
    BadChannel 0 x ↔
      (lowDigit x = 0 ∧ BadChannel 0 (tail3 x)) ∨
      (lowDigit x = 1 ∧ BadChannel 1 (tail3 x)) := by
  have ha := lowDigit_lt_three x
  rw [badChannel_iff]
  interval_cases h : lowDigit x <;>
    simp [h, lowSuccess, channelOut, channelNext, BadChannel] at *

/-- State `1`: all three trits survive, moving to states `0,1,3`. -/
theorem badChannel_one_iff (x : Nat) :
    BadChannel 1 x ↔
      (lowDigit x = 0 ∧ BadChannel 0 (tail3 x)) ∨
      (lowDigit x = 1 ∧ BadChannel 1 (tail3 x)) ∨
      (lowDigit x = 2 ∧ BadChannel 3 (tail3 x)) := by
  have ha := lowDigit_lt_three x
  rw [badChannel_iff]
  interval_cases h : lowDigit x <;>
    simp [h, lowSuccess, channelOut, channelNext, BadChannel] at *

/-- State `2`: all three trits survive, moving to states `0,2,3`. -/
theorem badChannel_two_iff (x : Nat) :
    BadChannel 2 x ↔
      (lowDigit x = 0 ∧ BadChannel 0 (tail3 x)) ∨
      (lowDigit x = 1 ∧ BadChannel 2 (tail3 x)) ∨
      (lowDigit x = 2 ∧ BadChannel 3 (tail3 x)) := by
  have ha := lowDigit_lt_three x
  rw [badChannel_iff]
  interval_cases h : lowDigit x <;>
    simp [h, lowSuccess, channelOut, channelNext, BadChannel] at *

/-- State `3`: trit `2` is an immediate success; only `0,1` survive. -/
theorem badChannel_three_iff (x : Nat) :
    BadChannel 3 x ↔
      (lowDigit x = 0 ∧ BadChannel 1 (tail3 x)) ∨
      (lowDigit x = 1 ∧ BadChannel 2 (tail3 x)) := by
  have ha := lowDigit_lt_three x
  rw [badChannel_iff]
  interval_cases h : lowDigit x <;>
    simp [h, lowSuccess, channelOut, channelNext, BadChannel] at *

#check pairCommonTwo_channel_iff
#check badChannel_iff
#check badChannel_zero_iff
#check badChannel_one_iff
#check badChannel_two_iff
#check badChannel_three_iff
#print axioms pairCommonTwo_channel_iff
#print axioms badChannel_zero_iff
#print axioms badChannel_one_iff
#print axioms badChannel_two_iff
#print axioms badChannel_three_iff

end GSTFourPowerAffineChannelAutomaton
