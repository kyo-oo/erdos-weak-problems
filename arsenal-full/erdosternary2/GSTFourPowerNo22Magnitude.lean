import GSTFourPowerDirectResidue

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerNo22Magnitude

open GSTFourPowerDirectResidue

/-- Pure ternary language: no adjacent pair of digits is `22`. -/
def No22Ternary (X : Nat) : Prop :=
  ∀ j : Nat, ¬ (digit3 X j = 2 ∧ digit3 X (j+1) = 2)

/-- Cutting off `q` low ternary digits shifts every remaining digit down by
exactly `q` positions. -/
theorem digit3_div_three_pow_shift (X q j : Nat) :
    digit3 (X / 3^q) j = digit3 X (q+j) := by
  simp [digit3, Nat.div_div_eq_div_mul, pow_add, Nat.mul_comm]

/-- The no-`22` language is stable under every ternary suffix cut. -/
theorem no22_div_three_pow
    (X q : Nat) (hno : No22Ternary X) :
    No22Ternary (X / 3^q) := by
  intro j h22
  apply hno (q+j)
  constructor
  · rw [← digit3_div_three_pow_shift X q j]
    exact h22.1
  · rw [show (q+j)+1 = q+(j+1) by omega,
        ← digit3_div_three_pow_shift X q (j+1)]
    exact h22.2

/-- A no-`22` ternary word has low two-trit block at most `21₃ = 7`. -/
theorem no22_low_pair_le_seven
    (X : Nat) (hno : No22Ternary X) :
    X % 9 ≤ 7 := by
  have h0lt : digit3 X 0 < 3 := by
    unfold digit3
    exact Nat.mod_lt _ (by decide)
  have h1lt : digit3 X 1 < 3 := by
    unfold digit3
    exact Nat.mod_lt _ (by decide)
  have hd0 : digit3 X 0 = 0 ∨ digit3 X 0 = 1 ∨ digit3 X 0 = 2 := by
    omega
  have hd1 : digit3 X 1 = 0 ∨ digit3 X 1 = 1 ∨ digit3 X 1 = 2 := by
    omega
  have hpair : ¬ (digit3 X 0 = 2 ∧ digit3 X 1 = 2) := by
    simpa using hno 0
  have hmod : X % 9 = digit3 X 0 + 3 * digit3 X 1 := by
    calc
      X % 9 = X % (3^1 * 3) := by norm_num
      _ = X % 3^1 + 3^1 * (X / 3^1 % 3) := by
        rw [Nat.mod_mul]
      _ = digit3 X 0 + 3 * digit3 X 1 := by
        simp [digit3]
  rw [hmod]
  rcases hd0 with h00 | h01 | h02 <;>
    rcases hd1 with h10 | h11 | h12
  all_goals omega

/-- Sharp finite magnitude bound for an even number of ternary positions.

If `X < 9^m` and the ternary expansion of `X` contains no adjacent `22`, then
`8*X ≤ 7*(9^m - 1)`.  The extremal pattern is the alternating word
`21 21 ... 21`, so the asymptotic density constant `7/8` is sharp. -/
theorem no22_nine_power_bound
    (X m : Nat)
    (hX : X < 9^m)
    (hno : No22Ternary X) :
    8 * X ≤ 7 * (9^m - 1) := by
  induction m generalizing X with
  | zero =>
      norm_num at hX ⊢
      omega
  | succ m ih =>
      let Y := X / 9
      have hpow : 9^(m+1) = 9 * 9^m := by
        rw [Nat.pow_succ]
        ac_rfl
      have hYlt : Y < 9^m := by
        have hx' : X < 9 * 9^m := by
          simpa [hpow] using hX
        dsimp [Y]
        rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 9)]
        simpa [Nat.mul_comm] using hx'
      have hYno : No22Ternary Y := by
        have h := no22_div_three_pow X 2 hno
        simpa [Y] using h
      have hYbound := ih Y hYlt hYno
      have hlow : X % 9 ≤ 7 := no22_low_pair_le_seven X hno
      have hdecomp : X = X % 9 + 9 * Y := by
        dsimp [Y]
        exact (Nat.mod_add_div X 9).symm
      have hP : 0 < 9^m := Nat.pow_pos (by decide)
      rw [hpow]
      omega

#check No22Ternary
#check digit3_div_three_pow_shift
#check no22_div_three_pow
#check no22_low_pair_le_seven
#check no22_nine_power_bound
#print axioms digit3_div_three_pow_shift
#print axioms no22_div_three_pow
#print axioms no22_low_pair_le_seven
#print axioms no22_nine_power_bound

end GSTFourPowerNo22Magnitude
