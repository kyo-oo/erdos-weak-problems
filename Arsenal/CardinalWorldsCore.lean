/-!
# THE CARDINAL WORLDS CORE — the ternary verdict carriers (S089r import diet)

The chamber chain (`KernelChamber406`: spines -> words -> pins -> census ->
crowns) rides on exactly three root-level declarations of
`Arsenal.CardinalWorlds`: `noTernaryTwo`, `hasTernaryTwo`, and
`hasTernaryTwo_of_digit`.  `CardinalWorlds` itself imports ALL of Mathlib
(vendored verbatim; 75+ fleet kernels ride its transitive scope), which
forced every chamber lean process to hold ~15GB RSS — the swap thrash that
made the chamber CI-carrier war unwinnable (swap-in storms, ~10%
elaboration speed, stochastic hosted-runner reaping at 9-50 minutes).

This module carries the three declarations VERBATIM (same root-level names,
same statements, same proofs) with a CORE-ONLY scope (zero imports — every
tactic used, including `ac_rfl`, is Lean core).  `Arsenal.CardinalWorlds`
imports this module and its own copies are REMOVED — the constants remain
THE SAME OBJECTS for every consumer (fleet unchanged, full scope
unchanged); the chamber chain simply stops paying for the 8600-module
closure it never used.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- The Cantor verdict: does the ternary expansion of `n` avoid the digit 2? -/
def noTernaryTwo (n : Nat) : Bool :=
  if n = 0 then true
  else if n % 3 = 2 then false
  else noTernaryTwo (n / 3)
termination_by n
decreasing_by
  have hk : 0 < n := by omega
  exact Nat.div_lt_self hk (by decide : 1 < 3)

/-- The signature scan: does the ternary expansion of `n` carry the digit 2? -/
def hasTernaryTwo (n : Nat) : Bool :=
  if n = 0 then false
  else if n % 3 = 2 then true
  else hasTernaryTwo (n / 3)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide : 1 < 3)

/-- **THE DIGIT-TO-SCAN LAW.**  A ternary digit 2 at any position fires the
signature scan. -/
theorem hasTernaryTwo_of_digit (n : Nat) (q : Nat) (h : n / 3^q % 3 = 2) :
    hasTernaryTwo n = true := by
  induction q generalizing n with
  | zero =>
    rw [Nat.pow_zero, Nat.div_one] at h
    have hn : n ≠ 0 := by intro hnn; rw [hnn, Nat.zero_mod] at h; exact absurd h (by decide)
    rw [hasTernaryTwo.eq_def n, if_neg hn, if_pos h]
  | succ q ih =>
    have hn : n ≠ 0 := by intro hnn; rw [hnn, Nat.zero_div, Nat.zero_mod] at h; exact absurd h (by decide)
    have hkey : n / 3^(q+1) = (n / 3) / 3^q := by
      rw [show 3^(q+1) = 3 * 3^q from by rw [Nat.pow_succ]; ac_rfl, Nat.div_div_eq_div_mul]
    rw [hkey] at h
    have hih : hasTernaryTwo (n / 3) = true := ih (n / 3) h
    by_cases hmod : n % 3 = 2
    · rw [hasTernaryTwo.eq_def n, if_neg hn, if_pos hmod]
    · rw [hasTernaryTwo.eq_def n, if_neg hn, if_neg hmod]; exact hih
