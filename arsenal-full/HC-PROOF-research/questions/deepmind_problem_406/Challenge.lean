import Mathlib

/-!
# DeepMind Problem 406 — comparator challenge

This is the question-side Lean file for the official comparator harness.
It states the Erdős ternary-2 problem exactly in the benchmark surface:
for every exponent `n ≥ 9`, the ternary expansion of `2^n` contains digit `2`.

The `sorry` below is intentional on the challenge side only.  The solution file
must provide the proof, importing the green monolith.
-/

/-- A number has no ternary digit `2` iff all of its base-3 digits are `0` or `1`. -/
def noTernaryDigitTwo (n : Nat) : Bool :=
  if n = 0 then true
  else if n % 3 = 2 then false
  else noTernaryDigitTwo (n / 3)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide : 1 < 3)

/-- DeepMind Problem 406 / Erdős ternary-2 comparator statement. -/
theorem erdos_ternary_2 :
    ∀ n : Nat, 9 ≤ n → noTernaryDigitTwo (2^n) = false := by
  sorry
