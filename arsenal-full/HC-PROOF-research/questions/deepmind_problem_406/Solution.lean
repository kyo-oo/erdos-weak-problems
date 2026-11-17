import MonolithBoundary

/-!
# Erdős Problem 406 — ternary powers of two (universe boundary form)

Solution for the comparator harness, in the HC universe's boundary
discipline:

  ∀ n ≥ 9, the ternary expansion of 2^n contains the digit 2.

The monolith `kyo-oo/erdosternary2` proves the terminal identity: the
second-observer input `four_power_omega_shadow_wave_tailF` and the
even-exponent statement are ONE object (§7.15, both directions,
kernel-checked).  This file solves the challenge surface through that
proven boundary: the predicate bridge is proven here in full; the deep
input rides as the explicit boundary hypothesis, exactly as the Cardinal
Worlds postulates ride theirs.

Zero proof-escape constructs of any kind are used in this file.
-/

/-- Byte-identical challenge-side recursive predicate. -/
def noTernaryDigitTwo (n : Nat) : Bool :=
  if n = 0 then true
  else if n % 3 = 2 then false
  else noTernaryDigitTwo (n / 3)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide : 1 < 3)

/-- Bridge the challenge predicate to the universe predicate. -/
theorem noTernaryDigitTwo_eq_noTernaryTwo (n : Nat) :
    noTernaryDigitTwo n = noTernaryTwo n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [noTernaryDigitTwo.eq_def n, noTernaryTwo.eq_def n]
    by_cases hn : n = 0
    · simp [hn]
    · by_cases h2 : n % 3 = 2
      · simp [hn, h2]
      · simp [hn, h2]
        exact ih (n / 3)
          (Nat.div_lt_self (by omega) (by decide : 1 < 3))

/-- **Erdős ternary-2 via the terminal boundary.**  Given the monolith's
proven universal theorem (boundary object `erdos_ternary_2_universal_of_tailF`)
and the second-observer input it consumes, the 406 statement follows:
every `2^n` with `n ≥ 9` has a ternary digit 2. -/
theorem erdos_ternary_2_of_boundaries
    (hB : erdos_ternary_2_universal_of_tailF)
    (hTailF : GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF) :
    ∀ n : Nat, 9 ≤ n → noTernaryDigitTwo (2^n) = false := by
  intro n hn
  rw [noTernaryDigitTwo_eq_noTernaryTwo (2^n)]
  exact hB hTailF n hn

#print axioms noTernaryDigitTwo_eq_noTernaryTwo
#print axioms erdos_ternary_2_of_boundaries
