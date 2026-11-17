/- ======================================================================
/- CHRONOLOGICAL LABEL — #0008 / 1133
/-    Path         : Solution.lean
/-    Ref          : main
/-    First-commit : 2026-08-14 14:36:44 +0530
/-    Last-commit  : 2026-08-14 14:36:44 +0530
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-14 14:36:44 +0530  6ec6cf4  (ker07-dev)
/- ====================================================================== -/

/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0008 / 1132
/-    Path         : Solution.lean
/-    Ref          : main
/-    First-commit : 2026-08-14 14:36:44 +0530  (6ec6cf4)
/-    Last-commit  : 2026-08-14 14:36:44 +0530  (6ec6cf4)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-14 14:36:44 +0530  6ec6cf4  (ker07-dev)
/-        feat: add comparator solution bridge
/- ====================================================================== -/

import ErdosTernary2

/-- Byte-identical challenge-side definition. -/
def noTernaryDigitTwo (n : Nat) : Bool :=
  if n = 0 then true
  else if n % 3 = 2 then false
  else noTernaryDigitTwo (n / 3)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide : 1 < 3)

/-- Bridge the challenge recursion to the project's `noTernaryTwo`. -/
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
        exact ih (n / 3) (Nat.div_lt_self (by omega) (by decide : 1 < 3))

/-- Comparator solution theorem. -/
theorem erdos_ternary_2 : ∀ n : Nat, 9 ≤ n → noTernaryDigitTwo (2^n) = false := by
  intro n hn
  rw [noTernaryDigitTwo_eq_noTernaryTwo (2^n)]
  exact erdos_ternary_2_universal n hn
