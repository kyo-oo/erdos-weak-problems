/- ======================================================================
/- CHRONOLOGICAL LABEL — #0007 / 1133
/-    Path         : Challenge.lean
/-    Ref          : main
/-    First-commit : 2026-08-14 14:36:32 +0530
/-    Last-commit  : 2026-08-14 14:36:32 +0530
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-14 14:36:32 +0530  eeabe82  (ker07-dev)
/- ====================================================================== -/

/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0007 / 1132
/-    Path         : Challenge.lean
/-    Ref          : main
/-    First-commit : 2026-08-14 14:36:32 +0530  (eeabe82)
/-    Last-commit  : 2026-08-14 14:36:32 +0530  (eeabe82)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-14 14:36:32 +0530  eeabe82  (ker07-dev)
/-        feat: add comparator challenge statement
/- ====================================================================== -/

import Mathlib

/-- A number has no ternary digit `2` iff all of its base-3 digits are `0` or `1`. -/
def noTernaryDigitTwo (n : Nat) : Bool :=
  if n = 0 then true
  else if n % 3 = 2 then false
  else noTernaryDigitTwo (n / 3)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide : 1 < 3)

/-- Erdős ternary-2 conjecture, comparator challenge statement. -/
def erdos_ternary_2_challenge_statement : Prop :=
  ∀ n : Nat, 9 ≤ n → noTernaryDigitTwo (2^n) = false
