import GSTProblem406CarryEntropyBound
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST exact cubic compression of the BAD trajectory automaton

This is an exact, non-circular reduction of the original
four carry-state GST survivor-count transition to three states.
From the all-ones initial vector, counts in incoming carries 1
and 2 are IDENTICAL at every depth.

Write a_n = C_n(0), b_n = C_n(1)=C_n(2), d_n = C_n(3).
Their exact recursion is
  a_(n+1) = a_n + b_n,
  b_(n+1) = a_n + b_n + d_n,
  d_(n+1) = 2 b_n.
Eliminating a,d gives the genuine linear recurrence
  b_(n+3) + 2 b_n = 2 b_(n+2) + 2 b_(n+1).

The characteristic polynomial is z^3-2z^2-2z+2
(with positive dominant root about 2.481194304).
This is an equality for all natural n, not a fitted pattern.
It does not directly exclude a single physical BAD source.
-/

namespace GSTProblem406CarryCubicRecurrence

open GSTProblem406CarryEntropyBound

private def a (n : Nat) := survivingCount n 0
private def b (n : Nat) := survivingCount n 1
private def c (n : Nat) := survivingCount n 2
private def d (n : Nat) := survivingCount n 3

private theorem a_succ (n : Nat) : a (n+1) = a n + b n := by rfl
private theorem b_succ (n : Nat) : b (n+1) = a n + b n + d n := by rfl
private theorem c_succ (n : Nat) : c (n+1) = a n + c n + d n := by rfl
private theorem d_succ (n : Nat) : d (n+1) = b n + c n := by rfl

/-- Equality of the two GST non-vacuum middle carry channels at
EVERY depth. This follows from exact physical transitions. -/
theorem middle_carry_survivor_symmetry (n : Nat) :
    b n = c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [b_succ, c_succ, ih]

/-- Every BAD trajectory count at carry one satisfies the exact
integer cubic recurrence for all natural depths. -/
theorem physical_carry_one_exact_cubic_recurrence (n : Nat) :
    b (n+3) + 2*b n =
      2*b (n+2) + 2*b (n+1) := by
  have hSymN := middle_carry_survivor_symmetry n
  have hSym1 := middle_carry_survivor_symmetry (n+1)
  have hA1 := a_succ n
  have hB1 := b_succ n
  have hD1 := d_succ n
  have hA2 : a (n+2) = a (n+1) + b (n+1) := by
    simpa only [show n+2 = (n+1)+1 by omega] using a_succ (n+1)
  have hB2 : b (n+2) = a (n+1) + b (n+1) + d (n+1) := by
    simpa only [show n+2 = (n+1)+1 by omega] using b_succ (n+1)
  have hD2 : d (n+2) = b (n+1) + c (n+1) := by
    simpa only [show n+2 = (n+1)+1 by omega] using d_succ (n+1)
  have hB3 : b (n+3) = a (n+2) + b (n+2) + d (n+2) := by
    simpa only [show n+3 = (n+2)+1 by omega] using b_succ (n+2)
  omega

/-- The original incoming carry-one language starts 1,3,7,18.
These are exact seed coefficients for the cubic recurrence. -/
theorem cubic_seed_coefficients :
    b 0 = 1 ∧ b 1 = 3 ∧ b 2 = 7 ∧ b 3 = 18 := by
  decide

/-- User-facing recurrence in original GST survivor-count symbols. -/
theorem original_bad_trajectory_cubic (n : Nat) :
    survivingCount (n+3) 1 + 2*survivingCount n 1 =
      2*survivingCount (n+2) 1 +
      2*survivingCount (n+1) 1 :=
  physical_carry_one_exact_cubic_recurrence n

#print axioms middle_carry_survivor_symmetry
#print axioms physical_carry_one_exact_cubic_recurrence
#print axioms cubic_seed_coefficients
#print axioms original_bad_trajectory_cubic

end GSTProblem406CarryCubicRecurrence
