import GSTProblem406CarryEntropyBound
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST four-state BAD trajectory: certified rational Perron barrier

The original GST no-shared-2 carry transducer has four carry states.
For each state, survivingCount n c counts depth-n BAD continuations.
The old two-trit estimate was at most 7^floor(n/2), with a
three-fold factor in odd depth.

We derive a strictly stronger *all-depth exact integer bound* by
a rational positive-vector supersolution to the carry transfer:

  weights w = [675, 1000, 1000, 806]
  1000 * T w <= 2482 * w       (componentwise)

Here T is the ACTUAL GST carry-state transfer; its four rows are:
[1,1,0,0], [1,1,0,1], [1,0,1,1], [0,1,1,0].

All four inequalities are integer exact:
1000*(675+1000) <= 2482*675,
1000*(675+1000+806) <= 2482*1000,
1000*(675+1000+806) <= 2482*1000,
1000*(1000+1000) <= 2482*806.

Therefore, from all-ones initial state, for every depth n,
  675 * 1000^n * survivingCount n 1 <= 1000 * 2482^n.
The new growth bound is 2.482^n, improving the old sqrt(7)^n
~2.64575^n without a universal hGate or any custom axiom.

This is a cardinality/entropy bound. Even an exponentially
shrinking fraction of BAD paths does NOT imply that the literal
natural exponent of a given 4^K cannot be BAD.
-/

namespace GSTProblem406RationalPerronBound

open GSTProblem406CarryEntropyBound

/-- Exact positive-vector one-step supersolution for the physical
four-state GST BAD automaton. No spectral approximation is assumed. -/
theorem exact_weighted_carry_barrier :
    1000 * (675 + 1000) ≤ 2482 * 675 ∧
    1000 * (675 + 1000 + 806) ≤ 2482 * 1000 ∧
    1000 * (675 + 1000 + 806) ≤ 2482 * 1000 ∧
    1000 * (1000 + 1000) ≤ 2482 * 806 := by
  decide

/-- Universal, simultaneous, exact integer exponential barrier
on every one of the four GST carry states. -/
theorem physical_survivors_rational_barrier :
    ∀ n : Nat,
      (675 * 1000^n * survivingCount n 0 ≤ 675 * 2482^n) ∧
      (675 * 1000^n * survivingCount n 1 ≤ 1000 * 2482^n) ∧
      (675 * 1000^n * survivingCount n 2 ≤ 1000 * 2482^n) ∧
      (675 * 1000^n * survivingCount n 3 ≤ 806 * 2482^n) := by
  intro n
  induction n with
  | zero =>
      norm_num [survivingCount]
  | succ n ih =>
      rcases ih with ⟨ha, hb, hc, hd⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · calc
          675 * 1000^(n+1) * survivingCount (n+1) 0 =
              1000 * (675 * 1000^n * survivingCount n 0 +
                675 * 1000^n * survivingCount n 1) := by
                simp [survivingCount, pow_succ]
                ring
          _ ≤ 1000 * (675 * 2482^n + 1000 * 2482^n) :=
                Nat.mul_le_mul_left 1000 (Nat.add_le_add ha hb)
          _ ≤ 675 * 2482^(n+1) := by
                rw [pow_succ]
                omega
      · calc
          675 * 1000^(n+1) * survivingCount (n+1) 1 =
              1000 * (675 * 1000^n * survivingCount n 0 +
                675 * 1000^n * survivingCount n 1 +
                675 * 1000^n * survivingCount n 3) := by
                simp [survivingCount, pow_succ]
                ring
          _ ≤ 1000 * (675 * 2482^n + 1000 * 2482^n +
                  806 * 2482^n) := by
                exact Nat.mul_le_mul_left 1000
                  (Nat.add_le_add (Nat.add_le_add ha hb) hd)
          _ ≤ 1000 * 2482^(n+1) := by
                rw [pow_succ]
                omega
      · calc
          675 * 1000^(n+1) * survivingCount (n+1) 2 =
              1000 * (675 * 1000^n * survivingCount n 0 +
                675 * 1000^n * survivingCount n 2 +
                675 * 1000^n * survivingCount n 3) := by
                simp [survivingCount, pow_succ]
                ring
          _ ≤ 1000 * (675 * 2482^n + 1000 * 2482^n +
                  806 * 2482^n) := by
                exact Nat.mul_le_mul_left 1000
                  (Nat.add_le_add (Nat.add_le_add ha hc) hd)
          _ ≤ 1000 * 2482^(n+1) := by
                rw [pow_succ]
                omega
      · calc
          675 * 1000^(n+1) * survivingCount (n+1) 3 =
              1000 * (675 * 1000^n * survivingCount n 1 +
                675 * 1000^n * survivingCount n 2) := by
                simp [survivingCount, pow_succ]
                ring
          _ ≤ 1000 * (1000 * 2482^n + 1000 * 2482^n) :=
                Nat.mul_le_mul_left 1000 (Nat.add_le_add hb hc)
          _ ≤ 806 * 2482^(n+1) := by
                rw [pow_succ]
                omega

/-- Direct sharpened exact upper count at the original incoming
carry-one physical source. -/
theorem original_source_entropy_2482 (n : Nat) :
    675 * 1000^n * survivingCount n 1 ≤ 1000 * 2482^n :=
  (physical_survivors_rational_barrier n).2.1

/-- Entire BAD carrier language obeys a single rational
exponential envelope; this does not claim survivor emptiness. -/
theorem all_carry_states_entropy_2482 (n c : Nat)
    (hc : c < 4) :
    675 * 1000^n * survivingCount n c ≤ 1000 * 2482^n := by
  obtain ⟨h0,h1,h2,h3⟩ := physical_survivors_rational_barrier n
  interval_cases c <;> omega

#print axioms exact_weighted_carry_barrier
#print axioms physical_survivors_rational_barrier
#print axioms original_source_entropy_2482
#print axioms all_carry_states_entropy_2482

end GSTProblem406RationalPerronBound
