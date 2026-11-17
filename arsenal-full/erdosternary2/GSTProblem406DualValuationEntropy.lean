import GSTProblem406CarryEntropyBound
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST exact weighted four-state carry-entropy contraction

This sharpens the inherited universal 7-of-9 bound by an exact
four-state super-eigenvector w=(7,10,10,8) for the original physical
source-neighbor no-common-two carry transition matrix M:

M*w=(17,25,25,20), and 2*M*w <= 5*w componentwise.

For EVERY depth n, the count S_n(c) of surviving ternary source
prefixes satisfies 7*2^n*S_n(c) <= w(c)*5^n, so in the actual
affine source-neighbor carry c=1, S_n(1) <= (10/7)*(5/2)^n.

This is a GLOBAL rigorous entropy improvement over 7^(n/2),
not a universal physical-exponent witness. The remaining dual-radix
challenge is exclusion of the particular high-binary-order source
R=4^K from the survivor set, not merely density zero.
-/

namespace GSTProblem406DualValuationEntropy

open GSTProblem406CarryEntropyBound

/-- Integer-scale count to avoid rational or floating estimates. -/
def scaledSurvivingCount (n c : Nat) : Nat :=
  7 * 2^n * survivingCount n c

private theorem scaled_count_succ_zero (n : Nat) :
    scaledSurvivingCount (n+1) 0 =
      2*(scaledSurvivingCount n 0+scaledSurvivingCount n 1) := by
  simp [scaledSurvivingCount, survivingCount, pow_succ]
  ring

private theorem scaled_count_succ_one (n : Nat) :
    scaledSurvivingCount (n+1) 1 =
      2*(scaledSurvivingCount n 0+scaledSurvivingCount n 1+
        scaledSurvivingCount n 3) := by
  simp [scaledSurvivingCount, survivingCount, pow_succ]
  ring

private theorem scaled_count_succ_two (n : Nat) :
    scaledSurvivingCount (n+1) 2 =
      2*(scaledSurvivingCount n 0+scaledSurvivingCount n 2+
        scaledSurvivingCount n 3) := by
  simp [scaledSurvivingCount, survivingCount, pow_succ]
  ring

private theorem scaled_count_succ_three (n : Nat) :
    scaledSurvivingCount (n+1) 3 =
      2*(scaledSurvivingCount n 1+scaledSurvivingCount n 2) := by
  simp [scaledSurvivingCount, survivingCount, pow_succ]
  ring

/-- All four carry controllers satisfy the same exact weighted
integer eigenbarrier at EVERY depth, without an all-exponent gate. -/
theorem four_state_weighted_entropy_all_depths (n : Nat) :
    scaledSurvivingCount n 0 ≤ 7*5^n ∧
    scaledSurvivingCount n 1 ≤ 10*5^n ∧
    scaledSurvivingCount n 2 ≤ 10*5^n ∧
    scaledSurvivingCount n 3 ≤ 8*5^n := by
  induction n with
  | zero =>
      norm_num [scaledSurvivingCount,survivingCount]
  | succ n ih =>
      obtain ⟨h0,h1,h2,h3⟩ := ih
      refine ⟨?_,?_,?_,?_⟩
      · rw [scaled_count_succ_zero,pow_succ]
        omega
      · rw [scaled_count_succ_one,pow_succ]
        omega
      · rw [scaled_count_succ_two,pow_succ]
        omega
      · rw [scaled_count_succ_three,pow_succ]
        omega

/-- Native original-affine carry c=1 has a uniformly improved
physical-prefix survivor bound at every depth n. -/
theorem original_affine_weighted_entropy_bound (n : Nat) :
    7 * 2^n * survivingCount n 1 ≤ 10*5^n := by
  exact (four_state_weighted_entropy_all_depths n).2.1

/-- Concrete bound at twice any depth:
the 7^m old branching factor is replaced by (25/4)^m,
with a fixed 10/7 normalization. -/
theorem original_affine_even_weighted_bound (m : Nat) :
    7 * 4^m * survivingCount (2*m) 1 ≤ 10*25^m := by
  have h := original_affine_weighted_entropy_bound (2*m)
  have h2 : (2:Nat)^(2*m) = 4^m := by
    rw [show (4:Nat)=2^2 by decide, pow_mul]
  have h5 : (5:Nat)^(2*m) = 25^m := by
    rw [show (25:Nat)=5^2 by decide, pow_mul]
  simpa only [h2, h5] using h

#print axioms four_state_weighted_entropy_all_depths
#print axioms original_affine_weighted_entropy_bound
#print axioms original_affine_even_weighted_bound

end GSTProblem406DualValuationEntropy
