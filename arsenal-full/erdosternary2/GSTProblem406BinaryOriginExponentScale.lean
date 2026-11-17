import GSTFourPowerDirectResidue
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST Problem 406: exact all-exponent binary/ternary physical-source gap

Unlike an arbitrary source automaton, the original physical source is 4^K.
For EVERY K >= 13, its ternary expansion fits below row floor((4K-1)/3),
while its binary valuation is 2K, which is STRICTLY greater than
3/2 times this row cutoff. This is proved unconditionally from the
3-step inequality 4^3 < 3^4 and the three checked origin cases.

This theorem does not assume CommonTwo, a global hGate or an arbitrary
source valuation-bound conjecture. The latter is a separate unproved
research route and MUST NOT be imported as an axiom.
-/

namespace GSTProblem406BinaryOriginExponentScale

open GSTFourPowerDirectResidue

/-- A rigorous uniform ternary endpoint for a genuine 4-power source. -/
def physicalShortCut (K : Nat) : Nat := (4*K-1)/3

/-- The exact physical 3-step exponential growth is strictly dominated
by the corresponding 4-step ternary place-value growth. -/
private theorem four_cubed_lt_three_fourth :
    (4:Nat)^3 < 3^4 := by decide

/-- For all actual exponents K>=13, a source is shorter than a strict
four-thirds-of-K ternary cut. The proof does not assume any digit hit. -/
theorem physical_source_lt_short_cut
    (K : Nat) (hK : 13 ≤ K) :
    (4:Nat)^K < 3^(physicalShortCut K) := by
  induction K using Nat.strongRecOn with
  | ind K ih =>
    by_cases hSmall : K < 16
    · have hc : K=13 ∨ K=14 ∨ K=15 := by omega
      rcases hc with h | h | h
      · subst K
        decide
      · subst K
        decide
      · subst K
        decide
    · have hKprev : 13 ≤ K-3 := by omega
      have hprev := ih (K-3) (by omega) hKprev
      have hE : physicalShortCut K =
          physicalShortCut (K-3) + 4 := by
        unfold physicalShortCut
        omega
      have hp : (4:Nat)^K = 4^(K-3)*4^3 := by
        conv_lhs => rw [show K = (K-3)+3 by omega]
        rw [pow_add]
      calc
        4^K = 4^(K-3)*4^3 := hp
        _ < 3^(physicalShortCut (K-3))*4^3 :=
          Nat.mul_lt_mul_of_pos_right hprev (by decide)
        _ < 3^(physicalShortCut (K-3))*3^4 :=
          Nat.mul_lt_mul_of_pos_left four_cubed_lt_three_fourth
            (by positivity)
        _ = 3^(physicalShortCut K) := by rw [hE, pow_add]

/-- The endpoint leaves a strict full binary-valuation margin.
This is the native GST two-scale inequality, for EVERY K>=13. -/
theorem strict_binary_origin_scale_gap
    (K : Nat) (hK : 13 ≤ K) :
    3 * physicalShortCut K < 4*K := by
  unfold physicalShortCut
  omega

/-- The true source 4^K carries a binary order ABOVE 3/2 times the
uniform ternary endpoint; no custom hypothesis is needed. -/
theorem physical_source_high_binary_order
    (K : Nat) (hK : 13 ≤ K) :
    (2:Nat)^((3*physicalShortCut K)/2+1) ∣ 4^K := by
  have hgap := strict_binary_origin_scale_gap K hK
  have hle : (3*physicalShortCut K)/2+1 ≤ 2*K := by omega
  have hd : (2:Nat)^((3*physicalShortCut K)/2+1) ∣ 2^(2*K) :=
    pow_dvd_pow 2 hle
  simpa only [show (4:Nat) = 2^2 by decide, pow_mul] using hd

/-- Every original ternary source digit at or above the new exact
K-dependent terminal cut is zero. This is stronger than the older
2(K+1)+1 endpoint and is proved without a shared-two witness. -/
theorem physical_source_digit_zero_above_short_cut
    (K p : Nat) (hK : 13 ≤ K)
    (hp : physicalShortCut K ≤ p) :
    digit3 (4^K) p = 0 := by
  have hpow : (3:Nat)^(physicalShortCut K) ≤ 3^p := by
    gcongr
    omega
  have hlt : (4:Nat)^K < 3^p :=
    lt_of_lt_of_le (physical_source_lt_short_cut K hK) hpow
  unfold digit3
  rw [Nat.div_eq_of_lt hlt]

#print axioms physical_source_lt_short_cut
#print axioms strict_binary_origin_scale_gap
#print axioms physical_source_high_binary_order
#print axioms physical_source_digit_zero_above_short_cut

/-- The exact binary terminal exponent singled out by the physical ternary
cut. This is deliberately the literal K-dependent source, not the larger
class of all multiples of 2^t. -/
def physicalBinaryThreshold (K : Nat) : Nat :=
  (3*physicalShortCut K)/2+1

/-- Exact all-exponent trichotomy, not merely high binary divisibility:
the original source 4^K is ONE of the two extremal binary source values.
The proof contains no CommonTwo, no hGate, and no custom axiom. -/
theorem physical_source_exact_binary_threshold
    (K : Nat) (hK : 13 ≤ K) :
    (K%3=0 ∧ (4:Nat)^K = 2^(physicalBinaryThreshold K+1)) ∨
    (K%3≠0 ∧ (4:Nat)^K = 2^(physicalBinaryThreshold K)) := by
  have hPower : (4:Nat)^K = 2^(2*K) := by
    calc
      4^K = (2^2)^K := by norm_num
      _ = 2^(2*K) := by rw [pow_mul]
  have hc : K%3=0 ∨ K%3=1 ∨ K%3=2 := by omega
  rcases hc with h0 | h1 | h2
  · left
    constructor
    · exact h0
    · rw [hPower]
      congr 1
      unfold physicalBinaryThreshold physicalShortCut
      omega
  · right
    constructor
    · omega
    · rw [hPower]
      congr 1
      unfold physicalBinaryThreshold physicalShortCut
      omega
  · right
    constructor
    · omega
    · rw [hPower]
      congr 1
      unfold physicalBinaryThreshold physicalShortCut
      omega

/-- Physical exponent shift K↦K+3 transports the two physical
scales by (L,t)↦(L+4,t+6). This is an exact scale identity,
not an assumed collision transport theorem. -/
theorem physical_scales_at_three_step
    (K : Nat) (hK : 13 ≤ K) :
    physicalShortCut (K+3) = physicalShortCut K+4 ∧
    physicalBinaryThreshold (K+3) = physicalBinaryThreshold K+6 := by
  constructor
  · unfold physicalShortCut
    omega
  · unfold physicalBinaryThreshold physicalShortCut
    omega

#print axioms physical_source_exact_binary_threshold
#print axioms physical_scales_at_three_step

end GSTProblem406BinaryOriginExponentScale
