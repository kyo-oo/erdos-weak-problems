import GSTGraphV2FourPowerRelocation

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Task33FreshPowerPropagation

open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2FourPowerRelocation

private theorem fresh_index_le_three_pow (r : Nat) : r ≤ 3^r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Nat.pow_succ]
      have hp : 0 < 3^r := by positivity
      omega

/-- A supplied physical Happy row cannot lie beyond the symbolic support
cutoff.  This is derived from the literal nonzero ternary digit of `4^K`, not
from any fixed computational bound. -/
theorem fresh_source_row_below_support_cutoff
    (K p : Nat)
    (hSource :
      HappyCell
        (graph 1 K p).seven.carry
        (graph 1 K p).seven.digit) :
    p + 1 < fourPowerSupportCutoff K := by
  have hDigitGraph :=
    (graph_happy_iff_consecutive_digit_two 1 K p).mp hSource
  have hDigit : GSTCanonicalSevenAxisBridge.digit3 (4^K) p = 2 := by
    simpa [GSTGraphV2InfiniteControl.graph,
      GSTGraphV2InfiniteControl.cell,
      GSTCanonicalSevenAxisBridge.vertex] using hDigitGraph.1
  have hpow : 3^p ≤ 4^K := by
    by_contra hnot
    have hlt : 4^K < 3^p := Nat.lt_of_not_ge hnot
    have hz : GSTCanonicalSevenAxisBridge.digit3 (4^K) p = 0 := by
      simp [GSTCanonicalSevenAxisBridge.digit3, Nat.div_eq_of_lt hlt]
    omega
  have hpindex : p ≤ 3^p := fresh_index_le_three_pow p
  have hpK : p ≤ 4^K := le_trans hpindex hpow
  have hstrict : 4^K < 4^(K+2) := by
    rw [Nat.pow_add]
    norm_num
  simp [fourPowerSupportCutoff]
  omega

/-- Fresh Task 3.3 starting lemma.

This theorem uses only the current production relocation laws.  It does not
import any historical classifier, residual/Omega bridge, origin-descent file,
or previous candidate propagation theorem.

If a source Happy row exists on the `K` sheet but the `(K+1)` sheet has no
Happy row anywhere above row zero, then the source overlap forces an exact
latent seed on the next sheet: the same row still has information digit `2`,
the physical carry there is strictly middle (`1` or `2`), and therefore the
very next vertical carry is exactly `3`.
-/
theorem fresh_failed_edge_forces_latent_seed
    (K p : Nat)
    (hp : 1 ≤ p)
    (hSource :
      HappyCell
        (graph 1 K p).seven.carry
        (graph 1 K p).seven.digit)
    (hNoRelocated : ¬ ∃ q : Nat, 1 ≤ q ∧
      HappyCell
        (graph 1 (K+1) q).seven.carry
        (graph 1 (K+1) q).seven.digit) :
    (graph 1 (K+1) p).seven.digit = 2 ∧
      ((graph 1 (K+1) p).seven.carry = 1 ∨
       (graph 1 (K+1) p).seven.carry = 2) ∧
      (graph 1 (K+1) (p+1)).seven.carry = 3 := by
  have hOverlap :=
    (graph_happy_iff_consecutive_digit_two 1 K p).mp hSource
  have hdNext : (graph 1 (K+1) p).seven.digit = 2 := by
    simpa [Nat.add_assoc] using hOverlap.2

  have hNotHappy :
      ¬ HappyCell
        (graph 1 (K+1) p).seven.carry
        (graph 1 (K+1) p).seven.digit := by
    intro hHappy
    apply hNoRelocated
    exact ⟨p, hp, hHappy⟩

  have hCarryLt : (graph 1 (K+1) p).seven.carry < 4 :=
    graph_carry_lt_four 1 (K+1) p

  have hCarryNeZero : (graph 1 (K+1) p).seven.carry ≠ 0 := by
    intro h0
    apply hNotHappy
    exact ⟨hdNext, Or.inl h0⟩

  have hCarryNeThree : (graph 1 (K+1) p).seven.carry ≠ 3 := by
    intro h3
    apply hNotHappy
    exact ⟨hdNext, Or.inr h3⟩

  have hMiddle :
      (graph 1 (K+1) p).seven.carry = 1 ∨
      (graph 1 (K+1) p).seven.carry = 2 := by
    omega

  have hRec := (graph_cell_exact 1 (K+1) p).2
  have hNextCarry : (graph 1 (K+1) (p+1)).seven.carry = 3 := by
    rcases hMiddle with h1 | h2
    · simpa [h1, hdNext, GST2DMixedEmergence.nextCarry] using hRec.symm
    · simpa [h2, hdNext, GST2DMixedEmergence.nextCarry] using hRec.symm

  exact ⟨hdNext, hMiddle, hNextCarry⟩

/-- A physical nonzero carry can fall to zero in one vertical step only through
input digit zero and carry 1 or 2.  This is the exact local arithmetic of
`nextCarry C d = (C + 4*d)/3`; in particular this boundary is not itself a
Happy cell. -/
theorem fresh_nonzero_predecessor_of_zero_carry
    (C d : Nat)
    (hC : C < 4)
    (hd : d < 3)
    (hCne : C ≠ 0)
    (hzero : nextCarry C d = 0) :
    d = 0 ∧ (C = 1 ∨ C = 2) := by
  simp only [nextCarry] at hzero
  omega

/-- Under literal failure of relocation, the forced carry-three seed must hit
carry zero at a first finite row before the symbolic support cutoff.  This is
a finite witness extracted from the actual `4^(K+1)` sheet, not an arbitrary
terminating word assumption. -/
theorem fresh_failed_edge_has_first_zero_carry
    (K p : Nat)
    (hp : 1 ≤ p)
    (hSource :
      HappyCell
        (graph 1 K p).seven.carry
        (graph 1 K p).seven.digit)
    (hNoRelocated : ¬ ∃ q : Nat, 1 ≤ q ∧
      HappyCell
        (graph 1 (K+1) q).seven.carry
        (graph 1 (K+1) q).seven.digit) :
    let B := fourPowerSupportCutoff K
    ∃ r : Nat,
      p + 1 ≤ r ∧ r < B ∧
      (graph 1 (K+1) r).seven.carry ≠ 0 ∧
      (graph 1 (K+1) (r+1)).seven.carry = 0 := by
  dsimp
  let s := p + 1
  let B := fourPowerSupportCutoff K
  have hsB : s < B := by
    simpa [s, B] using fresh_source_row_below_support_cutoff K p hSource
  have hSeed : (graph 1 (K+1) s).seven.carry = 3 := by
    simpa [s] using
      (fresh_failed_edge_forces_latent_seed K p hp hSource hNoRelocated).2.2
  have hTerminal : (graph 1 (K+1) B).seven.carry = 0 := by
    simpa [B] using (four_power_graph_neutral_at_support_cutoff K).1
  have hsle : s ≤ B := Nat.le_of_lt hsB
  have hzero : ∃ n : Nat, (graph 1 (K+1) (s+n)).seven.carry = 0 := by
    refine ⟨B-s, ?_⟩
    rw [Nat.add_sub_of_le hsle]
    exact hTerminal
  let n0 := Nat.find hzero
  have hn0zero : (graph 1 (K+1) (s+n0)).seven.carry = 0 :=
    Nat.find_spec hzero
  have hn0pos : 0 < n0 := by
    by_contra hnot
    have hn0 : n0 = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hn0] at hn0zero
    simp only [Nat.add_zero] at hn0zero
    rw [hSeed] at hn0zero
    omega
  let r := s + (n0-1)
  have hrnext : r + 1 = s + n0 := by
    dsimp [r]
    omega
  have hrNonzero : (graph 1 (K+1) r).seven.carry ≠ 0 := by
    intro hr0
    have hminimal : n0 ≤ n0 - 1 := by
      apply Nat.find_min'
      simpa [r] using hr0
    omega
  have hrLower : p + 1 ≤ r := by
    dsimp [r, s]
    omega
  have hn0le : n0 ≤ B-s := by
    apply Nat.find_min'
    rw [Nat.add_sub_of_le hsle]
    exact hTerminal
  have hrUpper : r < B := by
    dsimp [r]
    omega
  refine ⟨r, hrLower, hrUpper, hrNonzero, ?_⟩
  rw [hrnext]
  exact hn0zero

/-- The first nonzero-to-zero boundary forced by a failed relocation is exactly
a `(carry,digit) = (1,0)` or `(2,0)` cell on the actual next four-power sheet.
This is deliberately weaker than claiming the boundary is Happy; it records
the true local arithmetic and is the finite endpoint for the global
power-specific contradiction. -/
theorem fresh_failed_edge_first_zero_boundary_classified
    (K p : Nat)
    (hp : 1 ≤ p)
    (hSource :
      HappyCell
        (graph 1 K p).seven.carry
        (graph 1 K p).seven.digit)
    (hNoRelocated : ¬ ∃ q : Nat, 1 ≤ q ∧
      HappyCell
        (graph 1 (K+1) q).seven.carry
        (graph 1 (K+1) q).seven.digit) :
    let B := fourPowerSupportCutoff K
    ∃ r : Nat,
      p + 1 ≤ r ∧ r < B ∧
      (graph 1 (K+1) r).seven.digit = 0 ∧
      ((graph 1 (K+1) r).seven.carry = 1 ∨
       (graph 1 (K+1) r).seven.carry = 2) ∧
      (graph 1 (K+1) (r+1)).seven.carry = 0 := by
  dsimp
  obtain ⟨r, hrLower, hrUpper, hrNe, hrNextZero⟩ :=
    fresh_failed_edge_has_first_zero_carry K p hp hSource hNoRelocated
  have hCLt : (graph 1 (K+1) r).seven.carry < 4 :=
    graph_carry_lt_four 1 (K+1) r
  have hdLt : (graph 1 (K+1) r).seven.digit < 3 :=
    graph_digit_lt_three 1 (K+1) r
  have hRec := (graph_cell_exact 1 (K+1) r).2
  have hNext :
      nextCarry (graph 1 (K+1) r).seven.carry
        (graph 1 (K+1) r).seven.digit = 0 := by
    rw [hRec]
    simpa [Nat.add_assoc] using hrNextZero
  have hClass := fresh_nonzero_predecessor_of_zero_carry
    (graph 1 (K+1) r).seven.carry
    (graph 1 (K+1) r).seven.digit
    hCLt hdLt hrNe hNext
  exact ⟨r, hrLower, hrUpper, hClass.1, hClass.2, hrNextZero⟩

/-- Exact failed-edge obstruction packet for the fresh Task 3.3 proof.

Nothing here weakens or localizes the target existential.  Under the literal
negation of the required relocated witness, every positive row of the
`4^(K+1)` sheet is bad.  The supplied source Happy row forces the exact latent
seed at `p`, its whole vertical future is bad, and the same physical sheet is
exactly neutral at the symbolic four-power support cutoff.

The remaining Task 3.3 mathematics is therefore a power-specific
incompatibility theorem for this finite-support packet. -/
theorem fresh_failed_edge_power_obstruction_packet
    (K p : Nat)
    (hp : 1 ≤ p)
    (hSource :
      HappyCell
        (graph 1 K p).seven.carry
        (graph 1 K p).seven.digit)
    (hNoRelocated : ¬ ∃ q : Nat, 1 ≤ q ∧
      HappyCell
        (graph 1 (K+1) q).seven.carry
        (graph 1 (K+1) q).seven.digit) :
    let B := fourPowerSupportCutoff K
    (graph 1 (K+1) p).seven.digit = 2 ∧
      ((graph 1 (K+1) p).seven.carry = 1 ∨
       (graph 1 (K+1) p).seven.carry = 2) ∧
      (graph 1 (K+1) (p+1)).seven.carry = 3 ∧
      (∀ q : Nat, 1 ≤ q →
        ¬ HappyCell
          (graph 1 (K+1) q).seven.carry
          (graph 1 (K+1) q).seven.digit) ∧
      (∀ r : Nat,
        ¬ HappyCell
          (graph 1 (K+1) (p+1+r)).seven.carry
          (graph 1 (K+1) (p+1+r)).seven.digit) ∧
      (graph 1 (K+1) B).seven.carry = 0 ∧
      (graph 1 (K+1) B).seven.digit = 0 := by
  dsimp
  have hSeed :=
    fresh_failed_edge_forces_latent_seed K p hp hSource hNoRelocated
  have hAllBad : ∀ q : Nat, 1 ≤ q →
      ¬ HappyCell
        (graph 1 (K+1) q).seven.carry
        (graph 1 (K+1) q).seven.digit := by
    intro q hq hHappy
    exact hNoRelocated ⟨q, hq, hHappy⟩
  have hFutureBad :=
    future_bad_of_no_relocated_happy K p hNoRelocated
  have hNeutral := four_power_graph_neutral_at_support_cutoff K
  exact ⟨hSeed.1, hSeed.2.1, hSeed.2.2,
    hAllBad, hFutureBad, hNeutral.1, hNeutral.2⟩

#check fresh_source_row_below_support_cutoff
#print axioms fresh_source_row_below_support_cutoff
#check fresh_failed_edge_forces_latent_seed
#print axioms fresh_failed_edge_forces_latent_seed
#check fresh_nonzero_predecessor_of_zero_carry
#print axioms fresh_nonzero_predecessor_of_zero_carry
#check fresh_failed_edge_has_first_zero_carry
#print axioms fresh_failed_edge_has_first_zero_carry
#check fresh_failed_edge_first_zero_boundary_classified
#print axioms fresh_failed_edge_first_zero_boundary_classified
#check fresh_failed_edge_power_obstruction_packet
#print axioms fresh_failed_edge_power_obstruction_packet

end Task33FreshPowerPropagation