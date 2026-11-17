import GSTFourPowerDirectAdditionCarry

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerDirectNo22

open GSTFourPowerDirectResidue
open GSTFourPowerDirectAdditionCarry

/-- If a source digit is `2`, a zero next binary carry occurs exactly from the
forbidden `(previous digit, carry bit) = (0,0)` state. -/
theorem next_binary_zero_after_two_iff
    (prev bit : Nat) (hprev : prev < 3) (hbit : bit < 2) :
    (2 + prev + bit) / 3 = 0 ↔ (prev = 0 ∧ bit = 0) := by
  interval_cases prev <;> interval_cases bit <;> norm_num

/-- Under a globally no-common multiplication-by-four trace, every source
`2` forces the following binary carry bit to be `1`.  Otherwise the current
row would be the `(0,0) -> 2` forbidden common-two edge. -/
theorem source_two_forces_next_binary_one_of_no_common
    (R p : Nat) (hp : 1 ≤ p)
    (hNo : ¬ ∃ q : Nat, 1 ≤ q ∧
      digit3 R q = 2 ∧ digit3 (4*R) q = 2)
    (h2 : digit3 R p = 2) :
    binaryCarry R (p+1) = 1 := by
  have hbnext : binaryCarry R (p+1) < 2 :=
    binaryCarry_lt_two R (p+1) (by omega)
  have hrec := binaryCarry_forward_exact R p hp
  rw [h2] at hrec
  have hprev := digit3_lt_three R (p-1)
  have hbit := binaryCarry_lt_two R p hp
  have hnz : binaryCarry R (p+1) ≠ 0 := by
    intro hz
    have hq :
        (2 + digit3 R (p-1) + binaryCarry R p) / 3 = 0 := by
      rw [← hrec, hz]
    have hzero :=
      (next_binary_zero_after_two_iff
        (digit3 R (p-1)) (binaryCarry R p) hprev hbit).1 hq
    have hcommon :=
      (common_two_row_iff_forbidden_edges R p hp).2
        ⟨h2, Or.inl hzero⟩
    apply hNo
    exact ⟨p, hp, hcommon.1, hcommon.2⟩
  omega

/-- A globally no-common multiplication-by-four trace cannot contain two
consecutive source ternary digits `22` at positive rows. -/
theorem no_common_forbids_source_22
    (R p : Nat) (hp : 1 ≤ p)
    (hNo : ¬ ∃ q : Nat, 1 ≤ q ∧
      digit3 R q = 2 ∧ digit3 (4*R) q = 2)
    (h2 : digit3 R p = 2) :
    digit3 R (p+1) ≠ 2 := by
  intro hnext
  have hb1 := source_two_forces_next_binary_one_of_no_common R p hp hNo h2
  have hprev2 : digit3 R ((p+1)-1) = 2 := by
    simpa using h2
  have hcommon :=
    (common_two_row_iff_forbidden_edges R (p+1) (by omega)).2
      ⟨hnext, Or.inr ⟨hprev2, hb1⟩⟩
  apply hNo
  exact ⟨p+1, by omega, hcommon.1, hcommon.2⟩

/-- Power-specific form: a hypothetical direct counterexample has no `22`
block anywhere at positive ternary rows in the source power `4^K`. -/
theorem no_common_pow4_forbids_positive_22
    (K p : Nat) (hp : 1 ≤ p)
    (hNo : ¬ ∃ q : Nat, 1 ≤ q ∧
      digit3 (4^K) q = 2 ∧ digit3 (4^(K+1)) q = 2) :
    ¬ (digit3 (4^K) p = 2 ∧ digit3 (4^K) (p+1) = 2) := by
  intro h22
  have hNoMul : ¬ ∃ q : Nat, 1 ≤ q ∧
      digit3 (4^K) q = 2 ∧ digit3 (4*(4^K)) q = 2 := by
    intro h
    rcases h with ⟨q, hq, hs, ht⟩
    apply hNo
    refine ⟨q, hq, hs, ?_⟩
    simpa [pow_succ, Nat.mul_comm] using ht
  exact no_common_forbids_source_22 (4^K) p hp hNoMul h22.1 h22.2

/-- Full source-language consequence.  Row zero of a power of four is `1`, so
together with the positive-row theorem a direct counterexample is `22`-free
at every adjacent pair of ternary positions. -/
theorem no_common_pow4_forbids_all_22
    (K : Nat)
    (hNo : ¬ ∃ q : Nat, 1 ≤ q ∧
      digit3 (4^K) q = 2 ∧ digit3 (4^(K+1)) q = 2) :
    ∀ p : Nat, ¬ (digit3 (4^K) p = 2 ∧ digit3 (4^K) (p+1) = 2) := by
  intro p h22
  by_cases hp0 : p = 0
  · subst p
    have h0 := (pow4_binary_initial_state K).1
    omega
  · have hp : 1 ≤ p := by omega
    exact no_common_pow4_forbids_positive_22 K p hp hNo h22

#check next_binary_zero_after_two_iff
#check source_two_forces_next_binary_one_of_no_common
#check no_common_forbids_source_22
#check no_common_pow4_forbids_positive_22
#check no_common_pow4_forbids_all_22
#print axioms source_two_forces_next_binary_one_of_no_common
#print axioms no_common_forbids_source_22
#print axioms no_common_pow4_forbids_positive_22
#print axioms no_common_pow4_forbids_all_22

end GSTFourPowerDirectNo22
