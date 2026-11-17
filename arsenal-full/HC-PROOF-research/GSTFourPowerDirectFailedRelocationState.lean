import GSTFourPowerDirectExistence
import GSTFourPowerDirectNo22

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerDirectFailedRelocationState

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerDirectAdditionCarry
open GSTFourPowerDirectNo22

/-- A failed relocation has a rigid physical arithmetic state immediately
above every source common-two witness.  If row `p` is common for `4^K` and
`4^(K+1)`, but the next sheet has no common-two row anywhere, then on the
`4^(K+1)` source for the next x4 step:

* the binary carry entering row `p+1` is exactly one;
* hence the physical multiplication carry there is exactly three; and
* the source digit at row `p+1` is not two.

This is the direct-arithmetic replacement for the old latent navigation
packet.  It uses the actual witness row and no witness transport. -/
theorem failed_relocation_forces_post_witness_state
    (K p : Nat) (hp : 1 ≤ p)
    (hSource : digit3 (4^K) p = 2)
    (hTarget : digit3 (4^(K+1)) p = 2)
    (hNoNext : ¬ CommonTwo (K+1)) :
    binaryCarry (4^(K+1)) (p+1) = 1 ∧
      directCarry4 (4^(K+1)) (p+1) = 3 ∧
      digit3 (4^(K+1)) (p+1) ≠ 2 := by
  have hNoMul : ¬ ∃ q : Nat, 1 ≤ q ∧
      digit3 (4^(K+1)) q = 2 ∧
      digit3 (4 * (4^(K+1))) q = 2 := by
    intro h
    rcases h with ⟨q, hq, hs, ht⟩
    apply hNoNext
    refine ⟨q, hq, hs, ?_⟩
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using ht
  have hbit : binaryCarry (4^(K+1)) (p+1) = 1 :=
    source_two_forces_next_binary_one_of_no_common
      (4^(K+1)) p hp hNoMul hTarget
  have hcarryEq :=
    directCarry4_eq_prev_digit_add_binary (4^(K+1)) (p+1) (by omega)
  have hprev : digit3 (4^(K+1)) ((p+1)-1) = 2 := by
    simpa using hTarget
  rw [hprev, hbit] at hcarryEq
  have hcarry : directCarry4 (4^(K+1)) (p+1) = 3 := by
    omega
  have hnot2 : digit3 (4^(K+1)) (p+1) ≠ 2 :=
    no_common_forbids_source_22 (4^(K+1)) p hp hNoMul hTarget
  exact ⟨hbit, hcarry, hnot2⟩

/-- The forced carry-three state is an exact equal-digit row for the next x4
step.  Carry three is invisible modulo three, so multiplication by four leaves
the row digit unchanged.  Since relocation was assumed to fail, that common
value is necessarily `0` or `1`, never `2`. -/
theorem failed_relocation_forces_equal_non_two_row
    (K p : Nat) (hp : 1 ≤ p)
    (hSource : digit3 (4^K) p = 2)
    (hTarget : digit3 (4^(K+1)) p = 2)
    (hNoNext : ¬ CommonTwo (K+1)) :
    directCarry4 (4^(K+1)) (p+1) = 3 ∧
      digit3 (4^(K+1)) (p+1) = digit3 (4^(K+2)) (p+1) ∧
      digit3 (4^(K+1)) (p+1) < 2 := by
  have hstate :=
    failed_relocation_forces_post_witness_state K p hp hSource hTarget hNoNext
  have hcarry : directCarry4 (4^(K+1)) (p+1) = 3 := hstate.2.1
  have hnot2 : digit3 (4^(K+1)) (p+1) ≠ 2 := hstate.2.2
  have hdlt : digit3 (4^(K+1)) (p+1) < 3 :=
    digit3_lt_three (4^(K+1)) (p+1)
  have hformula := digit3_four_mul (4^(K+1)) (p+1)
  rw [hcarry] at hformula
  have hmod : digit3 (4^(K+1)) (p+1) % 3 =
      digit3 (4^(K+1)) (p+1) := Nat.mod_eq_of_lt hdlt
  have hmulEq :
      digit3 (4 * (4^(K+1))) (p+1) = digit3 (4^(K+1)) (p+1) := by
    calc
      digit3 (4 * (4^(K+1))) (p+1)
          = (digit3 (4^(K+1)) (p+1) + 3) % 3 := hformula
      _ = digit3 (4^(K+1)) (p+1) % 3 := by
            simp [Nat.add_mod]
      _ = digit3 (4^(K+1)) (p+1) := hmod
  have ht : digit3 (4^(K+2)) (p+1) = digit3 (4^(K+1)) (p+1) := by
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmulEq
  exact ⟨hcarry, ht.symm, by omega⟩

/-- Bundled existential form starting from the actual source `CommonTwo`
witness.  Any hypothetical failure of relocation therefore produces a real
row `p ≥ 1` whose next physical carry is exactly three. -/
theorem commonTwo_failed_relocation_has_carry_three_row
    (K : Nat) (hCommon : CommonTwo K) (hNoNext : ¬ CommonTwo (K+1)) :
    ∃ p : Nat, 1 ≤ p ∧
      digit3 (4^K) p = 2 ∧
      digit3 (4^(K+1)) p = 2 ∧
      directCarry4 (4^(K+1)) (p+1) = 3 ∧
      digit3 (4^(K+1)) (p+1) ≠ 2 := by
  rcases hCommon with ⟨p, hp, hs, ht⟩
  have hstate :=
    failed_relocation_forces_post_witness_state K p hp hs ht hNoNext
  exact ⟨p, hp, hs, ht, hstate.2.1, hstate.2.2⟩

/-- Strong bundled form: failed relocation exposes an actual row `q ≥ 2` on
the next sheet where the physical carry is three and the consecutive powers
have the same non-two ternary digit. -/
theorem commonTwo_failed_relocation_has_equal_non_two_row
    (K : Nat) (hCommon : CommonTwo K) (hNoNext : ¬ CommonTwo (K+1)) :
    ∃ q : Nat, 2 ≤ q ∧
      directCarry4 (4^(K+1)) q = 3 ∧
      digit3 (4^(K+1)) q = digit3 (4^(K+2)) q ∧
      digit3 (4^(K+1)) q < 2 := by
  rcases hCommon with ⟨p, hp, hs, ht⟩
  have hrow :=
    failed_relocation_forces_equal_non_two_row K p hp hs ht hNoNext
  exact ⟨p+1, by omega, hrow.1, hrow.2.1, hrow.2.2⟩

/-- One more exact automaton step out of the failed-relocation carry-three
state.  If the previous source digit is two, the current binary carry is one,
and the current digit is the forced non-two value `0` or `1`, then the next
binary carry is again exactly one. -/
theorem carry_three_non_two_state_forces_next_binary_one
    (R q : Nat) (hq : 1 ≤ q)
    (hprev : digit3 R (q-1) = 2)
    (hbit : binaryCarry R q = 1)
    (hcur : digit3 R q < 2) :
    binaryCarry R (q+1) = 1 := by
  have hrec := binaryCarry_forward_exact R q hq
  rw [hprev, hbit] at hrec
  have hd : digit3 R q = 0 ∨ digit3 R q = 1 := by omega
  rcases hd with hd | hd
  · rw [hd] at hrec
    norm_num at hrec ⊢
    exact hrec
  · rw [hd] at hrec
    norm_num at hrec ⊢
    exact hrec

/-- Therefore the next physical multiplication carry is no longer four-valued:
it is exactly `d+1`, where `d` is the forced equal non-two digit at the current
row.  In particular it is physically either one or two. -/
theorem carry_three_non_two_state_next_carry
    (R q : Nat) (hq : 1 ≤ q)
    (hprev : digit3 R (q-1) = 2)
    (hbit : binaryCarry R q = 1)
    (hcur : digit3 R q < 2) :
    directCarry4 R (q+1) = digit3 R q + 1 ∧
      (directCarry4 R (q+1) = 1 ∨ directCarry4 R (q+1) = 2) := by
  have hbnext :=
    carry_three_non_two_state_forces_next_binary_one R q hq hprev hbit hcur
  have hcarry := directCarry4_eq_prev_digit_add_binary R (q+1) (by omega)
  have hshape : (q+1)-1 = q := by omega
  rw [hshape, hbnext] at hcarry
  constructor
  · exact hcarry
  · omega

/-- Bundled physical transition produced by a failed relocation.  Starting
from the actual source common-two witness, row `q=p+1 ≥ 2` has carry three and
an equal digit `0` or `1`; one row later the binary carry is forced to remain
one and the physical carry is forced into `{1,2}`.  This is a deterministic
local arithmetic path, not navigation or witness transport. -/
theorem commonTwo_failed_relocation_two_step_physical_state
    (K : Nat) (hCommon : CommonTwo K) (hNoNext : ¬ CommonTwo (K+1)) :
    ∃ q : Nat, 2 ≤ q ∧
      directCarry4 (4^(K+1)) q = 3 ∧
      digit3 (4^(K+1)) q = digit3 (4^(K+2)) q ∧
      digit3 (4^(K+1)) q < 2 ∧
      binaryCarry (4^(K+1)) (q+1) = 1 ∧
      (directCarry4 (4^(K+1)) (q+1) = 1 ∨
       directCarry4 (4^(K+1)) (q+1) = 2) := by
  rcases hCommon with ⟨p, hp, hs, ht⟩
  have hstate :=
    failed_relocation_forces_post_witness_state K p hp hs ht hNoNext
  have heq :=
    failed_relocation_forces_equal_non_two_row K p hp hs ht hNoNext
  let q := p+1
  have hprev : digit3 (4^(K+1)) (q-1) = 2 := by
    dsimp [q]
    simpa using ht
  have hbq : binaryCarry (4^(K+1)) q = 1 := by
    dsimp [q]
    exact hstate.1
  have hcur : digit3 (4^(K+1)) q < 2 := by
    dsimp [q]
    exact heq.2.2
  have hbnext :=
    carry_three_non_two_state_forces_next_binary_one
      (4^(K+1)) q (by omega) hprev hbq hcur
  have hnextcarry :=
    carry_three_non_two_state_next_carry
      (4^(K+1)) q (by omega) hprev hbq hcur
  refine ⟨q, by omega, ?_, ?_, hcur, hbnext, hnextcarry.2⟩
  · dsimp [q]
    exact heq.1
  · dsimp [q]
    exact heq.2.1

#check failed_relocation_forces_post_witness_state
#check failed_relocation_forces_equal_non_two_row
#check commonTwo_failed_relocation_has_carry_three_row
#check commonTwo_failed_relocation_has_equal_non_two_row
#check carry_three_non_two_state_forces_next_binary_one
#check carry_three_non_two_state_next_carry
#check commonTwo_failed_relocation_two_step_physical_state
#print axioms failed_relocation_forces_post_witness_state
#print axioms failed_relocation_forces_equal_non_two_row
#print axioms commonTwo_failed_relocation_has_carry_three_row
#print axioms commonTwo_failed_relocation_has_equal_non_two_row
#print axioms carry_three_non_two_state_forces_next_binary_one
#print axioms carry_three_non_two_state_next_carry
#print axioms commonTwo_failed_relocation_two_step_physical_state

end GSTFourPowerDirectFailedRelocationState
