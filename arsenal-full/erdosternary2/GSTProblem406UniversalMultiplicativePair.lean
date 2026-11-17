import GSTProblem406SyndeticArchimedeanGate
import GSTFourPowerDirectNo22
import GSTFourPowerNo22Magnitude

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Universal positive-integer multiplicative pair theorem

For every natural A > 0, there exists 0 <= j <= 18 such that the
actual integers A*4^j and 4*A*4^j share a ternary digit 2 at p >= 1.
This is a MUCH broader theorem than the power-of-four source family.

The proof removes the least ternary digit. Under absence of a
positive-row pair, the entire tail cannot contain adjacent 22.
The 19-shift Archimedean cover is applied relative to odd ternary
powers 3*9^n, then the global sharp no22 magnitude bound gives the
contradiction. A=1 and A=2 are checked by exact finite arithmetic.
-/

namespace GSTProblem406UniversalMultiplicativePair

open GSTFourPowerDirectResidue
open GSTProblem406SyndeticArchimedeanGate

/-- No shared digit 2 at a positive row forces the ternary tail
after division by 3 to avoid EVERY adjacent 22 block. -/
theorem no_positive_pair_implies_no22_tail
    (R : Nat)
    (hNo : ¬∃ p : Nat, 1 ≤ p ∧
      digit3 R p=2 ∧ digit3 (4*R) p=2) :
    GSTFourPowerNo22Magnitude.No22Ternary (R/3) := by
  intro t ht
  have hsh1 := GSTFourPowerNo22Magnitude.digit3_div_three_pow_shift R 1 t
  have hsh2 := GSTFourPowerNo22Magnitude.digit3_div_three_pow_shift R 1 (t+1)
  have hs : digit3 R (t+1) = 2 := by
    have hh : digit3 (R/3) t = digit3 R (1+t) := by
      simpa using hsh1
    simpa [Nat.add_comm] using hh.symm.trans ht.1
  have hn : digit3 R ((t+1)+1) = 2 := by
    have hh : digit3 (R/3) (t+1) = digit3 R (1+(t+1)) := by
      simpa using hsh2
    simpa [Nat.add_comm, Nat.add_assoc] using hh.symm.trans ht.2
  have hforbid :=
    GSTFourPowerDirectNo22.no_common_forbids_source_22
      R (t+1) (by omega) hNo hs
  exact hforbid hn

/-- Physical archimedean escape for an arbitrary A>=3 relative to an
ODD ternary power, obtained from the proven 19-piece phase cover. -/
theorem odd_power_escape_within_eighteen
    (A : Nat) (hA : 3 ≤ A) :
    ∃ j m : Nat, j ≤ 18 ∧
      A*4^j < 3*9^m ∧ 7*(3*9^m) < 8*(A*4^j) := by
  have hmod : A%3 < 3 := Nat.mod_lt A (by decide)
  have hsplit : A%3 + 3*(A/3) = A := Nat.mod_add_div A 3
  have hQpos : 0 < A/3 := by omega
  obtain ⟨n,hnlo,hnhi⟩ :=
    exists_nine_envelope (A/3) hQpos
  let B := 3*9^n
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hBelow : B ≤ A := by dsimp [B]; omega
  have hp : 9^(n+1) = 9*9^n := by rw [pow_succ]; ring
  have hAbove : A < 9*B := by
    dsimp [B]
    omega
  obtain ⟨j,e,hj,hwin⟩ := phase_cover_nineteen A B hBpos hBelow hAbove
  unfold PhaseHit at hwin
  refine ⟨j,n+e,hj,?_,?_⟩
  · simpa [B, pow_add, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hwin.1
  · simpa [B, pow_add, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hwin.2

/-- The universal physical collision, for ALL positive integer sources A.
Within at most eighteen multiplications by four, consecutive orbit
iterates have the SAME ternary digit two at a positive row. -/
theorem any_positive_source_pair_within_eighteen
    (A : Nat) (hA : 0 < A) :
    ∃ j : Nat, j ≤ 18 ∧
      ∃ p : Nat, 1 ≤ p ∧
        digit3 (A*4^j) p=2 ∧
        digit3 (4*(A*4^j)) p=2 := by
  by_cases hA1 : A=1
  · subst A
    refine ⟨5,by decide,2,by decide,?_,?_⟩
    · norm_num [digit3]
    · norm_num [digit3]
  by_cases hA2 : A=2
  · subst A
    refine ⟨3,by decide,2,by decide,?_,?_⟩
    · norm_num [digit3]
    · norm_num [digit3]
  have hA3 : 3 ≤ A := by omega
  obtain ⟨j,m,hj,hsmall,htop⟩ :=
    odd_power_escape_within_eighteen A hA3
  refine ⟨j,hj,?_⟩
  by_contra hNo
  let R := A*4^j
  have hNoR : ¬∃ p : Nat, 1 ≤ p ∧
      digit3 R p=2 ∧ digit3 (4*R) p=2 := hNo
  have hword :
      GSTFourPowerNo22Magnitude.No22Ternary (R/3) :=
    no_positive_pair_implies_no22_tail R hNoR
  have hmod : R%3 < 3 := Nat.mod_lt R (by decide)
  have hsplit : R%3 + 3*(R/3) = R := Nat.mod_add_div R 3
  have hbelow : R/3 < 9^m := by
    omega
  have htop' : 7*(9^m-1) < 8*(R/3) := by
    have hpowpos : 0 < 9^m := by positivity
    omega
  have hbound :=
    GSTFourPowerNo22Magnitude.no22_nine_power_bound
      (R/3) m hbelow hword
  omega

#print axioms no_positive_pair_implies_no22_tail
#print axioms odd_power_escape_within_eighteen
#print axioms any_positive_source_pair_within_eighteen

end GSTProblem406UniversalMultiplicativePair
