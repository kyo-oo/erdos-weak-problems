import GSTFourPowerThirdWave
import GSTWorldtraceBlockLift
import GSTWorldtraceCoeffStability

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Exact exceptional-seven 3-adic tower: same-row digit-two witnesses

For every L >= 10 and every multiplier u = 1 (mod 3^10),
the *physical* consecutive powers 4^(7+u*3^L) and
4^(8+u*3^L) both have ternary digit 2 at row L+10.

This is a fresh source-seed 7 (the exceptional no-gate exponent),
not the earlier source-seed 4 Worldtrace family.
No universal hGate hypothesis is imported or assumed.
-/

namespace GSTProblem406ExceptionalSevenTower

open GSTCanonicalTailLTE
open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence

/-- The exact LTE coefficient has the frozen ten-trit residue at all
scales 9 and above. -/
theorem coeff_mod59049 (L : Nat) (hL : 9 ≤ L) :
    GSTCanonicalTailLTE.lteCoeff L % 59049 = 42217 := by
  have hstep (t : Nat) (ht : 9 ≤ t) :
      GSTCanonicalTailLTE.lteCoeff (t+1) % 59049 =
      GSTCanonicalTailLTE.lteCoeff t % 59049 := by
    have hdiv : 59049 ∣ 3^(t+1) := by
      have hd : 3^10 ∣ 3^(t+1) := Nat.pow_dvd_pow 3 (by omega)
      simpa only [show (3:Nat)^10=59049 by decide] using hd
    calc
      GSTCanonicalTailLTE.lteCoeff (t+1) % 59049 =
          (GSTCanonicalTailLTE.lteCoeff (t+1) % 3^(t+1)) % 59049 :=
            (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = (GSTCanonicalTailLTE.lteCoeff t % 3^(t+1)) % 59049 := by
            rw [GSTWorldtraceCoeffStability.coeff_step_mod]
      _ = GSTCanonicalTailLTE.lteCoeff t % 59049 :=
            Nat.mod_mod_of_dvd _ hdiv
  have hbase : ∀ k : Nat,
      GSTCanonicalTailLTE.lteCoeff (9+k) % 59049 = 42217 := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
        rw [show 9+(k+1)=(9+k)+1 by omega]
        rw [hstep (9+k) (by omega)]
        exact ih
  rw [show L=9+(L-9) by omega]
  exact hbase (L-9)

/-- Exact physical quotient word on the frozen ten-trit band. -/
private theorem physical_quotient_mod
    (M u L : Nat) (hL : 10 ≤ L)
    (hsmall : 4^M < 3^(L+1)) :
    (4^(M+u*3^L) / 3^(L+1)) % 59049 =
      (u*42217*4^M) % 59049 := by
  have h := GSTWorldtraceBlockLift.pow4_whole_block_lift
    M u L 10 (by decide) (by omega)
  have hz : 4^M / 3^(L+1) = 0 := Nat.div_eq_of_lt hsmall
  have hblock :
      (4^(M+u*3^L) / 3^(L+1)) % 59049 =
        (u*GSTCanonicalTailLTE.lteCoeff L*4^M)%59049 := by
    simpa only [show (3:Nat)^10=59049 by decide, hz, Nat.zero_add] using h
  calc
    (4^(M+u*3^L) / 3^(L+1)) % 59049 =
       (u*GSTCanonicalTailLTE.lteCoeff L*4^M)%59049 := hblock
    _ = (u*(GSTCanonicalTailLTE.lteCoeff L % 59049)*4^M)%59049 := by
      simp [Nat.mul_mod]
    _ = (u*42217*4^M)%59049 := by
      rw [coeff_mod59049 L (by omega)]

/-- Source-seed generality is retained until the final numerical readback:
for any M with a sufficiently short base source, the physical digit
at row L+10 is determined by exactly 42217*4^M modulo 3^10. -/
private theorem physical_digit_from_one_mod
    (M u L : Nat) (hL : 10 ≤ L)
    (hsmall : 4^M < 3^(L+1))
    (hu : u%59049=1) :
    digit3 (4^(M+u*3^L)) (L+10) =
      digit3 (42217*4^M) 9 := by
  have hq := physical_quotient_mod M u L hL hsmall
  have hperiod :
      (u*42217*4^M)%59049 = (42217*4^M)%59049 := by
    calc
      (u*42217*4^M)%59049 =
          ((u%59049)*42217*4^M)%59049 := by
            simp [Nat.mul_mod]
      _ = (42217*4^M)%59049 := by rw [hu]
  have hread :
      digit3 (4^(M+u*3^L)/3^(L+1)) 9 =
        digit3 (42217*4^M) 9 :=
    digit3_eq_of_mod_next _ _ 9 (by
      simpa only [show (3:Nat)^(9+1)=59049 by decide]
        using hq.trans hperiod)
  calc
    digit3 (4^(M+u*3^L)) (L+10) =
        digit3 (4^(M+u*3^L)/3^(L+1)) 9 := by
          unfold digit3
          have hp : 3^(L+10)=3^(L+1)*3^9 := by
            rw [show L+10=(L+1)+9 by omega, pow_add]
          rw [hp, ← Nat.div_div_eq_div_mul]
    _ = digit3 (42217*4^M) 9 := hread

/-- Genuine CommonTwo on an infinite tower centered at exceptional K=7.
The quantified L and u are unbounded and the physical source is 4^K. -/
theorem commonTwo_exceptional_seven_tower
    (L u : Nat) (hL : 10 ≤ L) (hu : u%59049=1) :
    CommonTwo (7+u*3^L) := by
  have hpow : (3:Nat)^11 ≤ 3^(L+1) :=
    Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat)) (by omega)
  have hs : (4:Nat)^7 < 3^(L+1) :=
    lt_of_lt_of_le (by decide : (4:Nat)^7 < 3^11) hpow
  have hn : (4:Nat)^8 < 3^(L+1) :=
    lt_of_lt_of_le (by decide : (4:Nat)^8 < 3^11) hpow
  refine ⟨L+10, by omega, ?_, ?_⟩
  · rw [physical_digit_from_one_mod 7 u L hL hs hu]
    norm_num [digit3]
  · have he : (7+u*3^L)+1=8+u*3^L := by omega
    rw [he, physical_digit_from_one_mod 8 u L hL hn hu]
    norm_num [digit3]

/-- Transfer to the exact original production third-wave gate body. -/
theorem original_thirdWave_exceptional_seven_tower
    (L u : Nat) (hL : 10 ≤ L) (hu : u%59049=1) :
    GSTFourPowerThirdWave.thirdWave (7+u*3^L) := by
  exact (GSTFourPowerThirdWave.thirdWave_iff_commonTwo _).2
    (commonTwo_exceptional_seven_tower L u hL hu)

/-- An entire additional third of the exceptional-seven multiplier
directions fires already at the FIRST postcut row. For u = 2 mod 3
the frozen LTE coefficient and both perfect-power source factors are 1
modulo 3, giving literal digit 2 in both physical sources. -/
private theorem physical_first_cut_two
    (M u L : Nat) (hL : 10 ≤ L)
    (hsmall : 4^M < 3^(L+1))
    (hu : u%3=2) (hM : 4^M%3=1) :
    digit3 (4^(M+u*3^L)) (L+1)=2 := by
  have h := GSTWorldtraceBlockLift.pow4_whole_block_lift
    M u L 1 (by decide) (by omega)
  have hz : 4^M / 3^(L+1)=0 := Nat.div_eq_of_lt hsmall
  have hq :
      (4^(M+u*3^L)/3^(L+1))%3 =
      (u*GSTCanonicalTailLTE.lteCoeff L*4^M)%3 := by
    simpa only [show (3:Nat)^1=3 by decide,
      hz, Nat.zero_add] using h
  have hval : (u*GSTCanonicalTailLTE.lteCoeff L*4^M)%3=2 := by
    calc
      (u*GSTCanonicalTailLTE.lteCoeff L*4^M)%3 =
        ((u%3)*(GSTCanonicalTailLTE.lteCoeff L%3)*(4^M%3))%3 := by
          simp [Nat.mul_mod]
      _ = 2 := by
        rw [hu, GSTCanonicalTailLTE.lteCoeff_mod3_one, hM]
  change (4^(M+u*3^L)/3^(L+1))%3=2
  exact hq.trans hval

/-- Unconditional infinite first-row family beside the rare tenth-row
class. Every L >= 10 and every u = 2 mod 3 is covered, without hGate. -/
theorem commonTwo_exceptional_seven_first_cut
    (L u : Nat) (hL : 10 ≤ L) (hu : u%3=2) :
    CommonTwo (7+u*3^L) := by
  have hpow : (3:Nat)^11 ≤ 3^(L+1) :=
    Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat)) (by omega)
  have hs : (4:Nat)^7 < 3^(L+1) :=
    lt_of_lt_of_le (by decide : (4:Nat)^7 < 3^11) hpow
  have hn : (4:Nat)^8 < 3^(L+1) :=
    lt_of_lt_of_le (by decide : (4:Nat)^8 < 3^11) hpow
  refine ⟨L+1, by omega, ?_, ?_⟩
  · exact physical_first_cut_two 7 u L hL hs hu (by norm_num)
  · have he : (7+u*3^L)+1=8+u*3^L := by omega
    rw [he]
    exact physical_first_cut_two 8 u L hL hn hu (by norm_num)

/-- The original production third wave, on the full u=2 mod3 cone. -/
theorem original_thirdWave_exceptional_seven_first_cut
    (L u : Nat) (hL : 10 ≤ L) (hu : u%3=2) :
    GSTFourPowerThirdWave.thirdWave (7+u*3^L) := by
  exact (GSTFourPowerThirdWave.thirdWave_iff_commonTwo _).2
    (commonTwo_exceptional_seven_first_cut L u hL hu)

#print axioms coeff_mod59049
#print axioms commonTwo_exceptional_seven_first_cut
#print axioms original_thirdWave_exceptional_seven_first_cut
#print axioms commonTwo_exceptional_seven_tower
#print axioms original_thirdWave_exceptional_seven_tower

end GSTProblem406ExceptionalSevenTower
