import GSTProblem406ExceptionalSevenTower
import GSTWorldtraceBlockLift
import GSTFourPowerThirdWave

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Full ten-trit exceptional-seven physical gate classifier

A fixed ten-trit residue certificate is transferred to genuine consecutive
perfect powers at ALL arbitrarily large 3-adic scales L >= 10.
Unlike a finite scan of exponents, this is uniform in unbounded L and u.
It is a *sufficient criterion* and is not a proof of the universal hGate.
-/

namespace GSTProblem406ExceptionalSevenTenBand

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTProblem406ExceptionalSevenTower

/-- Exact finite arithmetic predicate on the multiplier, involving both
physical source and neighbor coefficients at once. -/
def TenBandHit (u : Nat) : Prop :=
  ∃ j : Nat, j < 10 ∧
    digit3 (u*42217*4^7) j = 2 ∧
    digit3 (u*42217*4^8) j = 2

/-- The first ten ternary digits are determined by the modulus 3^10. -/
private theorem ten_band_digit_period (M u j : Nat) (hj : j < 10) :
    digit3 (u*42217*4^M) j =
      digit3 ((u%59049)*42217*4^M) j := by
  apply digit3_eq_of_mod_next
  have hdiv : 3^(j+1) ∣ 59049 := by
    have hd : 3^(j+1) ∣ 3^10 :=
      Nat.pow_dvd_pow 3 (by omega)
    simpa only [show (3:Nat)^10=59049 by decide] using hd
  calc
    (u*42217*4^M)%3^(j+1) =
      ((u*42217*4^M)%59049)%3^(j+1) :=
        (Nat.mod_mod_of_dvd _ hdiv).symm
    _ = (((u%59049)*42217*4^M)%59049)%3^(j+1) := by
      congr 1
      simp [Nat.mul_mod]
    _ = ((u%59049)*42217*4^M)%3^(j+1) :=
      Nat.mod_mod_of_dvd _ hdiv

/-- A finite certificate on u mod 59049 lifts to every integer u
in its entire infinite residue class. -/
theorem tenBandHit_of_mod (u : Nat) (h : TenBandHit (u%59049)) :
    TenBandHit u := by
  obtain ⟨j,hj,hs,hn⟩ := h
  refine ⟨j,hj,?_,?_⟩
  · rw [ten_band_digit_period 7 u j hj]
    exact hs
  · rw [ten_band_digit_period 8 u j hj]
    exact hn

/-- Exact physical readback on the full ten-trit window:
no approximation, no lifted axiom, no generic collision shortcut. -/
private theorem worldtrace_ten_band_digit
    (M u L j : Nat)
    (hL : 10 ≤ L)
    (hj : j < 10)
    (hsmall : 4^M < 3^(L+1)) :
    digit3 (4^(M+u*3^L)) (L+1+j) =
      digit3 (u*42217*4^M) j := by
  have hfull := GSTWorldtraceBlockLift.pow4_whole_block_lift
    M u L 10 (by decide) (by omega)
  have hz : 4^M / 3^(L+1)=0 := Nat.div_eq_of_lt hsmall
  have hmod :
      (4^(M+u*3^L)/3^(L+1))%59049 =
        (u*42217*4^M)%59049 := by
    calc
      (4^(M+u*3^L)/3^(L+1))%59049 =
          (4^M/3^(L+1)+u*GSTCanonicalTailLTE.lteCoeff L*4^M)%59049 := by
            simpa only [show (3:Nat)^10=59049 by decide] using hfull
      _ = (u*GSTCanonicalTailLTE.lteCoeff L*4^M)%59049 := by rw [hz]; simp
      _ = (u*(GSTCanonicalTailLTE.lteCoeff L%59049)*4^M)%59049 := by
            simp [Nat.mul_mod]
      _ = (u*42217*4^M)%59049 := by
            rw [coeff_mod59049 L (by omega)]
  have hdiv : 3^(j+1) ∣ 59049 := by
    have hd : 3^(j+1) ∣ 3^10 :=
      Nat.pow_dvd_pow 3 (by omega)
    simpa only [show (3:Nat)^10=59049 by decide] using hd
  have hread :
      digit3 (4^(M+u*3^L)/3^(L+1)) j =
        digit3 (u*42217*4^M) j := by
    apply digit3_eq_of_mod_next
    calc
      (4^(M+u*3^L)/3^(L+1))%3^(j+1) =
         ((4^(M+u*3^L)/3^(L+1))%59049)%3^(j+1) :=
           (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = ((u*42217*4^M)%59049)%3^(j+1) := by rw [hmod]
      _ = (u*42217*4^M)%3^(j+1) :=
           Nat.mod_mod_of_dvd _ hdiv
  calc
    digit3 (4^(M+u*3^L)) (L+1+j) =
      digit3 (4^(M+u*3^L)/3^(L+1)) j := by
        unfold digit3
        have hp : 3^(L+1+j)=3^(L+1)*3^j := by rw [pow_add]
        rw [hp, ← Nat.div_div_eq_div_mul]
    _ = digit3 (u*42217*4^M) j := hread

/-- Main infinite-family result: ANY ten-band arithmetic certificate
forces the ORIGINAL same-position physical CommonTwo. -/
theorem commonTwo_of_tenBandHit
    (L u : Nat) (hL : 10 ≤ L) (h : TenBandHit u) :
    CommonTwo (7+u*3^L) := by
  obtain ⟨j,hj,hs,hn⟩ := h
  have hpow : (3:Nat)^11 ≤ 3^(L+1) :=
    Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat)) (by omega)
  have hsmall7 : (4:Nat)^7 < 3^(L+1) :=
    lt_of_lt_of_le (by decide : (4:Nat)^7 < 3^11) hpow
  have hsmall8 : (4:Nat)^8 < 3^(L+1) :=
    lt_of_lt_of_le (by decide : (4:Nat)^8 < 3^11) hpow
  refine ⟨L+1+j, by omega, ?_, ?_⟩
  · rw [worldtrace_ten_band_digit 7 u L j hL hj hsmall7]
    exact hs
  · have he : (7+u*3^L)+1=8+u*3^L := by omega
    rw [he, worldtrace_ten_band_digit 8 u L j hL hj hsmall8]
    exact hn

/-- Covers full infinite multiplier residue classes via a decidable
ten-trit test, with no existential hypothesis on the exponent itself. -/
theorem original_thirdWave_of_mod_tenBandHit
    (L u : Nat) (hL : 10 ≤ L)
    (h : TenBandHit (u%59049)) :
    GSTFourPowerThirdWave.thirdWave (7+u*3^L) := by
  exact (GSTFourPowerThirdWave.thirdWave_iff_commonTwo _).2
    (commonTwo_of_tenBandHit L u hL (tenBandHit_of_mod u h))

/-- A candidate complement class: the finite-window survivor condition.
No universal claim about this remaining set is inferred. -/
def TenBandSurvivor (u : Nat) : Prop := ¬ TenBandHit (u%59049)

/-- Every exact bad exponent in the exceptional-seven tower MUST lie
in a surviving ten-trit multiplier class. -/
theorem noCommonTwo_implies_tenBandSurvivor
    (L u : Nat) (hL : 10 ≤ L)
    (hbad : ¬ CommonTwo (7+u*3^L)) :
    TenBandSurvivor u := by
  intro h
  exact hbad (commonTwo_of_tenBandHit L u hL (tenBandHit_of_mod u h))

#print axioms tenBandHit_of_mod
#print axioms commonTwo_of_tenBandHit
#print axioms original_thirdWave_of_mod_tenBandHit
#print axioms noCommonTwo_implies_tenBandSurvivor

end GSTProblem406ExceptionalSevenTenBand
