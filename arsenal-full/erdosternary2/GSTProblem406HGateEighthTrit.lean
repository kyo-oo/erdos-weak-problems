import GSTProblem406ExceptionalSevenTower
import GSTWorldtraceBlockLift
import GSTFourPowerThirdWave

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Eighth-trit exact physical HGate extension (genuine four-power sources)

This module directly supplies the original thirdWave/CommonTwo body on
previously uncovered multiplier residues; no theorem about a shifted
generic source is substituted for the literal pair of powers of four.

The result does not assert universal thirdWave. Its value is in
expanding the verified original HGate input domain, and in preserving
a strictly origin-exact proof architecture.
-/

namespace GSTProblem406HGateEighthTrit

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTWorldtraceBlockLift

/-- The Worldtrace LTE coefficient is frozen modulo the eight-trit
window for every physical scale L ≥ 9. Reuses the checked stronger
ten-trit coefficient theorem. -/
theorem coeff_mod6561_2851 (L : Nat) (hL : 9 ≤ L) :
    GSTCanonicalTailLTE.lteCoeff L % 6561 = 2851 := by
  have hlarge :=
    GSTProblem406ExceptionalSevenTower.coeff_mod59049 L hL
  have hdiv : 6561 ∣ 59049 := by decide
  calc
    GSTCanonicalTailLTE.lteCoeff L % 6561 =
      (GSTCanonicalTailLTE.lteCoeff L % 59049) % 6561 :=
        (Nat.mod_mod_of_dvd _ hdiv).symm
    _ = 42217 % 6561 := by rw [hlarge]
    _ = 2851 := by decide

/-- Exactly reduce each actual source-neighbor postcut quotient
to the frozen eight-trit Worldtrace coefficient. -/
private theorem coefficient_product_mod6561
    (L u M m : Nat) (hL : 9 ≤ L)
    (hm : (2851*M)%6561=m) :
    (u*GSTCanonicalTailLTE.lteCoeff L*M)%6561=(m*u)%6561 := by
  have hc : (GSTCanonicalTailLTE.lteCoeff L*M)%6561=m := by
    calc
      (GSTCanonicalTailLTE.lteCoeff L*M)%6561 =
        ((GSTCanonicalTailLTE.lteCoeff L%6561)*(M%6561))%6561 :=
          Nat.mul_mod _ _ _
      _ = (2851*M)%6561 := by
          rw [coeff_mod6561_2851 L hL]
          simpa using (Nat.mul_mod 2851 M 6561).symm
      _ = m := hm
  calc
    (u*GSTCanonicalTailLTE.lteCoeff L*M)%6561 =
        (u*(GSTCanonicalTailLTE.lteCoeff L*M))%6561 := by ring
    _ = (u*m)%6561 := by
      calc
        (u*(GSTCanonicalTailLTE.lteCoeff L*M))%6561 =
          ((u%6561)*((GSTCanonicalTailLTE.lteCoeff L*M)%6561))%6561 :=
            Nat.mul_mod _ _ _
        _ = ((u%6561)*m)%6561 := by rw [hc]
        _ = (u*m)%6561 := by
              simpa using (Nat.mul_mod u m 6561).symm
    _ = (m*u)%6561 := by ac_rfl


/-- Original source and neighbor, simultaneously, under the full
eight-digit physical Worldtrace quotient transport. -/
private theorem physical_eighth_block (L u : Nat) (hL : 9 ≤ L) :
    (4^(4+u*3^L) / 3^(L+1)) % 3^8 =
      (u*GSTCanonicalTailLTE.lteCoeff L*256) % 3^8 ∧
    (4^(5+u*3^L) / 3^(L+1)) % 3^8 =
      (u*GSTCanonicalTailLTE.lteCoeff L*1024) % 3^8 := by
  have hpow : (4:Nat)^5 < 3^(L+1) := by
    have h0 : (4:Nat)^5 < 3^10 := by decide
    have h1 : 3^10 ≤ 3^(L+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega
  have hs : (4:Nat)^4 < 3^(L+1) := by
    have hle : (4:Nat)^4 ≤ 4^5 := by norm_num
    omega
  have h4z : (256:Nat) / 3^(L+1) = 0 := by
    simpa only [show (4:Nat)^4 = 256 by decide] using
      (Nat.div_eq_of_lt hs)
  have h5z : (1024:Nat) / 3^(L+1) = 0 := by
    simpa only [show (4:Nat)^5 = 1024 by decide] using
      (Nat.div_eq_of_lt hpow)
  constructor
  · have h := GSTWorldtraceBlockLift.pow4_whole_block_lift
      4 u L 8 (by decide) (by omega)
    simpa only [show (4:Nat)^4 = 256 by decide,
      h4z, Nat.zero_add] using h
  · have h := GSTWorldtraceBlockLift.pow4_whole_block_lift
      5 u L 8 (by decide) (by omega)
    simpa only [show (4:Nat)^5 = 1024 by decide,
      h5z, Nat.zero_add] using h

/-- A physical digit at row L+1+j equals the j-th digit of the
exact Worldtrace quotient block, not a synthetic source. -/
private theorem eighth_physical_digit_readback
    (M L u j A : Nat) (hj : j < 8)
    (hwindow : (4^(M+u*3^L) / 3^(L+1)) % 3^8 = A % 3^8) :
    digit3 (4^(M+u*3^L)) (L+1+j) = digit3 A j := by
  have hdiv : 3^(j+1) ∣ (3:Nat)^8 :=
    Nat.pow_dvd_pow 3 (by omega)
  have hmod :
      (4^(M+u*3^L)/3^(L+1))%3^(j+1)=A%3^(j+1) := by
    calc
      (4^(M+u*3^L)/3^(L+1))%3^(j+1) =
          ((4^(M+u*3^L)/3^(L+1))%3^8)%3^(j+1) :=
            (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = (A%3^8)%3^(j+1) := by rw [hwindow]
      _ = A%3^(j+1) := Nat.mod_mod_of_dvd _ hdiv
  have hread := digit3_eq_of_mod_next
    (4^(M+u*3^L)/3^(L+1)) A j hmod
  calc
    digit3 (4^(M+u*3^L)) (L+1+j) =
        digit3 (4^(M+u*3^L)/3^(L+1)) j := by
          unfold digit3
          have hp : 3^(L+1+j)=3^(L+1)*3^j := by rw [pow_add]
          rw [hp, ← Nat.div_div_eq_div_mul]
    _ = digit3 A j := hread

/-- A source-neighbor physical pair certificate in the eighth
postcut trit, on the multiplier residue modulo 3^8. -/
def EighthPhysicalClass (r : Nat) : Prop :=
  digit3 (1585*r) 7=2 ∧ digit3 (6340*r) 7=2

/-- Every multiplier in this genuine physical eighth-trit class
produces a same-position digit two in 4^K and 4^(K+1).
The witness is p=L+8, not a shifted-exponent surrogate. -/
theorem commonTwo_eighth_physical_class
    (L u : Nat) (hL : 9 ≤ L)
    (hu : EighthPhysicalClass (u%6561)) :
    CommonTwo (4+u*3^L) := by
  have hpair := hu
  have hsource_mod : digit3 (1585*u) 7 =
      digit3 (1585*(u%6561)) 7 := by
    apply digit3_eq_of_mod_next
    change (1585*u)%6561=(1585*(u%6561))%6561
    simp [Nat.mul_mod]
  have hneighbor_mod : digit3 (6340*u) 7 =
      digit3 (6340*(u%6561)) 7 := by
    apply digit3_eq_of_mod_next
    change (6340*u)%6561=(6340*(u%6561))%6561
    simp [Nat.mul_mod]
  have hsource : digit3 (1585*u) 7=2 := by
    rw [hsource_mod]
    exact hpair.1
  have hneighbor : digit3 (6340*u) 7=2 := by
    rw [hneighbor_mod]
    exact hpair.2
  have hreadsource :
      digit3 (u*GSTCanonicalTailLTE.lteCoeff L*256) 7 =
        digit3 (1585*u) 7 := by
    apply digit3_eq_of_mod_next
    simpa only [show (3:Nat)^(7+1)=6561 by decide] using
      (coefficient_product_mod6561 L u 256 1585 hL (by norm_num))
  have hreadneighbor :
      digit3 (u*GSTCanonicalTailLTE.lteCoeff L*1024) 7 =
        digit3 (6340*u) 7 := by
    apply digit3_eq_of_mod_next
    simpa only [show (3:Nat)^(7+1)=6561 by decide] using
      (coefficient_product_mod6561 L u 1024 6340 hL (by norm_num))
  obtain ⟨h4, h5⟩ := physical_eighth_block L u hL
  refine ⟨L+1+7, by omega, ?_, ?_⟩
  · rw [eighth_physical_digit_readback 4 L u 7
      (u*GSTCanonicalTailLTE.lteCoeff L*256) (by decide) h4]
    exact hreadsource.trans hsource
  · have he : (4+u*3^L)+1=5+u*3^L := by omega
    rw [he, eighth_physical_digit_readback 5 L u 7
      (u*GSTCanonicalTailLTE.lteCoeff L*1024) (by decide) h5]
    exact hreadneighbor.trans hneighbor

/-- A concrete new class, not requiring any hypothesis about
the universal HGate. -/
theorem seed37_eighth_class : EighthPhysicalClass 37 := by
  norm_num [EighthPhysicalClass, digit3]

/-- This residue has no earlier hit in the first seven postcut rows
of the exact frozen coefficient pair. -/
theorem seed37_no_earlier_postcut_hit :
    ∀ j : Fin 7,
      ¬ (digit3 (37*2851*256) j.val=2 ∧
         digit3 (37*2851*1024) j.val=2) := by
  decide

theorem original_thirdWave_eighth_physical_class
    (L u : Nat) (hL : 9 ≤ L)
    (hu : EighthPhysicalClass (u%6561)) :
    GSTFourPowerThirdWave.thirdWave (4+u*3^L) := by
  exact (GSTFourPowerThirdWave.thirdWave_iff_commonTwo _).2
    (commonTwo_eighth_physical_class L u hL hu)

theorem original_thirdWave_seed37
    (L u : Nat) (hL : 9 ≤ L)
    (hu : u % 6561 = 37) :
    GSTFourPowerThirdWave.thirdWave (4+u*3^L) := by
  apply original_thirdWave_eighth_physical_class L u hL
  simpa only [hu] using seed37_eighth_class

#print axioms coeff_mod6561_2851
#print axioms seed37_eighth_class
#print axioms seed37_no_earlier_postcut_hit
#print axioms commonTwo_eighth_physical_class
#print axioms original_thirdWave_eighth_physical_class
#print axioms original_thirdWave_seed37

end GSTProblem406HGateEighthTrit
