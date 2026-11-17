import GSTOmegaExactDelayedEscape
import GSTOmegaArbitraryDelay

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Two-parameter exact GST delayed terminal response

For ALL L >= 5 and all natural u, the entire first three quotient
trits of 4^(4+u*3^L) are 19*u modulo 27, an infinite two-dimensional
result with no finite enumeration.

For all u == 2 mod 3, the first digit two occurs exactly at L+1.
This is a genuinely unbounded family of natural exponents.
-/

namespace GSTOmegaThreeTritMultiplierLaw

open GSTWorldtraceBlockLift

/-- Strong uniform exact 3-trit GST affine quotient response. -/
theorem quotient_mod27_all_multipliers
    (L u : Nat) (hL : 5 ≤ L) :
    (4^(4+u*3^L)/3^(L+1))%27 = (19*u)%27 := by
  have hsmall : 4^4 < 3^(L+1) := by
    have hnum : (4:Nat)^4 < 3^6 := by decide
    have hpow : 3^6 ≤ 3^(L+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega
  have hdiv : (4:Nat)^4 / 3^(L+1) = 0 :=
    Nat.div_eq_of_lt hsmall
  have h := pow4_whole_block_lift 4 u L 3 (by omega) (by omega)
  have h256div : (256:Nat)/3^(L+1)=0 := by
    simpa only [show (4:Nat)^4=256 by decide] using hdiv
  have hs :
      (4^(4+u*3^L)/3^(L+1))%27 =
        (u*GSTCanonicalTailLTE.lteCoeff L*256)%27 := by
    simpa only [show (3:Nat)^3=27 by decide,
      show (4:Nat)^4=256 by decide, h256div,
      Nat.zero_add] using h
  have hc :
      (GSTCanonicalTailLTE.lteCoeff L*256)%27=19 := by
    rw [Nat.mul_mod,
      GSTOmegaExactDelayedEscape.lteCoeff_mod27_sixteen L (by omega)] <;> decide
  calc
    (4^(4+u*3^L)/3^(L+1))%27 =
        (u*GSTCanonicalTailLTE.lteCoeff L*256)%27 := hs
    _ = (u*(GSTCanonicalTailLTE.lteCoeff L*256))%27 := by ring
    _ = (u*19)%27 := by
      calc
        (u*(GSTCanonicalTailLTE.lteCoeff L*256))%27 =
          ((u%27)*((GSTCanonicalTailLTE.lteCoeff L*256)%27))%27 :=
            Nat.mul_mod _ _ _
        _ = ((u%27)*19)%27 := by rw [hc]
        _ = (u*19)%27 := by
          simpa only [Nat.mod_eq_of_lt (by decide : (19:Nat)<27)] using
            (Nat.mul_mod u 19 27).symm
    _ = (19*u)%27 := by ac_rfl

/-- If u == 2 (mod 3), a two occurs at the very first new
postcut row, independently of the size of u or L. -/
theorem all_two_mod_three_multipliers_fire_at_cut
    (L u : Nat) (hL : 5 ≤ L) (hu : u % 3 = 2) :
    GSTFourPowerDirectResidue.digit3 (4^(4+u*3^L)) (L+1) = 2 := by
  have hsmall : 4^4 < 3^(L+1) := by
    have hnum : (4:Nat)^4 < 3^6 := by decide
    have hpow : 3^6 ≤ 3^(L+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega
  have hdiv : (4:Nat)^4/3^(L+1)=0 :=
    Nat.div_eq_of_lt hsmall
  have h := pow4_whole_block_lift 4 u L 1 (by omega) (by omega)
  rw [show (3:Nat)^1=3 by decide] at h
  simp only [hdiv, Nat.zero_add] at h
  change (4^(4+u*3^L)/3^(L+1))%3=2
  rw [h]
  simp [Nat.mul_mod, hu, GSTCanonicalTailLTE.lteCoeff_mod3_one]

/-- Exact FIRST digit, not just a witness, for all unbounded
two-mod-three multiplier cores. -/
theorem first_two_for_two_mod_three_multiplier
    (L u : Nat) (hL : 5 ≤ L) (hu : u % 3 = 2) :
    GSTFourPowerDirectResidue.digit3 (4^(4+u*3^L)) (L+1) = 2 ∧
      ∀ p, p < L+1 →
        GSTFourPowerDirectResidue.digit3 (4^(4+u*3^L)) p ≠ 2 := by
  constructor
  · exact all_two_mod_three_multipliers_fire_at_cut L u hL hu
  · intro p hp
    have hpow : 3^L = 3^p*3^(L-p) := by
      rw [← pow_add]
      congr 1
      omega
    have hrepr :
        4+u*3^L = 4+3^p*(u*3^(L-p)) := by
      rw [hpow]
      ring
    rw [hrepr, GSTFourPowerDirectResidue.pow4_digit_period]
    exact GSTOmegaArbitraryDelay.exceptional_four_is_clean p

#print axioms quotient_mod27_all_multipliers
#print axioms all_two_mod_three_multipliers_fire_at_cut
#print axioms first_two_for_two_mod_three_multiplier


/-- All u == 1 modulo 27 reproduce the canonical u=1
infinite-exponent trace through the first escape row L+3.
This is exact ternary phase agreement over an unbounded
two-parameter family. -/
theorem one_mod27_core_prefix_agrees
    (L u p : Nat) (hL : 5 ≤ L)
    (hu : u % 27 = 1) (hp : p ≤ L+3) :
    GSTFourPowerDirectResidue.digit3 (4^(4+u*3^L)) p =
      GSTFourPowerDirectResidue.digit3 (4^(4+3^L)) p := by
  have huRepr : u = 1+27*(u/27) := by
    have h := Nat.mod_add_div u 27
    omega
  have hpower : 3^(L+3) = 3^L*27 := by
    rw [pow_add]
    norm_num
  have hexp :
      4+u*3^L = (4+3^L)+3^(L+3)*(u/27) := by
    calc
      4+u*3^L = 4+(1+27*(u/27))*3^L := by rw [← huRepr]
      _ = (4+3^L)+3^(L+3)*(u/27) := by
        rw [hpower]
        ring
  have hfactor :
      3^(L+3) = 3^p*3^(L+3-p) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hexp,hfactor]
  simpa only [mul_assoc] using
    (GSTFourPowerDirectResidue.pow4_digit_period
      p (4+3^L) (3^(L+3-p)*(u/27)))

/-- Exact first two for all arbitrarily large u congruent one mod27,
not only the seed multiplier u=1. -/
theorem first_two_for_one_mod27_multiplier
    (L u : Nat) (hL : 5 ≤ L) (hu : u % 27 = 1) :
    GSTFourPowerDirectResidue.digit3 (4^(4+u*3^L)) (L+3) = 2 ∧
      ∀ p, p < L+3 →
        GSTFourPowerDirectResidue.digit3 (4^(4+u*3^L)) p ≠ 2 := by
  obtain ⟨hfirst,hbefore⟩ :=
    GSTOmegaExactDelayedEscape.delayed_seed_first_two_exact L hL
  constructor
  · rw [one_mod27_core_prefix_agrees L u (L+3) hL hu (by omega)]
    exact hfirst
  · intro p hp
    rw [one_mod27_core_prefix_agrees L u p hL hu (by omega)]
    exact hbefore p hp

#print axioms one_mod27_core_prefix_agrees
#print axioms first_two_for_one_mod27_multiplier

end GSTOmegaThreeTritMultiplierLaw
