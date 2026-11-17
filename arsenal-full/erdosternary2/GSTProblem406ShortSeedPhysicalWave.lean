import GSTWorldtraceBlockLift
import GSTFourPowerThirdWave

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Arbitrary-seed exact first-cut physical third-wave gate

The first postcut ternary digit is 2 in *both* original consecutive
powers 4^(M+u*3^L) and 4^((M+u*3^L)+1) whenever
  4^(M+1) < 3^(L+1)   and   u % 3 = 2.
The seed M, multiplier u, and scale L are ALL quantified.
There is no hGate, indirect prior witness, finite exponent bound or axiom.
-/

namespace GSTProblem406ShortSeedPhysicalWave

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence

/-- Every perfect power of four is 1 modulo 3. -/
theorem four_pow_mod_three_one (M : Nat) :
    4^M % 3 = 1 := by
  simp [Nat.pow_mod]

/-- The physical first postcut digit is the multiplier's first trit
when the literal source 4^M fits strictly below the ternary cut. -/
theorem first_cut_digit_eq_multiplier_mod_three
    (M u L : Nat)
    (hshort : 4^M < 3^(L+1)) :
    digit3 (4^(M+u*3^L)) (L+1) = u%3 := by
  have h := GSTWorldtraceBlockLift.pow4_whole_block_lift
    M u L 1 (by decide) (by omega)
  have hz : 4^M/3^(L+1)=0 := Nat.div_eq_of_lt hshort
  have hq :
      (4^(M+u*3^L)/3^(L+1))%3 =
        (u*GSTCanonicalTailLTE.lteCoeff L*4^M)%3 := by
    simpa only [show (3:Nat)^1=3 by decide,
      hz, Nat.zero_add] using h
  have hv :
      (u*GSTCanonicalTailLTE.lteCoeff L*4^M)%3 = u%3 := by
    calc
      (u*GSTCanonicalTailLTE.lteCoeff L*4^M)%3 =
        ((u%3)*(GSTCanonicalTailLTE.lteCoeff L%3)*(4^M%3))%3 := by
          simp [Nat.mul_mod]
      _ = u%3 := by
          rw [GSTCanonicalTailLTE.lteCoeff_mod3_one,
              four_pow_mod_three_one]
          simp
  change (4^(M+u*3^L)/3^(L+1))%3 = u%3
  exact hq.trans hv

/-- Uniform two-parameter gate: both physical perfect powers share
the exact digit two at the literal row L+1. -/
theorem commonTwo_of_short_seed_and_multiplier_two
    (M u L : Nat)
    (hshort : 4^(M+1) < 3^(L+1))
    (hu : u%3=2) :
    CommonTwo (M+u*3^L) := by
  have hseed : 4^M < 3^(L+1) := by
    have hle : 4^M ≤ 4^(M+1) := by
      rw [pow_succ]
      omega
    omega
  refine ⟨L+1, by omega, ?_, ?_⟩
  · rw [first_cut_digit_eq_multiplier_mod_three M u L hseed]
    exact hu
  · have hExp : (M+u*3^L)+1=(M+1)+u*3^L := by omega
    rw [hExp]
    rw [first_cut_digit_eq_multiplier_mod_three (M+1) u L hshort]
    exact hu

/-- Direct transfer to the ORIGINAL production third-wave predicate. -/
theorem thirdWave_of_short_seed_and_multiplier_two
    (M u L : Nat)
    (hshort : 4^(M+1) < 3^(L+1))
    (hu : u%3=2) :
    GSTFourPowerThirdWave.thirdWave (M+u*3^L) := by
  exact (GSTFourPowerThirdWave.thirdWave_iff_commonTwo _).2
    (commonTwo_of_short_seed_and_multiplier_two M u L hshort hu)

/-- Fully unconditional scale family with arbitrary unbounded L.
The exponent 2*3^L has an actual common two at row L+1. -/
theorem commonTwo_twice_three_power
    (L : Nat) (hL : 1 ≤ L) :
    CommonTwo (2*3^L) := by
  have hpow : 3^2 ≤ (3:Nat)^(L+1) :=
    Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat)) (by omega)
  have hshort : (4:Nat)^(0+1) < 3^(L+1) :=
    lt_of_lt_of_le (by decide : (4:Nat) < 3^2) hpow
  simpa only [Nat.zero_add] using
    (commonTwo_of_short_seed_and_multiplier_two 0 2 L
       hshort (by decide))

#print axioms four_pow_mod_three_one
#print axioms first_cut_digit_eq_multiplier_mod_three
#print axioms commonTwo_of_short_seed_and_multiplier_two
#print axioms thirdWave_of_short_seed_and_multiplier_two
#print axioms commonTwo_twice_three_power

end GSTProblem406ShortSeedPhysicalWave
