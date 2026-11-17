import GSTWorldtraceBlockLift
import GSTWorldtraceCoeffStability
import GSTFourPowerDirectResidue

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Exact unbounded GST delayed terminal escape for K=4+3^L

For ALL L>=5 the first digit two of 4^(4+3^L) occurs EXACTLY at
position L+3. This is an infinite theorem, not finite verification.
It proves both arbitrary delay and ultimate natural-path escape for
one infinite family, including exact transport of all early digits.

It does not assert that every nonexceptional natural exponent escapes.
-/

namespace GSTOmegaExactDelayedEscape

open GSTCanonicalTailLTE
open GSTWorldtraceCoeffStability

/-- Unbounded scale stabilization on the first 3 coefficient trits. -/
theorem lteCoeff_mod27_sixteen
    (L : Nat) (hL : 2 ≤ L) :
    lteCoeff L % 27 = 16 := by
  have hstep : ∀ t : Nat, 2 ≤ t →
      lteCoeff (t+1) % 27 = lteCoeff t % 27 := by
    intro t ht
    have hdiv : 27 ∣ 3^(t+1) := by
      have hz : 3^3 ∣ 3^(t+1) :=
        Nat.pow_dvd_pow 3 (by omega)
      simpa using hz
    rw [coeff_step]
    simp [Nat.add_mod, Nat.mul_mod,
      Nat.mod_eq_zero_of_dvd hdiv]
  have hbase : ∀ k : Nat,
      lteCoeff (2+k)%27 = 16 := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
        rw [show 2+(k+1)=(2+k)+1 by omega]
        rw [hstep (2+k) (by omega)]
        exact ih
  rw [show L=2+(L-2) by omega]
  exact hbase (L-2)

/-- The 27-residue of the first quotient block of 4^(4+3^L)
is the *constant* 19 for every natural L>=5. -/
theorem delayed_seed_quotient_mod27
    (L : Nat) (hL : 5 ≤ L) :
    (4^(4+3^L)/3^(L+1)) % 27 = 19 := by
  have hsmall : 4^4 < 3^(L+1) := by
    have h729 : (4:Nat)^4 < 3^6 := by decide
    have hpow : 3^6 ≤ 3^(L+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega
  have hdiv : 4^4 / 3^(L+1)=0 := Nat.div_eq_of_lt hsmall
  have h := GSTWorldtraceBlockLift.pow4_whole_block_lift
    4 1 L 3 (by omega) (by omega)
  have hc := lteCoeff_mod27_sixteen L (by omega)
  simp only [one_mul, hdiv, zero_add] at h
  calc
    (4^(4+3^L)/3^(L+1))%27 =
        (lteCoeff L * 256)%27 := by
          simpa only [show (3:Nat)^3=27 by decide, show (4:Nat)^4=256 by decide] using h
    _ = 19 := by
      rw [Nat.mul_mod, hc] <;> decide

/-- The first three quotient trits are exactly 1,0,2,
uniformly in L>=5. -/
theorem delayed_seed_three_trits
    (L k : Nat) (hL : 5 ≤ L) (hk : k < 3) :
    GSTFourPowerDirectResidue.digit3 (4^(4+3^L)) (L+1+k) = GSTFourPowerDirectResidue.digit3 19 k := by
  have hmod := delayed_seed_quotient_mod27 L hL
  have hdiv : 3^(k+1) ∣ 27 := by
    have h := Nat.pow_dvd_pow 3 (show k+1≤3 by omega)
    simpa using h
  have hs :
      (4^(4+3^L)/3^(L+1))%3^(k+1) = 19%3^(k+1) := by
    calc
      (4^(4+3^L)/3^(L+1))%3^(k+1) =
        ((4^(4+3^L)/3^(L+1))%27)%3^(k+1) :=
          (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = (19%27)%3^(k+1) := by
        simpa only [Nat.mod_eq_of_lt (by decide : (19:Nat)<27)] using congrArg (fun z : Nat => z%3^(k+1)) hmod
      _ = 19%3^(k+1) := Nat.mod_mod_of_dvd _ hdiv
  have hread := GSTFourPowerDirectResidue.digit3_eq_of_mod_next
    (4^(4+3^L)/3^(L+1)) 19 k hs
  calc
    GSTFourPowerDirectResidue.digit3 (4^(4+3^L)) (L+1+k) =
        GSTFourPowerDirectResidue.digit3 (4^(4+3^L)/3^(L+1)) k := by
          unfold GSTFourPowerDirectResidue.digit3
          have hp : 3^(L+1+k) = 3^(L+1)*3^k := by rw [pow_add]
          rw [hp, ← Nat.div_div_eq_div_mul]
    _ = GSTFourPowerDirectResidue.digit3 19 k := hread

/-- Every digit strictly before row L+3 is clean. -/
theorem delayed_seed_no_two_before
    (L p : Nat) (hL : 5 ≤ L) (hp : p < L+3) :
    GSTFourPowerDirectResidue.digit3 (4^(4+3^L)) p ≠ 2 := by
  by_cases hpL : p ≤ L
  · have hshape : 3^L = 3^p*3^(L-p) := by
      rw [← pow_add]
      congr 1
      omega
    have hrepr : 4+3^L = 4+3^p*3^(L-p) := by rw [hshape]
    rw [hrepr, GSTFourPowerDirectResidue.pow4_digit_period]
    by_cases hsmall : p < 6
    · interval_cases p <;> norm_num [GSTFourPowerDirectResidue.digit3]
    · have hpow : 3^6 ≤ 3^p :=
        Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
      have hlt : 4^4 < 3^p := by
        have h : (4:Nat)^4 < 3^6 := by decide
        omega
      have h256 : (256:Nat)<3^p := by
        simpa only [show (4:Nat)^4=256 by decide] using hlt
      have hz : (256:Nat)/3^p=0 := Nat.div_eq_of_lt h256
      change ((256:Nat)/3^p)%3 ≠ 2
      rw [hz]
      decide
  · have hcase : p=L+1 ∨ p=L+2 := by omega
    rcases hcase with rfl | rfl
    · have h := delayed_seed_three_trits L 0 hL (by omega)
      simpa [GSTFourPowerDirectResidue.digit3] using (show GSTFourPowerDirectResidue.digit3 (4^(4+3^L)) (L+1+0)≠2 from by
        rw [h]
        norm_num [GSTFourPowerDirectResidue.digit3])
    · have h := delayed_seed_three_trits L 1 hL (by omega)
      simpa [GSTFourPowerDirectResidue.digit3] using (show GSTFourPowerDirectResidue.digit3 (4^(4+3^L)) (L+1+1)≠2 from by
        rw [h]
        norm_num [GSTFourPowerDirectResidue.digit3])

/-- A fully explicit unbounded natural-path terminal gate, with
its first position exactly L+3, for every L>=5. -/
theorem delayed_seed_first_two_exact
    (L : Nat) (hL : 5 ≤ L) :
    GSTFourPowerDirectResidue.digit3 (4^(4+3^L)) (L+3) = 2 ∧
      ∀ p, p < L+3 → GSTFourPowerDirectResidue.digit3 (4^(4+3^L)) p ≠ 2 := by
  constructor
  · have h := delayed_seed_three_trits L 2 hL (by omega)
    simpa [GSTFourPowerDirectResidue.digit3] using h
  · intro p hp
    exact delayed_seed_no_two_before L p hL hp

#print axioms lteCoeff_mod27_sixteen
#print axioms delayed_seed_quotient_mod27
#print axioms delayed_seed_three_trits
#print axioms delayed_seed_first_two_exact

end GSTOmegaExactDelayedEscape
