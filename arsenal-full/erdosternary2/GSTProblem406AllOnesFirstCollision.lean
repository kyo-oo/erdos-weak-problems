import GSTProblem406GSTPeelFixedPoint
import GSTFourPowerThirdWave

set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000

/-!
GST-native all-ones exponent physical collision at row m+9.
This uses the exact peel1 polynomial and a fixed source coefficient 14049
rather than a generic infinite controller or an assumed hGate.

The target is CommonTwo(ternaryOnes m), ALL m>=8. Its proof relies
on one finite base instance and an all-m polynomial stability induction.
-/

namespace GSTProblem406AllOnesFirstCollision

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineExponentPeel
open GSTProblem406GSTPeelFixedPoint

/-- The source-specific stabilized nine-trit affine fixed core. -/
private def stableCore (m : Nat) : Nat :=
  ternaryOnes m + 3^m * 14049

private theorem stableCore_succ (m : Nat) :
    stableCore (m+1) = 1 + 3*stableCore m := by
  simp only [stableCore, ternaryOnes, pow_succ]
  ring

/-- True finite-core GST nonlinear fixed point, all m>=8. -/
private theorem stableCore_peel1_fixed
    (m : Nat) (hm : 8 ≤ m) :
    peel1 (stableCore m) % 3^(m+9) =
      stableCore m % 3^(m+9) := by
  have hshift : 2*stableCore m+1 = 3^m*28099 := by
    unfold stableCore
    have h := ternaryOnes_identity m
    omega
  have hdiv : 3^(m+9) ∣
      3*stableCore m*(2*stableCore m+1)^2 := by
    have hpower : 3^(m+9) ∣ 3^(2*m+1) :=
      Nat.pow_dvd_pow 3 (by omega)
    have hbig : 3^(2*m+1) ∣
        3*stableCore m*(2*stableCore m+1)^2 := by
      refine ⟨stableCore m * 28099^2, ?_⟩
      rw [hshift]
      have hp : 3^(2*m+1) = 3*(3^m)^2 := by
        rw [show 2*m+1=m*2+1 by omega, pow_succ, pow_mul]
        ring
      rw [hp]
      ring
    exact dvd_trans hpower hbig
  rw [peel1_exact_nonarchimedean_fixedpoint, Nat.add_mod,
      Nat.mod_eq_zero_of_dvd hdiv]
  simp

/-- The exact physical affineOrbit has this stabilized 9-trit prefix
for every ALL-ONES exponent length m>=8. This is an all-m induction. -/
private theorem physical_affine_stableCore_mod
    (m : Nat) (hm : 8 ≤ m) :
    affineOrbit (ternaryOnes m) % 3^(m+9) =
      stableCore m % 3^(m+9) := by
  obtain ⟨t, rfl⟩ : ∃ t : Nat, m = 8+t :=
    ⟨m-8, by omega⟩
  induction t with
  | zero =>
      decide
  | succ t ih =>
      have hpoly :
          peel1 (affineOrbit (ternaryOnes (8+t))) %
              3^((8+t)+9) =
          peel1 (stableCore (8+t)) % 3^((8+t)+9) := by
        simp [peel1, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, ih]
      have hfix := stableCore_peel1_fixed (8+t) (by omega)
      have htotal : peel1 (affineOrbit (ternaryOnes (8+t))) ≡
          stableCore (8+t) [MOD 3^((8+t)+9)] :=
        hpoly.trans hfix
      have hadd := (htotal.mul_left' 3).add_left 1
      have hstep :
          (1+3*peel1 (affineOrbit (ternaryOnes (8+t)))) %
              3^((8+t)+10) =
          (1+3*stableCore (8+t)) % 3^((8+t)+10) := by
        have hp : 3^((8+t)+10) = 3*3^((8+t)+9) := by
          rw [show (8+t)+10=((8+t)+9)+1 by omega, pow_succ]
          ring
        rw [hp]
        change
          (1+3*peel1 (affineOrbit (ternaryOnes (8+t)))) %
              (3*3^((8+t)+9)) =
          (1+3*stableCore (8+t)) % (3*3^((8+t)+9))
          at hadd
        exact hadd
      change
        affineOrbit (ternaryOnes ((8+t)+1)) % 3^((8+t)+10) =
          stableCore ((8+t)+1) % 3^((8+t)+10)
      rw [ternaryOnes, affineOrbit_three_mul_add_one, stableCore_succ]
      exact hstep

/-- The literal stabilized source has digit 2 at affine row m+8. -/
private theorem source_stableCore_hit (m : Nat) :
    digit3 (stableCore m) (m+8) = 2 := by
  unfold digit3 stableCore
  have hp : 3^(m+8) = 3^m*3^8 := by rw [pow_add]
  rw [hp, ← Nat.div_div_eq_div_mul]
  rw [Nat.add_mul_div_left _ _ (by positivity : 0<3^m),
      Nat.div_eq_of_lt (ternaryOnes_lt_pow m)]
  norm_num

/-- The ORIGINAL neighboring affine source also has digit 2
at that SAME affine row m+8. -/
private theorem neighbor_stableCore_hit (m : Nat) :
    digit3 (4*stableCore m+1) (m+8) = 2 := by
  have hshape :
      4*stableCore m+1 =
        2*ternaryOnes m+3^m*(1+4*14049) := by
    unfold stableCore
    have h := ternaryOnes_identity m
    omega
  have hlo : 2*ternaryOnes m<3^m := by
    have h := ternaryOnes_identity m
    omega
  unfold digit3
  rw [hshape]
  rw [show 3^(m+8)=3^m*3^8 by rw [pow_add],
      ← Nat.div_div_eq_div_mul]
  rw [Nat.add_mul_div_left _ _ (by positivity : 0<3^m),
      Nat.div_eq_of_lt hlo]
  norm_num

/-- New unconditional, source-specific original CommonTwo for all
unbounded all-one exponent lengths m>=8, exact row m+9. -/
theorem commonTwo_allones_at_m_plus_nine
    (m : Nat) (hm : 8 ≤ m) :
    CommonTwo (ternaryOnes m) := by
  have hmod := physical_affine_stableCore_mod m hm
  have hs :
      digit3 (affineOrbit (ternaryOnes m)) (m+8) = 2 := by
    have heq := digit3_eq_of_mod_next
        (affineOrbit (ternaryOnes m)) (stableCore m)
        (m+8) (by
          simpa only [show m+8+1=m+9 by omega] using hmod)
    exact heq.trans (source_stableCore_hit m)
  have hneighborMod :
      (4*affineOrbit (ternaryOnes m)+1)%3^(m+9) =
        (4*stableCore m+1)%3^(m+9) := by
    simp [Nat.add_mod, Nat.mul_mod, hmod]
  have hn :
      digit3 (affineOrbit (ternaryOnes m+1)) (m+8) = 2 := by
    rw [affineOrbit_succ]
    have heq := digit3_eq_of_mod_next
        (4*affineOrbit (ternaryOnes m)+1)
        (4*stableCore m+1) (m+8) (by
          simpa only [show m+8+1=m+9 by omega] using hneighborMod)
    exact heq.trans (neighbor_stableCore_hit m)
  refine ⟨m+9, by omega, ?_, ?_⟩
  · simpa only [show m+8+1=m+9 by omega] using
      (four_pow_digit_affine_shift (ternaryOnes m) (m+8)).trans hs
  · simpa only [show m+8+1=m+9 by omega] using
      (four_pow_digit_affine_shift (ternaryOnes m+1) (m+8)).trans hn

/-- Export the family directly into the original third-wave gate body. -/
theorem original_thirdWave_allones
    (m : Nat) (hm : 8 ≤ m) :
    GSTFourPowerThirdWave.thirdWave (ternaryOnes m) := by
  exact (GSTFourPowerThirdWave.thirdWave_iff_commonTwo _).2
    (commonTwo_allones_at_m_plus_nine m hm)

#print axioms commonTwo_allones_at_m_plus_nine
#print axioms original_thirdWave_allones

end GSTProblem406AllOnesFirstCollision
