import GSTFourPowerDirectResidue

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerExactExponentPeriod

open GSTFourPowerDirectResidue

private theorem three_pow_succ_gt_one (p : Nat) : 1 < 3^(p+1) := by
  have h3 : 3^1 ≤ 3^(p+1) :=
    Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  norm_num at h3 ⊢

/-- The familiar exponent period `3^p` at modulus `3^(p+1)` is exact:
    no smaller 3-adic exponent precision can disappear. -/
theorem pow4_mod_one_iff_three_pow_dvd : ∀ p n : Nat,
    4^n % 3^(p+1) = 1 ↔ 3^p ∣ n := by
  intro p
  induction p with
  | zero =>
      intro n
      constructor
      · intro _
        simp
      · intro _
        simpa using pow4_mod3_one n
  | succ p ih =>
      intro n
      constructor
      · intro hhigh
        have hpowdvd : 3^(p+1) ∣ 3^((p+1)+1) :=
          Nat.pow_dvd_pow 3 (by omega)
        have hlower : 4^n % 3^(p+1) = 1 := by
          calc
            4^n % 3^(p+1) = (4^n % 3^((p+1)+1)) % 3^(p+1) :=
              (Nat.mod_mod_of_dvd (4^n) hpowdvd).symm
            _ = 1 % 3^(p+1) := by rw [hhigh]
            _ = 1 := Nat.mod_eq_of_lt (three_pow_succ_gt_one p)
        have hdivp : 3^p ∣ n := (ih n).mp hlower
        obtain ⟨u, rfl⟩ := hdivp
        let a := u % 3
        let v := u / 3
        have ha : a < 3 := by
          dsimp [a]
          exact Nat.mod_lt _ (by norm_num)
        have huv : u = a + 3*v := by
          dsimp [a, v]
          have h := Nat.mod_add_div u 3
          omega
        have hexp : 3^p * u = a * 3^p + 3^(p+1) * v := by
          rw [huv, Nat.pow_succ]
          ring
        have hzero : digit3 (4^(3^p*u)) (p+1) = 0 := by
          apply Eq.trans (digit3_eq_of_mod_next (4^(3^p*u)) 1 (p+1) ?_) ?_
          · simpa [Nat.mod_eq_of_lt (three_pow_succ_gt_one (p+1))] using hhigh
          · unfold digit3
            rw [Nat.div_eq_of_lt (three_pow_succ_gt_one p)]
        have hperiod :
            digit3 (4^(3^p*u)) (p+1) = digit3 (4^(a*3^p)) (p+1) := by
          rw [hexp]
          simpa [Nat.mul_comm] using pow4_digit_period (p+1) (a*3^p) v
        have hlift := pow4_exponent_trit_lift_digit p 0 a ha
        have hbase : digit3 (4^0) (p+1) = 0 := by
          unfold digit3
          norm_num [Nat.div_eq_of_lt (three_pow_succ_gt_one p)]
        have ha0 : a = 0 := by
          rw [hperiod] at hzero
          rw [hbase] at hlift
          have hlift' : digit3 (4^(a*3^p)) (p+1) = a := by
            simpa [Nat.mod_eq_of_lt ha] using hlift
          rw [hlift'] at hzero
          exact hzero
        have hu3 : 3 ∣ u := by
          refine ⟨v, ?_⟩
          rw [huv, ha0]
          omega
        obtain ⟨w, rfl⟩ := hu3
        refine ⟨w, ?_⟩
        rw [Nat.pow_succ]
        ring
      · rintro ⟨u, rfl⟩
        simpa using pow4_scaled_mod_next (p+1) u

#check pow4_mod_one_iff_three_pow_dvd
#print axioms pow4_mod_one_iff_three_pow_dvd

end GSTFourPowerExactExponentPeriod
