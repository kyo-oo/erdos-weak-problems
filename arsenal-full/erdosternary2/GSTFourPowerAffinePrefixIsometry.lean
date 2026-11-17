import GSTFourPowerExactExponentPeriod
import GSTFourPowerAffineOrbit

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffinePrefixIsometry

open GSTFourPowerExactExponentPeriod
open GSTFourPowerAffineOrbit

private theorem three_pow_succ_gt_one (p : Nat) : 1 < 3^(p+1) := by
  have h3 : 3^1 ≤ 3^(p+1) :=
    Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  norm_num at h3 ⊢

/-- Exact 3-adic exponent period in two-point form.  Two powers of four agree
    modulo `3^(p+1)` exactly when their exponents agree modulo `3^p`. -/
theorem pow4_modeq_iff_exponent_modeq (p a b : Nat) :
    4^a ≡ 4^b [MOD 3^(p+1)] ↔ a ≡ b [MOD 3^p] := by
  have hM : 1 < 3^(p+1) := three_pow_succ_gt_one p
  have forward_le : ∀ {u v : Nat}, u ≤ v →
      4^u ≡ 4^v [MOD 3^(p+1)] → u ≡ v [MOD 3^p] := by
    intro u v huv hpow
    have hv : v = u + (v-u) := by omega
    have hvpow : 4^v = 4^u * 4^(v-u) := by
      calc
        4^v = 4^(u+(v-u)) := congrArg (fun t : Nat => 4^t) hv
        _ = 4^u * 4^(v-u) := by rw [pow_add]
    have hmul : 4^u * 1 ≡ 4^u * 4^(v-u) [MOD 3^(p+1)] := by
      simpa only [hvpow, Nat.mul_one] using hpow
    have hcop : Nat.Coprime (3^(p+1)) (4^u) := by
      exact (by norm_num : Nat.Coprime 3 4).pow (p+1) u
    have hcancel : 1 ≡ 4^(v-u) [MOD 3^(p+1)] :=
      Nat.ModEq.cancel_left_of_coprime hcop.gcd_eq_one hmul
    have hperiod : 4^(v-u) % 3^(p+1) = 1 := by
      change 1 % 3^(p+1) = 4^(v-u) % 3^(p+1) at hcancel
      rw [Nat.mod_eq_of_lt hM] at hcancel
      exact hcancel.symm
    have hd : 3^p ∣ v-u :=
      (pow4_mod_one_iff_three_pow_dvd p (v-u)).mp hperiod
    exact (Nat.modEq_iff_dvd' huv).2 hd
  have backward_le : ∀ {u v : Nat}, u ≤ v →
      u ≡ v [MOD 3^p] → 4^u ≡ 4^v [MOD 3^(p+1)] := by
    intro u v huv hexp
    have hd : 3^p ∣ v-u := (Nat.modEq_iff_dvd' huv).1 hexp
    have hperiod : 4^(v-u) % 3^(p+1) = 1 :=
      (pow4_mod_one_iff_three_pow_dvd p (v-u)).2 hd
    have hperModeq : 4^(v-u) ≡ 1 [MOD 3^(p+1)] := by
      change 4^(v-u) % 3^(p+1) = 1 % 3^(p+1)
      rw [hperiod, Nat.mod_eq_of_lt hM]
    have hmul := hperModeq.mul_left (4^u)
    have hv : v = u + (v-u) := by omega
    have hvpow : 4^v = 4^u * 4^(v-u) := by
      calc
        4^v = 4^(u+(v-u)) := congrArg (fun t : Nat => 4^t) hv
        _ = 4^u * 4^(v-u) := by rw [pow_add]
    simpa only [hvpow, Nat.mul_one] using hmul.symm
  constructor
  · intro h
    rcases le_total a b with hab | hba
    · exact forward_le hab h
    · exact (forward_le hba h.symm).symm
  · intro h
    rcases le_total a b with hab | hba
    · exact backward_le hab h
    · exact (backward_le hba h.symm).symm

/-- Residue-equality presentation of the exact exponent period. -/
theorem pow4_residue_eq_iff_exponent_residue_eq (p a b : Nat) :
    4^a % 3^(p+1) = 4^b % 3^(p+1) ↔
      a % 3^p = b % 3^p := by
  change (4^a ≡ 4^b [MOD 3^(p+1)]) ↔ (a ≡ b [MOD 3^p])
  exact pow4_modeq_iff_exponent_modeq p a b

/-- Star-crusher coordinate law: the affine coordinate
    `A_K = (4^K-1)/3` is an exact 3-adic prefix isometry of the exponent.
    It loses no ternary prefix information at any finite scale. -/
theorem affineOrbit_modeq_iff_exponent_modeq (p a b : Nat) :
    affineOrbit a ≡ affineOrbit b [MOD 3^p] ↔
      a ≡ b [MOD 3^p] := by
  rw [← pow4_modeq_iff_exponent_modeq p a b]
  constructor
  · intro hA
    have hmul :
        3 * affineOrbit a ≡ 3 * affineOrbit b [MOD 3 * 3^p] :=
      hA.mul_left' 3
    have hadd :
        1 + 3 * affineOrbit a ≡ 1 + 3 * affineOrbit b [MOD 3 * 3^p] :=
      hmul.add_left 1
    simpa [four_pow_eq_one_plus_three_affineOrbit, Nat.pow_succ,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hadd
  · intro hpow
    rw [four_pow_eq_one_plus_three_affineOrbit a,
      four_pow_eq_one_plus_three_affineOrbit b] at hpow
    have hmul :
        3 * affineOrbit a ≡ 3 * affineOrbit b [MOD 3^(p+1)] :=
      Nat.ModEq.add_left_cancel' 1 hpow
    have hmul' :
        3 * affineOrbit a ≡ 3 * affineOrbit b [MOD 3 * 3^p] := by
      simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
    exact Nat.ModEq.mul_left_cancel' (by norm_num : 3 ≠ 0) hmul'

/-- Concrete prefix equality form used by the finite-state classifier. -/
theorem affineOrbit_residue_eq_iff_exponent_residue_eq (p a b : Nat) :
    affineOrbit a % 3^p = affineOrbit b % 3^p ↔
      a % 3^p = b % 3^p := by
  change (affineOrbit a ≡ affineOrbit b [MOD 3^p]) ↔
    (a ≡ b [MOD 3^p])
  exact affineOrbit_modeq_iff_exponent_modeq p a b

#check pow4_modeq_iff_exponent_modeq
#check pow4_residue_eq_iff_exponent_residue_eq
#check affineOrbit_modeq_iff_exponent_modeq
#check affineOrbit_residue_eq_iff_exponent_residue_eq
#print axioms pow4_modeq_iff_exponent_modeq
#print axioms affineOrbit_modeq_iff_exponent_modeq

end GSTFourPowerAffinePrefixIsometry
