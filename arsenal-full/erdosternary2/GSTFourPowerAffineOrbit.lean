import GSTFourPowerDirectResidue
import GSTCanonicalTailStateIso

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineOrbit

open GSTFourPowerDirectResidue

/-- Affine orbit attached to the four-power exponent: A_0 = 0 and A_{K+1} = 4 A_K + 1. -/
def affineOrbit : Nat → Nat
  | 0 => 0
  | K + 1 => 4 * affineOrbit K + 1

@[simp] theorem affineOrbit_zero : affineOrbit 0 = 0 := rfl

@[simp] theorem affineOrbit_succ (K : Nat) :
    affineOrbit (K + 1) = 4 * affineOrbit K + 1 := rfl

/-- Closed affine-orbit identity: four-powers are exactly the one-trit lift of the orbit. -/
theorem four_pow_eq_one_plus_three_affineOrbit (K : Nat) :
    4^K = 1 + 3 * affineOrbit K := by
  induction K with
  | zero => simp [affineOrbit]
  | succ K ih =>
      rw [pow_succ, ih]
      simp only [affineOrbit]
      ring

/-- Removing the consumed low trit `1` exposes the affine orbit digit-for-digit. -/
theorem four_pow_digit_affine_shift (K q : Nat) :
    digit3 (4^K) (q + 1) = digit3 (affineOrbit K) q := by
  rw [four_pow_eq_one_plus_three_affineOrbit]
  have h := GSTCanonicalTailStateIso.prefix_slice_digit_exact
    1 1 (affineOrbit K) q (by norm_num : 1 < 3^1)
  simpa [GSTCanonicalTailStateIso.digit3, GSTFourPowerDirectResidue.digit3,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- The direct common-two problem rewritten on the affine orbit, with no inherited Happy witness. -/
def AffineCommonTwo (K : Nat) : Prop :=
  ∃ q : Nat,
    digit3 (affineOrbit K) q = 2 ∧
    digit3 (affineOrbit (K+1)) q = 2

/-- Exact coordinate equivalence between the original four-power overlap and the affine orbit overlap. -/
theorem power_common_two_iff_affine (K : Nat) :
    (∃ p : Nat, 1 ≤ p ∧
      digit3 (4^K) p = 2 ∧
      digit3 (4^(K+1)) p = 2) ↔
    AffineCommonTwo K := by
  constructor
  · rintro ⟨p, hp, hK, hK1⟩
    cases p with
    | zero => omega
    | succ q =>
        refine ⟨q, ?_, ?_⟩
        · rw [← four_pow_digit_affine_shift K q]
          simpa [Nat.succ_eq_add_one] using hK
        · rw [← four_pow_digit_affine_shift (K+1) q]
          simpa [Nat.succ_eq_add_one] using hK1
  · rintro ⟨q, hK, hK1⟩
    refine ⟨q+1, by omega, ?_, ?_⟩
    · rw [four_pow_digit_affine_shift K q]
      exact hK
    · rw [four_pow_digit_affine_shift (K+1) q]
      exact hK1

/-- The affine orbit evolves by the literal map x ↦ 4x+1. -/
theorem affineOrbit_forward (K : Nat) :
    affineOrbit (K+1) = 4 * affineOrbit K + 1 := by
  rfl

end GSTFourPowerAffineOrbit
