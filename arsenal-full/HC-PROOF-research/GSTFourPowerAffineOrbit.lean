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


/-! ## Affine time as an exact semigroup action -/

/-- **AFFINE ORBIT COCYCLE.**  Advancing by `L` exponent steps from time
`K` is exactly multiplication of the old affine state by `4^L`, followed
by the intrinsic `L`-step affine state.  Thus exponent addition acts on the
orbit without any loss of information. -/
theorem affineOrbit_add_exact (K L : Nat) :
    affineOrbit (K + L) = 4^L * affineOrbit K + affineOrbit L := by
  induction L with
  | zero =>
      simp [affineOrbit]
  | succ L ih =>
      rw [show K + (L + 1) = (K + L) + 1 by omega,
        affineOrbit_succ, ih, affineOrbit_succ, pow_succ]
      ring

/-- A one-step shift after an arbitrary block is the same affine action
written in block coordinates. -/
theorem affineOrbit_add_succ_exact (K L : Nat) :
    affineOrbit (K + L + 1) =
      4^(L+1) * affineOrbit K + affineOrbit (L+1) := by
  simpa [Nat.add_assoc] using affineOrbit_add_exact K (L+1)

/-- **THREE-BLOCK RENORMALIZATION.**  Every three-step exponent block acts
by the exact scale `64` plus the universal three-step offset. -/
theorem affineOrbit_add_three_exact (K : Nat) :
    affineOrbit (K + 3) = 64 * affineOrbit K + 21 := by
  simpa [affineOrbit] using affineOrbit_add_exact K 3

/-- The four-power lift intertwines the affine cocycle with ordinary exponent
addition: no separate transition law is needed above the affine state. -/
theorem four_pow_from_affine_cocycle (K L : Nat) :
    4^(K+L) =
      1 + 3 * (4^L * affineOrbit K + affineOrbit L) := by
  rw [four_pow_eq_one_plus_three_affineOrbit, affineOrbit_add_exact]

#check affineOrbit_add_exact
#check affineOrbit_add_succ_exact
#check affineOrbit_add_three_exact
#check four_pow_from_affine_cocycle
#print axioms affineOrbit_add_exact
#print axioms affineOrbit_add_three_exact

end GSTFourPowerAffineOrbit
