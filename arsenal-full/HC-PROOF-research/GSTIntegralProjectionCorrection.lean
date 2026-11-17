import Mathlib

/-!
# Finite integral correction of a nilpotent projection defect

Uncompiled proof draft. Every identity is in an arbitrary associative ring.
This algorithm exactifies a nilpotent algebraic error. Analytic smallness is
not a nilpotence hypothesis, and exactification does not create a new K0 class.
The hand derivation precedes this file in the 2026-10-28 singular-branch record.
-/

namespace GSTIntegralProjectionCorrection
variable {R : Type*} [Ring R]

def defect (a : R) : R := a*a-a
def correctOnce (a : R) : R := a-(2*a-1)*defect a

theorem correctOnce_polynomial (a : R) : correctOnce a=3*a^2-2*a^3 := by
  unfold correctOnce defect
  noncomm_ring

theorem defect_correctOnce (a : R) :
    defect (correctOnce a)=(defect a)^2*(4*defect a-3) := by
  unfold correctOnce defect
  noncomm_ring

theorem defect_factor_commutes (a : R) :
    Commute ((defect a)^2) (4*defect a-3) := by
  change (defect a)^2*(4*defect a-3)=(4*defect a-3)*(defect a)^2
  noncomm_ring

theorem doubled_defect_power (a : R) (m : ℕ) :
    (defect (correctOnce a))^m=(defect a)^(2*m)*(4*defect a-3)^m := by
  rw [defect_correctOnce, (defect_factor_commutes a).mul_pow, ← pow_mul]

theorem correction_halves_nilpotence (a : R) (m : ℕ)
    (h : (defect a)^(2*m)=0) : (defect (correctOnce a))^m=0 := by
  rw [doubled_defect_power, h, zero_mul]

def corrected (a : R) : ℕ → R
  | 0 => a
  | k+1 => corrected (correctOnce a) k

theorem corrected_idempotent (k : ℕ) (a : R)
    (h : (defect a)^(2^k)=0) : corrected a k*corrected a k=corrected a k := by
  induction k generalizing a with
  | zero =>
      have hd : defect a=0 := by simpa using h
      exact sub_eq_zero.mp hd
  | succ k ih =>
      apply ih (correctOnce a)
      apply correction_halves_nilpotence
      simpa only [pow_succ', Nat.mul_comm] using h

theorem power_vanishes_above {a : R} {n m : ℕ} (h : a ^ n = 0) (hnm : n ≤ m) :
    a ^ m = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [pow_add, h, zero_mul]

theorem self_le_two_power (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hp : 0<2^n := pow_pos (by norm_num : 0<(2 : ℕ)) n
      rw [pow_succ]
      omega

/-- An explicit finite constructor, including arbitrary nilpotence exponents. -/
theorem corrected_at_nilpotence_exponent (a : R) (n : ℕ)
    (h : (defect a) ^ n = 0) : corrected a n * corrected a n = corrected a n := by
  exact corrected_idempotent n a (power_vanishes_above h (self_le_two_power n))

theorem correction_fixes_idempotent (a : R) (ha : a*a=a) : correctOnce a=a := by
  simp [correctOnce, defect, ha]

theorem correction_is_complement_compatible (a : R) :
    correctOnce (1-a)=1-correctOnce a := by
  unfold correctOnce defect
  noncomm_ring

#print axioms defect_correctOnce
#print axioms corrected_idempotent
#print axioms corrected_at_nilpotence_exponent
end GSTIntegralProjectionCorrection
