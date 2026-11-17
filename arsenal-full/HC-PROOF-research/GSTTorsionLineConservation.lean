import Mathlib

/-!
# Rational rigidity of a nilpotent two-torsion line class

Uncompiled proof draft. The finite-dimensional geometric argument supplying
nilpotence of [K]-1 is in the hand derivation, not assumed as a universal
classical Hodge realization. Integral cancellation by two is not used.
-/

namespace GSTTorsionLineConservation
variable {R : Type*} [CommRing R]

theorem involution_augmentation_relation (x : R) (hx : x^2=1) :
    (x-1)^2=(-2)*(x-1) := by linear_combination hx

theorem involution_augmentation_powers (x : R) (hx : x^2=1) (k : ℕ) :
    (x-1)^(k+1)=(-2 : R)^k*(x-1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ,ih]
      calc
        ((-2 : R)^k*(x-1))*(x-1)=(-2 : R)^k*(x-1)^2 := by ring
        _ = (-2 : R)^k*((-2)*(x-1)) := by rw [involution_augmentation_relation x hx]
        _ = (-2 : R)^(k+1)*(x-1) := by rw [pow_succ]; ring

/-- Explicit integral annihilator before any rationalization. -/
theorem integral_two_power_annihilates (x : R) (hx : x^2=1) (k : ℕ)
    (hn : (x-1)^(k+1)=0) : (-2 : R)^k*(x-1)=0 := by
  rw [← involution_augmentation_powers x hx k]
  exact hn

theorem rational_nilpotent_involution [Algebra ℚ R] (x : R)
    (hx : x^2=1) (k : ℕ) (hn : (x-1)^(k+1)=0) : x=1 := by
  have hz : ((-2 : ℚ)^k) • (x-1)=0 := by
    have hlink : (algebraMap ℚ R) ((-2 : ℚ)^k) = (-2 : R)^k := by
      rw [map_pow, map_neg, map_ofNat]
    rw [Algebra.smul_def, hlink]
    exact integral_two_power_annihilates x hx k hn
  have hnz : (-2 : ℚ)^k≠0 := pow_ne_zero _ (by norm_num)
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left hnz)

theorem rational_involution_of_isNilpotent [Algebra ℚ R] [Nontrivial R]
    (x : R) (hx : x^2=1) (hn : IsNilpotent (x-1)) : x=1 := by
  obtain ⟨n,hn⟩ := hn
  cases n with
  | zero => norm_num at hn
  | succ k => exact rational_nilpotent_involution x hx k hn

/-- Applied to pushforward from a principal divisor: its unit class maps to zero. -/
theorem torsion_line_principal_push_zero {W : Type*} [AddCommGroup W]
    [Algebra ℚ R] (push : R →+ W) (hunit : push 1=0)
    (x : R) (hx : x^2=1) (k : ℕ) (hn : (x-1)^(k+1)=0) : push x=0 := by
  rw [rational_nilpotent_involution x hx k hn,hunit]

#print axioms integral_two_power_annihilates
#print axioms rational_nilpotent_involution
#print axioms torsion_line_principal_push_zero
end GSTTorsionLineConservation
