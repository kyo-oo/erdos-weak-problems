import Mathlib

/-!
# Extension-sensitive GST folds

Algebraic proof drafts for the hand derivation
`research/derivations/GST_extension_sensitive_causal_folds_2026_11_03.tex`.
`period` is the computed wedge coefficient on two actual elliptic handles;
its geometric Hodge interpretation is hand-level, not a field assumed here.
Monodromy invariance and balanced weight do not supply the period equation.
No compilation or original-X source-existence theorem is claimed.
-/

namespace GSTFoldPeriodDescent

variable {R : Type*} [CommRing R]

def period (A B C D x y : R) : R := A*x*y-B*x-C*y+D

theorem affine_period_coefficients (A B C D n m u v z : R) :
    period A B C D (n*z+u) (m*z+v) =
      A*n*m*z^2 + (A*(n*v+m*u)-n*B-m*C)*z +
        (A*u*v-B*u-C*v+D) := by
  simp only [period]
  ring

theorem balanced_period_constant (B C D n m u v z : R)
    (h : n*B+m*C=0) :
    period 0 B C D (n*z+u) (m*z+v) = D-B*u-C*v := by
  have hex : period 0 B C D (n*z+u) (m*z+v) =
      -(n*B+m*C)*z+(D-B*u-C*v) := by simp [period]; ring
  rw [hex,h]
  ring

def extensionDifference (n m u v : R) : R := m*u-n*v

theorem matched_period_zero (n m u v z : R) :
    period 0 m (-n) (extensionDifference n m u v) (n*z+u) (m*z+v)=0 := by
  simp [period,extensionDifference]
  ring

theorem extension_base_change (n m u v c : R) :
    extensionDifference n m (u-n*c) (v-m*c)=extensionDifference n m u v := by
  simp [extensionDifference]
  ring

theorem extension_ramification (n m u v e : R) :
    extensionDifference (e*n) (e*m) u v=e*extensionDifference n m u v := by
  simp [extensionDifference]
  ring

/-- Coordinates in the factor-ordered cross Kunneth block. -/
def monodromy (n m : R) (q : Fin 4 → R) : Fin 4 → R :=
  ![q 0,q 1+m*q 0,q 2+n*q 0,
    q 3+n*q 1+m*q 2+n*m*q 0]

theorem monodromy_additive_parameter (n m s t : R) (q : Fin 4 → R) :
    monodromy (s*n) (s*m) (monodromy (t*n) (t*m) q)=
      monodromy ((s+t)*n) ((s+t)*m) q := by
  ext i
  fin_cases i <;> simp [monodromy] <;> ring

theorem balanced_monodromy_fixed (B C D n m : R) (h : n*B+m*C=0) :
    monodromy n m ![0,B,C,D]=![0,B,C,D] := by
  ext i
  fin_cases i <;> simp [monodromy]
  linear_combination h

/-- A monodromy-fixed candidate can still have any prescribed period defect. -/
theorem fixed_balanced_period (u v z : R) :
    period 0 1 (-1) 0 (z+u) (z+v)=v-u := by
  simp [period]
  ring

/-- Exact exterior intersection coefficient, including the A*D term. -/
def crossIntersection (A B C D : R) : R := 2*(B*C-A*D)

theorem matched_self_intersection (n m u v : R) :
    crossIntersection 0 m (-n) (extensionDifference n m u v)= -2*n*m := by
  simp [crossIntersection]
  ring

section RationalCausality
def normalizedExtension (u v : ℚ) : ℚ := u-v

theorem normalized_extension_path (u v w : ℚ) :
    normalizedExtension u w=normalizedExtension u v+normalizedExtension v w := by
  simp [normalizedExtension]

theorem three_period_coefficients (A B C D n m u v : ℚ)
    (hn : n ≠ 0) (hm : m ≠ 0) :
    (A*n*m=0 ∧ A*(n*v+m*u)-n*B-m*C=0 ∧
      A*u*v-B*u-C*v+D=0) ↔
    (A=0 ∧ n*B+m*C=0 ∧ D=B*u+C*v) := by
  constructor
  · rintro ⟨h2,h1,h0⟩
    have hAn : A*n=0 := (mul_eq_zero.mp h2).resolve_right hm
    have hA : A=0 := (mul_eq_zero.mp hAn).resolve_right hn
    subst A
    simp only [zero_mul,zero_sub] at h1 h0
    exact ⟨rfl,by linarith,by linarith⟩
  · rintro ⟨rfl,h1,h0⟩
    refine ⟨by norm_num, ?_, ?_⟩ <;> linarith

end RationalCausality

/-! A finite three-test law for arbitrary representations. E,F,H must be
the ACTUAL tensor Lie operators in a geometric instance; this section
does not identify an arbitrary supplied module with H*(X). -/
section ThreeTests
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

def charge0 (E F : V →ₗ[ℚ] V) : V →ₗ[ℚ] V := E-F
def charge1 (E F : V →ₗ[ℚ] V) : V →ₗ[ℚ] V := (1/2 : ℚ) • E-2 • F
def charge2 (E F H : V →ₗ[ℚ] V) : V →ₗ[ℚ] V := -H+E-2 • F

theorem three_charge_kernels (E F H : V →ₗ[ℚ] V) (v : V) :
    (charge0 E F v=0 ∧ charge1 E F v=0 ∧ charge2 E F H v=0) ↔
      (E v=0 ∧ F v=0 ∧ H v=0) := by
  simp only [charge0,charge1,charge2,LinearMap.sub_apply,
    LinearMap.add_apply,LinearMap.smul_apply,LinearMap.neg_apply]
  constructor
  · rintro ⟨h0,h1,h2⟩
    have he : E v = (4/3 : ℚ) • (E v-F v)-
        (2/3 : ℚ) • ((1/2 : ℚ) • E v-2 • F v) := by module
    have hf : F v = (1/3 : ℚ) • (E v-F v)-
        (2/3 : ℚ) • ((1/2 : ℚ) • E v-2 • F v) := by module
    rw [h0,h1] at he hf
    simp only [smul_zero,sub_zero] at he hf
    refine ⟨he,hf,?_⟩
    rw [he,hf] at h2
    simpa using h2
  · rintro ⟨he,hf,hh⟩
    simp [he,hf,hh]

theorem all_linear_charges_zero (E F H : V →ₗ[ℚ] V) (v : V)
    (h : charge0 E F v=0 ∧ charge1 E F v=0 ∧ charge2 E F H v=0)
    (a b c : ℚ) : (a • E+b • F+c • H) v=0 := by
  rcases (three_charge_kernels E F H v).mp h with ⟨he,hf,hh⟩
  simp [he,hf,hh]

end ThreeTests

#print axioms affine_period_coefficients
#print axioms balanced_monodromy_fixed
#print axioms matched_self_intersection
#print axioms three_charge_kernels
end GSTFoldPeriodDescent
