import Mathlib

/-!
# Ordered dressing at arbitrary nilpotent depth

Uncompiled proof draft. The coordinate law x⋆y=x+y+xy works in every
associative ring. It replaces the additive-coordinate requirement, rather
than falsely deleting the commutator from an exponential formula.
No hypothesis here constructs a geometric deck or a Chow source.
-/

open scoped BigOperators
namespace GSTOrderedNilpotentDressing
variable {R : Type*} [Ring R]

def star (x y : R) : R := x + y + x*y

theorem one_add_star (x y : R) : 1 + star x y = (1+x)*(1+y) := by
  unfold star
  noncomm_ring

theorem star_assoc (x y z : R) : star (star x y) z = star x (star y z) := by
  unfold star
  noncomm_ring

@[simp] theorem star_zero (x : R) : star x 0 = x := by simp [star]
@[simp] theorem zero_star (x : R) : star 0 x = x := by simp [star]

def inverseSeries (x : R) (n : ℕ) : R := ∑ k ∈ Finset.range n, (-x)^k

theorem inverseSeries_left (x : R) (n : ℕ) :
    (1+x)*inverseSeries x n = 1-(-x)^n := by
  induction n with
  | zero => simp [inverseSeries]
  | succ n ih =>
      rw [inverseSeries, Finset.sum_range_succ, mul_add]
      change (1+x)*inverseSeries x n + (1+x)*(-x)^n = 1-(-x)^(n+1)
      rw [ih, add_mul, one_mul, pow_succ']
      noncomm_ring

theorem inverseSeries_right (x : R) (n : ℕ) :
    inverseSeries x n*(1+x) = 1-(-x)^n := by
  induction n with
  | zero => simp [inverseSeries]
  | succ n ih =>
      rw [inverseSeries, Finset.sum_range_succ, add_mul]
      change inverseSeries x n*(1+x) + (-x)^n*(1+x) = 1-(-x)^(n+1)
      rw [ih, mul_add, mul_one, pow_succ]
      noncomm_ring

/-- Explicit unit: arbitrary order, integral coefficients, no commutativity. -/
def unitOfNilpotent (x : R) (n : ℕ) (hx : x^n=0) : Rˣ where
  val := 1+x
  inv := inverseSeries x n
  val_inv := by
    rw [inverseSeries_left, neg_pow, hx, mul_zero, sub_zero]
  inv_val := by
    rw [inverseSeries_right, neg_pow, hx, mul_zero, sub_zero]

/-- Coordinates on actual units make multiplication ordered automatically. -/
def unitCoordinate (u : Rˣ) : R := (u : R)-1

theorem unitCoordinate_mul (u v : Rˣ) :
    unitCoordinate (u*v) = star (unitCoordinate u) (unitCoordinate v) := by
  simp only [unitCoordinate, Units.val_mul, star]
  noncomm_ring

theorem unitCoordinate_inverse (u : Rˣ) :
    star (unitCoordinate u) (unitCoordinate u⁻¹) = 0 := by
  rw [← unitCoordinate_mul]
  simp [unitCoordinate]

/-- Exact nonlinear defect, with multiplication order retained. -/
theorem ordered_gauge_defect (a b c S : R) (hS : (1+c)*S=1) :
    (1+a)*(1+b)*S-1 = (star a b-c)*S := by
  calc
    (1+a)*(1+b)*S-1 = ((1+a)*(1+b)-(1+c))*S := by
      rw [sub_mul, hS]
    _ = (star a b-c)*S := by unfold star; noncomm_ring

theorem exact_gauge_of_star_primitive (a b c S : R)
    (hS : (1+c)*S=1) (hc : star a b=c) :
    (1+a)*(1+b)*S=1 := by
  have hz := ordered_gauge_defect a b c S hS
  rw [hc, sub_self, zero_mul] at hz
  exact sub_eq_zero.mp hz

/-- An additive primitive leaves a specific product error. -/
theorem additive_primitive_quadratic_error (a b c S : R)
    (hS : (1+c)*S=1) (hc : a+b=c) :
    (1+a)*(1+b)*S-1 = (a*b)*S := by
  rw [ordered_gauge_defect a b c S hS]
  have h : star a b-c=a*b := by unfold star; rw [← hc]; noncomm_ring
  rw [h]

/-- Tracelessness does not supply nilpotence. Even an involutive element
cannot be nilpotent in a nontrivial ring. -/
theorem involutive_powers_ne_zero [Nontrivial R] (x : R) (hx : x*x=1) (n : ℕ) :
    x^n≠0 := by
  have hu : IsUnit x := ⟨⟨x,x,hx,hx⟩,rfl⟩
  exact (hu.pow n).ne_zero

def tracelessInvolution : Matrix (Fin 2) (Fin 2) ℚ := !![0,1;1,0]

theorem traceless_does_not_imply_nilpotent :
    Matrix.trace tracelessInvolution=0 ∧
      ∀ n : ℕ,tracelessInvolution^n≠0 := by
  constructor
  · norm_num [tracelessInvolution, Matrix.trace, Fin.sum_univ_two, Matrix.of_apply]
  · exact involutive_powers_ne_zero tracelessInvolution (by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [tracelessInvolution, Matrix.mul_apply, Matrix.one_apply,
          Matrix.of_apply])

#print axioms star_assoc
#print axioms unitOfNilpotent
#print axioms ordered_gauge_defect
end GSTOrderedNilpotentDressing
