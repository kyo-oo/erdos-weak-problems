import Mathlib

/-!
# Exact torsion transport, with actual groups and maps

Proof draft; not compiled in this session, at the owner's request.
The general bound is a*b, not lcm(a,b). No exactness proposition is
replaced by `True`. Instantiating this algebra with a particular group
cohomology sequence remains a separate geometric/cohomological obligation.
-/

namespace GSTExactSequenceTorsion

variable {K A B : Type*} [AddCommGroup K] [AddCommGroup A] [AddCommGroup B]

/-- Only exactness at A and annihilation of the actual image of q are needed. -/
theorem product_annihilates
    (i : K →+ A) (q : A →+ B)
    (exact_at : ∀ x, q x = 0 → ∃ k, i k = x)
    (a b : ℕ) (kernel_kill : ∀ k : K, a • k = 0)
    (image_kill : ∀ x : A, b • q x = 0) (x : A) :
    (a * b) • x = 0 := by
  have hx : q (b • x) = 0 := by
    rw [map_nsmul]
    exact image_kill x
  obtain ⟨k, hk⟩ := exact_at (b • x) hx
  calc
    (a * b) • x = a • (b • x) := mul_nsmul' x a b
    _ = a • i k := by rw [hk]
    _ = i (a • k) := (map_nsmul i a k).symm
    _ = 0 := by rw [kernel_kill k, map_zero]

/-- The 16-bound now has a mathematical conclusion. -/
theorem sixteen_annihilates
    (i : K →+ A) (q : A →+ B)
    (exact_at : ∀ x, q x = 0 → ∃ k, i k = x)
    (kernel_four : ∀ k : K, (4 : ℕ) • k = 0)
    (image_four : ∀ x, (4 : ℕ) • q x = 0) (x : A) :
    (16 : ℕ) • x = 0 := by
  simpa using product_annihilates i q exact_at 4 4 kernel_four image_four x

/-- Zero inflation and exactness force concentration/injectivity. -/
theorem injective_of_zero_inflation
    (i : K →+ A) (q : A →+ B)
    (exact_at : ∀ x, q x = 0 → ∃ k, i k = x)
    (inflation_zero : ∀ k, i k = 0) : Function.Injective q := by
  intro x y hxy
  have hker : q (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨k, hk⟩ := exact_at (x - y) hker
  have hz : x - y = 0 := hk.symm.trans (inflation_zero k)
  exact sub_eq_zero.mp hz

/-- When the inflation group itself vanishes there is no kernel. -/
theorem injective_of_subsingleton_kernel [Subsingleton K]
    (i : K →+ A) (q : A →+ B)
    (exact_at : ∀ x, q x = 0 → ∃ k, i k = x) :
    Function.Injective q := by
  apply injective_of_zero_inflation i q exact_at
  intro k
  rw [Subsingleton.elim k 0, map_zero]

/-- Order-16 middle term: exponent four on the ends cannot imply four here. -/
theorem product_bound_is_sharp_at_four :
    (16 : ℕ) • (1 : ZMod 16) = 0 ∧
      (4 : ℕ) • (1 : ZMod 16) ≠ 0 ∧
      (8 : ℕ) • (1 : ZMod 16) ≠ 0 := by
  decide

#print axioms product_annihilates
#print axioms injective_of_zero_inflation

end GSTExactSequenceTorsion
