import Mathlib

/-!
# GST constructive polarization of a rotation fold

Equation (1) constructs a positive invariant form from any positive symmetric
bilinear form. The existence of a chosen polarization is stronger than the
earlier lattice-skeleton result. Positivity of a preassigned geometric class
and realization of an arbitrary original X are separate questions.
Proof drafts; analytic torus realization is in the companion derivation.
-/

namespace GSTFoldPolarization

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

structure PositiveForm (V : Type*) [AddCommGroup V] [Module ℝ V] where
  form : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  symmetric : ∀ x y, form x y = form y x
  positive : ∀ x, x ≠ 0 → 0 < form x x

variable (b : PositiveForm V) (J : V →ₗ[ℝ] V)
  (hJ : ∀ x, J (J x) = -x)

def metric (x y : V) : ℝ := b.form x y + b.form (J x) (J y)
def alternatingForm (x y : V) : ℝ := metric b J (J x) y

theorem form_nonnegative (x : V) : 0 ≤ b.form x x := by
  by_cases hx : x = 0
  · subst x; simp
  · exact le_of_lt (b.positive x hx)

theorem metric_symmetric (x y : V) : metric b J x y = metric b J y x := by
  simp only [metric, b.symmetric x y, b.symmetric (J x) (J y)]

include hJ in
theorem metric_invariant (x y : V) :
    metric b J (J x) (J y) = metric b J x y := by
  simp only [metric, hJ, map_neg, LinearMap.neg_apply, neg_neg]
  ring

theorem metric_positive (x : V) (hx : x ≠ 0) : 0 < metric b J x x := by
  have hp := b.positive x hx
  have hn := form_nonnegative b (J x)
  dsimp [metric]
  linarith

include hJ in
theorem skew_adjoint (x y : V) : metric b J (J x) y = -metric b J x (J y) := by
  simp only [metric, hJ, map_neg, LinearMap.neg_apply]
  ring

include hJ in
theorem alternatingForm_skew (x y : V) :
    alternatingForm b J x y = -alternatingForm b J y x := by
  unfold alternatingForm
  rw [skew_adjoint b J hJ x y, metric_symmetric b J x (J y)]

include hJ in
theorem alternatingForm_self (x : V) : alternatingForm b J x x = 0 := by
  have h := alternatingForm_skew b J hJ x x
  linarith

include hJ in
theorem alternatingForm_invariant (x y : V) :
    alternatingForm b J (J x) (J y) = alternatingForm b J x y := by
  unfold alternatingForm
  exact metric_invariant b J hJ (J x) y

include hJ in
theorem polarization_positive (x : V) (hx : x ≠ 0) :
    0 < alternatingForm b J x (J x) := by
  unfold alternatingForm
  rw [metric_invariant b J hJ x x]
  exact metric_positive b J x hx

#print axioms metric_invariant
#print axioms polarization_positive
end GSTFoldPolarization
