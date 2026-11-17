import GSTGeneralSpaceRealization
import Mathlib.Algebra.Module.LinearMap.Basic

universe u v w

namespace GSTGeneralSpace

/-- Optional linear duality/probe capability on a General Space realization. -/
structure DualityGeometry (G : GeneralSpace) (R : Type w)
    [CommSemiring R] where
  State : Type w
  addCommMonoid : AddCommMonoid State
  module : Module R State
  pair : State →ₗ[R] State →ₗ[R] R
  left_nondegenerate : ∀ x : State,
    (∀ y : State, pair x y = 0) → x = 0
  right_nondegenerate : ∀ y : State,
    (∀ x : State, pair x y = 0) → y = 0

attribute [instance] DualityGeometry.addCommMonoid DualityGeometry.module

namespace DualityGeometry

variable {G : GeneralSpace} {R : Type w} [CommSemiring R]

/-- A nonzero state has a detecting dual probe. -/
theorem exists_probe_of_ne_zero (D : DualityGeometry G R)
    {x : D.State} (hx : x ≠ 0) :
    ∃ y : D.State, D.pair x y ≠ 0 := by
  by_contra h
  push_neg at h
  exact hx (D.left_nondegenerate x h)

/-- Symmetric statement using right nondegeneracy. -/
theorem exists_coprobe_of_ne_zero (D : DualityGeometry G R)
    {y : D.State} (hy : y ≠ 0) :
    ∃ x : D.State, D.pair x y ≠ 0 := by
  by_contra h
  push_neg at h
  exact hy (D.right_nondegenerate y h)

end DualityGeometry

#check DualityGeometry
#check DualityGeometry.exists_probe_of_ne_zero

end GSTGeneralSpace
