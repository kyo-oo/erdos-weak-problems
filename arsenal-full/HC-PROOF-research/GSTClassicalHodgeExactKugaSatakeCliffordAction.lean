import Mathlib

/-!
# Exact even-Clifford Kuga--Satake tensor: the linear algebra core

Mathematical source:
OpenAI/math, "Algebraic Kuga--Satake correspondences and Hodge conjectures
on a K3 quadratic locus", 30 September 2026, formula
    j_w(v)(a) = v a w.

In the paper, v and w belong to a Clifford algebra and w is nonisotropic,
so w has an inverse after normalizing by its nonzero quadratic value.
The map j_w embeds the quadratic space into rational endomorphisms of the
even-Clifford carrier.  Its exact right multiplier MATTERS: replacing j_w
by an unspecified Hodge embedding loses the prescribed correspondence
tensor and can conceal the hard geometry.

Here we prove the universal noncommutative algebra identity underlying that
construction, with arbitrary rational algebra A (eventually specialized to
the appropriate Clifford algebra).  We show:
* both argument directions are Q-linear;
* j_w is injective whenever w has a right inverse;
* evaluation at the identity recovers v*w;
* composition agrees exactly with ordered noncommutative multiplication.

We do not assert that the corresponding Hodge tensor is ALGEBRAIC on a K3
surface or any abelian variety; that would require a true algebraic cycle.

NEEDS CI RUN LATER.
-/

set_option maxHeartbeats 15000000

noncomputable section

namespace GSTClassicalHodgeExactKugaSatakeCliffordAction

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- A specific rational-linear Kuga--Satake-style endomorphism.
The order is LEFT multiplication by v and RIGHT multiplication by w.
Noncommutativity is retained; there is no commutativity assumption. -/
noncomputable def fixedRightCliffordAction
    (w v : A) : Module.End ℚ A where
  toFun := fun a => v * a * w
  map_add' := by
    intro a b
    simp [mul_add, add_mul]
  map_smul' := by
    intro c a
    simp [mul_smul_comm, smul_mul_assoc]

@[simp]
theorem fixedRightCliffordAction_apply
    (w v a : A) :
    fixedRightCliffordAction w v a = v * a * w := rfl

/-- The EXACT Kuga--Satake tensor in endomorphism form,
j_w : A -> End_Q(A), v |-> (a |-> v a w). -/
noncomputable def exactKugaSatakeMap
    (w : A) : A →ₗ[ℚ] Module.End ℚ A where
  toFun := fixedRightCliffordAction w
  map_add' := by
    intro v u
    ext a
    simp [fixedRightCliffordAction, add_mul]
  map_smul' := by
    intro c v
    ext a
    simp [fixedRightCliffordAction, smul_mul_assoc]

@[simp]
theorem exactKugaSatakeMap_apply
    (w v a : A) :
    exactKugaSatakeMap w v a = v * a * w := rfl

/-- The right-twisted Clifford tensor evaluates at 1 to right
multiplication by its defining nonisotropic vector. -/
@[simp]
theorem exactKugaSatakeMap_one
    (w v : A) :
    exactKugaSatakeMap w v (1 : A) = v * w := by
  simp [exactKugaSatakeMap_apply]

/-- Nonisotropic Clifford vectors admit explicit rational right inverses.
When such an inverse has been constructed in the underlying Clifford
algebra, the exact Kuga--Satake map is automatically injective.
No assumption of commutativity or absence of zero divisors is needed. -/
theorem exactKugaSatakeMap_injective
    (w winv : A)
    (hwinv : w * winv = 1) :
    Function.Injective (exactKugaSatakeMap w) := by
  intro v u hvu
  have hval : v * w = u * w := by
    have heval := congrArg (fun T : Module.End ℚ A => T 1) hvu
    simpa using heval
  have hright := congrArg (fun t : A => t * winv) hval
  simpa [mul_assoc, hwinv] using hright

/-- Two ordered Kuga--Satake endomorphisms compose with both right
multipliers in the REVERSED order dictated by noncommutative algebra. -/
theorem fixedRightCliffordAction_comp_apply
    (w z v u a : A) :
    ((fixedRightCliffordAction w v).comp
      (fixedRightCliffordAction z u)) a =
        v * (u * a * z) * w := rfl

/-- Rational left scaling of the exact tensor, used when passing from a
primitive Clifford vector to its scaled polarisation representative. -/
theorem exactKugaSatakeMap_smul
    (w v : A) (c : ℚ) :
    exactKugaSatakeMap w (c • v) =
      c • exactKugaSatakeMap w v := by
  exact (exactKugaSatakeMap w).map_smul c v

/-- Cancellation of the exact right multiplier is already visible on
individual Clifford elements, with no cohomological assumptions. -/
theorem fixedRightCliffordAction_eval_cancel
    (w winv v : A)
    (hwinv : w * winv = 1) :
    (fixedRightCliffordAction w v 1) * winv = v := by
  simp [fixedRightCliffordAction, mul_assoc, hwinv]

/-! ## Nonisotropic Clifford vectors provide their own inverse

For an exact Clifford relation w² = q(w,w)·1 and q(w,w) ≠ 0,
the right inverse used in the preceding injectivity theorem is
not a NEW hypothesis. It is the explicit element q(w,w)⁻¹·w.
This upgrades the tensor injectivity statement to the genuine
quadratic-input condition in the Kuga--Satake construction. -/

/-- An algebraic element with nonzero rational quadratic square has
the explicit right inverse prescribed by its quadratic value. -/
theorem right_inverse_of_quadratic_relation
    (w : A) (q : ℚ) (hq : q ≠ 0)
    (hsquare : w * w = algebraMap ℚ A q) :
    w * ((q⁻¹) • w) = 1 := by
  calc
    w * ((q⁻¹) • w) = q⁻¹ • (w * w) := by
      rw [mul_smul_comm]
    _ = q⁻¹ • algebraMap ℚ A q := by rw [hsquare]
    _ = 1 := by
      simp [Algebra.smul_def, ← map_mul, hq]

/-- The mirror left inverse follows from the same Clifford relation. -/
theorem left_inverse_of_quadratic_relation
    (w : A) (q : ℚ) (hq : q ≠ 0)
    (hsquare : w * w = algebraMap ℚ A q) :
    ((q⁻¹) • w) * w = 1 := by
  calc
    ((q⁻¹) • w) * w = q⁻¹ • (w * w) := by
      rw [smul_mul_assoc]
    _ = q⁻¹ • algebraMap ℚ A q := by rw [hsquare]
    _ = 1 := by
      simp [Algebra.smul_def, ← map_mul, hq]

/-- Exact Kuga--Satake tensor injectivity is now proved directly from
the actual NONISOTROPIC QUADRATIC RELATION, rather than assuming
a separately furnished inverse of the right Clifford multiplier. -/
theorem exactKugaSatakeMap_injective_of_quadratic_relation
    (w : A) (q : ℚ) (hq : q ≠ 0)
    (hsquare : w * w = algebraMap ℚ A q) :
    Function.Injective (exactKugaSatakeMap w) :=
  exactKugaSatakeMap_injective w ((q⁻¹) • w)
    (right_inverse_of_quadratic_relation w q hq hsquare)

#check exactKugaSatakeMap
#check exactKugaSatakeMap_injective
#check fixedRightCliffordAction_comp_apply
#print axioms exactKugaSatakeMap_injective

end GSTClassicalHodgeExactKugaSatakeCliffordAction
