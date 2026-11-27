import Mathlib

/-!
# Exact boundary correction and the remaining type defect

Proof draft; not compiled in this session. The splitting identity d h d=d
constructs a projection onto closed vectors. It does not supply a Hodge
projector, integral rectifiable current, or algebraic-cycle representative.
This separates exact correction from the category of the corrected object.
-/

noncomputable section
namespace GSTSplitBoundaryProjection

variable {V W U : Type*}
  [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W]
  [AddCommGroup U] [Module ℚ U]

def closedProjection (d : V →ₗ[ℚ] W) (h : W →ₗ[ℚ] V) : Module.End ℚ V :=
  1 - h.comp d

@[simp] theorem closedProjection_apply (d : V →ₗ[ℚ] W)
    (h : W →ₗ[ℚ] V) (x : V) : closedProjection d h x = x - h (d x) := rfl

theorem closedProjection_closed (d : V →ₗ[ℚ] W) (h : W →ₗ[ℚ] V)
    (hsplit : ∀ x, d (h (d x)) = d x) (x : V) :
    d (closedProjection d h x) = 0 := by
  rw [closedProjection_apply, map_sub, hsplit, sub_self]

theorem closedProjection_fixes_closed (d : V →ₗ[ℚ] W) (h : W →ₗ[ℚ] V)
    (x : V) (hx : d x = 0) : closedProjection d h x = x := by
  rw [closedProjection_apply, hx, map_zero, sub_zero]

theorem closedProjection_idempotent (d : V →ₗ[ℚ] W) (h : W →ₗ[ℚ] V)
    (hsplit : ∀ x, d (h (d x)) = d x) :
    (closedProjection d h).comp (closedProjection d h) = closedProjection d h := by
  ext x
  exact closedProjection_fixes_closed d h _ (closedProjection_closed d h hsplit x)

theorem closedProjection_range (d : V →ₗ[ℚ] W) (h : W →ₗ[ℚ] V)
    (hsplit : ∀ x, d (h (d x)) = d x) :
    LinearMap.range (closedProjection d h) = LinearMap.ker d := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact closedProjection_closed d h hsplit y
  · intro hx
    exact ⟨x, closedProjection_fixes_closed d h x hx⟩

/-- The repaired projection always has closed image. -/
theorem repaired_type_projection_closed (d : V →ₗ[ℚ] W)
    (h : W →ₗ[ℚ] V) (P : Module.End ℚ V)
    (hsplit : ∀ x, d (h (d x)) = d x) (x : V) :
    d (closedProjection d h (P x)) = 0 :=
  closedProjection_closed d h hsplit (P x)

/-- Exact additional requirement for keeping the projected type after repair.
The correction term itself must lie in the P-fixed subspace. -/
theorem repaired_type_iff_correction_has_type (d : V →ₗ[ℚ] W)
    (h : W →ₗ[ℚ] V) (P : Module.End ℚ V)
    (hP : ∀ x, P (P x) = P x) (x : V) :
    P (closedProjection d h (P x)) = closedProjection d h (P x) ↔
      P (h (d (P x))) = h (d (P x)) := by
  rw [closedProjection_apply, map_sub, hP]
  constructor
  · intro heq
    have hh : P x + -P (h (d (P x))) = P x + -h (d (P x)) := by
      simpa only [sub_eq_add_neg] using heq
    exact neg_injective (add_left_cancel hh)
  · intro heq
    rw [heq]

/-- Preserving a class also needs a separate comparison: the boundary
correction must have zero image under the chosen class map. -/
theorem repaired_class (d : V →ₗ[ℚ] W) (h : W →ₗ[ℚ] V)
    (P : Module.End ℚ V) (cl : V →ₗ[ℚ] U) (x : V)
    (hcorrection : cl (h (d (P x))) = 0) :
    cl (closedProjection d h (P x)) = cl (P x) := by
  rw [closedProjection_apply, map_sub, hcorrection, sub_zero]

#print axioms closedProjection_range
#print axioms repaired_type_iff_correction_has_type

end GSTSplitBoundaryProjection
