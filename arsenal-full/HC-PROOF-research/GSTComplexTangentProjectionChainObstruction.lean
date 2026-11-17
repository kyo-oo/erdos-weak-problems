import Mathlib
import GSTSplitBoundaryProjection

/-!
# GST Hodge geometric surgery: complex-tangent projection is NOT a chain map

Original all-X target: an integral homology preserving chain-level operator
that turns the primitive component of an ample-shifted Hodge cycle into a
Kähler-calibrated holomorphic integral current.

This file isolates a genuine differential-geometric obstruction to
a tempting LOCAL route: project each current tangent plane / differential
form to the J-invariant (1,1) component, then declare it a closed current.
The J-type projector does NOT commute with the exterior differential,
already on a projective square elliptic product E x E and in the ZERO
cohomology class.

Choose real global coordinates x,y,u,v on E x E, and J acting by
J* dx = -dy, J* dy=dx, J* du=-dv, J* dv=du.

Take the smooth 2-form
  omega = cos(x) dx ∧ du
which is EXACT since omega = d(sin(x) du), hence d omega = 0.
The real (1,1) projector is
  pi11 omega = (cos(x)/2)(dx ∧ du + dy ∧ dv).
But
  d(pi11 omega) = -(sin(x)/2) dx ∧ dy ∧ dv ≠ 0.

Therefore an arbitrary chain-level Hodge projector cannot be built
by pointwise complex-tangent projection. The missing universal GST
surgery must simultaneously CORRECT THE BOUNDARY and preserve integer
multiplicity and homology; no abstract N-window coordinate identity
proves that correction exists.

Lean verifies the exact rational Fourier-coefficient matrix, not the
entire analytic complex manifold theorem. There is NO claim of Hodge
completion or a bogus all-X geometric calibration operator.
-/

namespace GSTComplexTangentProjectionChainObstruction

/-- Coefficients of cos(x) dx∧du and cos(x) dy∧dv
in the specific exact torus Fourier block. -/
abbrev FourierTwoBlock := ℚ × ℚ

/-- Coefficient of sin(x) dx∧dy∧dv in the exterior differential,
with the order of wedge factors fixed. -/
def boundaryAmplitude (f : FourierTwoBlock) : ℚ := -f.2

/-- J-invariant (1,1) projector on this two-dimensional Fourier block. -/
def complexTypeProjection (f : FourierTwoBlock) : FourierTwoBlock :=
  ((f.1 + f.2)/2, (f.1 + f.2)/2)

/-- The exact smooth closed 2-form omega=cos(x) dx∧du. -/
def originalClosedForm : FourierTwoBlock := (1,0)

/-- d omega=0, reflecting the explicit exact primitive sin(x) du. -/
theorem original_is_closed :
    boundaryAmplitude originalClosedForm = 0 := by
  norm_num [boundaryAmplitude, originalClosedForm]

/-- J projection does not respect the exterior differential.
A zero-homology smooth input already gives a NON-CLOSED output. -/
theorem type_projector_breaks_closedness :
    boundaryAmplitude (complexTypeProjection originalClosedForm) =
      -(1/2 : ℚ) := by
  norm_num [boundaryAmplitude, complexTypeProjection, originalClosedForm]

theorem no_unconditional_chain_map_identity :
    ¬ ∀ f : FourierTwoBlock,
      boundaryAmplitude f = 0 →
      boundaryAmplitude (complexTypeProjection f) = 0 := by
  intro h
  have h1 := h originalClosedForm original_is_closed
  rw [type_projector_breaks_closedness] at h1
  norm_num at h1

/-- A J-projection correction must carry a nonzero boundary term;
it cannot preserve closedness by coefficient recoordination alone. -/
theorem corrected_boundary_necessarily_nonzero
    (g : FourierTwoBlock)
    (hclose : boundaryAmplitude
        (complexTypeProjection originalClosedForm + g) = 0) :
    boundaryAmplitude g = (1/2 : ℚ) := by
  have h1 : boundaryAmplitude (complexTypeProjection originalClosedForm + g) =
      boundaryAmplitude (complexTypeProjection originalClosedForm) +
      boundaryAmplitude g := by
    simp [boundaryAmplitude, Prod.snd_add]
    ring
  rw [h1, type_projector_breaks_closedness] at hclose
  linarith

/-- The coefficient of dx∧dy∧du∧dv in the square of the bivector
a dx∧du+b dy∧dv. A decomposable simple bivector must have zero
exterior square. -/
def bivectorWedgeSquare (f : FourierTwoBlock) : ℚ := -2 * f.1 * f.2

theorem original_bivector_is_simple :
    bivectorWedgeSquare originalClosedForm = 0 := by
  norm_num [bivectorWedgeSquare, originalClosedForm]

/-- Projecting a simple integer tangent bivector to J-invariant type (1,1)
produces a NON-SIMPLE fractional bivector, not a valid oriented tangent
2-plane of any integral rectifiable current. -/
theorem complex_projection_of_simple_is_not_simple :
    bivectorWedgeSquare (complexTypeProjection originalClosedForm) =
      -(1/2 : ℚ) := by
  norm_num [bivectorWedgeSquare, complexTypeProjection, originalClosedForm]

theorem complex_projection_cannot_be_single_integral_tangent :
    bivectorWedgeSquare (complexTypeProjection originalClosedForm) ≠ 0 := by
  rw [complex_projection_of_simple_is_not_simple]
  norm_num

#check original_is_closed
#check type_projector_breaks_closedness
#check complex_projection_cannot_be_single_integral_tangent
#check corrected_boundary_necessarily_nonzero
#print axioms no_unconditional_chain_map_identity

/-! ## Exact repair and the simultaneous type obstruction (2026-10-28)

The new generic splitting theorem repairs the boundary. On THIS genuine
Fourier coefficient block the repaired vector loses type: the intersection
of closed vectors with the type-fixed space is zero. These statements are
coefficient algebra; they do not formalize the analytic torus/current API.
The new declarations are proof drafts, not compiled in this session.
-/

/-- C=1-hd for the explicit right inverse h(t)=(0,-t). -/
def closedRepair (f : FourierTwoBlock) : FourierTwoBlock := (f.1, 0)

theorem closedRepair_is_closed (f : FourierTwoBlock) :
    boundaryAmplitude (closedRepair f) = 0 := by
  simp [closedRepair, boundaryAmplitude]

theorem closedRepair_fixes_closed (f : FourierTwoBlock)
    (hf : boundaryAmplitude f = 0) : closedRepair f = f := by
  rcases f with ⟨a,b⟩
  have hb : b = 0 := by simpa [boundaryAmplitude] using hf
  simp [closedRepair, hb]

/-- A sharp obstruction: there is no nonzero vector satisfying both demands. -/
theorem closed_and_type_fixed_iff_zero (f : FourierTwoBlock) :
    (boundaryAmplitude f = 0 ∧ complexTypeProjection f = f) ↔ f = 0 := by
  constructor
  · rintro ⟨hc, ht⟩
    rcases f with ⟨a,b⟩
    have hb : b = 0 := by simpa [boundaryAmplitude] using hc
    have hsecond := congrArg Prod.snd ht
    change (a+b)/2 = b at hsecond
    have ha : a = 0 := by linarith
    simp [ha, hb]
  · rintro rfl
    norm_num [boundaryAmplitude, complexTypeProjection]

/-- Removing the boundary alone leaves a nonzero and wrongly typed vector. -/
theorem boundary_repair_loses_type :
    closedRepair (complexTypeProjection originalClosedForm) = (1/2,0) ∧
      complexTypeProjection (closedRepair (complexTypeProjection originalClosedForm)) ≠
        closedRepair (complexTypeProjection originalClosedForm) := by
  constructor
  · norm_num [closedRepair, complexTypeProjection, originalClosedForm]
  · intro h
    have hsecond := congrArg Prod.snd h
    norm_num [closedRepair, complexTypeProjection, originalClosedForm] at hsecond

#print axioms closed_and_type_fixed_iff_zero
#print axioms boundary_repair_loses_type

end GSTComplexTangentProjectionChainObstruction
