import GSTPolarizedHodgeResidualEnergy

/-!
# GST canonical positive polarized primitive ghost from any Hodge residual

The previous GST separator library produces arbitrary rational-linear
ghosts by quotient duality. This file constructs a SPECIFIC, canonical
candidate from actual primitive Hodge-Riemann intersection geometry:

    r = alpha - cl(Z_alpha)
    ghost_alpha(v) = Q(r,v).

If r != 0, positive definiteness proves
    ghost_alpha(alpha) = Q(r,r) > 0.

All the known native basis cycles z_i are annihilated by this
ghost, because r is intersection-orthogonal to them.

When the z_i span the already-algebraic image (independent of
the conjecture, by finite Betti dimension), the ghost annihilates
EVERY actual native algebraic cycle class of the target X.

This supplies a CANONICAL rational positive-norm GST separator
to attack with strict common-carrier/trace geometry. It does not
claim the separator cannot exist: ruling out this canonical ghost
UNCONDITIONALLY would be exactly the missing Hodge argument.

The theorem is rational-linear. The genuine geometric Hodge-Riemann
form and actual scheme cycleClass are inputs to be instantiated
from Stage-2G, not silently presumed by formal algebra.
-/

set_option maxHeartbeats 4500000
noncomputable section

open GSTUniversalHodgeResidualProjection
open GSTPolarizedHodgeResidualEnergy

namespace GSTCanonicalPolarizedHodgeGhost

variable {ι N V : Type*}
  [Fintype ι] [DecidableEq ι]
  [AddCommGroup N] [Module ℚ N]
  [AddCommGroup V] [Module ℚ V]

/-- The canonical polarized residual ghost: intersection with the
unknown target Hodge residual, which is a valid rational cohomology
class and does not require it to be algebraic. -/
noncomputable def canonicalResidualGhost
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (alpha : V) : V →ₗ[ℚ] ℚ :=
  Q (residualClass P alpha)

/-- Ghost annihilates every individually known native geometric
cycle generator, without any arbitrary detector assumptions. -/
theorem canonicalGhost_annihilates_every_native_generator
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hGeometricPairing :
      ∀ (i : ι) (x : V),
        P.detectors i x = (Q x) (P.cycleClass (P.cycles i)))
    (alpha : V) (i : ι) :
    canonicalResidualGhost P Q alpha (P.cycleClass (P.cycles i)) = 0 := by
  change (Q (residualClass P alpha))
      (P.cycleClass (P.cycles i)) = 0
  rw [← hGeometricPairing i (residualClass P alpha)]
  exact residual_orthogonal_to_all_geometric_cycles P alpha i

/-- It detects its own target alpha with the exact positive
polarization residual norm, rather than an arbitrarily chosen
nonzero scalar or a circular target-cycle equation. -/
theorem canonicalGhost_detection_equals_residual_norm
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hGeometricPairing :
      ∀ (i : ι) (x : V),
        P.detectors i x = (Q x) (P.cycleClass (P.cycles i)))
    (alpha : V) :
    canonicalResidualGhost P Q alpha alpha =
      (Q (residualClass P alpha)) (residualClass P alpha) := by
  let a := P.cycleClass (projectedNativeCycle P alpha)
  let r := residualClass P alpha
  have hsum : a + r = alpha :=
    actual_cycle_plus_residual_equals_target P alpha
  have horth : (Q r) a = 0 :=
    residual_orthogonal_to_algebraic_projection
      P Q hGeometricPairing alpha
  change (Q r) alpha = (Q r) r
  calc
    (Q r) alpha = (Q r) (a+r) := by rw [hsum]
    _ = (Q r) a + (Q r) r := by rw [map_add]
    _ = (Q r) r := by rw [horth, zero_add]

/-- Once a finite independent family spans the native algebraic
image, the canonical ghost kills EVERY native cycle on X.
The span premise is about existing algebraic classes, NOT about
all rational Hodge classes: this can be obtained by taking a
basis of the finite-dimensional cycleClass IMAGE itself. -/
theorem canonicalGhost_annihilates_entire_native_cycleClass_image
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hGeometricPairing :
      ∀ (i : ι) (x : V),
        P.detectors i x = (Q x) (P.cycleClass (P.cycles i)))
    (hNativeImageSpanned :
      ∀ Z : N, ∃ coeff : ι → ℚ,
        P.cycleClass Z = ∑ i, coeff i • P.cycleClass (P.cycles i))
    (alpha : V) (Z : N) :
    canonicalResidualGhost P Q alpha (P.cycleClass Z) = 0 := by
  classical
  obtain ⟨coeff, hcoeff⟩ := hNativeImageSpanned Z
  rw [hcoeff]
  simp [canonicalGhost_annihilates_every_native_generator
    P Q hGeometricPairing alpha]

/-- If Hodge conjecture were false for the present primitive class,
its canonically constructed separator would pair POSITIVELY with
that class and vanish on the ENTIRE known native image.
This is the mathematically exact target for the GST ghost strike. -/
theorem missing_Hodge_class_produces_positive_canonical_ghost
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hGeometricPairing :
      ∀ (i : ι) (x : V),
        P.detectors i x = (Q x) (P.cycleClass (P.cycles i)))
    (hPositive : ∀ v : V, v ≠ 0 → 0 < (Q v) v)
    (alpha : V)
    (hmissing : alpha ∉ LinearMap.range P.cycleClass) :
    0 < canonicalResidualGhost P Q alpha alpha := by
  rw [canonicalGhost_detection_equals_residual_norm
    P Q hGeometricPairing alpha]
  exact nonalgebraic_primitive_forces_positive_residual_energy
    P Q hPositive alpha hmissing

#check canonicalResidualGhost
#check canonicalGhost_annihilates_every_native_generator
#check canonicalGhost_detection_equals_residual_norm
#check canonicalGhost_annihilates_entire_native_cycleClass_image
#check missing_Hodge_class_produces_positive_canonical_ghost
#print axioms missing_Hodge_class_produces_positive_canonical_ghost

end GSTCanonicalPolarizedHodgeGhost
