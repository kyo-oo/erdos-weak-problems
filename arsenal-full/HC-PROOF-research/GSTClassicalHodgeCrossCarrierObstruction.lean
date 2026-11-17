import GSTClassicalHodgeCrossCarrierGeometricTransfer

/-!
# GST algebraic-range conservation and geometric obstruction

A genuine correspondence between distinct algebraic carriers preserves the
ALREADY ALGEBRAIC subspace under its Betti action.

Theorems in this file establish:
* cross-carrier preservation of the cycle-class range;
* cross-carrier and composite transport of the cycle-class kernel;
* nonzero detector exclusion for arbitrary chains of genuine transfers;
* the precise obstruction to a rank-one "ghost-killing" operator.

In particular, merely passing a class through an auxiliary surface, a CM
abelian variety, or an abelian cover does not create a non-algebraic Hodge
class.  An actual algebraic-cycle source plus a genuine correspondence
forces the output to be algebraic.

This is a new constraint on GST geometric-program construction rather than a
surjectivity assumption.

NEEDS CI RUN LATER.  No Lean compilation is performed in this session.
-/

set_option maxHeartbeats 10000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCrossCarrierGeometricTransfer

namespace GSTClassicalHodgeCrossCarrierObstruction

variable {V W U : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {J : HodgeBigradedBettiData W}
variable {K : HodgeBigradedBettiData U}
variable {p q r : Nat}

namespace CrossCarrierTransfer

/-- The transfer preserves the kernel of the cycle-class map, a necessary
precondition for descending to algebraic cycle classes modulo homology. -/
theorem maps_cycleClass_kernel
    (R : CrossCarrierTransfer V W H J p q)
    (Z : codimensionCycles V.X p)
    (hZ : H.cycleClass p Z = 0) :
    J.cycleClass q (R.native Z) = 0 := by
  rw [R.naturality Z, hZ]
  exact map_zero R.betti

/-- Cohomological images of ALL rational algebraic cycles on the source
remain algebraic on the target.  The statement is a subspace containment,
not a claim of full Hodge surjectivity. -/
theorem maps_algebraicRange
    (R : CrossCarrierTransfer V W H J p q) :
    Submodule.map R.betti (LinearMap.range (H.cycleClass p)) ≤
      LinearMap.range (J.cycleClass q) := by
  intro y hy
  rcases hy with ⟨x, hx, hxy⟩
  rcases hx with ⟨Z, hZ⟩
  subst x
  subst y
  exact R.native_range_preserved Z

/-- Every rational linear detector annihilating target algebraic classes
also annihilates all images of source algebraic classes under any actual
cross-carrier transfer.  The detector can detect a ghost only OUTSIDE the
geometric image. -/
theorem algebraic_detector_kills_transport
    (R : CrossCarrierTransfer V W H J p q)
    (detector :
      RationalSingularCohomology J.analytification (2 * q) →ₗ[ℚ] ℚ)
    (hkill : ∀ Z : codimensionCycles W.X q,
       detector (J.cycleClass q Z) = 0)
    (Z : codimensionCycles V.X p) :
    detector (R.betti (H.cycleClass p Z)) = 0 := by
  rw [← R.naturality Z]
  exact hkill (R.native Z)

/-- An independent cohomological detector forbids the claimed normalization
of an algebraic source into a nonalgebraic target, unless the target detector
itself vanishes.  This prevents making the Hodge conjecture true by declaring
a rank-one projection to be "geometric." -/
theorem nonzero_detector_forbids_period_hit
    (R : CrossCarrierTransfer V W H J p q)
    (detector :
      RationalSingularCohomology J.analytification (2 * q) →ₗ[ℚ] ℚ)
    (hkill : ∀ Z : codimensionCycles W.X q,
       detector (J.cycleClass q Z) = 0)
    (Z : codimensionCycles V.X p)
    (target : RationalSingularCohomology J.analytification (2 * q))
    (k : ℚ) (hk : k ≠ 0)
    (htarget : detector target ≠ 0)
    (hperiod : R.betti (H.cycleClass p Z) = k • target) : False := by
  have hz := R.algebraic_detector_kills_transport detector hkill Z
  rw [hperiod, map_smul] at hz
  have hprod : k * detector target = 0 := by
    simpa [smul_eq_mul] using hz
  exact (mul_ne_zero hk htarget) hprod

/-- Composition does not evade the algebraic-image constraint. -/
theorem detector_kills_composed_transport
    (R : CrossCarrierTransfer V W H J p q)
    (S : CrossCarrierTransfer W U J K q r)
    (detector :
      RationalSingularCohomology K.analytification (2 * r) →ₗ[ℚ] ℚ)
    (hkill : ∀ Z : codimensionCycles U.X r,
       detector (K.cycleClass r Z) = 0)
    (Z : codimensionCycles V.X p) :
    detector
      (S.betti (R.betti (H.cycleClass p Z))) = 0 := by
  exact (S.compose R).algebraic_detector_kills_transport
    detector hkill Z

/-- The same contradiction applies to any two-step geometry program.
An intermediate Kuga--Satake or Gale carrier cannot hide non-algebraic
output by a composition of commuting squares. -/
theorem nonzero_detector_forbids_composed_period_hit
    (R : CrossCarrierTransfer V W H J p q)
    (S : CrossCarrierTransfer W U J K q r)
    (detector :
      RationalSingularCohomology K.analytification (2 * r) →ₗ[ℚ] ℚ)
    (hkill : ∀ Z : codimensionCycles U.X r,
       detector (K.cycleClass r Z) = 0)
    (Z : codimensionCycles V.X p)
    (target : RationalSingularCohomology K.analytification (2 * r))
    (k : ℚ) (hk : k ≠ 0)
    (htarget : detector target ≠ 0)
    (hperiod :
      S.betti (R.betti (H.cycleClass p Z)) = k • target) : False := by
  exact (S.compose R).nonzero_detector_forbids_period_hit
    detector hkill Z target k hk htarget hperiod

/-- An exact nonzero period on an algebraic source forbids any separating
functional at the target, even without a chosen Hodge-basis coordinate. -/
theorem period_hit_forces_detector_zero
    (R : CrossCarrierTransfer V W H J p q)
    (detector :
      RationalSingularCohomology J.analytification (2 * q) →ₗ[ℚ] ℚ)
    (hkill : ∀ Z : codimensionCycles W.X q,
      detector (J.cycleClass q Z) = 0)
    (Z : codimensionCycles V.X p)
    (target : RationalSingularCohomology J.analytification (2 * q))
    (k : ℚ) (hk : k ≠ 0)
    (hperiod : R.betti (H.cycleClass p Z) = k • target) :
    detector target = 0 := by
  by_contra hnonzero
  exact R.nonzero_detector_forbids_period_hit
    detector hkill Z target k hk hnonzero hperiod

end CrossCarrierTransfer

#check CrossCarrierTransfer.maps_cycleClass_kernel
#check CrossCarrierTransfer.maps_algebraicRange
#check CrossCarrierTransfer.nonzero_detector_forbids_period_hit
#check CrossCarrierTransfer.detector_kills_composed_transport
#print axioms CrossCarrierTransfer.nonzero_detector_forbids_composed_period_hit

end GSTClassicalHodgeCrossCarrierObstruction
