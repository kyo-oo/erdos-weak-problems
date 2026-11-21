import GSTImageThreeOriginalXNativeLanding
import GSTGraphV2NativeCurvatureBirth
import Mathlib

/-!
# GST Image 3 — TWO INDEPENDENT BORN NATIVE DIRECTIONS ON ORIGINAL X

This is a NEW geometrically meaningful form of the owner's existing
one-source residual detector. The verified native GST two-world wave
constructs TWO transverse missing modes, with rational dual readout
minor -4. This file proves the precise GENERAL REALIZATION RULE:

Given actual ORIGINAL-X native rational cycles Z2,Z3, and two rational
Hodge-space detectors annihilating the OLD source span, if their 2x2
detector minor is nonzero, their CANONICAL cycle classes are
independent MODULO the old subspace. No preselected Chow inverse and
no assumption that all Hodge classes already are algebraic.

The geometric births Z2,Z3 and their nonzero original-X detector
minor are EXPLICIT premises: the wave information-space minor -4
cannot automatically be substituted without a proved landing map.
-/

set_option maxHeartbeats 5000000
noncomputable section

namespace GSTImageThreeGeometricTwoSourceBirth

universe u
variable {E : Type u} [AddCommGroup E] [Module ℚ E]

/-- A two-dimensional rational detector minor certifies exactly
TWO born independent directions modulo the old GST source sector.
This result is intrinsic linear algebra, independent of any choice
of coordinates or classical model. -/
theorem two_detectors_force_independence_mod_old
    (old : Submodule ℚ E) (d₁ d₂ : E →ₗ[ℚ] ℚ)
    (z₂ z₃ : E)
    (hOld₁ : ∀ z ∈ old, d₁ z = 0)
    (hOld₂ : ∀ z ∈ old, d₂ z = 0)
    (hMinor : d₁ z₂ * d₂ z₃ - d₁ z₃ * d₂ z₂ ≠ 0)
    (a b : ℚ) (hOld : a • z₂ + b • z₃ ∈ old) :
    a = 0 ∧ b = 0 := by
  have h₁ : a * d₁ z₂ + b * d₁ z₃ = 0 := by
    simpa only [map_add, map_smul, smul_eq_mul] using
      hOld₁ _ hOld
  have h₂ : a * d₂ z₂ + b * d₂ z₃ = 0 := by
    simpa only [map_add, map_smul, smul_eq_mul] using
      hOld₂ _ hOld
  have hA : a * (d₁ z₂ * d₂ z₃ - d₁ z₃ * d₂ z₂) = 0 := by
    calc
      _ = (a * d₁ z₂ + b * d₁ z₃) * d₂ z₃ -
          (a * d₂ z₂ + b * d₂ z₃) * d₁ z₃ := by ring
      _ = 0 := by rw [h₁, h₂]; ring
  have hB : b * (d₁ z₂ * d₂ z₃ - d₁ z₃ * d₂ z₂) = 0 := by
    calc
      _ = (a * d₂ z₂ + b * d₂ z₃) * d₁ z₂ -
          (a * d₁ z₂ + b * d₁ z₃) * d₂ z₂ := by ring
      _ = 0 := by rw [h₁, h₂]; ring
  constructor
  · rcases mul_eq_zero.mp hA with ha | hzero
    · exact ha
    · exact False.elim (hMinor hzero)
  · rcases mul_eq_zero.mp hB with hb | hzero
    · exact hb
    · exact False.elim (hMinor hzero)

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Exact realization on the ORIGINAL smooth projective X:
two ACTUAL native rational algebraic cycles Z2, Z3 have canonical
Betti classes independent modulo the old sector if and only if
their TWO genuine rational detector readouts have full minor.

This is the appropriate formal geometric destination of the
native original Wave-II SURVIVE/CM two-mode source birth; the
existence of such source cycles is NOT assumed to follow from
the original symbolic 12-state information-space calculation. -/
theorem originalX_two_native_source_directions_independent
    (old : Submodule ℚ
      (RationalSingularCohomology H.analytification (2 * p)))
    (d₁ d₂ : RationalSingularCohomology H.analytification (2 * p)
      →ₗ[ℚ] ℚ)
    (Z₂ Z₃ : codimensionCycles V.X p)
    (hOld₁ : ∀ z ∈ old, d₁ z = 0)
    (hOld₂ : ∀ z ∈ old, d₂ z = 0)
    (hMinor :
      d₁ (H.cycleClass p Z₂) * d₂ (H.cycleClass p Z₃) -
      d₁ (H.cycleClass p Z₃) * d₂ (H.cycleClass p Z₂) ≠ 0)
    (a b : ℚ)
    (hOld : H.cycleClass p (a • Z₂ + b • Z₃) ∈ old) :
    a = 0 ∧ b = 0 := by
  have hClass :
      a • H.cycleClass p Z₂ + b • H.cycleClass p Z₃ ∈ old := by
    simpa only [map_add, map_smul] using hOld
  exact two_detectors_force_independence_mod_old
    old d₁ d₂ (H.cycleClass p Z₂) (H.cycleClass p Z₃)
    hOld₁ hOld₂ hMinor a b hClass

#check two_detectors_force_independence_mod_old
#check originalX_two_native_source_directions_independent
#print axioms two_detectors_force_independence_mod_old
#print axioms originalX_two_native_source_directions_independent

end GSTImageThreeGeometricTwoSourceBirth
