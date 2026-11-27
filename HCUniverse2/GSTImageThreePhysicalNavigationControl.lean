import HCUniverse2.GSTPerfectPowerTailNavigation
import HCUniverse2.GSTImageThreeCurvatureResonance
import Mathlib

/-!
# Original GST Navigation controls the CM source without half-curvature artifacts

The owner's genuine predicate Navigation : Nat -> Prop is converted
into its already-constructed exact 0/1 rational navigationCharge.
This file connects THAT original physical arithmetic gate to the
original U/J/M/[J,M] source curvature family, rather than pretending
a freely chosen rational b was itself an original physical constant.

The half-strength resonance b=1/2 is a mathematically meaningful
interpolation obstruction but is NEVER a physical charge value.
Therefore every ACTUAL original navigation state retains the full
TWO-CELL independent native CM source, at any rational direct M strength.
This is NOT a claim of 12-state cyclicity at navigation-off inputs:
other ten-cell and cross-spectrum obstructions remain possible.
-/

set_option maxHeartbeats 3000000
noncomputable section

namespace GSTImageThreePhysicalNavigationControl

open GSTPerfectPowerTailNavigation
open GSTCanonicalTailStateIso
open GSTImageThreeCurvatureResonance
open GSTGraphV2CMWaveFusion

/-- Exact physical GST source; the SAME original navigation truth value
controls original source curvature, without a new spatial dimension. -/
def physicalCurvatureFold (R : Nat) (a : ℚ) (u : WaveSignal) :
    WaveSignal :=
  curvatureFold a (navigationCharge R) u

/-- The genuine physical navigation charge is a Boolean rational gate,
not a continuum of arbitrary rational source strengths. -/
theorem physicalNavigationCharge_binary (R : Nat) :
    navigationCharge R = 0 ∨ navigationCharge R = 1 := by
  by_cases h : Navigation R
  · exact Or.inr ((navigationCharge_eq_one_iff R).2 h)
  · exact Or.inl ((navigationCharge_eq_zero_iff R).2 h)

/-- Original physical navigation can NEVER be the unique permanent
half-curvature resonance strength in the source-parameter extension. -/
theorem physicalNavigationCharge_ne_half (R : Nat) :
    navigationCharge R ≠ (1/2 : ℚ) := by
  rcases physicalNavigationCharge_binary R with h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num

/-- All ORIGINAL physical navigation states preserve exact
two-cell source controllability, for EVERY rational direct strength. -/
theorem physicalCurvature_two_step_det_nonzero (R : Nat) (a : ℚ) :
    seed nullCell * physicalCurvatureFold R a seed maximumCell -
      seed maximumCell * physicalCurvatureFold R a seed nullCell ≠ 0 := by
  exact fixedPair_independent_off_resonance
    a (navigationCharge R) (physicalNavigationCharge_ne_half R)

/-- Every requested original null/max information pair is synthesized
by the actual physical GST source and first fold, WITHOUT any restriction
on input arithmetic state R and WITHOUT assuming a Hodge cycle selector. -/
theorem physicalCurvature_two_step_reconstruct
    (R : Nat) (a x y : ℚ) :
    ∃ s t : ℚ,
      s * seed nullCell + t * physicalCurvatureFold R a seed nullCell = x ∧
      s * seed maximumCell + t * physicalCurvatureFold R a seed maximumCell = y := by
  exact fixedPair_two_step_reconstruct
    a (navigationCharge R) x y (physicalNavigationCharge_ne_half R)

/-- The exact original canonical perfect-power tail equivalence
commutes with the entire physical rational CM source F. -/
theorem physicalCurvature_canonicalTail
    (s b : Nat) (hs : 1 ≤ s) (a : ℚ) (u : WaveSignal) :
    physicalCurvatureFold (4^(3^s*b)) a u =
      physicalCurvatureFold (canonicalTail s b) a u := by
  simp only [physicalCurvatureFold, navigationCharge_canonicalTail s b hs]

/-- Actual navigation-on state uses unit curvature in the original
CM source, independently of the direct SURVIVE strength a. -/
theorem physicalCurvature_active (R : Nat) (h : Navigation R)
    (a : ℚ) (u : WaveSignal) :
    physicalCurvatureFold R a u = curvatureFold a 1 u := by
  rw [physicalCurvatureFold, (navigationCharge_eq_one_iff R).2 h]

/-- Actual navigation-off state uses zero CM curvature, not half
curvature, so the fixed two-cell source does not resonate. -/
theorem physicalCurvature_inactive (R : Nat) (h : ¬ Navigation R)
    (a : ℚ) (u : WaveSignal) :
    physicalCurvatureFold R a u = curvatureFold a 0 u := by
  rw [physicalCurvatureFold, (navigationCharge_eq_zero_iff R).2 h]

#check physicalNavigationCharge_binary
#check physicalNavigationCharge_ne_half
#check physicalCurvature_two_step_det_nonzero
#check physicalCurvature_two_step_reconstruct
#check physicalCurvature_canonicalTail
#check physicalCurvature_active
#check physicalCurvature_inactive
#print axioms physicalCurvature_two_step_reconstruct
#print axioms physicalCurvature_canonicalTail

end GSTImageThreePhysicalNavigationControl
