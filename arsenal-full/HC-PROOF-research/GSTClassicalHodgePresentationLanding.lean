import GSTClassicalHodgeCycleLanding
import GSTNativeCodimensionCyclePresentation

/-!
# GST CLASSICAL HODGE FINITE PRESENTATION LANDING

The native cycle layer now represents finite rational combinations of genuine
codimension-p scheme points directly inside Mathlib's algebraic-cycle type.
This module wires those presentations into the fibered limitless Hodge basis.

The result is a concrete sufficient bridge for the genuine Stage-2G Hodge
target: for each genuine rational `(p,p)` basis direction, give a finite
rational combination of codimension-p points whose actual supplied cycle
class equals that basis vector.

No surjectivity, Hodge conclusion, realization obligation, or custom axiom is
contained in the presentation data.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeCycleLanding
open GSTNativeCodimensionCyclePresentation

namespace GSTClassicalHodgePresentationLanding

/-- For each basis direction in one genuine rational `(p,p)` Hodge fiber,
choose an explicit finite rational combination of genuine codimension-p
scheme points and prove its actual cycle class is that basis vector. -/
structure FiberedBasisPresentationBridge
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) where
  basisPresentation :
    ClassicalHodgeBasisIndex V H p →
      FiniteCodimensionPresentation V.X p
  basisPresentation_spec :
    ∀ i : ClassicalHodgeBasisIndex V H p,
      H.cycleClass p
          (realizeFiniteCodimensionPresentation V.X p
            (basisPresentation i)) =
        (classicalHodgeBasis V H p i).1

/-- A finite-presentation bridge canonically produces the native basis-cycle
bridge required by the preceding landing layer. -/
noncomputable def FiberedBasisPresentationBridge.toBasisCycleBridge
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    (R : FiberedBasisPresentationBridge V H p) :
    FiberedBasisCycleBridge V H p where
  basisCycle i :=
    realizeFiniteCodimensionPresentation V.X p (R.basisPresentation i)
  basisCycle_spec i := R.basisPresentation_spec i

/-- Every genuine `(p,p)` class gets an actual native codimension-p cycle
from a finite-presentation bridge. -/
theorem hodge_class_has_cycle_of_finite_presentations
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    {p : Nat}
    (R : FiberedBasisPresentationBridge V H p)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  exact hodge_class_has_cycle_of_fibered_basis_bridge
    V H R.toBasisCycleBridge alpha halpha

/-- Finite native presentations for every Hodge basis direction close the
exact Stage-2G rational Hodge target. -/
theorem bigraded_hodge_of_finite_presentation_family
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (R : ∀ p : Nat, FiberedBasisPresentationBridge V H p) :
    BigradedBettiHodgeStatement V H := by
  exact bigraded_hodge_of_fibered_basis_cycle_family V H
    (fun p => (R p).toBasisCycleBridge)

/-- Expand a basis-presentation specification into the explicit finite linear
combination of the actual cycle classes of genuine codimension-p point cycles.
This is the concrete equation that remains to be established geometrically. -/
theorem basisPresentation_spec_iff_point_class_sum
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (φ : FiniteCodimensionPresentation V.X p)
    (i : ClassicalHodgeBasisIndex V H p) :
    H.cycleClass p (realizeFiniteCodimensionPresentation V.X p φ) =
        (classicalHodgeBasis V H p i).1 ↔
      φ.sum (fun x q =>
          q • H.cycleClass p (codimensionPointCycle V.X p x)) =
        (classicalHodgeBasis V H p i).1 := by
  rw [linearMap_realizeFiniteCodimensionPresentation]

/-- The full finite-presentation bridge is equivalently a family of concrete
finite point-class equations.  This removes the last abstract
`codimensionCycles` existential from the forward GST construction route. -/
theorem fiberedBasisPresentationBridge_iff_point_class_sums
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :
    Nonempty (FiberedBasisPresentationBridge V H p) ↔
      ∃ presentation :
          ClassicalHodgeBasisIndex V H p →
            FiniteCodimensionPresentation V.X p,
        ∀ i : ClassicalHodgeBasisIndex V H p,
          (presentation i).sum (fun x q =>
              q • H.cycleClass p (codimensionPointCycle V.X p x)) =
            (classicalHodgeBasis V H p i).1 := by
  constructor
  · rintro ⟨R⟩
    refine ⟨R.basisPresentation, ?_⟩
    intro i
    exact (basisPresentation_spec_iff_point_class_sum
      V H p (R.basisPresentation i) i).mp (R.basisPresentation_spec i)
  · rintro ⟨presentation, hpresentation⟩
    refine ⟨{
      basisPresentation := presentation
      basisPresentation_spec := ?_ }⟩
    intro i
    exact (basisPresentation_spec_iff_point_class_sum
      V H p (presentation i) i).mpr (hpresentation i)

/-- The concrete finite-point-class family is sufficient for the genuine
classical Hodge target in every codimension. -/
theorem bigraded_hodge_of_point_class_sum_family
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (presentation :
      ∀ p : Nat,
        ClassicalHodgeBasisIndex V H p →
          FiniteCodimensionPresentation V.X p)
    (hclass :
      ∀ p : Nat, ∀ i : ClassicalHodgeBasisIndex V H p,
        (presentation p i).sum (fun x q =>
            q • H.cycleClass p (codimensionPointCycle V.X p x)) =
          (classicalHodgeBasis V H p i).1) :
    BigradedBettiHodgeStatement V H := by
  apply bigraded_hodge_of_finite_presentation_family V H
  intro p
  exact {
    basisPresentation := presentation p
    basisPresentation_spec := fun i =>
      (basisPresentation_spec_iff_point_class_sum
        V H p (presentation p i) i).mpr (hclass p i)
  }

/-- Pair the concrete native presentation with the unconditional limitless
GST cosmic projection of the same genuine Hodge basis direction. -/
theorem finite_presentation_projects_to_limitless_cosmos
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (R : FiberedBasisPresentationBridge V H p)
    (i : ClassicalHodgeBasisIndex V H p) :
    ∃ φ : FiniteCodimensionPresentation V.X p,
      H.cycleClass p (realizeFiniteCodimensionPresentation V.X p φ) =
          (classicalHodgeBasis V H p i).1 ∧
      forgetMultiplicityToGST
          (fiberedWeightCoordinates V H p
            (classicalHodgeBasis V H p i)) =
        Finsupp.single
          (GSTUniversalAddressBridge.cosmicAddressEquiv (p, p)) 1 := by
  refine ⟨R.basisPresentation i, R.basisPresentation_spec i, ?_⟩
  exact classical_basis_projects_to_cosmic_diagonal V H p i

#check FiberedBasisPresentationBridge
#check FiberedBasisPresentationBridge.toBasisCycleBridge
#check hodge_class_has_cycle_of_finite_presentations
#check bigraded_hodge_of_finite_presentation_family
#check basisPresentation_spec_iff_point_class_sum
#check fiberedBasisPresentationBridge_iff_point_class_sums
#check bigraded_hodge_of_point_class_sum_family
#check finite_presentation_projects_to_limitless_cosmos

#print axioms hodge_class_has_cycle_of_finite_presentations
#print axioms bigraded_hodge_of_finite_presentation_family
#print axioms basisPresentation_spec_iff_point_class_sum
#print axioms fiberedBasisPresentationBridge_iff_point_class_sums
#print axioms bigraded_hodge_of_point_class_sum_family
#print axioms finite_presentation_projects_to_limitless_cosmos

end GSTClassicalHodgePresentationLanding
