import GSTClassicalHodgeCMNativeRationalDescent
import GSTClassicalHodgeFiberedCosmology

/-!
# Rigidity of the rational algebraic-cycle range under K/Q extension

Fix an actual projective complex variety V and its codimension-q native
cycle-class map. A rational cohomology class alpha lies in the algebraic
range if and only if, AFTER extension of rational coordinates to ANY
field K/Q, it is a finite K-linear combination of actual rational native
cycle classes. The backward direction is constructed by rational
coefficient descent, not by claiming coefficients are originally rational.

This provides a precise unconditional equivalence for CM surface proof
outputs over Qbar, and prevents a false jump from complex Hodge tensors
to rational cycles when no actual algebraic representatives have been
constructed.

NEEDS CI RUN LATER.
-/

set_option maxHeartbeats 35000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCMNativeRationalDescent

namespace GSTClassicalHodgeCMExtendedRangeRigidity

variable {K : Type*} [Field K] [Algebra ℚ K]
variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {q : Nat}

/-- Genuine finite extended-coefficient presentation of a RATIONAL Betti
class, with each summand the class of an ACTUAL rational algebraic cycle. -/
def FiniteExtendedNativePresentation
    (alpha : RationalSingularCohomology H.analytification (2 * q)) : Prop :=
  ∃ s : Finset (codimensionCycles V.X q),
  ∃ coeff : codimensionCycles V.X q → K,
    let b := Module.Free.chooseBasis ℚ
      (RationalSingularCohomology H.analytification (2 * q))
    ∀ i : Module.Free.ChooseBasisIndex ℚ
      (RationalSingularCohomology H.analytification (2 * q)),
      algebraMap ℚ K ((b.repr alpha) i) =
        ∑ Z ∈ s, coeff Z * algebraMap ℚ K
          ((b.repr (H.cycleClass q Z)) i)

/-- Algebraicity can be recognized over any coefficient extension K:
the intersection of the K-linear algebraic-cycle range with the original
rational cohomology is EXACTLY the original Q-linear algebraic range. -/
theorem finiteExtendedNativePresentation_iff_nativeRange
    (alpha : RationalSingularCohomology H.analytification (2 * q)) :
    FiniteExtendedNativePresentation (K := K) (H := H) (q := q) alpha ↔
      alpha ∈ LinearMap.range (H.cycleClass q) := by
  constructor
  · rintro ⟨s, coeff, hcoords⟩
    exact rational_native_cycle_of_extended_span (K := K)
      s (fun Z => Z) coeff alpha hcoords
  · rintro ⟨Z, hZ⟩
    classical
    refine ⟨{Z}, (fun _ => (1 : K)), ?_⟩
    intro i
    rw [← hZ]
    simp

/-- The same equivalence directly detects Hodge-type algebraicity at a
specific codimension, without adding any universal geometry premise. -/
theorem hodgeSubspace_le_extendedNative_iff
    (q : Nat) :
    (∀ alpha : RationalSingularCohomology H.analytification (2 * q),
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading q) →
      FiniteExtendedNativePresentation (K := K) (H := H) (q := q) alpha) ↔
        rationalHodgeSubspace (H.hodgeBigrading q) ≤
          LinearMap.range (H.cycleClass q) := by
  constructor
  · intro h alpha ha
    exact (finiteExtendedNativePresentation_iff_nativeRange alpha).mp
      (h alpha ha)
  · intro h alpha ha
    exact (finiteExtendedNativePresentation_iff_nativeRange alpha).mpr
      (h ha)

#check finiteExtendedNativePresentation_iff_nativeRange
#print axioms finiteExtendedNativePresentation_iff_nativeRange

end GSTClassicalHodgeCMExtendedRangeRigidity
