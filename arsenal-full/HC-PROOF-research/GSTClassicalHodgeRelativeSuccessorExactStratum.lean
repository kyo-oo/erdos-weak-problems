import GSTClassicalHodgeRelativeSuccessorLowerBound
import GSTClassicalHodgeNativeCycleCosmicShadow

/-!
# GST CLASSICAL HODGE — RELATIVE SUCCESSOR EXACT STRATUM

The principal-cut successor operator is already constructed geometrically, but
its finite presentation retains only those relative coheight-one successors
whose ambient coheight is exactly one larger than the source.

This file isolates the precise pure-geometric statement that makes that filter
redundant.  No Hodge class, Hodge basis, or cycle-class surjectivity occurs.

For a codimension-p source x, `RelativeSuccessorAmbientExact V p x` says that
every relative coheight-one point selected by the actual principal cut lands in
ambient coheight p+1.  Under this law:

* every selected successor contributes its unit atom rather than zero;
* the canonical native successor mass is exactly the cardinality of the
  relative successor finset;
* nonemptiness of the relative height-one cut therefore forces a genuinely
  nonzero native successor cycle.

Thus the remaining geometric frontier separates cleanly into two classical
scheme statements: ambient codimension additivity and nonemptiness in live
positive dimension.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeNativeCycleCosmicShadow

namespace GSTClassicalHodgeRelativeSuccessorExactStratum

/-- Every relative coheight-one successor selected by the source-specific
principal cut lands in the exact next ambient codimension stratum. -/
def RelativeSuccessorAmbientExact
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) : Prop :=
  ∀ y : {y : pointClosureScheme V x.1 // Order.coheight y = 1},
    y ∈ relativeCodimensionOneFinset V x.1 →
      Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1

/-- Under exact ambient grading, every selected relative successor contributes
its unit point atom to the successor presentation. -/
theorem selected_successorAtomPresentation_eq_single
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hExact : RelativeSuccessorAmbientExact V p x)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
    (hy : y ∈ relativeCodimensionOneFinset V x.1) :
    successorAtomPresentation V p x y =
      Finsupp.single
        (⟨ambientSuccessorPoint V x.1 y, hExact y hy⟩ :
          CodimensionPoint V.X (p + 1)) 1 := by
  exact successorAtomPresentation_eq_single V p x y (hExact y hy)

/-- Exact-stratum geometry turns the native successor mass into the literal
number of relative height-one successors.  No cancellation is possible:
every selected component enters with coefficient one. -/
theorem successorMass_eq_relativeCard
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hExact : RelativeSuccessorAmbientExact V p x) :
    successorMass V p x =
      (relativeCodimensionOneFinset V x.1).card := by
  classical
  unfold successorMass successorPresentation
  rw [map_sum]
  calc
    ∑ y ∈ relativeCodimensionOneFinset V x.1,
        presentationMass (successorAtomPresentation V p x y) =
      ∑ y ∈ relativeCodimensionOneFinset V x.1, (1 : ℚ) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [selected_successorAtomPresentation_eq_single V p x hExact y hy]
        simp
    _ = (relativeCodimensionOneFinset V x.1).card := by simp

/-- A nonempty exact relative successor locus has strictly nonzero canonical
native mass. -/
theorem successorMass_ne_zero_of_nonempty
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hExact : RelativeSuccessorAmbientExact V p x)
    (hNonempty : (relativeCodimensionOneFinset V x.1).Nonempty) :
    successorMass V p x ≠ 0 := by
  rw [successorMass_eq_relativeCard V p x hExact]
  exact_mod_cast (Finset.card_pos.mpr hNonempty).ne'

/-- The geometry-built successor of a point atom is itself a nonzero native
codimension-(p+1) cycle whenever the exact relative cut is nonempty. -/
theorem successorNativeOperator_point_ne_zero
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hExact : RelativeSuccessorAmbientExact V p x)
    (hNonempty : (relativeCodimensionOneFinset V x.1).Nonempty) :
    successorNativeOperator V p (codimensionPointCycle V.X p x) ≠ 0 := by
  intro hzero
  have hmass := congrArg
    (nativeCycleMass V (p + 1)) hzero
  rw [nativeCycleMass_successor_point] at hmass
  simp only [LinearMap.map_zero] at hmass
  exact successorMass_ne_zero_of_nonempty V p x hExact hNonempty hmass

/-- Bundled exact-successor crown: once ambient codimension additivity and
nonemptiness are established by pure scheme geometry, the principal-cut
operator has an honest nonzero next-stratum point image. -/
theorem relative_successor_exact_stratum_crown
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hExact : RelativeSuccessorAmbientExact V p x)
    (hNonempty : (relativeCodimensionOneFinset V x.1).Nonempty) :
    successorMass V p x =
        (relativeCodimensionOneFinset V x.1).card
      ∧ successorMass V p x ≠ 0
      ∧ successorNativeOperator V p
          (codimensionPointCycle V.X p x) ≠ 0 := by
  exact ⟨successorMass_eq_relativeCard V p x hExact,
    successorMass_ne_zero_of_nonempty V p x hExact hNonempty,
    successorNativeOperator_point_ne_zero V p x hExact hNonempty⟩

#check RelativeSuccessorAmbientExact
#check selected_successorAtomPresentation_eq_single
#check successorMass_eq_relativeCard
#check successorMass_ne_zero_of_nonempty
#check successorNativeOperator_point_ne_zero
#check relative_successor_exact_stratum_crown

#print axioms successorMass_eq_relativeCard
#print axioms successorNativeOperator_point_ne_zero
#print axioms relative_successor_exact_stratum_crown

end GSTClassicalHodgeRelativeSuccessorExactStratum
