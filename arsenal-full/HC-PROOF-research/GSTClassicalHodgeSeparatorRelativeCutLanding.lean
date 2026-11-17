import GSTClassicalHodgeSeparatorPointClosureLift
import GSTClassicalHodgePointClosureRelativeCut

/-!
# GST CLASSICAL HODGE — SEPARATOR SUCCESSOR LANDS IN THE RELATIVE CUT

The separator successor has been constructed in projective space, descended to
the actual smooth-projective carrier, and lifted to the reduced closure of its
source.  This file proves that the lifted point lies in the actual
scheme-theoretic relative principal cut.

The key identity is Mathlib's pullback range formula: the range of the first
projection of a scheme pullback is the preimage of the range of the second
morphism.  Since the descended successor lies in the principal-section
support, hence in the range of the principal-section closed immersion, its
point-closure lift lies in the range of the pullback projection.

No Hodge data occurs.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory Limits
open TopologicalSpace
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTClassicalHodgeProjectivePrincipalSection
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgePointClosureIrreducible
open GSTClassicalHodgeHeightOneProjectiveRelevance
open GSTClassicalHodgeProjectiveSeparatorCarrierDescent
open GSTClassicalHodgeSeparatorPointClosureLift

namespace GSTClassicalHodgeSeparatorRelativeCutLanding

/-- The descended successor belongs to the range of the actual principal
section closed immersion. -/
theorem carrierSeparatorSuccessor_mem_principalSectionRange
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)) :
    carrierSeparatorSuccessor V x hlive ∈ Set.range (principalSectionAtι V x) :=
  (Scheme.IdealSheafData.range_subschemeι
    (principalSectionIdeal V
      (positiveHomogeneousSeparator V.projective.n
        (V.projective.immersion x)).equation)).symm.subset
    (carrierSeparatorSuccessor_mem_principalSection V x hlive)

/-- **GENUINE RELATIVE-CUT LANDING.**
The point-closure lift of the separator successor lies in the actual
scheme-theoretic relative principal cut. -/
theorem pointClosureSeparatorSuccessor_mem_relativeCut
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)) :
    pointClosureSeparatorSuccessor V x hlive ∈ relativeCutSet V x := by
  rw [relativeCutSet]
  rw [show Set.range (closurePrincipalCutToClosure V x) =
      (pointClosureι V x) ⁻¹' Set.range (principalSectionAtι V x) from
    Scheme.Pullback.range_fst (pointClosureι V x) (principalSectionAtι V x)]
  rw [Set.mem_preimage, pointClosureSeparatorSuccessor_maps]
  exact carrierSeparatorSuccessor_mem_principalSectionRange V x hlive

/-- The landed relative-cut point is non-generic. -/
theorem pointClosureSeparatorSuccessor_relativeCut_ne_generic
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)) :
    pointClosureSeparatorSuccessor V x hlive ∈ relativeCutSet V x
      ∧ pointClosureSeparatorSuccessor V x hlive ≠ closureGenericPoint V x := by
  exact ⟨pointClosureSeparatorSuccessor_mem_relativeCut V x hlive,
    pointClosureSeparatorSuccessor_ne_generic V x hlive⟩

#check carrierSeparatorSuccessor_mem_principalSectionRange
#check pointClosureSeparatorSuccessor_mem_relativeCut
#check pointClosureSeparatorSuccessor_relativeCut_ne_generic

#print axioms pointClosureSeparatorSuccessor_mem_relativeCut
#print axioms pointClosureSeparatorSuccessor_relativeCut_ne_generic

end GSTClassicalHodgeSeparatorRelativeCutLanding
