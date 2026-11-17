import GSTClassicalHodgeProjectiveSeparatorCarrierDescent
import GSTClassicalHodgePointClosureIrreducible

/-!
# GST CLASSICAL HODGE — SEPARATOR SUCCESSOR LIFT TO THE SOURCE CLOSURE

The ambient projective separator successor has already been descended to a
genuine point of the smooth-projective carrier.  This file places that point
inside the reduced closure of its source.

Because the projective immersion is a closed embedding, its embedding topology
reflects singleton closures.  The projective successor lies in the closure of
the projective source, hence its descended carrier point lies in the closure of
the carrier source.  The established homeomorphism between the reduced
point-closure scheme and `closure {x}` then gives a canonical point of
`pointClosureScheme V x`.

No Hodge datum occurs.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

open TopologicalSpace
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgePointClosureIrreducible
open GSTClassicalHodgeHeightOneProjectiveRelevance
open GSTClassicalHodgeProjectiveSeparatorSuccessorPoint
open GSTClassicalHodgeProjectiveSeparatorCarrierDescent

namespace GSTClassicalHodgeSeparatorPointClosureLift

/-- The descended separator successor belongs to the singleton closure of its
source inside the actual carrier. -/
theorem carrierSeparatorSuccessor_mem_sourceClosure
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)) :
    carrierSeparatorSuccessor V x hlive ∈ closure ({x} : Set V.X) := by
  haveI : IsClosedImmersion (V.projective.immersion) := V.projective.closedImmersion
  let f := V.projective.immersion
  let y := carrierSeparatorSuccessor V x hlive
  have hyImage : f y ∈ closure ({f x} : Set (projectiveSpace V.projective.n)) := by
    rw [carrierSeparatorSuccessor_image V x hlive]
    exact separatorSuccessorPoint_mem_source_closure
      V.projective.n (f x) hlive
  have hclosure := f.isEmbedding.closure_eq_preimage_closure_image ({x} : Set V.X)
  have himageSingleton : f '' ({x} : Set V.X) = ({f x} : Set (projectiveSpace V.projective.n)) := by
    simp
  rw [himageSingleton] at hclosure
  have : y ∈ f ⁻¹' closure ({f x} : Set (projectiveSpace V.projective.n)) := hyImage
  rwa [← hclosure] at this

/-- The successor packaged as a point of the topological singleton closure. -/
noncomputable def carrierSeparatorSuccessorInClosure
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)) :
    closure ({x} : Set V.X) :=
  ⟨carrierSeparatorSuccessor V x hlive,
    carrierSeparatorSuccessor_mem_sourceClosure V x hlive⟩

/-- Canonical point of the reduced point-closure scheme corresponding to the
separator successor. -/
noncomputable def pointClosureSeparatorSuccessor
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)) :
    pointClosureScheme V x :=
  (pointClosureHomeomorph V x).symm
    (carrierSeparatorSuccessorInClosure V x hlive)

/-- The point-closure inclusion sends the lifted successor back to the genuine
carrier separator successor. -/
@[simp]
theorem pointClosureSeparatorSuccessor_maps
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)) :
    pointClosureι V x (pointClosureSeparatorSuccessor V x hlive) =
      carrierSeparatorSuccessor V x hlive := by
  change
    ((pointClosureHomeomorph V x)
      (pointClosureSeparatorSuccessor V x hlive)).1 =
        carrierSeparatorSuccessor V x hlive
  simp [pointClosureSeparatorSuccessor,
    carrierSeparatorSuccessorInClosure]

/-- The lifted successor is not the generic source point of the closure. -/
theorem pointClosureSeparatorSuccessor_ne_generic
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)) :
    pointClosureSeparatorSuccessor V x hlive ≠ closureGenericPoint V x := by
  intro h
  have hmap := congrArg (pointClosureι V x) h
  rw [pointClosureSeparatorSuccessor_maps,
    closureGenericPoint_maps_to_source] at hmap
  exact carrierSeparatorSuccessor_ne_source V x hlive hmap

/-- Point-closure lift crown. -/
theorem separator_pointClosure_lift_crown
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)) :
    pointClosureι V x (pointClosureSeparatorSuccessor V x hlive) =
        carrierSeparatorSuccessor V x hlive
      ∧ pointClosureSeparatorSuccessor V x hlive ≠ closureGenericPoint V x := by
  exact ⟨pointClosureSeparatorSuccessor_maps V x hlive,
    pointClosureSeparatorSuccessor_ne_generic V x hlive⟩

#check carrierSeparatorSuccessor_mem_sourceClosure
#check carrierSeparatorSuccessorInClosure
#check pointClosureSeparatorSuccessor
#check pointClosureSeparatorSuccessor_maps
#check pointClosureSeparatorSuccessor_ne_generic
#check separator_pointClosure_lift_crown

#print axioms carrierSeparatorSuccessor_mem_sourceClosure
#print axioms pointClosureSeparatorSuccessor_maps
#print axioms separator_pointClosure_lift_crown

end GSTClassicalHodgeSeparatorPointClosureLift
