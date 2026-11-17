import GSTClassicalHodgeProjectiveSeparatorSuccessorPoint
import GSTClassicalHodgePointClosurePrincipalCut

/-!
# GST CLASSICAL HODGE — PROJECTIVE SEPARATOR CARRIER DESCENT

The previous layer constructs an actual height-one successor point in the
ambient projective space.  This file proves that successor remains on the
embedded smooth-projective carrier.

The argument is purely topological/algebraic:

* source-prime containment puts the successor in the Zariski closure of the
  source projective point;
* the image of the carrier's closed projective immersion is closed and contains
  the source;
* hence it contains the whole source closure and therefore the successor.

Consequently the projective successor descends to a genuine point of `V.X`.
It is distinct from the source and lies on the source-specific principal
section.  No Hodge data or cycle-class map occurs.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

open TopologicalSpace
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTClassicalHodgeProjectivePrincipalSection
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgeHeightOneProjectiveRelevance
open GSTClassicalHodgeProjectiveSeparatorSuccessorPoint

namespace GSTClassicalHodgeProjectiveSeparatorCarrierDescent

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Prime containment places the projective successor in the closure of the
source projective point. -/
theorem separatorSuccessorPoint_mem_source_closure
    (n : Nat) (x : projectiveSpace n)
    (hlive : ProjectivelyLiveSource n x) :
    separatorSuccessorPoint n x hlive ∈ closure ({x} : Set (projectiveSpace n)) :=
  (ProjectiveSpectrum.le_iff_mem_closure (ProjectiveGrading n) x
    (separatorSuccessorPoint n x hlive)).mp
    ((ProjectiveSpectrum.as_ideal_le_as_ideal (ProjectiveGrading n) x
      (separatorSuccessorPoint n x hlive)).mp
      (source_le_separatorSuccessorPoint n x hlive))

/-- For a source point of the embedded carrier, its projective successor lies
in the closed image of the carrier. -/
theorem separatorSuccessorPoint_mem_carrierRange
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)) :
    separatorSuccessorPoint V.projective.n (V.projective.immersion x) hlive ∈
      Set.range V.projective.immersion := by
  let s := V.projective.immersion x
  let y := separatorSuccessorPoint V.projective.n s hlive
  have hycl : y ∈ closure ({s} : Set (projectiveSpace V.projective.n)) :=
    separatorSuccessorPoint_mem_source_closure V.projective.n s hlive
  have hclosed : IsClosed (Set.range V.projective.immersion) :=
    V.projective.closedImmersion.isClosedEmbedding.isClosed_range
  have hsrange : ({s} : Set (projectiveSpace V.projective.n)) ⊆
      Set.range V.projective.immersion := by
    intro z hz
    have hzx : z = V.projective.immersion x := by simpa [s] using hz
    exact ⟨x, hzx.symm⟩
  exact (closure_minimal hsrange hclosed) hycl

/-- Genuine carrier point underlying the projective separator successor. -/
noncomputable def carrierSeparatorSuccessor
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)) : V.X :=
  Classical.choose
    (separatorSuccessorPoint_mem_carrierRange V x hlive)

/-- The projective image of the descended carrier point is exactly the
constructed projective successor. -/
theorem carrierSeparatorSuccessor_image
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)) :
    V.projective.immersion (carrierSeparatorSuccessor V x hlive) =
      separatorSuccessorPoint V.projective.n (V.projective.immersion x) hlive :=
  Classical.choose_spec
    (separatorSuccessorPoint_mem_carrierRange V x hlive)

/-- The descended successor is genuinely distinct from the source. -/
theorem carrierSeparatorSuccessor_ne_source
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)) :
    carrierSeparatorSuccessor V x hlive ≠ x := by
  intro h
  have himg := congrArg V.projective.immersion h
  rw [carrierSeparatorSuccessor_image] at himg
  exact separatorSuccessorPoint_ne_source
    V.projective.n (V.projective.immersion x) hlive himg

/-- The chosen separator equation vanishes at the descended successor. -/
theorem separator_mem_carrierSuccessor_prime
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)) :
    (positiveHomogeneousSeparator V.projective.n
      (V.projective.immersion x)).equation ∈
      (V.projective.immersion (carrierSeparatorSuccessor V x hlive)).asHomogeneousIdeal := by
  rw [carrierSeparatorSuccessor_image]
  exact separator_mem_separatorAmbientPrime
    V.projective.n (V.projective.immersion x)

/-- Therefore the descended successor lies in the support of the actual
principal section on the carrier. -/
theorem carrierSeparatorSuccessor_mem_principalSection
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)) :
    carrierSeparatorSuccessor V x hlive ∈
      (principalSectionIdeal V
        (positiveHomogeneousSeparator V.projective.n
          (V.projective.immersion x)).equation).support := by
  rw [mem_principalSection_support_iff]
  exact separator_mem_carrierSuccessor_prime V x hlive

/-- Carrier descent crown. -/
theorem projective_separator_carrier_descent_crown
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)) :
    carrierSeparatorSuccessor V x hlive ≠ x
      ∧ carrierSeparatorSuccessor V x hlive ∈
        (principalSectionIdeal V
          (positiveHomogeneousSeparator V.projective.n
            (V.projective.immersion x)).equation).support := by
  exact ⟨carrierSeparatorSuccessor_ne_source V x hlive,
    carrierSeparatorSuccessor_mem_principalSection V x hlive⟩

#check separatorSuccessorPoint_mem_source_closure
#check separatorSuccessorPoint_mem_carrierRange
#check carrierSeparatorSuccessor
#check carrierSeparatorSuccessor_image
#check carrierSeparatorSuccessor_ne_source
#check carrierSeparatorSuccessor_mem_principalSection
#check projective_separator_carrier_descent_crown

#print axioms separatorSuccessorPoint_mem_source_closure
#print axioms carrierSeparatorSuccessor_image
#print axioms projective_separator_carrier_descent_crown

end GSTClassicalHodgeProjectiveSeparatorCarrierDescent
