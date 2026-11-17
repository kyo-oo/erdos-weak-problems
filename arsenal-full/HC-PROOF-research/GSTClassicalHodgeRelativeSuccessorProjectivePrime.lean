import GSTClassicalHodgeProjectiveSeparatorHeightOne
import GSTClassicalHodgeRelativeSuccessorLowerBound

/-!
# GST CLASSICAL HODGE — PROJECTIVE PRIME DATA OF RELATIVE SUCCESSORS

The recursive principal-cut engine selects relative codimension-one points in
`closure {x}`.  This file records the projective-prime data carried by those
points.

For every selected successor:

* its ambient image still lies in the closure of the source point;
* after applying the actual projective embedding, it lies in the closure of
  the source projective point;
* hence the source homogeneous prime is contained in the successor
  homogeneous prime;
* the generator-specific separator is absent from the source prime and present
  in the successor prime.

Thus every relative successor lives in the genuine one-equation prime interval
cut out by the separator.  No Hodge data and no cycle-class map occur here.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace
open GSTProjectiveOverC
open GSTClassicalHodgeProjectivePrincipalSection
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeRelativeSuccessorLowerBound

namespace GSTClassicalHodgeRelativeSuccessorProjectivePrime

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Membership in the finite relative-successor finset remembers that the
underlying point lies in the restricted principal cut. -/
theorem mem_relativeCodimensionOneFinset_cut
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : {y : pointClosureScheme V x // Order.coheight y = 1})
    (hy : y ∈ relativeCodimensionOneFinset V x) :
    y.1 ∈ relativeCutSet V x := by
  classical
  unfold relativeCodimensionOneFinset at hy
  rcases Finset.mem_map.mp hy with ⟨a, ha, hya⟩
  have hval : a.1 = y.1 := congrArg Subtype.val hya
  rw [← hval]
  have hmem : a.1 ∈ relativeCutSet V x := by
    have h2 : a.1 ∈ {y : pointClosureScheme V x |
        y ∈ relativeCutSet V x ∧ Order.coheight y = 1} := by
      simpa only [Set.Finite.mem_toFinset] using a.2
    exact h2.1
  exact hmem

/-- The actual projective image of every point in the reduced closure of `x`
lies in the projective closure of the image of `x`. -/
theorem projective_image_mem_source_closure
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : pointClosureScheme V x) :
    V.projective.immersion (pointClosureι V x y) ∈
      closure ({V.projective.immersion x} : Set (projectiveSpace V.projective.n)) := by
  have hy : pointClosureι V x y ∈ closure ({x} : Set V.X) :=
    pointClosure_image_mem_closure V x y
  have himage :
      V.projective.immersion (pointClosureι V x y) ∈
        V.projective.immersion '' closure ({x} : Set V.X) :=
    ⟨pointClosureι V x y, hy, rfl⟩
  have hclosed :=
    image_closure_subset_closure_image V.projective.immersion.continuous himage
  simpa using hclosed

/-- Specialization in projective space is inclusion of the corresponding
homogeneous primes. -/
theorem sourcePrime_le_successorPrime
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : pointClosureScheme V x) :
    (V.projective.immersion x).asHomogeneousIdeal ≤
      (V.projective.immersion (pointClosureι V x y)).asHomogeneousIdeal := by
  intro f hf
  let Z : Set (projectiveSpace V.projective.n) :=
    ProjectiveSpectrum.zeroLocus (ProjectiveGrading V.projective.n) ({f} : Set _)
  have hZclosed : IsClosed Z := by
    exact ProjectiveSpectrum.isClosed_zeroLocus
      (ProjectiveGrading V.projective.n) ({f} : Set _)
  have hxZ : V.projective.immersion x ∈ Z := by
    change ({f} : Set (ProjectiveCoordinateRing V.projective.n)) ⊆
      (V.projective.immersion x).asHomogeneousIdeal
    simpa using hf
  have hclosure :
      closure ({V.projective.immersion x} : Set (projectiveSpace V.projective.n)) ⊆ Z := by
    exact closure_minimal (by simpa using hxZ) hZclosed
  have hyZ : V.projective.immersion (pointClosureι V x y) ∈ Z :=
    hclosure (projective_image_mem_source_closure V x y)
  change f ∈ (V.projective.immersion (pointClosureι V x y)).asHomogeneousIdeal
  exact hyZ (Set.mem_singleton f)

/-- The selected separator is absent from the source homogeneous prime. -/
theorem separator_not_mem_sourcePrime
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    (positiveHomogeneousSeparator V.projective.n
      (V.projective.immersion x)).equation ∉
        (V.projective.immersion x).asHomogeneousIdeal := by
  exact positiveHomogeneousSeparator_not_mem _ _

/-- Every point of the restricted principal cut makes the selected separator
vanish at its ambient projective image. -/
theorem separator_mem_successorPrime_of_mem_cut
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : pointClosureScheme V x)
    (hy : y ∈ relativeCutSet V x) :
    (positiveHomogeneousSeparator V.projective.n
      (V.projective.immersion x)).equation ∈
        (V.projective.immersion (pointClosureι V x y)).asHomogeneousIdeal := by
  rcases hy with ⟨z, hz⟩
  have hrange :
      pointClosureι V x y ∈ Set.range (principalSectionAtι V x) := by
    refine ⟨closurePrincipalCutToSection V x z, ?_⟩
    have hcond := congrArg (fun f => f z) (closurePrincipalCut_condition V x)
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hz] at hcond
    exact hcond.symm
  have hsupport :
      pointClosureι V x y ∈
        (principalSectionIdeal V
          (positiveHomogeneousSeparator V.projective.n
            (V.projective.immersion x)).equation).support := by
    exact (Scheme.IdealSheafData.range_subschemeι
      (principalSectionIdeal V
        (positiveHomogeneousSeparator V.projective.n
          (V.projective.immersion x)).equation)).subset hrange
  exact (mem_principalSection_support_iff V _ _).mp hsupport

/-- The source prime is strictly contained in every cut-successor prime. -/
theorem sourcePrime_lt_successorPrime_of_mem_cut
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : pointClosureScheme V x)
    (hy : y ∈ relativeCutSet V x) :
    (V.projective.immersion x).asHomogeneousIdeal <
      (V.projective.immersion (pointClosureι V x y)).asHomogeneousIdeal := by
  refine lt_of_le_of_ne (sourcePrime_le_successorPrime V x y) ?_
  intro heq
  have hmem := separator_mem_successorPrime_of_mem_cut V x y hy
  have hnot := separator_not_mem_sourcePrime V x
  rw [← heq] at hmem
  exact hnot hmem

/-- Finset-selected relative successors carry the full projective-prime
incidence package. -/
theorem selected_successor_projective_prime_crown
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : {y : pointClosureScheme V x // Order.coheight y = 1})
    (hy : y ∈ relativeCodimensionOneFinset V x) :
    (V.projective.immersion x).asHomogeneousIdeal <
        (V.projective.immersion (pointClosureι V x y.1)).asHomogeneousIdeal
      ∧ (positiveHomogeneousSeparator V.projective.n
          (V.projective.immersion x)).equation ∉
            (V.projective.immersion x).asHomogeneousIdeal
      ∧ (positiveHomogeneousSeparator V.projective.n
          (V.projective.immersion x)).equation ∈
            (V.projective.immersion (pointClosureι V x y.1)).asHomogeneousIdeal := by
  have hycut := mem_relativeCodimensionOneFinset_cut V x y hy
  exact ⟨sourcePrime_lt_successorPrime_of_mem_cut V x y.1 hycut,
    separator_not_mem_sourcePrime V x,
    separator_mem_successorPrime_of_mem_cut V x y.1 hycut⟩

#check mem_relativeCodimensionOneFinset_cut
#check projective_image_mem_source_closure
#check sourcePrime_le_successorPrime
#check separator_not_mem_sourcePrime
#check separator_mem_successorPrime_of_mem_cut
#check sourcePrime_lt_successorPrime_of_mem_cut
#check selected_successor_projective_prime_crown

#print axioms mem_relativeCodimensionOneFinset_cut
#print axioms sourcePrime_le_successorPrime
#print axioms separator_mem_successorPrime_of_mem_cut
#print axioms sourcePrime_lt_successorPrime_of_mem_cut
#print axioms selected_successor_projective_prime_crown

end GSTClassicalHodgeRelativeSuccessorProjectivePrime
