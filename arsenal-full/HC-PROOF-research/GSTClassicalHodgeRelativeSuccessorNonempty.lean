import GSTClassicalHodgeSeparatorRelativeCoheightOne

/-!
# GST CLASSICAL HODGE — NONEMPTY RELATIVE SUCCESSOR LOCUS

The projective-separator construction has now produced a genuine point of the
relative principal cut whose relative coheight is exactly one.  This file
feeds that explicit point into the finite successor locus used by the native
principal-cut operator.

Thus, at every projectively live source, the relative codimension-one successor
finset is not merely finite: it is provably nonempty.

No Hodge data or cycle-class map occurs.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgeHeightOneProjectiveRelevance
open GSTClassicalHodgeSeparatorRelativeCutLanding
open GSTClassicalHodgeSeparatorRelativeCoheightOne
open GSTClassicalHodgeSeparatorPointClosureLift

namespace GSTClassicalHodgeRelativeSuccessorNonempty

/-- The explicitly constructed separator successor belongs to the finite
relative codimension-one successor finset. -/
theorem relativeHeightOneSeparatorSuccessor_mem_finset
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)) :
    relativeHeightOneSeparatorSuccessor V x hlive ∈
      relativeCodimensionOneFinset V x := by
  classical
  unfold relativeCodimensionOneFinset
  simp only [Finset.mem_map]
  let s : Set (pointClosureScheme V x) :=
    {y ∈ relativeCutSet V x | Order.coheight y = 1}
  let y : pointClosureScheme V x := pointClosureSeparatorSuccessor V x hlive
  have hyS : y ∈ s := by
    exact ⟨pointClosureSeparatorSuccessor_mem_relativeCut V x hlive,
      pointClosureSeparatorSuccessor_coheight_one V x hlive⟩
  have hyFin : y ∈ (finite_relative_coheight_one V x).toFinset := by
    exact (Set.Finite.mem_toFinset (finite_relative_coheight_one V x)).2 hyS
  refine ⟨⟨y, hyFin⟩, ?_, ?_⟩
  · exact Finset.mem_attach _ _
  · apply Subtype.ext
    rfl

/-- **RELATIVE SUCCESSOR NONEMPTINESS.**
A projectively live source has at least one genuine relative coheight-one
successor in its source-specific principal cut. -/
theorem relativeCodimensionOneFinset_nonempty
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)) :
    (relativeCodimensionOneFinset V x).Nonempty := by
  exact ⟨relativeHeightOneSeparatorSuccessor V x hlive,
    relativeHeightOneSeparatorSuccessor_mem_finset V x hlive⟩

/-- Cardinality form: the relative successor locus has positive size. -/
theorem relativeCodimensionOneFinset_card_pos
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)) :
    0 < (relativeCodimensionOneFinset V x).card :=
  Finset.card_pos.mpr (relativeCodimensionOneFinset_nonempty V x hlive)

#check relativeHeightOneSeparatorSuccessor_mem_finset
#check relativeCodimensionOneFinset_nonempty
#check relativeCodimensionOneFinset_card_pos

#print axioms relativeHeightOneSeparatorSuccessor_mem_finset
#print axioms relativeCodimensionOneFinset_nonempty
#print axioms relativeCodimensionOneFinset_card_pos

end GSTClassicalHodgeRelativeSuccessorNonempty
