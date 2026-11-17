import GSTClassicalHodgeRelativeSuccessorNonempty
import GSTClassicalHodgeNativeCycleCosmicShadow
import GSTClassicalHodgePointClosurePrincipalCut

/-!
# GST CLASSICAL HODGE — SINGLE EXACT SUCCESSOR SURVIVAL

The exact-stratum crown previously asked that every relative coheight-one
successor land in ambient codimension `p+1`.  That is stronger than the native
nonvanishing argument needs.

For one source atom, filter the finite relative successor locus by the actual
ambient grading test already used by `successorAtomPresentation`.  The native
successor mass is exactly the cardinality of this filtered locus: each exact
successor contributes `+1`, every inexact successor contributes `0`, and there
is no cancellation.

Consequently ONE explicitly constructed relative successor with ambient
coheight `p+1` is enough to force a nonzero successor mass and hence a nonzero
native principal-cut image.  This is the surgical interface consumed by the
separator successor: no all-successor exactness hypothesis remains.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgeHeightOneProjectiveRelevance
open GSTClassicalHodgeSeparatorRelativeCoheightOne
open GSTClassicalHodgeRelativeSuccessorNonempty

namespace GSTClassicalHodgeSingleExactSuccessorSurvival

/-- Relative successors that survive the native operator's exact ambient
codimension filter. -/
noncomputable def exactRelativeSuccessorFinset
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    Finset {y : pointClosureScheme V x.1 // Order.coheight y = 1} := by
  classical
  exact (relativeCodimensionOneFinset V x.1).filter fun y =>
    Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1

@[simp]
theorem mem_exactRelativeSuccessorFinset
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1}) :
    y ∈ exactRelativeSuccessorFinset V p x ↔
      y ∈ relativeCodimensionOneFinset V x.1 ∧
      Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1 := by
  classical
  simp [exactRelativeSuccessorFinset]

/-- Every relative successor contributes mass exactly `1` or `0` according to
whether it survives the ambient grading filter. -/
theorem presentationMass_successorAtom
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1}) :
    presentationMass (successorAtomPresentation V p x y) =
      if Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1 then 1 else 0 := by
  classical
  by_cases hy : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1
  · rw [successorAtomPresentation_eq_single V p x y hy]
    simp [hy]
  · rw [successorAtomPresentation_eq_zero V p x y hy]
    simp [hy]

/-- **EXACT-SURVIVOR COUNT FORMULA.**
The native successor mass is literally the number of exact ambient
codimension-`p+1` successors. -/
theorem successorMass_eq_exactRelativeCard
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    successorMass V p x = (exactRelativeSuccessorFinset V p x).card := by
  classical
  unfold successorMass successorPresentation
  rw [map_sum]
  simp only [presentationMass_successorAtom]
  rw [exactRelativeSuccessorFinset, Finset.card_filter]
  simp

/-- One exact relative successor is sufficient for nonzero successor mass. -/
theorem successorMass_ne_zero_of_one_exact
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
    (hyMem : y ∈ relativeCodimensionOneFinset V x.1)
    (hyExact : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1) :
    successorMass V p x ≠ 0 := by
  rw [successorMass_eq_exactRelativeCard]
  have hpos : 0 < (exactRelativeSuccessorFinset V p x).card := by
    exact Finset.card_pos.mpr ⟨y,
      (mem_exactRelativeSuccessorFinset V p x y).2 ⟨hyMem, hyExact⟩⟩
  exact_mod_cast hpos.ne'

/-- One exact successor therefore forces the geometry-built native principal
cut of the source point atom to be nonzero. -/
theorem successorNativeOperator_point_ne_zero_of_one_exact
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
    (hyMem : y ∈ relativeCodimensionOneFinset V x.1)
    (hyExact : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1) :
    successorNativeOperator V p (codimensionPointCycle V.X p x) ≠ 0 := by
  intro hzero
  have hmass := congrArg (nativeCycleMass V (p + 1)) hzero
  rw [nativeCycleMass_successor_point] at hmass
  simp only [LinearMap.map_zero] at hmass
  exact successorMass_ne_zero_of_one_exact V p x y hyMem hyExact hmass

/-- Separator specialization: after the already-proved membership theorem,
only the absolute ambient-coheight equality of the one canonical separator
successor remains. -/
theorem separator_successor_survives_of_ambient_exact
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1) :
    successorMass V p x ≠ 0 ∧
      successorNativeOperator V p (codimensionPointCycle V.X p x) ≠ 0 := by
  have hmem := relativeHeightOneSeparatorSuccessor_mem_finset V x.1 hlive
  exact ⟨
    successorMass_ne_zero_of_one_exact V p x
      (relativeHeightOneSeparatorSuccessor V x.1 hlive) hmem hExact,
    successorNativeOperator_point_ne_zero_of_one_exact V p x
      (relativeHeightOneSeparatorSuccessor V x.1 hlive) hmem hExact⟩

#check exactRelativeSuccessorFinset
#check successorMass_eq_exactRelativeCard
#check successorMass_ne_zero_of_one_exact
#check successorNativeOperator_point_ne_zero_of_one_exact
#check separator_successor_survives_of_ambient_exact

#print axioms successorMass_eq_exactRelativeCard
#print axioms successorMass_ne_zero_of_one_exact
#print axioms successorNativeOperator_point_ne_zero_of_one_exact
#print axioms separator_successor_survives_of_ambient_exact

end GSTClassicalHodgeSingleExactSuccessorSurvival
