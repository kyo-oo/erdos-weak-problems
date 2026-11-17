import GSTClassicalHodgeDegreeCertifiedFullCorrespondenceCompiler
import GSTClassicalHodgePiOmniverseBranchSynthesis

/-!
# GST CLASSICAL HODGE — DEGREE-CERTIFIED OMNIVERSE LIVE-BRANCH COLLAPSE

The full-correspondence weight crown asked for a source-to-target program for
every Hodge basis direction in a weight.  The handwritten Pi/omniverse
construction is strictly more local: a concrete Hodge class has finite support,
so only its live causal branches need to be materialized.

This file implements that exact proof direction.

* The source is the already-proved degree-certified algebraic GST seed.  It is
  not the unknown target class.
* For each live target coordinate j of alpha, one genuine full-correspondence
  program carries the degree-certified source to the normalized j-th basis
  sheet.
* The native target cycle of that program is therefore already available from
  the exact source compiler.
* The final native cycle is the finite rational sum

      Z_alpha = sum_{j in supp(alpha)} alpha_j Z_j.

  Linearity of the genuine cycle-class map and the basis reconstruction theorem
  give cl(Z_alpha) = alpha exactly.

No program is requested for a dead basis direction.  No global cyclicity,
finite Hodge rank, saturation, arbitrary matrix-unit externalization, or
algebraicity of alpha is assumed.  This is the native-cycle realization of the
handwritten "branch into the active GST subspaces and collapse the branches
back to one Hodge class" calculation.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeDegreeCertifiedOmniverseLiveCollapse

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgeSingleExactSuccessorSurvival
open GSTClassicalHodgeGSTDegreeCertifiedSource
open GSTClassicalHodgeDegreeCertifiedFullCorrespondenceCompiler
open GSTClassicalHodgeDegreeCertifiedFullCorrespondenceCompiler.FullCorrespondenceSourceTargetProgram
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgePiOmniverseBranchSynthesis

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Only the live branches of one concrete target Hodge state require genuine
geometric materialization. -/
abbrev LiveDegreeCertifiedProgramFamily
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1)
    (alpha : ClassicalHodgeFiber V H (p + 1)) :=
  ∀ j : ClassicalHodgeBasisIndex V H (p + 1),
    (classicalHodgeBasis V H (p + 1)).repr alpha j ≠ 0 →
      DegreeCertifiedFullCorrespondenceProgram
        G D p x hlive hExact j

/-- Native target cycle associated to one coordinate.  Dead coordinates are
sent to zero; live coordinates execute their genuine source-specific program. -/
noncomputable def liveBranchTargetCycle
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1)
    (alpha : ClassicalHodgeFiber V H (p + 1))
    (R : LiveDegreeCertifiedProgramFamily G D p x hlive hExact alpha)
    (j : ClassicalHodgeBasisIndex V H (p + 1)) :
    codimensionCycles V.X (p + 1) := by
  classical
  by_cases hj : (classicalHodgeBasis V H (p + 1)).repr alpha j ≠ 0
  · exact (R j hj).targetCycle
  · exact 0

/-- On a live branch the selected native cycle represents exactly that Hodge
basis sheet. -/
theorem liveBranchTargetCycle_spec
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1)
    (alpha : ClassicalHodgeFiber V H (p + 1))
    (R : LiveDegreeCertifiedProgramFamily G D p x hlive hExact alpha)
    (j : ClassicalHodgeBasisIndex V H (p + 1))
    (hj : (classicalHodgeBasis V H (p + 1)).repr alpha j ≠ 0) :
    H.cycleClass (p + 1)
        (liveBranchTargetCycle G D p x hlive hExact alpha R j) =
      (classicalHodgeBasis V H (p + 1) j).1 := by
  unfold liveBranchTargetCycle
  rw [dif_pos hj]
  exact (R j hj).targetCycle_spec

/-- **THE HANDWRITTEN FINITE BRANCH COLLAPSE CYCLE.**
The coefficients are exactly the genuine Hodge-basis coordinates of alpha;
only its finite support contributes. -/
noncomputable def omniverseLiveCollapseCycle
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1)
    (alpha : ClassicalHodgeFiber V H (p + 1))
    (R : LiveDegreeCertifiedProgramFamily G D p x hlive hExact alpha) :
    codimensionCycles V.X (p + 1) :=
  ∑ j ∈ ((classicalHodgeBasis V H (p + 1)).repr alpha).support,
    ((classicalHodgeBasis V H (p + 1)).repr alpha j) •
      liveBranchTargetCycle G D p x hlive hExact alpha R j

/-- **EXACT PI/OMNIVERSE BRANCH COLLAPSE.**
The native finite branch sum lands exactly on the original requested rational
Hodge class. -/
theorem omniverseLiveCollapseCycle_spec
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1)
    (alpha : ClassicalHodgeFiber V H (p + 1))
    (R : LiveDegreeCertifiedProgramFamily G D p x hlive hExact alpha) :
    H.cycleClass (p + 1)
        (omniverseLiveCollapseCycle G D p x hlive hExact alpha R) =
      alpha.1 := by
  classical
  unfold omniverseLiveCollapseCycle
  rw [map_sum]
  simp only [LinearMap.map_smul]
  have hsum := (classicalHodgeBasis V H (p + 1)).sum_repr alpha
  have hval :
      (∑ j ∈ ((classicalHodgeBasis V H (p + 1)).repr alpha).support,
        ((classicalHodgeBasis V H (p + 1)).repr alpha j) •
          (classicalHodgeBasis V H (p + 1) j).1) = alpha.1 := by
    exact congrArg Subtype.val hsum
  rw [← hval]
  apply Finset.sum_congr rfl
  intro j hj
  have hjne :
      (classicalHodgeBasis V H (p + 1)).repr alpha j ≠ 0 :=
    Finsupp.mem_support_iff.mp hj
  rw [liveBranchTargetCycle_spec G D p x hlive hExact alpha R j hjne]

/-- Elementwise existential form: materializing only alpha's finite live branch
packet is sufficient to construct its exact algebraic representative. -/
theorem target_has_native_cycle_of_live_degreeCertified_branches
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1)
    (alpha : ClassicalHodgeFiber V H (p + 1))
    (R : LiveDegreeCertifiedProgramFamily G D p x hlive hExact alpha) :
    ∃ Z : codimensionCycles V.X (p + 1),
      H.cycleClass (p + 1) Z = alpha.1 := by
  exact ⟨omniverseLiveCollapseCycle G D p x hlive hExact alpha R,
    omniverseLiveCollapseCycle_spec G D p x hlive hExact alpha R⟩

#check LiveDegreeCertifiedProgramFamily
#check liveBranchTargetCycle
#check liveBranchTargetCycle_spec
#check omniverseLiveCollapseCycle
#check omniverseLiveCollapseCycle_spec
#check target_has_native_cycle_of_live_degreeCertified_branches

#print axioms liveBranchTargetCycle_spec
#print axioms omniverseLiveCollapseCycle_spec
#print axioms target_has_native_cycle_of_live_degreeCertified_branches

end GSTClassicalHodgeDegreeCertifiedOmniverseLiveCollapse
