import GSTClassicalHodgeDegreeCertifiedOmniverseLiveCollapse
import GSTClassicalHodgePiOmniverseBranchSynthesis
import GSTClassicalHodgeAugmentedTargetMatrixUnit

/-!
# GST CLASSICAL HODGE — DEGREE-CERTIFIED OMNIVERSE CAUSAL COMPILER

This file identifies the primitive causal arrow of the Hodge omniverse with
the source-specific full-correspondence compiler.

The causal source is NOT the unknown target Hodge class.  It is the already
constructed degree-certified algebraic GST source.  Its selected source
coordinate is nonzero by projective intersection degree.  Hence that selected
coordinate is an honest live support index and the existing augmented GST
causal event may be fired from exactly that coordinate to any requested target
sheet.

If primitive omniverse causal events are materialized by genuine realized
correspondence expressions, the materialized event automatically satisfies the
precise source-action equation required by `FullCorrespondenceSourceTargetProgram`.
No extra matrix-unit equation is assumed.

Combined with the live-branch collapse file, this gives the direct proof path:

  degree-certified algebraic source
    -> GST causal event
    -> genuine realized correspondence expression
    -> native target basis cycle
    -> finite rational branch collapse
    -> requested Hodge class.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeDegreeCertifiedOmniverseCausalCompiler

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeAugmentedTargetMatrixUnit
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgeSingleExactSuccessorSurvival
open GSTClassicalHodgeGSTDegreeCertifiedSource
open GSTClassicalHodgeDegreeCertifiedFullCorrespondenceCompiler
open GSTClassicalHodgeDegreeCertifiedFullCorrespondenceCompiler.FullCorrespondenceSourceTargetProgram
open GSTClassicalHodgeDegreeCertifiedOmniverseLiveCollapse
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgePiOmniverseBranchSynthesis
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The distinguished degree-certified GST source coordinate is an actual live
support index of the degree-certified Hodge seed. -/
noncomputable def degreeCertifiedLiveSourceIndex
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1) :
    HodgeSupportIndex (degreeCertifiedSuccessorSeed G D p x hlive hExact).hodge := by
  let S := degreeCertifiedSuccessorSeed G D p x hlive hExact
  refine ⟨S.sourceIndex, ?_⟩
  apply Finsupp.mem_support_iff.mpr
  simpa [hodgeCoordinate] using S.sourceCoefficient_ne_zero

/-- The exact GST causal edge from the degree-certified source to one target
basis direction, using the already-proved augmented finite-support transport. -/
theorem degreeCertified_causal_event_to_target
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
    (j : ClassicalHodgeBasisIndex V H (p + 1)) :
    HodgeBranchEvent
      (V := V) (H := H) (p := p + 1)
      ⟨GSTGraphV2OmniversalCore.Sector.gstPlus,
        (degreeCertifiedSuccessorSeed G D p x hlive hExact).hodge⟩
      ⟨GSTGraphV2OmniversalCore.Sector.gstPlus,
        hodgeMatrixUnit
          (degreeCertifiedSuccessorSeed G D p x hlive hExact).sourceIndex j
          (degreeCertifiedSuccessorSeed G D p x hlive hExact).hodge⟩ := by
  let S := degreeCertifiedSuccessorSeed G D p x hlive hExact
  let i : HodgeSupportIndex S.hodge :=
    degreeCertifiedLiveSourceIndex G D p x hlive hExact
  refine ⟨j, i, ?_⟩
  simpa [S, i, degreeCertifiedLiveSourceIndex] using
    (augmentedConcreteHodgeMatrixUnit_eq S.hodge j i).symm

/-- **CAUSAL EVENT -> FULL CORRESPONDENCE PROGRAM.**
A primitive realized-expression compiler for the omniverse causal graph
instantly gives the exact source-specific full correspondence program from the
degree-certified algebraic source to any requested Hodge basis sheet. -/
noncomputable def degreeCertifiedProgramOfPrimitiveCompiler
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
    (C : PrimitiveBranchCompiler (V := V) (H := H) (p := p + 1))
    (j : ClassicalHodgeBasisIndex V H (p + 1)) :
    DegreeCertifiedFullCorrespondenceProgram G D p x hlive hExact j := by
  let S := degreeCertifiedSuccessorSeed G D p x hlive hExact
  let u : HodgeBranchNode (V := V) (H := H) (p := p + 1) :=
    ⟨GSTGraphV2OmniversalCore.Sector.gstPlus, S.hodge⟩
  let v : HodgeBranchNode (V := V) (H := H) (p := p + 1) :=
    ⟨GSTGraphV2OmniversalCore.Sector.gstPlus,
      hodgeMatrixUnit S.sourceIndex j S.hodge⟩
  have hev : HodgeBranchEvent u v := by
    simpa [u, v, S] using
      degreeCertified_causal_event_to_target G D p x hlive hExact j
  obtain ⟨E, hE⟩ := C hev
  have haction :
      E.cohomologyOperator S.hodge.1 =
        (classicalHodgeBasis V H (p + 1)).repr S.hodge S.sourceIndex •
          (classicalHodgeBasis V H (p + 1) j).1 := by
    have heq := hE.symm
    change E.cohomologyOperator S.hodge.1 =
      (hodgeMatrixUnit S.sourceIndex j S.hodge).1 at heq
    rw [hodgeMatrixUnit_apply] at heq
    simpa [hodgeCoordinate] using heq
  exact FullCorrespondenceSourceTargetProgram.ofCorrespondenceExpr
    G S j E haction

/-- A primitive omniverse compiler therefore materializes every live branch of
a concrete target Hodge state from the one degree-certified algebraic source. -/
noncomputable def liveProgramsOfPrimitiveCompiler
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
    (C : PrimitiveBranchCompiler (V := V) (H := H) (p := p + 1))
    (alpha : ClassicalHodgeFiber V H (p + 1)) :
    LiveDegreeCertifiedProgramFamily G D p x hlive hExact alpha := by
  intro j _hj
  exact degreeCertifiedProgramOfPrimitiveCompiler
    G D p x hlive hExact C j

/-- **DEGREE-CERTIFIED OMNIVERSE EXACT COLLAPSE.**
Once primitive GST causal events are genuinely materialized, every concrete
rational Hodge state in the degree-certified successor weight is represented
by the explicit finite native branch-collapse cycle. -/
theorem target_has_native_cycle_of_primitive_omniverse_compiler
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
    (C : PrimitiveBranchCompiler (V := V) (H := H) (p := p + 1))
    (alpha : ClassicalHodgeFiber V H (p + 1)) :
    ∃ Z : codimensionCycles V.X (p + 1),
      H.cycleClass (p + 1) Z = alpha.1 := by
  exact target_has_native_cycle_of_live_degreeCertified_branches
    G D p x hlive hExact alpha
      (liveProgramsOfPrimitiveCompiler G D p x hlive hExact C alpha)

#check degreeCertifiedLiveSourceIndex
#check degreeCertified_causal_event_to_target
#check degreeCertifiedProgramOfPrimitiveCompiler
#check liveProgramsOfPrimitiveCompiler
#check target_has_native_cycle_of_primitive_omniverse_compiler

#print axioms degreeCertified_causal_event_to_target
#print axioms target_has_native_cycle_of_primitive_omniverse_compiler

end GSTClassicalHodgeDegreeCertifiedOmniverseCausalCompiler
