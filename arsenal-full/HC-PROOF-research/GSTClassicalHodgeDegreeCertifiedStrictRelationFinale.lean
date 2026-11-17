import GSTClassicalHodgeDegreeCertifiedFullCorrespondenceCompiler
import GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull

/-!
# GST CLASSICAL HODGE — DEGREE-CERTIFIED STRICT-RELATION FINALE

This file removes the remaining source-action equation from the
full-correspondence compiler.

For a genuine scheme-bi-finite correspondence K, the intrinsic analytic span
carries canonical pullbacks

  l^*, r^* : H^n(X,Q) -> H^n(C_an,Q).

A nonzero finite-map Betti trace on the right projection makes r^* injective.
Therefore a target of the strict Betti relation is unique.  To force the
correspondence push-pull to carry one synchronized GST source to one target
basis sheet, it is enough to prove the raw geometric relation

  l^*(source) = r^*(sourceScalar * targetBasis).

No arbitrary ambient operator equation is assumed.  Uniqueness of related
targets derives that equation, and point-cycle compatibility turns the total
trace push-pull into an honest realized finite closed correspondence.  The
source-specific GST normalization then constructs the exact target algebraic
cycle.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeDegreeCertifiedStrictRelationFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgeSingleExactSuccessorSurvival
open GSTClassicalHodgeDegreeCertifiedFullCorrespondenceCompiler
open GSTClassicalHodgeGSTDegreeCertifiedSource
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeStrictCorrespondenceBettiObstruction
open GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer
open GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A finite-trace strict correspondence is an honest realized closed
correspondence as soon as its point-cycle compatibility is known. -/
noncomputable def realizedFiniteCorrespondenceOfTrace
    (K : SchemeBiFiniteClosedCorrespondence V)
    (T : RightFiniteBettiTrace H.analytification K (2 * p))
    (C : PointCycleCompatibility (n := p) K T) :
    RealizedFiniteClosedCorrespondence V H p where
  geometry := K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
  cohomologyOperator := T.pushPull
  realizes_on_points := by
    intro x
    exact C.point_natural x

/-- Correspondence-expression atom supplied by the intrinsic finite trace. -/
noncomputable def traceExpr
    (K : SchemeBiFiniteClosedCorrespondence V)
    (T : RightFiniteBettiTrace H.analytification K (2 * p))
    (C : PointCycleCompatibility (n := p) K T) :
    RealizedCorrespondenceExpr V H p :=
  .atom (realizedFiniteCorrespondenceOfTrace K T C)

@[simp]
theorem traceExpr_cohomologyOperator
    (K : SchemeBiFiniteClosedCorrespondence V)
    (T : RightFiniteBettiTrace H.analytification K (2 * p))
    (C : PointCycleCompatibility (n := p) K T) :
    (traceExpr K T C).cohomologyOperator = T.pushPull := by
  rfl

/-- **STRICT-RELATION TARGET UNIQUENESS.**
If the scaled target basis sheet satisfies the actual intrinsic left/right
pullback relation with the synchronized source, the finite-trace push-pull is
forced to send the source to exactly that scaled target. -/
theorem pushPull_source_action_of_related
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (T : RightFiniteBettiTrace H.analytification K (2 * p))
    (hrel : BettiRelated H.analytification K (2 * p)
      S.hodge.1
      ((classicalHodgeBasis V H p).repr S.hodge S.sourceIndex •
        (classicalHodgeBasis V H p j).1)) :
    T.pushPull S.hodge.1 =
      (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex •
        (classicalHodgeBasis V H p j).1 := by
  let beta : RationalSingularCohomology H.analytification (2 * p) :=
    (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex •
      (classicalHodgeBasis V H p j).1
  have hzero :
      transferObstruction H.analytification K (2 * p) S.hodge.1 = 0 :=
    (transferObstruction_apply_eq_zero_iff_exists_related
      H.analytification K (2 * p) S.hodge.1).2 ⟨beta, hrel⟩
  let alpha : transferableSubspace H.analytification K (2 * p) :=
    ⟨S.hodge.1, hzero⟩
  have hpush :
      BettiRelated H.analytification K (2 * p)
        S.hodge.1 (T.pushPull S.hodge.1) := by
    simpa [alpha] using T.pushPull_related_of_transferable alpha
  have huniq := related_target_unique
    H.analytification K (2 * p) T.rightPullback_injective hpush hrel
  exact huniq

/-- Build the source-target full correspondence program directly from the raw
strict Betti relation. -/
noncomputable def sourceTargetProgramOfStrictRelation
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (T : RightFiniteBettiTrace H.analytification K (2 * p))
    (C : PointCycleCompatibility (n := p) K T)
    (hrel : BettiRelated H.analytification K (2 * p)
      S.hodge.1
      ((classicalHodgeBasis V H p).repr S.hodge S.sourceIndex •
        (classicalHodgeBasis V H p j).1)) :
    FullCorrespondenceSourceTargetProgram G S j :=
  FullCorrespondenceSourceTargetProgram.ofCorrespondenceExpr
    G S j (traceExpr K T C)
      (by
        simpa [traceExpr_cohomologyOperator] using
          pushPull_source_action_of_related S j K T hrel)

/-- **STRICT-RELATION TARGET CYCLE.**
The raw analytic correspondence relation itself now suffices to construct the
exact algebraic target cycle. -/
theorem targetCycle_ofStrictRelation
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (T : RightFiniteBettiTrace H.analytification K (2 * p))
    (C : PointCycleCompatibility (n := p) K T)
    (hrel : BettiRelated H.analytification K (2 * p)
      S.hodge.1
      ((classicalHodgeBasis V H p).repr S.hodge S.sourceIndex •
        (classicalHodgeBasis V H p j).1)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = (classicalHodgeBasis V H p j).1 := by
  let R := sourceTargetProgramOfStrictRelation G S j K T C hrel
  exact ⟨R.targetCycle, R.targetCycle_spec⟩

/-- Degree-certified specialization: projective degree supplies the genuine
nonzero algebraic GST source, while the target-specific input is only one
intrinsic strict-correspondence pullback equality. -/
theorem degreeCertifiedTargetCycle_ofStrictRelation
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (q : Nat)
    (x : CodimensionPoint V.X q)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = q + 1)
    (j : ClassicalHodgeBasisIndex V H (q + 1))
    (K : SchemeBiFiniteClosedCorrespondence V)
    (T : RightFiniteBettiTrace H.analytification K (2 * (q + 1)))
    (C : PointCycleCompatibility (n := q + 1) K T)
    (hrel : BettiRelated H.analytification K (2 * (q + 1))
      (degreeCertifiedSuccessorSeed G D q x hlive hExact).hodge.1
      ((classicalHodgeBasis V H (q + 1)).repr
          (degreeCertifiedSuccessorSeed G D q x hlive hExact).hodge
          (degreeCertifiedSuccessorSeed G D q x hlive hExact).sourceIndex •
        (classicalHodgeBasis V H (q + 1) j).1)) :
    ∃ Z : codimensionCycles V.X (q + 1),
      H.cycleClass (q + 1) Z =
        (classicalHodgeBasis V H (q + 1) j).1 := by
  exact targetCycle_ofStrictRelation
    G (degreeCertifiedSuccessorSeed G D q x hlive hExact) j K T C hrel

/-- **WEIGHT CROWN FROM RAW STRICT RELATIONS.**
For one degree-certified GST source, it is enough to provide, for each target
basis sheet, an actual scheme-bi-finite correspondence carrying a finite Betti
trace, point-cycle compatibility, and the intrinsic pullback relation from the
source to the scaled target.  These are raw geometric data.  No cyclicity,
saturation, matrix-unit package, native-mass bridge, or ambient-operator action
is an input. -/
theorem hodge_weight_of_degreeCertifiedStrictRelations
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (q : Nat)
    (x : CodimensionPoint V.X q)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = q + 1)
    (K : ∀ j : ClassicalHodgeBasisIndex V H (q + 1),
      SchemeBiFiniteClosedCorrespondence V)
    (T : ∀ j : ClassicalHodgeBasisIndex V H (q + 1),
      RightFiniteBettiTrace H.analytification (K j) (2 * (q + 1)))
    (C : ∀ j : ClassicalHodgeBasisIndex V H (q + 1),
      PointCycleCompatibility (n := q + 1) (K j) (T j))
    (hrel : ∀ j : ClassicalHodgeBasisIndex V H (q + 1),
      BettiRelated H.analytification (K j) (2 * (q + 1))
        (degreeCertifiedSuccessorSeed G D q x hlive hExact).hodge.1
        ((classicalHodgeBasis V H (q + 1)).repr
            (degreeCertifiedSuccessorSeed G D q x hlive hExact).hodge
            (degreeCertifiedSuccessorSeed G D q x hlive hExact).sourceIndex •
          (classicalHodgeBasis V H (q + 1) j).1)) :
    rationalHodgeSubspace (H.hodgeBigrading (q + 1)) ≤
      LinearMap.range (H.cycleClass (q + 1)) := by
  apply hodge_weight_of_degreeCertifiedFullCorrespondencePrograms
    G D q x hlive hExact
  intro j
  exact sourceTargetProgramOfStrictRelation
    G (degreeCertifiedSuccessorSeed G D q x hlive hExact) j
    (K j) (T j) (C j) (hrel j)

/-- Elementwise constructive form of the strict-relation weight crown. -/
theorem everyHodgeClass_weightSucc_of_degreeCertifiedStrictRelations
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (q : Nat)
    (x : CodimensionPoint V.X q)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = q + 1)
    (K : ∀ j : ClassicalHodgeBasisIndex V H (q + 1),
      SchemeBiFiniteClosedCorrespondence V)
    (T : ∀ j : ClassicalHodgeBasisIndex V H (q + 1),
      RightFiniteBettiTrace H.analytification (K j) (2 * (q + 1)))
    (C : ∀ j : ClassicalHodgeBasisIndex V H (q + 1),
      PointCycleCompatibility (n := q + 1) (K j) (T j))
    (hrel : ∀ j : ClassicalHodgeBasisIndex V H (q + 1),
      BettiRelated H.analytification (K j) (2 * (q + 1))
        (degreeCertifiedSuccessorSeed G D q x hlive hExact).hodge.1
        ((classicalHodgeBasis V H (q + 1)).repr
            (degreeCertifiedSuccessorSeed G D q x hlive hExact).hodge
            (degreeCertifiedSuccessorSeed G D q x hlive hExact).sourceIndex •
          (classicalHodgeBasis V H (q + 1) j).1))
    (alpha : RationalSingularCohomology H.analytification (2 * (q + 1)))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading (q + 1))) :
    ∃ Z : codimensionCycles V.X (q + 1),
      H.cycleClass (q + 1) Z = alpha := by
  exact hodge_weight_of_degreeCertifiedStrictRelations
    G D q x hlive hExact K T C hrel halpha

#check realizedFiniteCorrespondenceOfTrace
#check traceExpr
#check pushPull_source_action_of_related
#check sourceTargetProgramOfStrictRelation
#check targetCycle_ofStrictRelation
#check degreeCertifiedTargetCycle_ofStrictRelation
#check hodge_weight_of_degreeCertifiedStrictRelations
#check everyHodgeClass_weightSucc_of_degreeCertifiedStrictRelations

#print axioms pushPull_source_action_of_related
#print axioms targetCycle_ofStrictRelation
#print axioms degreeCertifiedTargetCycle_ofStrictRelation
#print axioms hodge_weight_of_degreeCertifiedStrictRelations
#print axioms everyHodgeClass_weightSucc_of_degreeCertifiedStrictRelations

end GSTClassicalHodgeDegreeCertifiedStrictRelationFinale
