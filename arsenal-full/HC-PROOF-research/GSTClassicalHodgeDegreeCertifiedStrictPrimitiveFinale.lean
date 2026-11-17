import GSTClassicalHodgeDegreeCertifiedFullCorrespondenceCompiler
import GSTClassicalHodgeStrictCorrespondenceTransferFromPrimitives

/-!
# GST CLASSICAL HODGE — DEGREE-CERTIFIED STRICT-PRIMITIVE FINALE

This file removes the last high-level correspondence-naturality input from the
degree-certified full-correspondence compiler.

A strict scheme correspondence is supplied only with the repository's
low-level Betti/intersection primitives: cup product, Gysin, a genuine middle
Betti kernel, point fundamental classes, and geometric incidence.  The strict
transfer theorem derives `RealizesAmbientOnPoints`; from that theorem we build
an honest `RealizedFiniteClosedCorrespondence`, embed it as an atom of the full
correspondence expression algebra, and then feed it directly to the
source-specific GST compiler.

Consequently the target-cycle theorem below does NOT assume an arbitrary
cycle-class commuting square.  Its only target-specific statement is the
whole-Betti action computed from the actual strict kernel on the already
algebraic, degree-certified GST source.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeDegreeCertifiedStrictPrimitiveFinale

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
open GSTClassicalHodgeStrictCorrespondenceTransferFromPrimitives
open GSTClassicalHodgeAmbientBettiSelfProduct
open GSTClassicalHodgeBettiCupGysinPrimitives
open GSTClassicalHodgeAmbientCorrespondenceKernelAction
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeCycleClassIntersectionPrimitives
open GSTClassicalHodgeAmbientCorrespondenceIncidenceNaturality

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {d p : Nat}

/-- Build a genuine realized finite closed correspondence entirely from the
strict low-level incidence primitives.  The realization equation is derived,
not supplied. -/
noncomputable def realizedFiniteCorrespondenceOfStrictPrimitives
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (kappa : MiddleBettiCorrespondenceKernel H.analytification d K)
    (pt : PointBettiClass (V := V) p H.analytification)
    (hpoint : ∀ x : CodimensionPoint V.X p,
      H.cycleClass p (codimensionPointCycle V.X p x) = pt x)
    (I : GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p) P K kappa pt) :
    RealizedFiniteClosedCorrespondence V H p where
  geometry := K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
  cohomologyOperator := kernelAction H.analytification P kappa (2 * p)
  realizes_on_points :=
    GSTClassicalHodgeStrictCorrespondenceTransferFromPrimitives.realizesAmbientOnPoints
      P K kappa pt hpoint I

/-- The corresponding atom of the noncommutative realized-correspondence
expression algebra. -/
noncomputable def strictPrimitiveExpr
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (kappa : MiddleBettiCorrespondenceKernel H.analytification d K)
    (pt : PointBettiClass (V := V) p H.analytification)
    (hpoint : ∀ x : CodimensionPoint V.X p,
      H.cycleClass p (codimensionPointCycle V.X p x) = pt x)
    (I : GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p) P K kappa pt) :
    RealizedCorrespondenceExpr V H p :=
  .atom (realizedFiniteCorrespondenceOfStrictPrimitives
    P K kappa pt hpoint I)

/-- The strict primitive atom denotes exactly the whole-Betti kernel action
constructed from cup and Gysin. -/
theorem strictPrimitiveExpr_cohomologyOperator
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (kappa : MiddleBettiCorrespondenceKernel H.analytification d K)
    (pt : PointBettiClass (V := V) p H.analytification)
    (hpoint : ∀ x : CodimensionPoint V.X p,
      H.cycleClass p (codimensionPointCycle V.X p x) = pt x)
    (I : GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p) P K kappa pt) :
    (strictPrimitiveExpr P K kappa pt hpoint I).cohomologyOperator =
      kernelAction H.analytification P kappa (2 * p) := by
  rfl

/-- Convert an independently COMPUTED strict-kernel action on one synchronized
GST source into the full-correspondence source-target program.  Naturality is
not an argument: it was already derived from incidence primitives above. -/
noncomputable def sourceTargetProgramOfStrictPrimitives
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (kappa : MiddleBettiCorrespondenceKernel H.analytification d K)
    (pt : PointBettiClass (V := V) p H.analytification)
    (hpoint : ∀ x : CodimensionPoint V.X p,
      H.cycleClass p (codimensionPointCycle V.X p x) = pt x)
    (I : GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p) P K kappa pt)
    (hact :
      kernelAction H.analytification P kappa (2 * p) S.hodge.1 =
        (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex •
          (classicalHodgeBasis V H p j).1) :
    FullCorrespondenceSourceTargetProgram G S j :=
  FullCorrespondenceSourceTargetProgram.ofCorrespondenceExpr
    G S j (strictPrimitiveExpr P K kappa pt hpoint I) (by
      simpa [strictPrimitiveExpr_cohomologyOperator] using hact)

/-- **STRICT-PRIMITIVE TARGET CYCLE.**
A whole-Betti kernel action computed from an actual strict incidence carrier,
on one synchronized algebraic GST source, produces the exact target algebraic
cycle. -/
theorem targetCycle_ofStrictPrimitives
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (kappa : MiddleBettiCorrespondenceKernel H.analytification d K)
    (pt : PointBettiClass (V := V) p H.analytification)
    (hpoint : ∀ x : CodimensionPoint V.X p,
      H.cycleClass p (codimensionPointCycle V.X p x) = pt x)
    (I : GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p) P K kappa pt)
    (hact :
      kernelAction H.analytification P kappa (2 * p) S.hodge.1 =
        (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex •
          (classicalHodgeBasis V H p j).1) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = (classicalHodgeBasis V H p j).1 := by
  let R := sourceTargetProgramOfStrictPrimitives
    G S j P K kappa pt hpoint I hact
  exact ⟨R.targetCycle, R.targetCycle_spec⟩

/-- Degree-certified specialization of the strict-primitive target-cycle
construction.  The source is nonzero for projective-degree reasons. -/
theorem degreeCertifiedTargetCycle_ofStrictPrimitives
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
    (j : ClassicalHodgeBasisIndex V H (p + 1))
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (kappa : MiddleBettiCorrespondenceKernel H.analytification d K)
    (pt : PointBettiClass (V := V) (p + 1) H.analytification)
    (hpoint : ∀ y : CodimensionPoint V.X (p + 1),
      H.cycleClass (p + 1) (codimensionPointCycle V.X (p + 1) y) = pt y)
    (I : GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p + 1) P K kappa pt)
    (hact :
      kernelAction H.analytification P kappa (2 * (p + 1))
          (degreeCertifiedSuccessorSeed G D p x hlive hExact).hodge.1 =
        (classicalHodgeBasis V H (p + 1)).repr
            (degreeCertifiedSuccessorSeed G D p x hlive hExact).hodge
            (degreeCertifiedSuccessorSeed G D p x hlive hExact).sourceIndex •
          (classicalHodgeBasis V H (p + 1) j).1) :
    ∃ Z : codimensionCycles V.X (p + 1),
      H.cycleClass (p + 1) Z =
        (classicalHodgeBasis V H (p + 1) j).1 := by
  exact targetCycle_ofStrictPrimitives
    G (degreeCertifiedSuccessorSeed G D p x hlive hExact) j
    P K kappa pt hpoint I hact

#check realizedFiniteCorrespondenceOfStrictPrimitives
#check strictPrimitiveExpr
#check strictPrimitiveExpr_cohomologyOperator
#check sourceTargetProgramOfStrictPrimitives
#check targetCycle_ofStrictPrimitives
#check degreeCertifiedTargetCycle_ofStrictPrimitives

#print axioms realizedFiniteCorrespondenceOfStrictPrimitives
#print axioms strictPrimitiveExpr_cohomologyOperator
#print axioms targetCycle_ofStrictPrimitives
#print axioms degreeCertifiedTargetCycle_ofStrictPrimitives

end GSTClassicalHodgeDegreeCertifiedStrictPrimitiveFinale
