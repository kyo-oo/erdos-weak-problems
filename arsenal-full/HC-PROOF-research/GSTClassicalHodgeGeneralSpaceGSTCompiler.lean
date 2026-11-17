import GSTClassicalHodgeGeneralSpaceDefectExtinction
import GSTClassicalHodgeGSTSourceProgramCompiler
import GSTClassicalHodgeGSTDegreeCertifiedSource

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGeneralSpaceGSTCompiler

open GSTGeneralSpace
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGSTSourceProgramCompiler
open GSTClassicalHodgeGSTDegreeCertifiedSource
open GSTClassicalHodgeGeneralSpaceRealization
open GSTClassicalHodgeGeneralSpaceSynchronization

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- General Space point carried by one synchronized native/Hodge source. -/
def sourcePoint
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) :
    EvenBettiPoint V H :=
  ⟨p, S.hodge.1⟩

/-- General Space point carried by one true Hodge basis sheet. -/
def basisPoint
    (j : ClassicalHodgeBasisIndex V H p) :
    EvenBettiPoint V H :=
  ⟨p, (classicalHodgeBasis V H p j).1⟩

/-- The synchronized source is genuinely native. -/
theorem sourcePoint_native
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) :
    NativeLocus G (sourcePoint S) := by
  exact ⟨S.cycle, S.class_eq⟩

/-- Normalize the source-specific geometric program by the inverse nonzero GST
source coordinate.  Its cohomological action sends the source exactly to the
target basis state, not merely to a nonzero scalar multiple. -/
noncomputable def normalizedProgram
    {G : GeometricCycleClassSpine V H}
    {S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)}
    {j : ClassicalHodgeBasisIndex V H p}
    (R : GSTSourceTargetProgram G S j) :
    GradedGeometricProgram V p p :=
  .smul R.sourceScalar⁻¹ R.program

/-- Exact normalized source action. -/
theorem normalizedProgram_source_action
    {G : GeometricCycleClassSpine V H}
    {S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)}
    {j : ClassicalHodgeBasisIndex V H p}
    (R : GSTSourceTargetProgram G S j) :
    (normalizedProgram R).cohomologyEval G S.hodge.1 =
      (classicalHodgeBasis V H p j).1 := by
  change R.sourceScalar⁻¹ • R.program.cohomologyEval G S.hodge.1 =
    (classicalHodgeBasis V H p j).1
  rw [R.source_action]
  simp [GSTSourceTargetProgram.sourceScalar, R.sourceScalar_ne_zero, smul_smul]

/-- **GST -> GENERAL SPACE COMPILER.**
Every source-specific GST/geometric synchronization certificate becomes an
actual General Space path from the native synchronized source to the exact
requested Hodge basis state. -/
theorem sourceProgram_generalSpacePath
    {G : GeometricCycleClassSpine V H}
    {S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)}
    {j : ClassicalHodgeBasisIndex V H p}
    (R : GSTSourceTargetProgram G S j) :
    (hodgeGeneralSpace G).Path (sourcePoint S) (basisPoint j) := by
  refine ⟨normalizedProgram R, ?_⟩
  exact normalizedProgram_source_action R

/-- General Space path-closure now reconstructs the target cycle directly. -/
theorem sourceProgram_basis_native
    {G : GeometricCycleClassSpine V H}
    {S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)}
    {j : ClassicalHodgeBasisIndex V H p}
    (R : GSTSourceTargetProgram G S j) :
    NativeLocus G (basisPoint j) := by
  exact nativeLocus_of_reachable G
    (sourceProgram_generalSpacePath R)
    (sourcePoint_native G S)

/-- Elementwise target cycle recovered through the General Space synchronization
calculus. -/
theorem sourceProgram_basis_cycle
    {G : GeometricCycleClassSpine V H}
    {S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)}
    {j : ClassicalHodgeBasisIndex V H p}
    (R : GSTSourceTargetProgram G S j) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = (classicalHodgeBasis V H p j).1 := by
  exact sourceProgram_basis_native R

/-- The degree-certified source route is therefore already a General Space path
construction; projective degree supplies the live source and GST supplies the
normalized target motion. -/
theorem degreeCertifiedProgram_generalSpacePath
    (G : GeometricCycleClassSpine V H)
    (D : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H)
    (q : Nat)
    (x : CodimensionPoint V.X q)
    (hlive : GSTClassicalHodgePointClosureRelativeCut.ProjectivelyLiveSource
      V.projective.n (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (GSTClassicalHodgePointClosureRelativeCut.ambientSuccessorPoint V x.1
          (GSTClassicalHodgePointClosureRelativeCut.relativeHeightOneSeparatorSuccessor
            V x.1 hlive)) = q + 1)
    (j : ClassicalHodgeBasisIndex V H (q + 1))
    (R : DegreeCertifiedGSTProgram G D q x hlive hExact j) :
    (hodgeGeneralSpace G).Path
      (sourcePoint (degreeCertifiedSuccessorSeed G D q x hlive hExact))
      (basisPoint j) :=
  sourceProgram_generalSpacePath R

#check sourcePoint
#check basisPoint
#check sourcePoint_native
#check normalizedProgram
#check normalizedProgram_source_action
#check sourceProgram_generalSpacePath
#check sourceProgram_basis_native
#check sourceProgram_basis_cycle
#check degreeCertifiedProgram_generalSpacePath

#print axioms normalizedProgram_source_action
#print axioms sourceProgram_generalSpacePath
#print axioms sourceProgram_basis_native
#print axioms degreeCertifiedProgram_generalSpacePath

end GSTClassicalHodgeGeneralSpaceGSTCompiler
