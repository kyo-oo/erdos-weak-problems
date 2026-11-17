import GSTClassicalHodgeGlobalSheetSaturation
import GSTClassicalHodgeGradedGeometricProgramOrbit
import GSTClassicalHodgeProjectiveGeneratorWordCompiler

/-!
# GST CLASSICAL HODGE — SOURCE-SPECIFIC GST GEOMETRIC PROGRAM COMPILER

The total GST sheet algebra is larger than the native algebraic-cycle algebra;
the repository correctly proves that arbitrary multiplicity matrix units do
not descend through the native projection.  The right geometric interface is
therefore source-specific.

A synchronized source already contains an actual native cycle and its exact
Hodge class.  For one target sheet we ask only for a genuine graded geometric
program whose cohomological execution on THAT source agrees with the GST
matrix-unit prediction.  Program naturality then executes the same program on
the actual native source cycle.  After normalization by the source coordinate,
this constructs the requested target algebraic cycle.

No target algebraicity, basis-cycle witness, universal reachability statement,
or arbitrary matrix-unit naturality is stored in the certificate.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGSTSourceProgramCompiler

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeProjectiveWordOrbit
open GSTClassicalHodgeProjectiveGeneratorWordCompiler
open GSTClassicalHodgeGlobalSheetCosmos

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A genuine geometry program realizing the GST source-to-target move only on
one synchronized live source.  This is the precise interface permitted by the
native-descent obstruction. -/
structure GSTSourceTargetProgram
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p) where
  program : GradedGeometricProgram V p p
  source_action :
    program.cohomologyEval G S.hodge.1 =
      (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex •
        (classicalHodgeBasis V H p j).1

namespace GSTSourceTargetProgram

/-- The nonzero GST source scalar selected by the synchronized source. -/
noncomputable def sourceScalar
    {G : GeometricCycleClassSpine V H}
    {S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)}
    {j : ClassicalHodgeBasisIndex V H p}
    (R : GSTSourceTargetProgram G S j) : ℚ :=
  (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex

/-- The source scalar is nonzero because the source index is chosen from a
nonzero coordinate of the synchronized Hodge state. -/
theorem sourceScalar_ne_zero
    {G : GeometricCycleClassSpine V H}
    {S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)}
    {j : ClassicalHodgeBasisIndex V H p}
    (R : GSTSourceTargetProgram G S j) :
    R.sourceScalar ≠ 0 := by
  exact S.sourceCoefficient_ne_zero

/-- Execute the genuine native program on the actual synchronized source and
normalize by the nonzero GST source coordinate. -/
noncomputable def targetCycle
    {G : GeometricCycleClassSpine V H}
    {S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)}
    {j : ClassicalHodgeBasisIndex V H p}
    (R : GSTSourceTargetProgram G S j) :
    codimensionCycles V.X p :=
  R.sourceScalar⁻¹ • R.program.cycleEval G S.cycle

/-- **SOURCE-SPECIFIC GST/NATIVE SYNCHRONIZATION.**
A genuine graded geometric program agreeing with the GST matrix-unit action on
one synchronized source constructs an actual native cycle representing the
target Hodge basis sheet. -/
theorem targetCycle_spec
    {G : GeometricCycleClassSpine V H}
    {S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)}
    {j : ClassicalHodgeBasisIndex V H p}
    (R : GSTSourceTargetProgram G S j) :
    H.cycleClass p R.targetCycle =
      (classicalHodgeBasis V H p j).1 := by
  have hnat := R.program.cycleClass_cycleEval G S.cycle
  rw [S.class_eq, R.source_action] at hnat
  rw [show (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex =
      R.sourceScalar from rfl] at hnat
  unfold targetCycle
  rw [LinearMap.map_smul, hnat]
  rw [smul_smul, inv_mul_cancel₀ (R.sourceScalar_ne_zero), one_smul]

/-- The target basis sheet therefore belongs to the genuine cycle-class range. -/
theorem target_mem_cycleClass_range
    {G : GeometricCycleClassSpine V H}
    {S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)}
    {j : ClassicalHodgeBasisIndex V H p}
    (R : GSTSourceTargetProgram G S j) :
    (classicalHodgeBasis V H p j).1 ∈
      LinearMap.range (H.cycleClass p) := by
  exact ⟨R.targetCycle, R.targetCycle_spec⟩

/-- On total GST sheet coordinates, the geometric program's source action is
exactly the same nonzero target hit predicted by the global sheet matrix unit. -/
theorem source_action_matches_global_sheet_move
    {G : GeometricCycleClassSpine V H}
    {S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)}
    {j : ClassicalHodgeBasisIndex V H p}
    (R : GSTSourceTargetProgram G S j) :
    fiberedWeightCoordinates V H p
        ⟨R.sourceScalar • (classicalHodgeBasis V H p j).1,
          (rationalHodgeSubspace (H.hodgeBigrading p)).smul_mem
            R.sourceScalar (classicalHodgeBasis V H p j).2⟩ =
      sheetMatrixUnit
        (⟨p,S.sourceIndex⟩ : FiberedHodgeIndex V H)
        (⟨p,j⟩ : FiberedHodgeIndex V H)
        (fiberedWeightCoordinates V H p S.hodge) := by
  have hcoeff : (fiberedWeightCoordinates V H p S.hodge)
      (⟨p, S.sourceIndex⟩ : FiberedHodgeIndex V H) = R.sourceScalar :=
    Finsupp.embDomain_apply_self (weightFiberEmbedding V H p)
      ((classicalHodgeBasis V H p).repr S.hodge) S.sourceIndex
  change fiberedWeightCoordinates V H p
      (R.sourceScalar • classicalHodgeBasis V H p j) = _
  rw [fiberedWeightCoordinates_smul_basis, sheetMatrixUnit_apply, ← hcoeff]

/-- Every previous actual projective-word live-source certificate is already a
source-specific GST geometric program: embed the projective word as one
same-weight graded program. -/
noncomputable def ofProjectiveWord
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (R : ProjectiveWordLiveSourceTarget G S j) :
    GSTSourceTargetProgram G S j where
  program := .word R.word
  source_action := by
    exact R.source_action

/-- The normalized target cycle produced by the new compiler agrees in cycle
class with the old projective-word construction. -/
theorem ofProjectiveWord_target_spec
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (R : ProjectiveWordLiveSourceTarget G S j) :
    H.cycleClass p (ofProjectiveWord G S j R).targetCycle =
      (classicalHodgeBasis V H p j).1 := by
  exact (ofProjectiveWord G S j R).targetCycle_spec

/-- Existing two-generator projective realizations compile through the already
proved projective-word compiler into the new source-specific GST program
interface. -/
noncomputable def ofProjectiveTwoGenerator
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (hij : S.sourceIndex ≠ j)
    (R : GSTClassicalHodgeProjectiveTwoGeneratorExternalization.ProjectiveTwoGenerator
      (V := V) (H := H) S.sourceIndex j) :
    GSTSourceTargetProgram G S j :=
  ofProjectiveWord G S j
    (GSTClassicalHodgeProjectiveGeneratorWordCompiler.ProjectiveTwoGenerator.toWordLiveSourceTarget
      G S j hij R)

#check GSTSourceTargetProgram
#check GSTSourceTargetProgram.sourceScalar
#check GSTSourceTargetProgram.targetCycle
#check GSTSourceTargetProgram.targetCycle_spec
#check GSTSourceTargetProgram.target_mem_cycleClass_range
#check GSTSourceTargetProgram.source_action_matches_global_sheet_move
#check GSTSourceTargetProgram.ofProjectiveWord
#check GSTSourceTargetProgram.ofProjectiveTwoGenerator

#print axioms GSTSourceTargetProgram.targetCycle_spec
#print axioms GSTSourceTargetProgram.target_mem_cycleClass_range
#print axioms GSTSourceTargetProgram.source_action_matches_global_sheet_move

end GSTSourceTargetProgram

end GSTClassicalHodgeGSTSourceProgramCompiler
