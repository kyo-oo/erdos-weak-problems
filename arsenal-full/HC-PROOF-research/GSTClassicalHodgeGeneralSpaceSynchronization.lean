import GSTClassicalHodgeGeneralSpaceRealization

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGeneralSpaceSynchronization

open GSTGeneralSpace
open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeGeneralSpaceRealization

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- A synchronized execution packet: one genuine geometric program, one source
native cycle, and the native target obtained by executing the same program. -/
structure SynchronizedPathExecution
    (G : GeometricCycleClassSpine V H)
    (x y : (hodgeGeneralSpace G).Point) where
  program : GradedGeometricProgram V x.1 y.1
  reaches : program.cohomologyEval G x.2 = y.2
  sourceCycle : codimensionCycles V.X x.1
  source_sync : H.cycleClass x.1 sourceCycle = x.2

namespace SynchronizedPathExecution

variable {G : GeometricCycleClassSpine V H}
variable {x y : (hodgeGeneralSpace G).Point}

/-- Native target produced by executing the same General Space path. -/
noncomputable def targetCycle
    (E : SynchronizedPathExecution G x y) :
    codimensionCycles V.X y.1 :=
  E.program.cycleEval G E.sourceCycle

/-- **COSMIC SYNCHRONIZATION SQUARE.**  Native and Betti execution of the same
General Space path land at the same state. -/
theorem target_sync
    (E : SynchronizedPathExecution G x y) :
    H.cycleClass y.1 E.targetCycle = y.2 := by
  unfold targetCycle
  rw [E.program.cycleClass_cycleEval G E.sourceCycle]
  rw [E.source_sync]
  exact E.reaches

/-- Therefore every synchronized target lies in the genuine native locus. -/
theorem target_native
    (E : SynchronizedPathExecution G x y) :
    NativeLocus G y := by
  exact ⟨E.targetCycle, E.target_sync⟩

end SynchronizedPathExecution

/-- Build a synchronized execution from any genuine General Space path and any
native witness at its source. -/
noncomputable def synchronizePath
    (G : GeometricCycleClassSpine V H)
    {x y : (hodgeGeneralSpace G).Point}
    (γ : (hodgeGeneralSpace G).Path x y)
    (hx : NativeLocus G x) :
    SynchronizedPathExecution G x y := by
  let P := Classical.choose γ
  have hP := Classical.choose_spec γ
  let Z := Classical.choose hx
  have hZ := Classical.choose_spec hx
  exact
    { program := P
      reaches := hP
      sourceCycle := Z
      source_sync := hZ }

/-- General Space path synchronization is exactly the earlier path-closure law,
now with the actual target native cycle exposed. -/
theorem synchronized_path_native
    (G : GeometricCycleClassSpine V H)
    {x y : (hodgeGeneralSpace G).Point}
    (γ : (hodgeGeneralSpace G).Path x y)
    (hx : NativeLocus G x) :
    ∃ Z : codimensionCycles V.X y.1,
      H.cycleClass y.1 Z = y.2 := by
  let E := synchronizePath G γ hx
  exact ⟨E.targetCycle, E.target_sync⟩

#check SynchronizedPathExecution
#check SynchronizedPathExecution.targetCycle
#check SynchronizedPathExecution.target_sync
#check synchronizePath
#check synchronized_path_native

#print axioms SynchronizedPathExecution.target_sync
#print axioms synchronized_path_native

end GSTClassicalHodgeGeneralSpaceSynchronization
