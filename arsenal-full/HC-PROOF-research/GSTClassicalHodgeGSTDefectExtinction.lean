import GSTClassicalHodgeGSTSourceProgramCompiler
import GSTClassicalHodgeFiberedSeparatorDefect
import GSTClassicalHodgeSingleSheetCrown
import GSTClassicalHodgeAtomicSpan

/-!
# GST CLASSICAL HODGE — GST DEFECT EXTINCTION

A single-sheet Hodge failure is already encoded in the repository as a
nonzero fibered GST cycle-class defect detected by an atomic separator.
The new source-specific program compiler gives the opposite piece: whenever a
genuine graded geometric program synchronizes with the GST source-to-target
move, it constructs an actual native cycle whose class is exactly the target
Hodge sheet.

These two facts collide directly.  The separator annihilates the whole actual
atomic cycle-class span, while the synchronized program puts the detected
basis sheet in that span.  Therefore the separator reading is simultaneously
nonzero and zero.

This file makes that contradiction explicit and then states it in the native
fibered-defect language: every defect event over a target reached by a
synchronized GST/geometric program is empty.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGSTDefectExtinction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeSingleSheetCrown
open GSTClassicalHodgeFiberedSeparatorDefect
open GSTClassicalHodgeGSTSourceProgramCompiler
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeGSTSpineGlobalSource
open GSTClassicalHodgeLimitlessSpinePropagation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A synchronized GST/geometric program puts its target basis sheet in the
actual point-cycle span, not merely in an abstract orbit. -/
theorem basis_mem_atomicSpan_of_sourceProgram
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (R : GSTSourceTargetProgram G S j) :
    (classicalHodgeBasis V H p j).1 ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  have hrange := R.target_mem_cycleClass_range
  rw [smoothProjective_cycleClass_range_eq_atomic_span V H p] at hrange
  exact hrange

/-- **MICROSCOPIC GST DEFECT COLLISION.**
A basis separator cannot coexist with a genuine source-specific program
realizing the GST move to that basis sheet. -/
theorem separator_false_of_sourceProgram
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (R : GSTSourceTargetProgram G S j)
    (Sep : BasisAtomicSeparator V H p j) :
    False := by
  have hmem := basis_mem_atomicSpan_of_sourceProgram G S j R
  have hker :
      pointCycleClassSpan p (H.cycleClass p) ≤
        LinearMap.ker Sep.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      p (H.cycleClass p) Sep.detector).mp Sep.annihilates_atoms
  exact Sep.detects_basis (hker hmem)

/-- No microscopic separator survives a synchronized source-specific GST
program. -/
theorem isEmpty_basisSeparator_of_sourceProgram
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (R : GSTSourceTargetProgram G S j) :
    IsEmpty (BasisAtomicSeparator V H p j) := by
  refine ⟨?_⟩
  intro Sep
  exact separator_false_of_sourceProgram G S j R Sep

/-- The same contradiction stated in the repo's fibered GST defect language:
there is no nonzero separator defect event over a target synchronized by a
genuine geometry program. -/
theorem isEmpty_fiberedDefectEvent_of_sourceProgram
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (R : GSTSourceTargetProgram G S j) :
    IsEmpty (FiberedDefectEvent V H p j) := by
  have hSep := isEmpty_basisSeparator_of_sourceProgram G S j R
  refine ⟨?_⟩
  intro E
  exact isEmpty_iff.mp hSep E.separator

/-- Equivalently the target atomic defect vanishes. -/
theorem target_atomicDefect_zero_of_sourceProgram
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (R : GSTSourceTargetProgram G S j) :
    GSTClassicalHodgeAtomicDefectDuality.atomicDefectLinearMap V H p
        (classicalHodgeBasis V H p j) = 0 := by
  exact (basis_atomicDefect_zero_iff_no_separator V H p j).2
    (isEmpty_basisSeparator_of_sourceProgram G S j R)

/-- Canonical-spine specialization: the only source used is the actual
nonzero projective spine constructed from weight zero and native mass. -/
abbrev CanonicalSpineGSTProgram
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (p : Nat)
    (j : ClassicalHodgeBasisIndex V H p) :=
  GSTSourceTargetProgram G (globalSpineOrbitSeed G M p) j

/-- A canonical-spine GST program extinguishes the target separator. -/
theorem canonicalSpineProgram_extinguishes_separator
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (p : Nat)
    (j : ClassicalHodgeBasisIndex V H p)
    (R : CanonicalSpineGSTProgram G M p j) :
    IsEmpty (BasisAtomicSeparator V H p j) :=
  isEmpty_basisSeparator_of_sourceProgram
    G (globalSpineOrbitSeed G M p) j R

/-- A family of canonical-spine source-specific programs eliminates every
basis separator at one weight. -/
theorem no_basis_separator_of_canonicalSpinePrograms
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (p : Nat)
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      CanonicalSpineGSTProgram G M p j) :
    ∀ j : ClassicalHodgeBasisIndex V H p,
      IsEmpty (BasisAtomicSeparator V H p j) := by
  intro j
  exact canonicalSpineProgram_extinguishes_separator G M p j (R j)

/-- The same family places every Hodge basis sheet in the genuine algebraic
cycle-class range. -/
theorem every_basis_mem_cycleClassRange_of_canonicalSpinePrograms
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (p : Nat)
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      CanonicalSpineGSTProgram G M p j) :
    ∀ j : ClassicalHodgeBasisIndex V H p,
      (classicalHodgeBasis V H p j).1 ∈
        LinearMap.range (H.cycleClass p) := by
  intro j
  exact (R j).target_mem_cycleClass_range

#check basis_mem_atomicSpan_of_sourceProgram
#check separator_false_of_sourceProgram
#check isEmpty_basisSeparator_of_sourceProgram
#check isEmpty_fiberedDefectEvent_of_sourceProgram
#check target_atomicDefect_zero_of_sourceProgram
#check CanonicalSpineGSTProgram
#check canonicalSpineProgram_extinguishes_separator
#check no_basis_separator_of_canonicalSpinePrograms
#check every_basis_mem_cycleClassRange_of_canonicalSpinePrograms

#print axioms separator_false_of_sourceProgram
#print axioms isEmpty_basisSeparator_of_sourceProgram
#print axioms isEmpty_fiberedDefectEvent_of_sourceProgram
#print axioms target_atomicDefect_zero_of_sourceProgram
#print axioms no_basis_separator_of_canonicalSpinePrograms

end GSTClassicalHodgeGSTDefectExtinction
