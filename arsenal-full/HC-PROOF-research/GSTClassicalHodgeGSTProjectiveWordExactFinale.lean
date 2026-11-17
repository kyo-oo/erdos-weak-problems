import GSTClassicalHodgeGSTExactFinale
import GSTClassicalHodgeProjectiveWordOrbit
import GSTClassicalHodgeProjectiveGeneratorWordCompiler

/-!
# GST CLASSICAL HODGE — CANONICAL-SPINE PROJECTIVE-WORD EXACT FINALE

This file removes the packaging gap between the genuine projective-word
operator algebra and the exact GST finale.

The canonical projective spine already supplies, in every weight, one actual
native algebraic cycle with a nonzero Hodge coordinate.  A projective operator
word is built only from genuine scheme self-maps by finite addition, rational
scaling and noncommutative composition; its cohomological action is forced by
cycle-class naturality.

Accordingly, to compile a source-to-target GST program we do not assume a
basis-cycle witness, a native matrix-unit lift, or target algebraicity.  We
supply only actual projective geometry.  The two-generator compiler proves the
required source action from the rank-free GST word theorem, and
`GSTExactFinale` returns the literal rational Hodge statement.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGSTProjectiveWordExactFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeGSTSpineGlobalSource
open GSTClassicalHodgeProjectiveWordOrbit
open GSTClassicalHodgeProjectiveTwoGeneratorExternalization
open GSTClassicalHodgeProjectiveGeneratorWordCompiler
open GSTClassicalHodgeGSTSourceProgramCompiler
open GSTClassicalHodgeGSTDefectExtinction
open GSTClassicalHodgeGSTExactFinale
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Compile an actual same-weight projective word into the source-specific GST
program used by the exact finale.  The only equation required is the word's
cohomological action on the already-constructed canonical algebraic spine
source. -/
noncomputable def canonicalSpineProgramOfProjectiveWord
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (p : Nat)
    (j : ClassicalHodgeBasisIndex V H p)
    (W : ProjectiveOperatorWord V p)
    (hW :
      (W.operatorPair G).cohomologyOperator
          (globalSpineOrbitSeed G M p).hodge.1 =
        (classicalHodgeBasis V H p).repr
            (globalSpineOrbitSeed G M p).hodge
            (globalSpineOrbitSeed G M p).sourceIndex •
          (classicalHodgeBasis V H p j).1) :
    CanonicalSpineGSTProgram G M p j :=
  GSTSourceTargetProgram.ofProjectiveWord
    G (globalSpineOrbitSeed G M p) j
    { word := W
      source_action := hW }

/-- The same genuine projective word constructs an explicit native cycle whose
class is the requested Hodge basis sheet. -/
noncomputable def canonicalSpineTargetCycleOfProjectiveWord
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (p : Nat)
    (j : ClassicalHodgeBasisIndex V H p)
    (W : ProjectiveOperatorWord V p)
    (hW :
      (W.operatorPair G).cohomologyOperator
          (globalSpineOrbitSeed G M p).hodge.1 =
        (classicalHodgeBasis V H p).repr
            (globalSpineOrbitSeed G M p).hodge
            (globalSpineOrbitSeed G M p).sourceIndex •
          (classicalHodgeBasis V H p j).1) :
    GSTGeometricRealizationStage2D.codimensionCycles V.X p :=
  (canonicalSpineProgramOfProjectiveWord G M p j W hW).targetCycle

/-- Exact receipt for the cycle manufactured by the canonical-spine projective
word compiler. -/
theorem canonicalSpineTargetCycleOfProjectiveWord_spec
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (p : Nat)
    (j : ClassicalHodgeBasisIndex V H p)
    (W : ProjectiveOperatorWord V p)
    (hW :
      (W.operatorPair G).cohomologyOperator
          (globalSpineOrbitSeed G M p).hodge.1 =
        (classicalHodgeBasis V H p).repr
            (globalSpineOrbitSeed G M p).hodge
            (globalSpineOrbitSeed G M p).sourceIndex •
          (classicalHodgeBasis V H p j).1) :
    H.cycleClass p
        (canonicalSpineTargetCycleOfProjectiveWord G M p j W hW) =
      (classicalHodgeBasis V H p j).1 := by
  exact (canonicalSpineProgramOfProjectiveWord G M p j W hW).targetCycle_spec

/-- **PROJECTIVE-WORD GST EXACT FINALE — ALGEBRAIC-CYCLE FORM.** -/
theorem everyHodgeClassIsRationalAlgebraic_of_canonicalSpine_projectiveWords
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (W : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        ProjectiveOperatorWord V p)
    (hW : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        ((W p j).operatorPair G).cohomologyOperator
            (globalSpineOrbitSeed G M p).hodge.1 =
          (classicalHodgeBasis V H p).repr
              (globalSpineOrbitSeed G M p).hodge
              (globalSpineOrbitSeed G M p).sourceIndex •
            (classicalHodgeBasis V H p j).1) :
    EveryHodgeClassIsRationalAlgebraic H := by
  let R : CanonicalSpineGSTProgramFamily G M :=
    fun p j => canonicalSpineProgramOfProjectiveWord G M p j (W p j) (hW p j)
  exact gst_everyHodgeClassIsRationalAlgebraic G M R

/-- **LITERAL WORDING OF THE RATIONAL HODGE CONJECTURE.** -/
theorem everyHodgeClassIsFiniteRationalCombination_of_canonicalSpine_projectiveWords
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (W : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        ProjectiveOperatorWord V p)
    (hW : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        ((W p j).operatorPair G).cohomologyOperator
            (globalSpineOrbitSeed G M p).hodge.1 =
          (classicalHodgeBasis V H p).repr
              (globalSpineOrbitSeed G M p).hodge
              (globalSpineOrbitSeed G M p).sourceIndex •
            (classicalHodgeBasis V H p j).1) :
    EveryHodgeClassIsFiniteRationalCombination H := by
  let R : CanonicalSpineGSTProgramFamily G M :=
    fun p j => canonicalSpineProgramOfProjectiveWord G M p j (W p j) (hW p j)
  exact gst_everyHodgeClassIsFiniteRationalCombination G M R

/-- Compile the two genuine projective GST primitives automatically.  The
source-action equation is no longer an input: it is the theorem
`compileProjectiveTwoGenerator_source_action`. -/
noncomputable def canonicalSpineProgramOfProjectiveTwoGenerator
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (p : Nat)
    (j : ClassicalHodgeBasisIndex V H p)
    (hij : (globalSpineOrbitSeed G M p).sourceIndex ≠ j)
    (R : ProjectiveTwoGenerator (V := V) (H := H)
      (globalSpineOrbitSeed G M p).sourceIndex j) :
    CanonicalSpineGSTProgram G M p j :=
  canonicalSpineProgramOfProjectiveWord G M p j
    (compileProjectiveTwoGenerator R)
    (compileProjectiveTwoGenerator_source_action
      G (globalSpineOrbitSeed G M p) j hij R)

/-- One pair of genuine projective primitives from the canonical live source
to each target sheet closes the exact algebraic-cycle form of rational Hodge. -/
theorem everyHodgeClassIsRationalAlgebraic_of_projectiveTwoGenerators
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (R : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        ProjectiveTwoGenerator (V := V) (H := H)
          (globalSpineOrbitSeed G M p).sourceIndex j)
    (hdiag : ∀ p : Nat,
      CanonicalSpineGSTProgram G M p
        (globalSpineOrbitSeed G M p).sourceIndex) :
    EveryHodgeClassIsRationalAlgebraic H := by
  let P : CanonicalSpineGSTProgramFamily G M := by
    intro p j
    by_cases h : (globalSpineOrbitSeed G M p).sourceIndex = j
    · subst h
      exact hdiag p
    · exact canonicalSpineProgramOfProjectiveTwoGenerator G M p j h (R p j)
  exact gst_everyHodgeClassIsRationalAlgebraic G M P

/-- **TWO-GENERATOR EXACT CLAY LANDING.**
The same two genuine projective primitives close the literal finite-rational-
combination wording of the conjecture.  The GST rank-free matrix-unit word,
source normalization, target-cycle extraction and arbitrary-class finite
reconstruction are all derived internally. -/
theorem everyHodgeClassIsFiniteRationalCombination_of_projectiveTwoGenerators
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (R : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        ProjectiveTwoGenerator (V := V) (H := H)
          (globalSpineOrbitSeed G M p).sourceIndex j)
    (hdiag : ∀ p : Nat,
      CanonicalSpineGSTProgram G M p
        (globalSpineOrbitSeed G M p).sourceIndex) :
    EveryHodgeClassIsFiniteRationalCombination H := by
  let P : CanonicalSpineGSTProgramFamily G M := by
    intro p j
    by_cases h : (globalSpineOrbitSeed G M p).sourceIndex = j
    · subst h
      exact hdiag p
    · exact canonicalSpineProgramOfProjectiveTwoGenerator G M p j h (R p j)
  exact gst_everyHodgeClassIsFiniteRationalCombination G M P

#check canonicalSpineProgramOfProjectiveWord
#check canonicalSpineTargetCycleOfProjectiveWord
#check canonicalSpineTargetCycleOfProjectiveWord_spec
#check everyHodgeClassIsRationalAlgebraic_of_canonicalSpine_projectiveWords
#check everyHodgeClassIsFiniteRationalCombination_of_canonicalSpine_projectiveWords
#check canonicalSpineProgramOfProjectiveTwoGenerator
#check everyHodgeClassIsRationalAlgebraic_of_projectiveTwoGenerators
#check everyHodgeClassIsFiniteRationalCombination_of_projectiveTwoGenerators

#print axioms canonicalSpineTargetCycleOfProjectiveWord_spec
#print axioms everyHodgeClassIsRationalAlgebraic_of_canonicalSpine_projectiveWords
#print axioms everyHodgeClassIsFiniteRationalCombination_of_canonicalSpine_projectiveWords
#print axioms everyHodgeClassIsRationalAlgebraic_of_projectiveTwoGenerators
#print axioms everyHodgeClassIsFiniteRationalCombination_of_projectiveTwoGenerators

end GSTClassicalHodgeGSTProjectiveWordExactFinale
