import GSTClassicalHodgeProjectiveWordOrbit
import GSTClassicalHodgeProjectiveTwoGeneratorExternalization
import GSTClassicalHodgeRankFreePrimitiveGeneration

/-!
# GST CLASSICAL HODGE — PROJECTIVE TWO-GENERATOR -> WORD COMPILER

The earlier externalization layer asked for two genuine projective primitives:
a code observable and a two-step Lefschetz action.  The new projective word
algebra can compile those primitives into the exact noncommutative GST transfer
word instead of carrying the two-generator package as an opaque final input.

This file proves that compilation is faithful on native cycles and, therefore,
on every synchronized live source.  In particular every old
`ProjectiveTwoGenerator` automatically supplies the strictly smaller
`ProjectiveWordLiveSourceTarget` interface.

The result is a compatibility theorem, but also a structural strengthening:
future geometry may construct the final word directly without realizing either
primitive on the whole Hodge fiber.  The old route remains a sufficient special
case of the new one.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeProjectiveGeneratorWordCompiler

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeGeometryFirstTwoGenerator
open GSTClassicalHodgeProjectiveTwoGeneratorExternalization
open GSTClassicalHodgeProjectiveWordOrbit

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Compile the exact normalized GST word

    scalar^-1 * code o lefschetz o (id - code)

from the two actual projective self-maps. -/
noncomputable def compileProjectiveTwoGenerator
    {i j : ClassicalHodgeBasisIndex V H p}
    (R : ProjectiveTwoGenerator (V := V) (H := H) i j) :
    ProjectiveOperatorWord V p :=
  .smul (forwardScalar sourceSlot targetSlot : ℚ)⁻¹
    (.comp (.geometric R.code.map)
      (.comp (.geometric R.lefschetz.map)
        (.add .id (.smul (-1) (.geometric R.code.map)))))

/-- Native interpretation of the compiled word is exactly the native face of
the already-verified geometry-first GST word. -/
theorem compileProjectiveTwoGenerator_eval
    {i j : ClassicalHodgeBasisIndex V H p}
    (R : ProjectiveTwoGenerator (V := V) (H := H) i j) :
    (compileProjectiveTwoGenerator R).eval =
      (geometryFirstWordPair R.toGeometryFirst).cycleOperator := by
  ext Z
  simp [compileProjectiveTwoGenerator,
    ProjectiveOperatorWord.eval,
    geometryFirstWordPair, pairSmul, pairComp, pairSub, pairId,
    primitivePair,
    ProjectiveTwoGenerator.toGeometryFirst,
    ProjectivePrimitiveRealization.toNativeHodgePrimitive]
  ring

/-- On any synchronized live source, the compiled geometric word has the exact
rank-one target action required by the new one-source interface. -/
theorem compileProjectiveTwoGenerator_source_action
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (hij : S.sourceIndex ≠ j)
    (R : ProjectiveTwoGenerator (V := V) (H := H) S.sourceIndex j) :
    ((compileProjectiveTwoGenerator R).operatorPair G).cohomologyOperator
        S.hodge.1 =
      (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex •
        (classicalHodgeBasis V H p j).1 := by
  let T := R.toGeometryFirst
  calc
    ((compileProjectiveTwoGenerator R).operatorPair G).cohomologyOperator
        S.hodge.1 =
      H.cycleClass p ((compileProjectiveTwoGenerator R).eval S.cycle) := by
        rw [← S.class_eq]
        exact ((compileProjectiveTwoGenerator R).cycleClass_eval G S.cycle).symm
    _ = H.cycleClass p
        ((geometryFirstWordPair T).cycleOperator S.cycle) := by
          rw [compileProjectiveTwoGenerator_eval R]
    _ = (geometryFirstWordPair T).cohomologyOperator
        (H.cycleClass p S.cycle) := by
          exact (geometryFirstWordPair T).cycleClass_cycleOperator S.cycle
    _ = (geometryFirstWordPair T).cohomologyOperator S.hodge.1 := by
          rw [S.class_eq]
    _ = (hodgeMatrixUnit S.sourceIndex j S.hodge).1 := by
          exact geometryFirstWordPair_on_hodge hij T S.hodge
    _ = (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex •
        (classicalHodgeBasis V H p j).1 := by
          simp [hodgeMatrixUnit_apply, hodgeCoordinate,
            Submodule.coe_smul_of_tower]

/-- Every old projective two-generator realization compiles to the new, weaker
one-word/one-source target certificate. -/
noncomputable def ProjectiveTwoGenerator.toWordLiveSourceTarget
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (hij : S.sourceIndex ≠ j)
    (R : ProjectiveTwoGenerator (V := V) (H := H) S.sourceIndex j) :
    ProjectiveWordLiveSourceTarget G S j where
  word := compileProjectiveTwoGenerator R
  source_action := compileProjectiveTwoGenerator_source_action G S j hij R

/-- The new fixed-weight word route therefore subsumes the previous
projective-two-generator route. -/
theorem hodge_weight_of_projective_two_generators_via_words
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      ProjectiveTwoGenerator (V := V) (H := H) S.sourceIndex j)
    (hdiag : ProjectiveWordLiveSourceTarget G S S.sourceIndex) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  refine hodge_weight_of_projective_word_live_source G S ?_
  intro j
  by_cases h : S.sourceIndex = j
  · subst h; exact hdiag
  · exact ProjectiveTwoGenerator.toWordLiveSourceTarget G S j h (R j)

#check compileProjectiveTwoGenerator
#check compileProjectiveTwoGenerator_eval
#check compileProjectiveTwoGenerator_source_action
#check ProjectiveTwoGenerator.toWordLiveSourceTarget
#check hodge_weight_of_projective_two_generators_via_words

#print axioms compileProjectiveTwoGenerator_eval
#print axioms compileProjectiveTwoGenerator_source_action
#print axioms ProjectiveTwoGenerator.toWordLiveSourceTarget
#print axioms hodge_weight_of_projective_two_generators_via_words

end GSTClassicalHodgeProjectiveGeneratorWordCompiler