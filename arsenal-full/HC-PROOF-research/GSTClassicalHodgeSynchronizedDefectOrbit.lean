import GSTClassicalHodgeGeometryFirstTwoGenerator
import GSTClassicalHodgeConcreteRankFreeGeneration
import GSTClassicalHodgeCycleOperatorNaturality
import GSTClassicalHodgeBasisCycleBridge

/-!
# GST CLASSICAL HODGE — SYNCHRONIZED DEFECT ORBITS

The fibered point-presentation model records a useful common refinement, but a
cycle-class-natural operator should not be forced to compare its Hodge action
with the total coefficient mass of a chosen point presentation.  The genuine
classical datum is the commuting cycle-class square itself.

This module therefore keeps the two mathematical faces synchronized directly:

* a native codimension-p algebraic cycle;
* an ambient rational cohomology class.

Their defect is `cycleClass(native) - classical`.  Every genuine
`CycleClassOperatorPair` acts on both faces, and its commuting square implies
that the transformed defect is exactly the cohomological image of the old
defect.  In particular zero defect propagates without any point-mass or
normalization hypothesis.

The geometry-first two-generator GST construction already supplies the exact
rank-free Hodge matrix-unit word.  We mirror that word on the native cycle
operators, package the two sides into a genuine operator pair, and obtain a
native target-basis cycle from any zero-defect source state.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeSynchronizedDefectOrbit

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeTwoGeneratorNativeArsenal
open GSTClassicalHodgeUniversalTwoSlotNativeClosure
open GSTClassicalHodgeConcreteRankFreeGeneration
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeNativeOperatorCohomologyRealization
open GSTClassicalHodgeGeometryFirstTwoGenerator

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

abbrev NativeCycles (V : SmoothProjectiveComplexScheme) (p : Nat) :=
  codimensionCycles V.X p
abbrev AmbientCoh {V : SmoothProjectiveComplexScheme}
    (H : HodgeBigradedBettiData V) (p : Nat) :=
  RationalSingularCohomology H.analytification (2 * p)
abbrev HodgeFiber (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) (p : Nat) :=
  ClassicalHodgeFiber V H p

/-! ## Operator-pair algebra -/

/-- Identity cycle/cohomology pair. -/
noncomputable def pairId : CycleClassOperatorPair V H p where
  cycleOperator := LinearMap.id
  cohomologyOperator := LinearMap.id
  cycleClass_natural := by
    ext Z
    rfl

/-- Difference of two genuine cycle-class-natural operator pairs. -/
noncomputable def pairSub
    (A B : CycleClassOperatorPair V H p) :
    CycleClassOperatorPair V H p where
  cycleOperator := A.cycleOperator - B.cycleOperator
  cohomologyOperator := A.cohomologyOperator - B.cohomologyOperator
  cycleClass_natural := by
    ext Z
    simp [CycleClassOperatorPair.cycleClass_cycleOperator]

/-- Composition of genuine cycle-class-natural operator pairs. -/
noncomputable def pairComp
    (A B : CycleClassOperatorPair V H p) :
    CycleClassOperatorPair V H p where
  cycleOperator := A.cycleOperator.comp B.cycleOperator
  cohomologyOperator := A.cohomologyOperator.comp B.cohomologyOperator
  cycleClass_natural := by
    ext Z
    simp [CycleClassOperatorPair.cycleClass_cycleOperator]

/-- Rational scalar multiple of a genuine operator pair. -/
noncomputable def pairSmul
    (q : ℚ) (A : CycleClassOperatorPair V H p) :
    CycleClassOperatorPair V H p where
  cycleOperator := q • A.cycleOperator
  cohomologyOperator := q • A.cohomologyOperator
  cycleClass_natural := by
    ext Z
    simp [CycleClassOperatorPair.cycleClass_cycleOperator]

/-- A geometry-first native Hodge primitive canonically determines a complete
cycle/cohomology operator pair. -/
noncomputable def primitivePair
    {T : Module.End ℚ (HodgeFiber V H p)}
    (R : NativeHodgePrimitive (V := V) (H := H) T) :
    CycleClassOperatorPair V H p where
  cycleOperator := R.cycleOperator
  cohomologyOperator := R.cohomologyOperator
  cycleClass_natural := by
    ext Z
    exact R.cycleClass_natural Z

/-- Native counterpart of the universal two-slot GST word
`D ∘ L² ∘ (I-D)`, with the same rational normalization. -/
noncomputable def geometryFirstWordPair
    {i j : ClassicalHodgeBasisIndex V H p}
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    CycleClassOperatorPair V H p :=
  pairSmul (V := V) (H := H) (p := p)
    (forwardScalar sourceSlot targetSlot : ℚ)⁻¹
    (pairComp
      (primitivePair R.code)
      (pairComp
        (primitivePair R.lefschetz)
        (pairSub pairId (primitivePair R.code))))

/-- The cohomological face of the synchronized native word is exactly the
rank-free Hodge matrix unit generated by the finite GST
projector/Lefschetz/Poincare arsenal. -/
theorem geometryFirstWordPair_on_hodge
    {i j : ClassicalHodgeBasisIndex V H p}
    (hij : i ≠ j)
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j)
    (alpha : HodgeFiber V H p) :
    (geometryFirstWordPair R).cohomologyOperator alpha.1 =
      (hodgeMatrixUnit i j alpha).1 := by
  simpa [geometryFirstWordPair, pairSmul, pairComp, pairSub, pairId,
    primitivePair, toCycleClassOperatorPair, NativeHodgePrimitive.ambient,
    GeometryFirstTwoGenerator.ambientWord,
    GeometryFirstTwoGenerator.ambientCode,
    GeometryFirstTwoGenerator.ambientLefschetz,
    GeometryFirstTwoGenerator.ambientSource] using
      R.ambientWord_on_hodge hij alpha

/-! ## Synchronized native/classical states -/

/-- A common state with a genuine native algebraic-cycle face and an ambient
classical cohomology face. -/
structure SynchronizedState where
  native : NativeCycles V p
  classical : AmbientCoh H p

/-- Classical defect of a synchronized state. -/
noncomputable def synchronizedDefect
    (S : SynchronizedState (V := V) (H := H) (p := p)) :
    AmbientCoh H p :=
  H.cycleClass p S.native - S.classical

/-- Apply a genuine cycle-class-natural pair to both synchronized faces. -/
noncomputable def SynchronizedState.map
    (T : CycleClassOperatorPair V H p)
    (S : SynchronizedState (V := V) (H := H) (p := p)) :
    SynchronizedState (V := V) (H := H) (p := p) where
  native := T.cycleOperator S.native
  classical := T.cohomologyOperator S.classical

/-- **SYNCHRONIZED DEFECT EQUIVARIANCE.**  The defect after a genuine operator
pair is exactly the cohomological image of the old defect. -/
theorem synchronizedDefect_map
    (T : CycleClassOperatorPair V H p)
    (S : SynchronizedState (V := V) (H := H) (p := p)) :
    synchronizedDefect (S.map T) =
      T.cohomologyOperator (synchronizedDefect S) := by
  unfold synchronizedDefect SynchronizedState.map
  rw [T.cycleClass_cycleOperator]
  exact (T.cohomologyOperator.map_sub _ _).symm

/-- Zero defect propagates through every genuine synchronized transport. -/
theorem synchronizedDefect_map_eq_zero
    (T : CycleClassOperatorPair V H p)
    (S : SynchronizedState (V := V) (H := H) (p := p))
    (hS : synchronizedDefect S = 0) :
    synchronizedDefect (S.map T) = 0 := by
  rw [synchronizedDefect_map, hS, map_zero]

/-- Build a synchronized zero-defect state from an actual native cycle whose
class is a genuine Hodge vector. -/
noncomputable def synchronizedStateOfCycle
    (Z : NativeCycles V p)
    (alpha : HodgeFiber V H p)
    (hZ : H.cycleClass p Z = alpha.1) :
    SynchronizedState (V := V) (H := H) (p := p) where
  native := Z
  classical := alpha.1

@[simp]
theorem synchronizedStateOfCycle_defect
    (Z : NativeCycles V p)
    (alpha : HodgeFiber V H p)
    (hZ : H.cycleClass p Z = alpha.1) :
    synchronizedDefect (synchronizedStateOfCycle Z alpha hZ) = 0 := by
  simp [synchronizedDefect, synchronizedStateOfCycle, hZ]

/-! ## Limitless orbit extraction from one arbitrary nonzero algebraic state -/

/-- One arbitrary nonzero algebraic Hodge state.  It need not already be a
basis direction and it need not be a point cycle. -/
structure NativeHodgeOrbitSeed where
  cycle : NativeCycles V p
  hodge : HodgeFiber V H p
  hodge_ne_zero : hodge ≠ 0
  class_eq : H.cycleClass p cycle = hodge.1

namespace NativeHodgeOrbitSeed

/-- Live source coordinate selected canonically from the unrestricted Hodge
basis support of the seed. -/
noncomputable def sourceIndex
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) :
    ClassicalHodgeBasisIndex V H p :=
  (chosenLiveSource S.hodge S.hodge_ne_zero).1

/-- The selected source coefficient is nonzero. -/
theorem sourceCoefficient_ne_zero
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) :
    (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex ≠ 0 := by
  exact chosenLiveSource_coefficient_ne_zero S.hodge S.hodge_ne_zero

/-- Apply the genuine geometry-first GST word from the selected live source to
an arbitrary target sheet and normalize by the nonzero live source
coefficient.  The result is an actual native codimension-p cycle. -/
noncomputable def targetCycle
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (R : GeometryFirstTwoGenerator (V := V) (H := H) S.sourceIndex j) :
    NativeCycles V p :=
  let c := (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex
  c⁻¹ • (geometryFirstWordPair R).cycleOperator S.cycle

/-- **LIMITLESS NATIVE ORBIT EXTRACTION.**  The normalized geometry-first GST
word produces an actual native cycle representing any requested genuine Hodge
basis vector. -/
theorem targetCycle_spec
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (hij : S.sourceIndex ≠ j)
    (R : GeometryFirstTwoGenerator (V := V) (H := H) S.sourceIndex j) :
    H.cycleClass p (S.targetCycle j R) =
      (classicalHodgeBasis V H p j).1 := by
  let c := (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex
  have hc : c ≠ 0 := S.sourceCoefficient_ne_zero
  have hpair := (geometryFirstWordPair R).cycleClass_cycleOperator S.cycle
  rw [S.class_eq, geometryFirstWordPair_on_hodge hij R S.hodge] at hpair
  have hmatrix :
      (hodgeMatrixUnit S.sourceIndex j S.hodge).1 =
        c • (classicalHodgeBasis V H p j).1 := by
    simp [hodgeMatrixUnit_apply, hodgeCoordinate, sourceIndex, c]
  rw [hmatrix] at hpair
  unfold targetCycle
  rw [LinearMap.map_smul, hpair]
  simp [c, hc]

/-- One nonzero algebraic Hodge state plus geometry-first realizations of the
limitless two-generator word produces a genuine basis-cycle bridge.
The diagonal sheet is the code observable itself (normalized by the nonzero
live source coefficient); the off-diagonal sheets are the geometry-first
universal word. -/
noncomputable def basisCycleBridge
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      GeometryFirstTwoGenerator (V := V) (H := H) S.sourceIndex j) :
    HodgeConjecture.HodgeBasisCycleBridge V H p where
  basisCycle j :=
    if S.sourceIndex = j then
      ((classicalHodgeBasis V H p).repr S.hodge S.sourceIndex)⁻¹ •
        (R j).code.cycleOperator S.cycle
    else S.targetCycle j (R j)
  basisCycle_spec j := by
    by_cases hij : S.sourceIndex = j
    · rw [if_pos hij, LinearMap.map_smul]
      have hc : (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex ≠ 0 :=
        S.sourceCoefficient_ne_zero
      have hpair := (primitivePair (R j).code).cycleClass_cycleOperator S.cycle
      rw [S.class_eq] at hpair
      have hcoh : (primitivePair (R j).code).cohomologyOperator S.hodge.1 =
          (twoSlotCodeHodge S.sourceIndex j S.hodge).1 := by
        simpa [primitivePair, toCycleClassOperatorPair,
          NativeHodgePrimitive.ambient] using
          (R j).code.ambient_on_hodge S.hodge
      rw [hcoh] at hpair
      have hdiag : (twoSlotCodeHodge S.sourceIndex j S.hodge).1 =
          ((classicalHodgeBasis V H p).repr S.hodge S.sourceIndex) •
            (classicalHodgeBasis V H p j).1 := by
        subst j
        simp [twoSlotCodeHodge, twoSlotHodgeOperator,
          liftFiniteHodgeOperator, finiteHodgeRead, finiteHodgeWrite,
          twoSlotCode, sourceSlot, targetSlot, pairBasisIndex,
          hodgeMatrixUnit_apply, hodgeCoordinate_basis_self, hodgeCoordinate]
      rw [hdiag] at hpair
      rw [show (R j).code.cycleOperator S.cycle =
          (primitivePair (R j).code).cycleOperator S.cycle from rfl]
      rw [hpair, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rfl
    · rw [if_neg hij]
      exact S.targetCycle_spec j hij (R j)

/-- Weight-p classical landing from one arbitrary nonzero algebraic Hodge
state and the genuine limitless GST two-generator externalization. -/
theorem hodge_weight
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      GeometryFirstTwoGenerator (V := V) (H := H) S.sourceIndex j) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  intro alpha halpha
  exact HodgeConjecture.hodge_class_has_cycle_of_basis_bridge
    V H (S.basisCycleBridge R) alpha halpha

end NativeHodgeOrbitSeed

/-- Family crown: one arbitrary nonzero algebraic Hodge state in every nonzero
weight, together with the geometry-first limitless GST word, closes the exact
Stage-2G Hodge statement. -/
theorem bigradedBettiHodge_of_synchronized_limitless_orbits
    (seed : ∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥ →
        NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (R : ∀ p : Nat,
      ∀ hp : rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        GeometryFirstTwoGenerator
          (V := V) (H := H) (seed p hp).sourceIndex j) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  by_cases hp : rationalHodgeSubspace (H.hodgeBigrading p) = ⊥
  · have : alpha = 0 := by
      have ha : alpha ∈ (⊥ : Submodule ℚ (AmbientCoh H p)) := by
        simpa [hp] using halpha
      simpa using ha
    subst alpha
    exact ⟨0, by simp⟩
  · exact (seed p hp).hodge_weight (R p hp) halpha

#check pairId
#check pairSub
#check pairComp
#check pairSmul
#check geometryFirstWordPair
#check geometryFirstWordPair_on_hodge
#check SynchronizedState
#check synchronizedDefect_map
#check NativeHodgeOrbitSeed
#check NativeHodgeOrbitSeed.targetCycle
#check NativeHodgeOrbitSeed.targetCycle_spec
#check NativeHodgeOrbitSeed.basisCycleBridge
#check bigradedBettiHodge_of_synchronized_limitless_orbits

#print axioms synchronizedDefect_map
#print axioms NativeHodgeOrbitSeed.targetCycle_spec
#print axioms NativeHodgeOrbitSeed.hodge_weight
#print axioms bigradedBettiHodge_of_synchronized_limitless_orbits

end GSTClassicalHodgeSynchronizedDefectOrbit

