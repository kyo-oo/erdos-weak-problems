import GSTClassicalHodgeTwoGeneratorNativeArsenal
import GSTClassicalHodgeNativeOperatorCohomologyRealization
import GSTClassicalHodgeRankFreeArsenalIrreducibility
import GSTClassicalHodgeAtomicOperatorAlgebra
import GSTNativeCodimensionCyclePresentation
import GSTClassicalHodgeGeneratorwiseAtomicStability

/-!
# GST CLASSICAL HODGE — GEOMETRY-FIRST TWO-GENERATOR EXTERNALIZATION

The previous two-generator reduction identified the entire limitless Hodge
arsenal with two primitive Hodge-fiber operators: the two-slot code observable
and the exact two-step Lefschetz transport.  This file reverses the direction
of externalization.

We do not first choose an arbitrary ambient extension and then ask geometry to
realize it.  Instead a native operator on actual codimension-p algebraic cycles
is primary.  Kernel stability makes its action well-defined on the actual
cycle-class range, and the native-operator realization theorem extends that
action to genuine rational singular cohomology.  Native point lifts are then
a theorem, not an input.

A primitive is accepted only after proving that this geometry-generated
ambient action restricts on the genuine rational (p,p) fiber to the desired
GST primitive.  Two such primitives generate the universal normalized two-slot
word.  The existing limitless two-slot theorem identifies that word with the
rank-free matrix unit.  Therefore the actual algebraic Hodge subspace is
invariant under every matrix unit as soon as the two primitive native
geometric operators have the required Hodge restrictions.

This file contains no Hodge-surjectivity assumption and no basis-cycle choice.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeNativeGeneratorNaturality
open GSTClassicalHodgeAtomicOperatorAlgebra
open GSTClassicalHodgeUniversalTwoSlotNativeClosure
open GSTClassicalHodgeTwoGeneratorNativeArsenal
open GSTClassicalHodgeNativeOperatorCohomologyRealization
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeExplicitArsenalGeneration
open GSTClassicalHodgeGeneratorwiseAtomicStability

namespace GSTClassicalHodgeGeometryFirstTwoGenerator

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

/-- A kernel-stable native algebraic-cycle operator automatically gives native
point lifts for the ambient cohomology operator manufactured from it. -/
theorem kernelStable_ambient_hasNativePointLifts
    (A : NativeCycles V p →ₗ[ℚ] NativeCycles V p)
    (hA : KernelStable (H := H) A) :
    HasNativePointLifts (p := p) (cl := H.cycleClass p)
      (ambientOperator (H := H) A hA) := by
  intro x
  refine ⟨A (codimensionPointCycle V.X p x), ?_⟩
  symm
  exact cycleClass_ambientOperator (H := H) A hA
    (codimensionPointCycle V.X p x)

/-- Geometry-first realization of one Hodge-fiber primitive.

The native cycle operator acts on actual algebraic cycles. Its cohomological
action is the genuinely realized ambient geometric operator, accompanied by
the exact cycle-class commuting square. Kernel preservation follows from
this square, but does NOT determine the action outside the algebraic range:
the canonical image retraction would kill transcendental directions and
must not be substituted for genuine Betti functoriality. -/
structure NativeHodgePrimitive
    (T : Module.End ℚ (HodgeFiber V H p)) where
  cycleOperator : NativeCycles V p →ₗ[ℚ] NativeCycles V p
  cohomologyOperator : AmbientCoh H p →ₗ[ℚ] AmbientCoh H p
  cycleClass_natural :
    ∀ Z : NativeCycles V p,
      H.cycleClass p (cycleOperator Z) =
        cohomologyOperator (H.cycleClass p Z)
  restricts_to_hodge :
    ∀ alpha : HodgeFiber V H p,
      cohomologyOperator alpha.1 = (T alpha).1

namespace NativeHodgePrimitive

variable {T : Module.End ℚ (HodgeFiber V H p)}

/-- Kernel stability is derived from the actual geometric commuting square,
rather than supplied as an independent hypothesis. -/
theorem kernelStable
    (R : NativeHodgePrimitive (V := V) (H := H) T) :
    KernelStable (H := H) R.cycleOperator := by
  intro Z hZ
  rw [R.cycleClass_natural Z, hZ]
  exact R.cohomologyOperator.map_zero

/-- The true ambient geometric action, not the projection onto algebraic
classes. These coincide on the algebraic range, but not necessarily elsewhere. -/
noncomputable def ambient
    (R : NativeHodgePrimitive (V := V) (H := H) T) :
    AmbientCoh H p →ₗ[ℚ] AmbientCoh H p :=
  R.cohomologyOperator

/-- Native point lifts come directly from the geometric commuting square.
No arbitrary choice of an off-range extension is used. -/
theorem hasNativePointLifts
    (R : NativeHodgePrimitive (V := V) (H := H) T) :
    HasNativePointLifts (p := p) (cl := H.cycleClass p) R.ambient := by
  intro x
  refine ⟨R.cycleOperator (codimensionPointCycle V.X p x), ?_⟩
  exact R.cycleClass_natural _

/-- The actual geometric cohomology action has the prescribed Hodge action. -/
@[simp]
theorem ambient_on_hodge
    (R : NativeHodgePrimitive (V := V) (H := H) T)
    (alpha : HodgeFiber V H p) :
    R.ambient alpha.1 = (T alpha).1 :=
  R.restricts_to_hodge alpha

end NativeHodgePrimitive

/-- The two genuinely noncommuting native geometric primitives.

Unlike `TwoGeneratorNative`, this structure stores native algebraic-cycle
operators.  Their ambient cohomological actions are derived from kernel
stability. -/
structure GeometryFirstTwoGenerator
    (i j : ClassicalHodgeBasisIndex V H p) where
  code : NativeHodgePrimitive (V := V) (H := H)
    (twoSlotCodeHodge i j)
  lefschetz : NativeHodgePrimitive (V := V) (H := H)
    (twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2))

namespace GeometryFirstTwoGenerator

variable {i j : ClassicalHodgeBasisIndex V H p}

/-- Geometry-generated code action on ambient rational cohomology. -/
noncomputable def ambientCode
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    AmbientCoh H p →ₗ[ℚ] AmbientCoh H p :=
  R.code.ambient

/-- Geometry-generated two-step Lefschetz action on ambient cohomology. -/
noncomputable def ambientLefschetz
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    AmbientCoh H p →ₗ[ℚ] AmbientCoh H p :=
  R.lefschetz.ambient

/-- Source projector generated polynomially from the geometry-first code
observable. -/
noncomputable def ambientSource
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    AmbientCoh H p →ₗ[ℚ] AmbientCoh H p :=
  LinearMap.id - R.ambientCode

/-- Universal normalized two-slot transfer word generated entirely from the
two native geometric primitives. -/
noncomputable def ambientWord
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    AmbientCoh H p →ₗ[ℚ] AmbientCoh H p :=
  (forwardScalar sourceSlot targetSlot : ℚ)⁻¹ •
    (R.ambientCode.comp (R.ambientLefschetz.comp R.ambientSource))

/-- Identity-minus-code remains native-natural. -/
theorem source_hasNativePointLifts
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    HasNativePointLifts (p := p) (cl := H.cycleClass p) R.ambientSource := by
  rw [← smoothProjective_atomicStable_iff_nativePointLifts]
  exact atomicSpanStable_sub atomicSpanStable_id
    ((smoothProjective_atomicStable_iff_nativePointLifts
      (R.ambientCode)).2 R.code.hasNativePointLifts)

/-- The universal geometry-first word is native-natural by pure operator
closure; no basis cycle is chosen. -/
theorem ambientWord_hasNativePointLifts
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    HasNativePointLifts (p := p) (cl := H.cycleClass p) R.ambientWord := by
  unfold ambientWord
  apply GSTClassicalHodgeNativeGeneratorNaturality.HasNativePointLifts.smul
  exact nativePointLifts_comp R.code.hasNativePointLifts
    (nativePointLifts_comp R.lefschetz.hasNativePointLifts
      R.source_hasNativePointLifts)

/-- On the genuine Hodge fiber the geometry-first source operator is exactly
the source sheet projector. -/
theorem ambientSource_on_hodge
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j)
    (alpha : HodgeFiber V H p) :
    R.ambientSource alpha.1 =
      ((LinearMap.id - twoSlotCodeHodge i j :
        ClassicalHodgeFiber V H p →ₗ[ℚ] ClassicalHodgeFiber V H p) alpha).1 := by
  simp [ambientSource, ambientCode, NativeHodgePrimitive.ambient_on_hodge]

/-- **GEOMETRY-FIRST UNIVERSAL WORD.**
On the genuine Hodge fiber the native-geometric word is exactly the rank-free
matrix unit `E_{i,j}` generated by the full GST projector/Lefschetz/Poincare
arsenal. -/
theorem ambientWord_on_hodge
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j)
    (hij : i ≠ j)
    (alpha : HodgeFiber V H p) :
    R.ambientWord alpha.1 = (hodgeMatrixUnit i j alpha).1 := by
  let src : HodgeFiber V H p :=
    ((LinearMap.id - twoSlotCodeHodge i j :
      ClassicalHodgeFiber V H p →ₗ[ℚ] ClassicalHodgeFiber V H p) alpha)
  let mid : HodgeFiber V H p :=
    twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2) src
  have hsrc : R.ambientSource alpha.1 = src.1 := by
    simpa [src] using R.ambientSource_on_hodge alpha
  have hmid : R.ambientLefschetz src.1 = mid.1 := by
    simpa [ambientLefschetz, mid] using R.lefschetz.ambient_on_hodge src
  have htgt : R.ambientCode mid.1 = (twoSlotCodeHodge i j mid).1 := by
    simpa [ambientCode] using R.code.ambient_on_hodge mid
  unfold ambientWord
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [hsrc, hmid, htgt]
  have h01 : hodgeCoordinate i (classicalHodgeBasis V H p j) = 0 :=
    hodgeCoordinate_basis_other i j hij
  have h10 : hodgeCoordinate j (classicalHodgeBasis V H p i) = 0 :=
    hodgeCoordinate_basis_other j i (Ne.symm hij)
  have hrw : ∀ w : RationalPureWindow 2,
      finiteHodgeRead (pairBasisIndex i j)
        (finiteHodgeWrite (pairBasisIndex i j) w) = w := by
    intro w
    funext r
    fin_cases r
    · simp [finiteHodgeRead, finiteHodgeWrite, sourceSlot, targetSlot,
        pairBasisIndex, h01]
    · simp [finiteHodgeRead, finiteHodgeWrite, sourceSlot, targetSlot,
        pairBasisIndex, h10]
  have hLval : (GSTTruncatedWorldCohomologyRing.worldAct 2 2
      ((GSTTruncatedWorldCohomologyRing.L 2 2) ^ 2)
      (GSTWorldPoincareDuality.worldBasis
        (GSTGlobalPureHodgeCosmology.pureDiagonalState (0 : Fin 2)))
      (GSTGlobalPureHodgeCosmology.pureDiagonalState (1 : Fin 2))) =
      (2 : ℤ) :=
    gst_forward_scalar_receipt (N := 2) (p := sourceSlot) (q := targetSlot)
      (by decide)
  have hfs : (forwardScalar (N := 2) (0 : Fin 2) (1 : Fin 2) : ℚ) = 2 := by
    exact_mod_cast
      (show forwardScalar (N := 2) (0 : Fin 2) (1 : Fin 2) = 2 from by decide)
  simp [src, mid, twoSlotCodeHodge, twoSlotHodgeOperator,
    liftFiniteHodgeOperator, finiteHodgeRead, finiteHodgeWrite,
    pureMatrixUnit, rationalPureBasis, diagonalLefschetzQ, sheetProjectorQ,
    twoSlotCode, hodgeMatrixUnit_apply, sourceSlot, targetSlot, hrw,
    pairBasisIndex, h01, h10, hodgeCoordinate_basis_self, hLval,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply]
  rw [hfs]
  norm_num
  rw [one_div, smul_smul, ← mul_assoc,
    inv_mul_cancel₀ (by norm_num : (2:ℚ) ≠ 0), one_mul]

/-- The code primitive realizes the diagonal matrix unit on genuine Hodge
classes. The diagonal route is distinct from the normalized off-diagonal
Lefschetz word, whose proof explicitly requires `i ≠ j`. -/
theorem ambientCode_on_hodge_of_eq
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j)
    (hij : i = j)
    (alpha : HodgeFiber V H p) :
    R.ambientCode alpha.1 = (hodgeMatrixUnit i j alpha).1 := by
  subst j
  calc
    R.ambientCode alpha.1 = (twoSlotCodeHodge i i alpha).1 := by
      simpa [ambientCode] using R.code.ambient_on_hodge alpha
    _ = (hodgeMatrixUnit i i alpha).1 := by
      simp [twoSlotCodeHodge, twoSlotHodgeOperator,
        liftFiniteHodgeOperator, finiteHodgeRead, finiteHodgeWrite,
        pureMatrixUnit, rationalPureBasis, twoSlotCode, sourceSlot,
        targetSlot, pairBasisIndex, hodgeMatrixUnit_apply,
        hodgeCoordinate_basis_self]

/-- Every geometry-first two-generator realization forces the corresponding
rank-free matrix unit to preserve the actual algebraic Hodge subspace.
The diagonal case is the code observable itself (which picks the target
sheet); the off-diagonal case is the geometry-first universal word. -/
theorem matrixUnit_mem_algebraic
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j)
    (alpha : HodgeFiber V H p)
    (halpha : alpha ∈ AlgebraicHodgeSubspace V H p) :
    hodgeMatrixUnit i j alpha ∈ AlgebraicHodgeSubspace V H p := by
  by_cases hij : i = j
  · subst j
    have hstable : AtomicSpanStable (p := p) (cl := H.cycleClass p)
        R.ambientCode :=
      (smoothProjective_atomicStable_iff_nativePointLifts
        (R.ambientCode)).2 R.code.hasNativePointLifts
    have himage := hstable alpha.1 halpha
    rw [show R.ambientCode alpha.1 = (twoSlotCodeHodge i i alpha).1 from
      R.code.ambient_on_hodge alpha] at himage
    have hdiag : (twoSlotCodeHodge i i alpha).1 =
        (hodgeMatrixUnit i i alpha).1 := by
      simp [twoSlotCodeHodge, twoSlotHodgeOperator,
        liftFiniteHodgeOperator, finiteHodgeRead, finiteHodgeWrite,
        pureMatrixUnit, rationalPureBasis, twoSlotCode, sourceSlot,
        targetSlot, pairBasisIndex, hodgeMatrixUnit_apply,
        hodgeCoordinate_basis_self]
    rw [hdiag] at himage
    exact himage
  · have hstable : AtomicSpanStable (p := p) (cl := H.cycleClass p)
        R.ambientWord :=
      (smoothProjective_atomicStable_iff_nativePointLifts
        (R.ambientWord)).2 R.ambientWord_hasNativePointLifts
    have himage := hstable alpha.1 halpha
    rw [R.ambientWord_on_hodge hij alpha] at himage
    exact himage

end GeometryFirstTwoGenerator

/-- A geometry-first realization for every ordered Hodge-basis pair gives the
full unrestricted arsenal invariance theorem. -/
theorem rankFreeArsenalInvariant_of_geometryFirstTwoGenerators
    (R : ∀ i j : ClassicalHodgeBasisIndex V H p,
      GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    RankFreeArsenalInvariant (AlgebraicHodgeSubspace V H p) := by
  intro i j alpha halpha
  exact (R i j).matrixUnit_mem_algebraic alpha halpha

/-- Consequently, once the algebraic Hodge subspace is nonzero, geometry-first
two-generator naturality saturates the entire genuine Hodge fiber. -/
theorem algebraicHodgeSubspace_eq_top_of_geometryFirstTwoGenerators
    (R : ∀ i j : ClassicalHodgeBasisIndex V H p,
      GeometryFirstTwoGenerator (V := V) (H := H) i j)
    (hne : AlgebraicHodgeSubspace V H p ≠ ⊥) :
    AlgebraicHodgeSubspace V H p = ⊤ := by
  exact rankFreeArsenalInvariant_eq_top
    (AlgebraicHodgeSubspace V H p)
    (rankFreeArsenalInvariant_of_geometryFirstTwoGenerators R)
    hne

#check kernelStable_ambient_hasNativePointLifts
#check NativeHodgePrimitive
#check NativeHodgePrimitive.ambient
#check NativeHodgePrimitive.hasNativePointLifts
#check GeometryFirstTwoGenerator
#check GeometryFirstTwoGenerator.ambientWord
#check GeometryFirstTwoGenerator.ambientWord_hasNativePointLifts
#check GeometryFirstTwoGenerator.ambientWord_on_hodge
#check GeometryFirstTwoGenerator.matrixUnit_mem_algebraic
#check rankFreeArsenalInvariant_of_geometryFirstTwoGenerators
#check algebraicHodgeSubspace_eq_top_of_geometryFirstTwoGenerators

#print axioms kernelStable_ambient_hasNativePointLifts
#print axioms GeometryFirstTwoGenerator.ambientWord_hasNativePointLifts
#print axioms GeometryFirstTwoGenerator.ambientWord_on_hodge
#print axioms GeometryFirstTwoGenerator.matrixUnit_mem_algebraic
#print axioms rankFreeArsenalInvariant_of_geometryFirstTwoGenerators
#print axioms algebraicHodgeSubspace_eq_top_of_geometryFirstTwoGenerators

end GSTClassicalHodgeGeometryFirstTwoGenerator
