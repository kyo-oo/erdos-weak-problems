import GSTClassicalHodgeFiberedNativeTensorArsenal
import GSTNativeCodimensionCyclePresentation

/-!
# GST CLASSICAL HODGE — NATIVE DESCENT SEPARATION

The fibered native pullback has two independent coordinates: Hodge
multiplicity and genuine projective-cycle position.  A final classical proof
must never identify those two coordinates by forgetting one of them.

This file isolates the exact descent principle.  Operators lifted from genuine
native cycle operators descend tautologically through `toNativeCycle`.  By
contrast, a bare multiplicity matrix unit does not descend whenever two
multiplicity labels lie over the same nonzero native point atom.  Therefore a
multiplicity transfer used in the classical landing must be accompanied by a
genuine geometric correspondence on the native face; the limitless tensor
algebra itself keeps those factors separate.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFiberedNativeDescentSeparation

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiberedNativeOperatorLift
open GSTClassicalHodgeFiberedNativeTensorArsenal

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A fibered operator genuinely descends to the native cycle universe when
its native face is induced by one honest native cycle endomorphism. -/
def NativeDescends
    (T : Module.End ℚ (FiberedNativeAddress V H p)) : Prop :=
  ∃ A : Module.End ℚ (codimensionCycles V.X p),
    ∀ Φ : FiberedNativeAddress V H p,
      toNativeCycle V H p (T Φ) =
        A (toNativeCycle V H p Φ)

/-- Every operator obtained by lifting a genuine native operator descends by
construction. -/
theorem liftNativeOperator_descends
    (A : Module.End ℚ (codimensionCycles V.X p)) :
    NativeDescends (V := V) (H := H) (p := p) (liftNativeOperator A) := by
  refine ⟨A, ?_⟩
  intro Φ
  exact toNativeCycle_liftNativeOperator A Φ

/-- Native descent forces preservation of the kernel of the native-face map. -/
theorem nativeDescends_preserves_nativeKernel
    {T : Module.End ℚ (FiberedNativeAddress V H p)}
    (hT : NativeDescends (V := V) (H := H) (p := p) T)
    {Φ : FiberedNativeAddress V H p}
    (hΦ : toNativeCycle V H p Φ = 0) :
    toNativeCycle V H p (T Φ) = 0 := by
  rcases hT with ⟨A, hA⟩
  rw [hA, hΦ]
  exact A.map_zero

/-- A genuine unit point cycle is nonzero in the native algebraic-cycle
module. -/
theorem codimensionPointCycle_ne_zero
    (x : CodimensionPoint V.X p) :
    codimensionPointCycle V.X p x ≠ 0 := by
  intro h
  have hx := congrArg
    (fun Z : codimensionCycles V.X p =>
      ((Z : AlgebraicCycle V.X ℚ) x.1)) h
  simpa [codimensionPointCycle,
    Function.locallyFinsuppWithin.single_apply] using hx

/-- Two different multiplicity labels over the same native point have equal
native faces. -/
theorem atom_sub_atom_nativeFace_zero
    (i k : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    toNativeCycle V H p
      (atom V H p i x - atom V H p k x) = 0 := by
  simp [toNativeCycle_atom]

/-- A bare multiplicity matrix unit separates those two labels while leaving
the projective point untouched.  Hence its image has a nonzero native face. -/
theorem multiplicityMatrixUnit_kernelWitness
    (i j k : ClassicalHodgeBasisIndex V H p)
    (hki : k ≠ i)
    (x : CodimensionPoint V.X p) :
    toNativeCycle V H p
      (multiplicityMatrixUnit i j
        (atom V H p i x - atom V H p k x)) =
      codimensionPointCycle V.X p x := by
  rw [map_sub]
  rw [multiplicityMatrixUnit_atom_source]
  rw [multiplicityMatrixUnit_atom_other i j k hki x]
  simp [toNativeCycle_atom]

/-- **MULTIPLICITY/NATIVE SEPARATION THEOREM.**
If the Hodge multiplicity fiber contains two distinct labels over a genuine
codimension-p point, a bare Hodge-label matrix unit cannot descend through the
native-cycle face.  A genuine projective correspondence must supply the native
part of the transfer. -/
theorem multiplicityMatrixUnit_not_nativeDescends
    (i j k : ClassicalHodgeBasisIndex V H p)
    (hki : k ≠ i)
    (x : CodimensionPoint V.X p) :
    ¬ NativeDescends (V := V) (H := H) (p := p)
      (multiplicityMatrixUnit i j) := by
  intro hdesc
  let Φ : FiberedNativeAddress V H p :=
    atom V H p i x - atom V H p k x
  have hzero : toNativeCycle V H p Φ = 0 := by
    simpa [Φ] using atom_sub_atom_nativeFace_zero (V := V) (H := H) i k x
  have himageZero :=
    nativeDescends_preserves_nativeKernel
      (V := V) (H := H) (p := p) hdesc hzero
  have himagePoint :
      toNativeCycle V H p (multiplicityMatrixUnit i j Φ) =
        codimensionPointCycle V.X p x := by
    simpa [Φ] using
      multiplicityMatrixUnit_kernelWitness
        (V := V) (H := H) i j k hki x
  rw [himagePoint] at himageZero
  exact codimensionPointCycle_ne_zero (V := V) (p := p) x himageZero

/-- The same separation applies to a tensor word whenever its native operator
acts nontrivially on the shared point atom. -/
theorem tensorWord_not_nativeDescends_of_nonzero
    (i j k : ClassicalHodgeBasisIndex V H p)
    (hki : k ≠ i)
    (A : Module.End ℚ (codimensionCycles V.X p))
    (x : CodimensionPoint V.X p)
    (hAx : A (codimensionPointCycle V.X p x) ≠ 0) :
    ¬ NativeDescends (V := V) (H := H) (p := p)
      (tensorWord i j A) := by
  intro hdesc
  let Φ : FiberedNativeAddress V H p :=
    atom V H p i x - atom V H p k x
  have hzero : toNativeCycle V H p Φ = 0 := by
    simpa [Φ] using atom_sub_atom_nativeFace_zero (V := V) (H := H) i k x
  have himageZero :=
    nativeDescends_preserves_nativeKernel
      (V := V) (H := H) (p := p) hdesc hzero
  have hi :
      toNativeCycle V H p (tensorWord i j A (atom V H p i x)) =
        A (codimensionPointCycle V.X p x) :=
    tensorWord_nativeFace_atom_source i j A x
  have hk : tensorWord i j A (atom V H p k x) = 0 := by
    unfold tensorWord
    rw [LinearMap.comp_apply, liftNativeOperator_atom,
      multiplicityMatrixUnit_labelPresentation_other i j k hki]
  have himage :
      toNativeCycle V H p (tensorWord i j A Φ) =
        A (codimensionPointCycle V.X p x) := by
    simp only [Φ, map_sub, hi, hk, map_zero, sub_zero]
  rw [himage] at himageZero
  exact hAx himageZero

#check NativeDescends
#check liftNativeOperator_descends
#check nativeDescends_preserves_nativeKernel
#check multiplicityMatrixUnit_not_nativeDescends
#check tensorWord_not_nativeDescends_of_nonzero

#print axioms liftNativeOperator_descends
#print axioms nativeDescends_preserves_nativeKernel
#print axioms multiplicityMatrixUnit_not_nativeDescends
#print axioms tensorWord_not_nativeDescends_of_nonzero

end GSTClassicalHodgeFiberedNativeDescentSeparation
