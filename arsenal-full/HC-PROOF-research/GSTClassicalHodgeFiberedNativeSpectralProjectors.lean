import GSTClassicalHodgeFiberedNativeRecoordination
import GSTWorldRecoordinationGroupoid
import GSTClassicalHodgeRecoordinationArsenalCrown
import GSTClassicalHodgeFiniteSupportArsenalConjugation
import GSTNativeCodimensionCyclePresentation
import GSTClassicalHodgeFiberedTransferCompletion

/-!
# GST CLASSICAL HODGE — FIBERED NATIVE SPECTRAL PROJECTORS

The common native/classical pullback is now a genuine target of the GST code
spectral calculus.

A finite live Hodge support may be displayed in any equal-cardinality GST
shape.  Each shaped state carries its live classical coefficient on one
multiplicity-labelled genuine codimension-p point atom.  The invariant code
projector isolates one state exactly.

After summing the isolated field, all three faces agree on the same scalar:

* classical face = live coefficient times one genuine Hodge multiplicity sheet;
* native face = live coefficient times one actual codimension-p point cycle;
* limitless face = live coefficient times the established transfer generator.

Thus GST spectral isolation acts simultaneously in the classical fiber, the
native projective cycle universe, and the limitless transfer universe.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open scoped BigOperators

namespace GSTClassicalHodgeFiberedNativeSpectralProjectors

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeSupportCardinalityBridge
open GSTClassicalHodgeRecoordinationArsenalCrown
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiberedNativeRecoordination
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeNativeTransferAddressIdentification
open GSTWorldRecoordinationGroupoid
open GSTTransferBridgeV2
open GSTClassicalHodgeFiniteSupportArsenalConjugation
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedTransferCompletion

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Exact invariant-code projector on a pullback-valued shaped field. -/
def fiberedNativeCodeProj
    {N : Nat}
    (S : GSTWorldShape N) (k : Nat)
    (f : ShapeState S → FiberedNativeAddress V H p) :
    ShapeState S → FiberedNativeAddress V H p :=
  fun y => if worldCode S y = k then f y else 0

/-- The pullback-valued projector is natural under arbitrary world
recoordination for the same reason as the scalar GST projector: invariant code
is preserved exactly. -/
theorem transportFiberedNative_codeProj
    {N : Nat}
    (S T : GSTWorldShape N)
    (k : Nat)
    (f : ShapeState S → FiberedNativeAddress V H p) :
    transportFiberedNative S T (fiberedNativeCodeProj S k f) =
      fiberedNativeCodeProj T k (transportFiberedNative S T f) := by
  funext y
  have hcode :
      worldCode S ((worldRecoordinate S T).symm y) = worldCode T y := by
    rw [worldRecoordinate_inverse S T y]
    exact worldRecoordinate_code T S y
  simp only [transportFiberedNative, fiberedNativeCodeProj]
  rw [hcode]

/-- A code projector keyed by one shaped state isolates exactly that state,
because `shapeCodeEquiv` is injective. -/
theorem codeProj_shapedField_isolates
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y z : ShapeState S)
    (x : CodimensionPoint V.X p) :
    fiberedNativeCodeProj S (worldCode S y)
        (shapedFiberedNativeField alpha S x) z =
      if z = y then
        liveCoordinateVector alpha (shapeCodeEquiv S y) •
          shapedLiveNativeAtom alpha S y x
      else 0 := by
  by_cases hzy : z = y
  · subst z
    simp [fiberedNativeCodeProj, shapedFiberedNativeField]
  · have hcode : worldCode S z ≠ worldCode S y := by
      intro h
      apply hzy
      apply (shapeCodeEquiv S).injective
      apply Fin.ext
      exact h
    simp only [fiberedNativeCodeProj, shapedFiberedNativeField]
    rw [if_neg hzy, if_neg hcode]

/-- Sum a pullback-valued shaped field over its finite GST observation chart. -/
noncomputable def sumShapedField
    {N : Nat} (S : GSTWorldShape N)
    (f : ShapeState S → FiberedNativeAddress V H p) :
    FiberedNativeAddress V H p :=
  ∑ y : ShapeState S, f y

/-- Projecting at one state and summing gives exactly one scalar multiple of
one common-refinement atom. -/
theorem sum_codeProj_shapedField
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    sumShapedField S
      (fiberedNativeCodeProj S (worldCode S y)
        (shapedFiberedNativeField alpha S x)) =
      liveCoordinateVector alpha (shapeCodeEquiv S y) •
        shapedLiveNativeAtom alpha S y x := by
  classical
  unfold sumShapedField
  rw [Finset.sum_eq_single y]
  · rw [codeProj_shapedField_isolates, if_pos rfl]
  · intro z hz hzy
    rw [codeProj_shapedField_isolates]
    simp [hzy]
  · intro hy
    exact (hy (Finset.mem_univ y)).elim

/-- Classical multiplicity face of one isolated live sheet. -/
theorem projected_hodgeFace_exact
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    toGlobalHodgeAddress V H p
      (sumShapedField S
        (fiberedNativeCodeProj S (worldCode S y)
          (shapedFiberedNativeField alpha S x))) =
      liveCoordinateVector alpha (shapeCodeEquiv S y) •
        fiberedSheetGenerator V H
          ⟨p, shapedLiveBasisIndex alpha S y⟩ := by
  rw [sum_codeProj_shapedField, map_smul, shapedLiveNativeAtom,
    toGlobalHodgeAddress_atom]

/-- Genuine native projective-cycle face of the same isolated live sheet. -/
theorem projected_nativeFace_exact
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    toNativeCycle V H p
      (sumShapedField S
        (fiberedNativeCodeProj S (worldCode S y)
          (shapedFiberedNativeField alpha S x))) =
      liveCoordinateVector alpha (shapeCodeEquiv S y) •
        codimensionPointCycle V.X p x := by
  rw [sum_codeProj_shapedField, map_smul, shapedLiveNativeAtom,
    toNativeCycle_atom]

/-- Limitless universal-address face of the isolated native atom. -/
theorem projected_limitlessFace_exact
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    pureWeightToUniversalAddress
      (nativeCycleCosmicShadow V p
        (toNativeCycle V H p
          (sumShapedField S
            (fiberedNativeCodeProj S (worldCode S y)
              (shapedFiberedNativeField alpha S x))))) =
      liveCoordinateVector alpha (shapeCodeEquiv S y) •
        rationalizeCompactAddress (compactClMono p) := by
  rw [projected_nativeFace_exact]
  rw [map_smul, map_smul]
  rw [nativeCycleCosmicShadow_point]
  rw [pureWeightToUniversalAddress_basis]
  rw [rationalize_compactClMono]

/-- Every live slot has nonzero coefficient, so its native/projective spectral
atom is nonzero whenever the underlying point cycle is nonzero. -/
theorem projected_live_coefficient_ne_zero
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S) :
    liveCoordinateVector alpha (shapeCodeEquiv S y) ≠ 0 :=
  liveCoordinateVector_ne_zero_at alpha (shapeCodeEquiv S y)

/-- The entire three-face spectral statement is independent of the rectangular
chart chosen to display the finite live support. -/
theorem spectral_projection_recoordination_natural
    (alpha : ClassicalHodgeFiber V H p)
    (S T : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    transportFiberedNative S T
      (fiberedNativeCodeProj S (worldCode S y)
        (shapedFiberedNativeField alpha S x)) =
      fiberedNativeCodeProj T (worldCode S y)
        (shapedFiberedNativeField alpha T x) := by
  rw [transportFiberedNative_codeProj]
  rw [transport_shapedFiberedNativeField]

/-- **FIBERED NATIVE SPECTRAL CROWN.**
Every finite live classical Hodge sheet can be isolated by the intrinsic GST
code projector directly inside the multiplicity-preserving native pullback,
and the resulting atom has exact classical, native and limitless faces. -/
theorem fibered_native_spectral_crown
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    let q := liveCoordinateVector alpha (shapeCodeEquiv S y)
    let Φ := sumShapedField S
      (fiberedNativeCodeProj S (worldCode S y)
        (shapedFiberedNativeField alpha S x))
    q ≠ 0
      ∧ toGlobalHodgeAddress V H p Φ =
          q • fiberedSheetGenerator V H
            ⟨p, shapedLiveBasisIndex alpha S y⟩
      ∧ toNativeCycle V H p Φ =
          q • codimensionPointCycle V.X p x
      ∧ pureWeightToUniversalAddress
          (nativeCycleCosmicShadow V p (toNativeCycle V H p Φ)) =
          q • rationalizeCompactAddress (compactClMono p) := by
  dsimp
  exact ⟨projected_live_coefficient_ne_zero alpha S y,
    projected_hodgeFace_exact alpha S y x,
    projected_nativeFace_exact alpha S y x,
    projected_limitlessFace_exact alpha S y x⟩

#check fiberedNativeCodeProj
#check transportFiberedNative_codeProj
#check codeProj_shapedField_isolates
#check sum_codeProj_shapedField
#check projected_hodgeFace_exact
#check projected_nativeFace_exact
#check projected_limitlessFace_exact
#check spectral_projection_recoordination_natural
#check fibered_native_spectral_crown

#print axioms transportFiberedNative_codeProj
#print axioms codeProj_shapedField_isolates
#print axioms sum_codeProj_shapedField
#print axioms projected_hodgeFace_exact
#print axioms projected_nativeFace_exact
#print axioms projected_limitlessFace_exact
#print axioms fibered_native_spectral_crown

end GSTClassicalHodgeFiberedNativeSpectralProjectors
