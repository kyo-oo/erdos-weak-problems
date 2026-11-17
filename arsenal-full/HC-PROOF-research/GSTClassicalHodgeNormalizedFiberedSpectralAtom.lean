import GSTClassicalHodgeFiberedNativeSpectralProjectors
import GSTClassicalHodgeThreeUniverseSeedIdentification
import GSTClassicalHodgeFiniteSupportArsenalConjugation
import GSTWorldRecoordinationGroupoid
import GSTNativeCodimensionCyclePresentation
import GSTClassicalHodgeFiberedTransferCompletion

/-!
# GST CLASSICAL HODGE — NORMALIZED FIBERED SPECTRAL ATOMS

The fibered native spectral projector already isolates every live classical
Hodge sheet simultaneously on three faces: the full classical multiplicity
address, the genuine native codimension-p cycle space, and the limitless
universal GST transfer address.

The isolated state carries the nonzero live coefficient of the original Hodge
class. Over Q that coefficient is invertible. This file divides it out once
and for all, producing coefficient one on all three faces.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open scoped BigOperators

namespace GSTClassicalHodgeNormalizedFiberedSpectralAtom

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTClassicalHodgeFiniteSupportArsenalConjugation
open GSTWorldRecoordinationGroupoid
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedTransferCompletion
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiberedNativeRecoordination
open GSTClassicalHodgeFiberedNativeSpectralProjectors
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeNativeTransferAddressIdentification
open GSTClassicalHodgeThreeUniverseSeedIdentification
open GSTTransferBridgeV2

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

noncomputable def liveSpectralCoefficient
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S) : ℚ :=
  liveCoordinateVector alpha (shapeCodeEquiv S y)

noncomputable def isolatedFiberedState
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    FiberedNativeAddress V H p :=
  sumShapedField S
    (fiberedNativeCodeProj S (worldCode S y)
      (shapedFiberedNativeField alpha S x))

noncomputable def normalizedSpectralAtom
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    FiberedNativeAddress V H p :=
  (liveSpectralCoefficient alpha S y)⁻¹ •
    isolatedFiberedState alpha S y x

theorem liveSpectralCoefficient_ne_zero
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S) :
    liveSpectralCoefficient alpha S y ≠ 0 := by
  exact projected_live_coefficient_ne_zero alpha S y

theorem normalized_hodgeFace_exact
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    toGlobalHodgeAddress V H p
      (normalizedSpectralAtom alpha S y x) =
      fiberedSheetGenerator V H
        ⟨p, shapedLiveBasisIndex alpha S y⟩ := by
  unfold normalizedSpectralAtom liveSpectralCoefficient isolatedFiberedState
  rw [map_smul]
  rw [projected_hodgeFace_exact alpha S y x]
  simp [projected_live_coefficient_ne_zero alpha S y]

theorem normalized_nativeFace_exact
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    toNativeCycle V H p
      (normalizedSpectralAtom alpha S y x) =
      codimensionPointCycle V.X p x := by
  unfold normalizedSpectralAtom liveSpectralCoefficient isolatedFiberedState
  rw [map_smul]
  rw [projected_nativeFace_exact alpha S y x]
  simp [projected_live_coefficient_ne_zero alpha S y]

theorem normalized_limitlessFace_exact
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    pureWeightToUniversalAddress
      (nativeCycleCosmicShadow V p
        (toNativeCycle V H p
          (normalizedSpectralAtom alpha S y x))) =
      rationalizeCompactAddress (compactClMono p) := by
  rw [normalized_nativeFace_exact alpha S y x]
  exact nativePoint_shadow_eq_rationalized_transfer V p x

theorem normalized_fibered_spectral_crown
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    toGlobalHodgeAddress V H p
        (normalizedSpectralAtom alpha S y x) =
      fiberedSheetGenerator V H
        ⟨p, shapedLiveBasisIndex alpha S y⟩
    ∧ toNativeCycle V H p
        (normalizedSpectralAtom alpha S y x) =
      codimensionPointCycle V.X p x
    ∧ pureWeightToUniversalAddress
        (nativeCycleCosmicShadow V p
          (toNativeCycle V H p
            (normalizedSpectralAtom alpha S y x))) =
      rationalizeCompactAddress (compactClMono p) := by
  exact ⟨normalized_hodgeFace_exact alpha S y x,
    normalized_nativeFace_exact alpha S y x,
    normalized_limitlessFace_exact alpha S y x⟩

#check normalizedSpectralAtom
#check normalized_hodgeFace_exact
#check normalized_nativeFace_exact
#check normalized_limitlessFace_exact
#check normalized_fibered_spectral_crown

#print axioms normalized_hodgeFace_exact
#print axioms normalized_nativeFace_exact
#print axioms normalized_limitlessFace_exact
#print axioms normalized_fibered_spectral_crown

end GSTClassicalHodgeNormalizedFiberedSpectralAtom
