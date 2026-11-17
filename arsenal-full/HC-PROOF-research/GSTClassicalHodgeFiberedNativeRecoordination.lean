import GSTClassicalHodgeFiberedNativePullback
import GSTClassicalHodgeRecoordinationArsenalCrown
import GSTClassicalHodgeFiniteSupportArsenalConjugation
import GSTClassicalHodgeSupportCardinalityBridge
import GSTWorldRecoordinationGroupoid

/-!
# GST CLASSICAL HODGE — FIBERED NATIVE RECOORDINATION

Finite rectangular GST worlds are observation charts, not ontology.  The
fibered native pullback from `GSTClassicalHodgeFiberedNativePullback` therefore
must be independent of the rectangle used to display a finite live Hodge
support.

For one genuine Hodge state `alpha`, every live slot is intrinsically indexed
by its invariant code in `Fin (liveRank alpha)`.  Any equal-cardinality GST
shape merely decodes that same code into a different pair of coordinates.
We use the code to select the genuine classical basis sheet, pair it with an
actual codimension-p projective point, and obtain one common-refinement atom.

World recoordination preserves the code exactly, hence it preserves the atom
itself.  Consequently all three faces of the pullback — classical
multiplicity, native projective cycle, and limitless transfer address — are
strictly natural under every finite world recoordination.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFiberedNativeRecoordination

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeSupportCardinalityBridge
open GSTClassicalHodgeRecoordinationArsenalCrown
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiniteSupportArsenalConjugation
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeNativeTransferAddressIdentification
open GSTWorldRecoordinationGroupoid

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The live-slot basis index selected by a state of an arbitrary equal-size
GST chart. -/
noncomputable def shapedLiveBasisIndex
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S) :
    ClassicalHodgeBasisIndex V H p :=
  liveBasisIndex alpha (shapeCodeEquiv S y)

/-- Pair the intrinsic live Hodge sheet selected by a shaped state with one
actual native codimension-p point. -/
noncomputable def shapedLiveNativeAtom
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    FiberedNativeAddress V H p :=
  atom V H p (shapedLiveBasisIndex alpha S y) x

/-- Recoordination preserves the intrinsic live basis index exactly. -/
theorem shapedLiveBasisIndex_recoordinate
    (alpha : ClassicalHodgeFiber V H p)
    (S T : GSTWorldShape (liveRank alpha))
    (y : ShapeState S) :
    shapedLiveBasisIndex alpha T (worldRecoordinate S T y) =
      shapedLiveBasisIndex alpha S y := by
  unfold shapedLiveBasisIndex
  congr 1
  apply Fin.ext
  exact worldRecoordinate_code S T y

/-- **ATOM-LEVEL RECOORDINATION NATURALITY.**
Changing the finite rectangular observation chart does not change the
multiplicity-labelled native atom. -/
theorem shapedLiveNativeAtom_recoordinate
    (alpha : ClassicalHodgeFiber V H p)
    (S T : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    shapedLiveNativeAtom alpha T (worldRecoordinate S T y) x =
      shapedLiveNativeAtom alpha S y x := by
  simp [shapedLiveNativeAtom, shapedLiveBasisIndex_recoordinate]

/-- The classical multiplicity face is recoordination-invariant. -/
theorem shapedLiveNativeAtom_hodgeFace_recoordinate
    (alpha : ClassicalHodgeFiber V H p)
    (S T : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    toGlobalHodgeAddress V H p
        (shapedLiveNativeAtom alpha T (worldRecoordinate S T y) x) =
      toGlobalHodgeAddress V H p
        (shapedLiveNativeAtom alpha S y x) := by
  rw [shapedLiveNativeAtom_recoordinate]

/-- The genuine native-cycle face is recoordination-invariant. -/
theorem shapedLiveNativeAtom_nativeFace_recoordinate
    (alpha : ClassicalHodgeFiber V H p)
    (S T : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    toNativeCycle V H p
        (shapedLiveNativeAtom alpha T (worldRecoordinate S T y) x) =
      toNativeCycle V H p
        (shapedLiveNativeAtom alpha S y x) := by
  rw [shapedLiveNativeAtom_recoordinate]

/-- The limitless universal-address face is recoordination-invariant. -/
theorem shapedLiveNativeAtom_limitlessFace_recoordinate
    (alpha : ClassicalHodgeFiber V H p)
    (S T : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    pureWeightToUniversalAddress
      (nativeCycleCosmicShadow V p
        (toNativeCycle V H p
          (shapedLiveNativeAtom alpha T (worldRecoordinate S T y) x))) =
    pureWeightToUniversalAddress
      (nativeCycleCosmicShadow V p
        (toNativeCycle V H p
          (shapedLiveNativeAtom alpha S y x))) := by
  rw [shapedLiveNativeAtom_recoordinate]

/-- A shaped live coefficient field valued directly in the common-refinement
native/Hodge pullback.  Each state carries its genuine live classical
coefficient on one actual native point atom. -/
noncomputable def shapedFiberedNativeField
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (x : CodimensionPoint V.X p) :
    ShapeState S → FiberedNativeAddress V H p :=
  fun y =>
    liveCoordinateVector alpha (shapeCodeEquiv S y) •
      shapedLiveNativeAtom alpha S y x

/-- Transport a pullback-valued field through the GST world groupoid. -/
def transportFiberedNative
    {N : Nat} (S T : GSTWorldShape N)
    (f : ShapeState S → FiberedNativeAddress V H p) :
    ShapeState T → FiberedNativeAddress V H p :=
  fun y => f ((worldRecoordinate S T).symm y)

/-- **FULL PULLBACK-VALUED RECOORDINATION NATURALITY.**
The complete multiplicity-labelled native field transports exactly through
arbitrary equal-cardinality GST charts. -/
theorem transport_shapedFiberedNativeField
    (alpha : ClassicalHodgeFiber V H p)
    (S T : GSTWorldShape (liveRank alpha))
    (x : CodimensionPoint V.X p) :
    transportFiberedNative S T (shapedFiberedNativeField alpha S x) =
      shapedFiberedNativeField alpha T x := by
  funext y
  have hcode :
      shapeCodeEquiv S ((worldRecoordinate S T).symm y) =
        shapeCodeEquiv T y := by
    apply Fin.ext
    rw [worldRecoordinate_inverse S T y]
    exact worldRecoordinate_code T S y
  unfold transportFiberedNative shapedFiberedNativeField
  rw [hcode]
  have hatom := shapedLiveNativeAtom_recoordinate
    alpha T S y x
  rw [worldRecoordinate_inverse S T y]
  rw [hatom]

/-- The native-cycle-valued shaped field is therefore also chart independent. -/
theorem transport_nativeFace_field
    (alpha : ClassicalHodgeFiber V H p)
    (S T : GSTWorldShape (liveRank alpha))
    (x : CodimensionPoint V.X p) :
    (fun y =>
      toNativeCycle V H p
        (transportFiberedNative S T
          (shapedFiberedNativeField alpha S x) y)) =
      (fun y =>
        toNativeCycle V H p
          (shapedFiberedNativeField alpha T x y)) := by
  funext y
  rw [transport_shapedFiberedNativeField]

/-- Likewise the classical multiplicity face is chart independent. -/
theorem transport_hodgeFace_field
    (alpha : ClassicalHodgeFiber V H p)
    (S T : GSTWorldShape (liveRank alpha))
    (x : CodimensionPoint V.X p) :
    (fun y =>
      toGlobalHodgeAddress V H p
        (transportFiberedNative S T
          (shapedFiberedNativeField alpha S x) y)) =
      (fun y =>
        toGlobalHodgeAddress V H p
          (shapedFiberedNativeField alpha T x y)) := by
  funext y
  rw [transport_shapedFiberedNativeField]

/-- Crown: the common native/classical/limitless pullback is intrinsic to the
finite live state universe and independent of every rectangular GST
observation chart. -/
theorem fibered_native_recoordination_crown
    (alpha : ClassicalHodgeFiber V H p)
    (x : CodimensionPoint V.X p) :
    ∀ S T : GSTWorldShape (liveRank alpha),
      transportFiberedNative S T (shapedFiberedNativeField alpha S x) =
        shapedFiberedNativeField alpha T x := by
  intro S T
  exact transport_shapedFiberedNativeField alpha S T x

#check shapedLiveBasisIndex
#check shapedLiveNativeAtom
#check shapedLiveNativeAtom_recoordinate
#check shapedFiberedNativeField
#check transportFiberedNative
#check transport_shapedFiberedNativeField
#check fibered_native_recoordination_crown

#print axioms shapedLiveBasisIndex_recoordinate
#print axioms shapedLiveNativeAtom_recoordinate
#print axioms transport_shapedFiberedNativeField
#print axioms fibered_native_recoordination_crown

end GSTClassicalHodgeFiberedNativeRecoordination
