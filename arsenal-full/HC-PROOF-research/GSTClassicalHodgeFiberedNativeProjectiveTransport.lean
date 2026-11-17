import GSTClassicalHodgeFiberedNativeSpectralProjectors
import GSTClassicalHodgeProjectivePointTransport
import GSTNativeCodimensionCyclePresentation
import GSTClassicalHodgeProjectiveCorrespondenceAlgebra
import GSTClassicalHodgeFiberedTransferCompletion

/-!
# GST CLASSICAL HODGE — FIBERED NATIVE PROJECTIVE TRANSPORT

The fibered native pullback is now acted on by genuine projective geometry.
A scheme endomorphism transports the native point coordinate by the actual
residue-degree weighted point pushforward while retaining the classical
multiplicity label above the fixed Hodge weight.

Forgetting the multiplicity label after this transport recovers the actual
native algebraic-cycle pushforward on point generators.  Forgetting the point
instead records the same residue-degree scalar on the corresponding classical
multiplicity sheet.  Thus one genuine geometric transport acts on both faces
of the common pullback before any cycle-class comparison is invoked.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeFiberedNativeProjectiveTransport

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiberedNativeSpectralProjectors
open GSTClassicalHodgeProjectivePointTransport
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeNativeTransferAddressIdentification
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedTransferCompletion

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Transport one multiplicity-labelled native point atom through an actual
scheme endomorphism.  If codimension p is not preserved, its p-component is
zero exactly as in the native point-pushforward construction. -/
noncomputable def transportAtom
    (f : V.X ⟶ V.X)
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    FiberedNativeAddress V H p := by
  classical
  by_cases hcod : Order.coheight (f x.1) = p
  · exact pointResidueWeight f x.1 •
      atom V H p i ⟨f x.1,hcod⟩
  · exact 0

/-- Linear extension to every finite multiplicity-labelled native state. -/
noncomputable def fiberedNativePushforward
    (f : V.X ⟶ V.X) :
    FiberedNativeAddress V H p →ₗ[ℚ] FiberedNativeAddress V H p where
  toFun φ := φ.sum fun ix q => q • transportAtom f ix.1 ix.2
  map_add' := by
    intro φ ψ
    classical
    show (φ + ψ).sum
        (fun ix q => q • transportAtom f ix.1 ix.2) =
      (φ.sum fun ix q => q • transportAtom f ix.1 ix.2)
        + (ψ.sum fun ix q => q • transportAtom f ix.1 ix.2)
    rw [Finsupp.sum_add_index'
      (f := φ) (g := ψ)
      (h := fun ix q => q • transportAtom f ix.1 ix.2)
      (fun ix => zero_smul ℚ (transportAtom f ix.1 ix.2))
      (fun ix b₁ b₂ => add_smul b₁ b₂ (transportAtom f ix.1 ix.2))]
  map_smul' := by
    intro q φ
    classical
    induction φ using Finsupp.induction_linear with
    | zero =>
        show (q • (0 : FiberedNativeAddress V H p)).sum
            (fun ix q => q • transportAtom f ix.1 ix.2) =
          q • (0 : FiberedNativeAddress V H p).sum
            (fun ix q => q • transportAtom f ix.1 ix.2)
        rw [smul_zero]
        simp only [Finsupp.sum, Finsupp.support_zero, Finset.sum_empty,
          smul_zero]
    | add a b ha hb =>
        simp [ha, hb, add_smul, Finsupp.sum_add_index']
    | single i c =>
        have h1 : ∀ (t : ℚ), (Finsupp.single i t).sum
            (fun ix s => s • transportAtom f ix.1 ix.2)
            = t • transportAtom f i.1 i.2 := fun t =>
          Finsupp.sum_single_index (a := i) (b := t)
            (h := fun ix s => s • transportAtom f ix.1 ix.2) (by simp)
        have h2 : q • Finsupp.single i c = Finsupp.single i (q * c) := by
          rw [show Finsupp.single i c = c • atom V H p i.1 i.2 by simp [atom],
            smul_smul,
            show (q * c) • atom V H p i.1 i.2 = Finsupp.single i (q * c) by
              simp [atom]]
        show (q • Finsupp.single i c).sum
            (fun ix t => t • transportAtom f ix.1 ix.2) =
          q • (Finsupp.single i c).sum
            (fun ix t => t • transportAtom f ix.1 ix.2)
        rw [h2, h1 (q * c), h1 c, smul_smul]

@[simp]
theorem fiberedNativePushforward_atom
    (f : V.X ⟶ V.X)
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    fiberedNativePushforward f (atom V H p i x) =
      transportAtom f i x := by
  classical
  simp [fiberedNativePushforward, atom]

/-- Native face of one transported common-refinement atom is exactly the
repo's genuine residue-weighted native point pushforward. -/
theorem nativeFace_transportAtom
    (f : V.X ⟶ V.X)
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    toNativeCycle V H p (transportAtom f i x) =
      nativePointPushforward f p x := by
  classical
  unfold transportAtom nativePointPushforward pointPushforwardPresentation
  split_ifs with hcod
  · rw [map_smul, toNativeCycle_atom]
    rw [realizeFiniteCodimensionPresentation_single]
  · simp [toNativeCycle]

/-- Therefore on point atoms, forgetting multiplicity after fibered transport
is exactly the genuine smooth-projective native pushforward. -/
theorem nativeFace_fiberedPushforward_atom
    (f : V.X ⟶ V.X)
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    toNativeCycle V H p
      (fiberedNativePushforward f (atom V H p i x)) =
      smoothProjectiveNativePushforward V f p
        (codimensionPointCycle V.X p x) := by
  rw [fiberedNativePushforward_atom]
  rw [nativeFace_transportAtom]
  exact (smoothProjectiveNativePushforward_point V f p x).symm

/-- Classical multiplicity face of a transported atom: geometry changes the
point but carries the same Hodge multiplicity label with the actual residue
multiplicity. -/
theorem hodgeFace_transportAtom_of_codim
    (f : V.X ⟶ V.X)
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p)
    (hcod : Order.coheight (f x.1) = p) :
    toGlobalHodgeAddress V H p (transportAtom f i x) =
      pointResidueWeight f x.1 • fiberedSheetGenerator V H ⟨p,i⟩ := by
  classical
  simp [transportAtom, hcod, map_smul, toGlobalHodgeAddress_atom]

/-- If the geometric image leaves codimension p, both the native p-component
and the fibered p-face vanish. -/
theorem hodgeFace_transportAtom_of_wrong_codim
    (f : V.X ⟶ V.X)
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p)
    (hcod : Order.coheight (f x.1) ≠ p) :
    toGlobalHodgeAddress V H p (transportAtom f i x) = 0 := by
  classical
  simp [transportAtom, hcod]

/-- On the limitless base address, geometric transport of one atom is just its
actual residue-degree multiplier on the same codimension-p transfer ray. -/
theorem limitlessFace_transportAtom_of_codim
    (f : V.X ⟶ V.X)
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p)
    (hcod : Order.coheight (f x.1) = p) :
    pureWeightToUniversalAddress
      (nativeCycleCosmicShadow V p
        (toNativeCycle V H p (transportAtom f i x))) =
      pointResidueWeight f x.1 •
        rationalizeCompactAddress (GSTTransferBridgeV2.compactClMono p) := by
  rw [nativeFace_transportAtom]
  rw [nativePointPushforward_eq f p x hcod]
  rw [map_smul, map_smul]
  rw [nativeCycleCosmicShadow_point]
  rw [pureWeightToUniversalAddress_basis]
  rw [rationalize_compactClMono]

/-- Fibered projective transport commutes with arbitrary rational scaling of
one common-refinement atom. -/
theorem fiberedNativePushforward_smul_atom
    (f : V.X ⟶ V.X)
    (q : ℚ)
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    fiberedNativePushforward f (q • atom V H p i x) =
      q • transportAtom f i x := by
  simp [fiberedNativePushforward_atom]

/-- Applying a projective transport after GST spectral isolation therefore
transports the isolated genuine native point cycle with exactly the same live
classical coefficient. -/
theorem project_then_projectiveTransport_nativeFace
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldRecoordinationGroupoid.GSTWorldShape
      (GSTClassicalHodgeFiniteSupportArsenalConjugation.liveRank alpha))
    (y : GSTWorldRecoordinationGroupoid.ShapeState S)
    (x : CodimensionPoint V.X p)
    (f : V.X ⟶ V.X) :
    toNativeCycle V H p
      (fiberedNativePushforward f
        (sumShapedField S
          (fiberedNativeCodeProj S
            (GSTWorldRecoordinationGroupoid.worldCode S y)
            (GSTClassicalHodgeFiberedNativeRecoordination.shapedFiberedNativeField
              alpha S x)))) =
      GSTClassicalHodgeFiniteSupportArsenalConjugation.liveCoordinateVector alpha
        (GSTWorldRecoordinationGroupoid.shapeCodeEquiv S y) •
        nativePointPushforward f p x := by
  rw [sum_codeProj_shapedField, map_smul,
    GSTClassicalHodgeFiberedNativeRecoordination.shapedLiveNativeAtom,
    fiberedNativePushforward_atom, map_smul, nativeFace_transportAtom]

/-- **PROJECTIVE TRANSPORT CROWN.** Genuine scheme endomorphisms act directly
on the multiplicity-preserving native pullback, and the native face is exactly
the actual projective point pushforward. -/
theorem fibered_native_projective_transport_crown
    (f : V.X ⟶ V.X) :
    ∀ i : ClassicalHodgeBasisIndex V H p,
    ∀ x : CodimensionPoint V.X p,
      toNativeCycle V H p
        (fiberedNativePushforward f (atom V H p i x)) =
        smoothProjectiveNativePushforward V f p
          (codimensionPointCycle V.X p x) := by
  intro i x
  exact nativeFace_fiberedPushforward_atom f i x

#check transportAtom
#check fiberedNativePushforward
#check nativeFace_transportAtom
#check nativeFace_fiberedPushforward_atom
#check hodgeFace_transportAtom_of_codim
#check limitlessFace_transportAtom_of_codim
#check project_then_projectiveTransport_nativeFace
#check fibered_native_projective_transport_crown

#print axioms nativeFace_transportAtom
#print axioms nativeFace_fiberedPushforward_atom
#print axioms hodgeFace_transportAtom_of_codim
#print axioms limitlessFace_transportAtom_of_codim
#print axioms project_then_projectiveTransport_nativeFace
#print axioms fibered_native_projective_transport_crown

end GSTClassicalHodgeFiberedNativeProjectiveTransport

