import GSTClassicalHodgeFiberedCycleClassDefect
import GSTClassicalHodgeFiberedNativeProjectiveTransport
import GSTClassicalHodgePrimitivePushforwardNaturality

/-!
# GST CLASSICAL HODGE — FIBERED DEFECT PROJECTIVE COCYCLE

The fibered cycle-class defect is insensitive to the joint interaction sector.
This module computes what can actually change it: genuine projective geometry.

For a scheme endomorphism `f`, primitive cycle-class naturality identifies the
native class of the transported point with the cohomological pushforward of the
source point class.  If the transported native point is relabelled from Hodge
sheet `i` to sheet `j`, the defect satisfies the exact cocycle law

  defect(f · (i,x), relabelled j)
    = f_*^H(defect(i,x))
      + (f_*^H e_i - deg_x(f) e_j).

Hence a defect-zero source atom remains defect-zero after a relabelled
projective transport exactly when the genuine cohomological pushforward sends
its source Hodge sheet to the residue-weighted target sheet.

This is the precise lower geometric content behind an apex spoke.  No Hodge
surjectivity, branch-packet realization, ghost extinction, or target cycle is
assumed.
-/

set_option maxHeartbeats 80000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeFiberedDefectProjectiveCocycle

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiberedCycleClassDefect
open GSTClassicalHodgeFiberedNativeProjectiveTransport
open GSTClassicalHodgeProjectivePointTransport
open GSTClassicalHodgePrimitivePushforwardNaturality
open GSTNativeCodimensionCyclePresentation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Naturality on one codimension-preserving point, written in the exact
residue-weighted atom form used by the fibered transport. -/
theorem pointClass_pushforward_eq_residue_smul
    (f : V.X ⟶ V.X)
    (N : GeometricPushforwardNaturality V H p f)
    (x : CodimensionPoint V.X p)
    (hcod : Order.coheight (f x.1) = p) :
    N.cohomologyPushforward
        (H.cycleClass p (codimensionPointCycle V.X p x)) =
      pointResidueWeight f x.1 •
        H.cycleClass p
          (codimensionPointCycle V.X p ⟨f x.1, hcod⟩) := by
  have hnat := N.naturality (codimensionPointCycle V.X p x)
  rw [smoothProjectiveNativePushforward_point V f p x,
    nativePointPushforward_eq f p x hcod,
    LinearMap.map_smul] at hnat
  exact hnat.symm

/-- Defect of an actual projective transport when the Hodge multiplicity label
is retained. -/
theorem fiberedCycleClassDefect_transportAtom_of_codim
    (f : V.X ⟶ V.X)
    (N : GeometricPushforwardNaturality V H p f)
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p)
    (hcod : Order.coheight (f x.1) = p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (transportAtom f i x) =
      N.cohomologyPushforward
          (H.cycleClass p (codimensionPointCycle V.X p x)) -
        pointResidueWeight f x.1 •
          (classicalHodgeBasis V H p i).1 := by
  have hnat :=
    pointClass_pushforward_eq_residue_smul
      (V := V) (H := H) f N x hcod
  have htransport :
      transportAtom (V := V) (H := H) (p := p) f i x =
        pointResidueWeight f x.1 •
          atom V H p i ⟨f x.1, hcod⟩ := by
    simp [transportAtom, hcod]
  rw [htransport, LinearMap.map_smul,
    fiberedCycleClassDefect_atom, smul_sub]
  rw [← hnat]

/-- **RELABELLED PROJECTIVE DEFECT COCYCLE.**

The native point is transported by the actual scheme map while the classical
multiplicity face is allowed to carry a requested target sheet `j`.  The
correction term is exactly the difference between the genuine cohomological
pushforward of the old sheet and the residue-weighted new sheet. -/
theorem fiberedCycleClassDefect_relabelledTransport_cocycle
    (f : V.X ⟶ V.X)
    (N : GeometricPushforwardNaturality V H p f)
    (i j : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p)
    (hcod : Order.coheight (f x.1) = p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (transportAtom f j x) =
      N.cohomologyPushforward
          (fiberedCycleClassDefect (V := V) (H := H) (p := p)
            (atom V H p i x))
        +
      (N.cohomologyPushforward (classicalHodgeBasis V H p i).1 -
        pointResidueWeight f x.1 •
          (classicalHodgeBasis V H p j).1) := by
  rw [fiberedCycleClassDefect_transportAtom_of_codim
    (V := V) (H := H) f N j x hcod]
  rw [fiberedCycleClassDefect_atom, LinearMap.map_sub]
  abel

/-- Retaining the same sheet is the diagonal specialization of the cocycle. -/
theorem fiberedCycleClassDefect_transport_cocycle
    (f : V.X ⟶ V.X)
    (N : GeometricPushforwardNaturality V H p f)
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p)
    (hcod : Order.coheight (f x.1) = p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (transportAtom f i x) =
      N.cohomologyPushforward
          (fiberedCycleClassDefect (V := V) (H := H) (p := p)
            (atom V H p i x))
        +
      (N.cohomologyPushforward (classicalHodgeBasis V H p i).1 -
        pointResidueWeight f x.1 •
          (classicalHodgeBasis V H p i).1) :=
  fiberedCycleClassDefect_relabelledTransport_cocycle
    (V := V) (H := H) f N i i x hcod

/-- If the source atom is already a genuine landing state, then the defect of
a relabelled projective transport is *exactly* the projective sheet-action
error. -/
theorem defect_relabelledTransport_of_source_zero
    (f : V.X ⟶ V.X)
    (N : GeometricPushforwardNaturality V H p f)
    (i j : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p)
    (hcod : Order.coheight (f x.1) = p)
    (hsource :
      fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (atom V H p i x) = 0) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (transportAtom f j x) =
      N.cohomologyPushforward (classicalHodgeBasis V H p i).1 -
        pointResidueWeight f x.1 •
          (classicalHodgeBasis V H p j).1 := by
  rw [fiberedCycleClassDefect_relabelledTransport_cocycle
    (V := V) (H := H) f N i j x hcod, hsource, LinearMap.map_zero, zero_add]

/-- **EXACT PROJECTIVE SHEET-TRANSPORT CRITERION.**

Starting from one defect-zero atom, a genuine projective transport produces a
defect-zero atom on target sheet `j` iff its actual cohomological pushforward
sends the source basis sheet to the residue-weighted target sheet.  This is an
iff, not a new premise: it pinpoints the exact geometric equation that must be
constructed. -/
theorem relabelledTransport_defect_zero_iff_sheet_action
    (f : V.X ⟶ V.X)
    (N : GeometricPushforwardNaturality V H p f)
    (i j : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p)
    (hcod : Order.coheight (f x.1) = p)
    (hsource :
      fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (atom V H p i x) = 0) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (transportAtom f j x) = 0 ↔
      N.cohomologyPushforward (classicalHodgeBasis V H p i).1 =
        pointResidueWeight f x.1 •
          (classicalHodgeBasis V H p j).1 := by
  rw [defect_relabelledTransport_of_source_zero
    (V := V) (H := H) f N i j x hcod hsource]
  exact sub_eq_zero

#check pointClass_pushforward_eq_residue_smul
#check fiberedCycleClassDefect_transportAtom_of_codim
#check fiberedCycleClassDefect_relabelledTransport_cocycle
#check fiberedCycleClassDefect_transport_cocycle
#check defect_relabelledTransport_of_source_zero
#check relabelledTransport_defect_zero_iff_sheet_action

#print axioms pointClass_pushforward_eq_residue_smul
#print axioms fiberedCycleClassDefect_relabelledTransport_cocycle
#print axioms relabelledTransport_defect_zero_iff_sheet_action

end GSTClassicalHodgeFiberedDefectProjectiveCocycle
