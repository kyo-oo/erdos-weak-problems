import GSTClassicalHodgeFiberedDefectEquivariance
import GSTClassicalHodgeFiberedNativeProjectiveTransport
import GSTClassicalHodgePrimitivePushforwardNaturality

/-!
# GST CLASSICAL HODGE — PROJECTIVE DEFECT TRANSPORT

Actual scheme endomorphisms already act on the common fibered/native universe.
Their point action carries the genuine residue-degree multiplier on both the
native point pushforward and the retained Hodge multiplicity label.

When the genuine cohomological pushforward has that same action on a selected
Hodge basis sheet, the classical fibered defect commutes with projective
transport exactly.  Thus zero-defect states are stable under every genuinely
geometric self-transport satisfying the standard cycle-class naturality
square.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeProjectiveDefectTransport

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiberedCycleClassDefect
open GSTClassicalHodgeFiberedNativeProjectiveTransport
open GSTClassicalHodgeProjectivePointTransport
open GSTClassicalHodgePrimitivePushforwardNaturality

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Exact Hodge-vector face of one genuine projective transport when the image
remains in codimension p. -/
theorem fiberedHodgeClass_transportAtom_of_codim
    (f : V.X ⟶ V.X)
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p)
    (hcod : Order.coheight (f x.1) = p) :
    fiberedHodgeClass (V := V) (H := H) (p := p)
        (transportAtom f i x) =
      pointResidueWeight f x.1 • classicalHodgeBasis V H p i := by
  classical
  simp [transportAtom, hcod,
    GSTClassicalHodgeFiberedCycleClassDefect.fiberedHodgeClass]

/-- If the image leaves codimension p, the retained p-face is zero. -/
theorem fiberedHodgeClass_transportAtom_of_wrong_codim
    (f : V.X ⟶ V.X)
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p)
    (hcod : Order.coheight (f x.1) ≠ p) :
    fiberedHodgeClass (V := V) (H := H) (p := p)
        (transportAtom f i x) = 0 := by
  classical
  simp [transportAtom, hcod,
    GSTClassicalHodgeFiberedCycleClassDefect.fiberedHodgeClass]

/-- The expected geometric action on one Hodge sheet: the actual cohomology
pushforward acts by the same residue scalar as the genuine point pushforward,
or vanishes when the p-graded point component vanishes. -/
def ProjectiveSheetIntertwines
    {f : V.X ⟶ V.X}
    (N : GeometricPushforwardNaturality V H p f)
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) : Prop :=
  if hcod : Order.coheight (f x.1) = p then
    N.cohomologyPushforward (classicalHodgeBasis V H p i).1 =
      pointResidueWeight f x.1 • (classicalHodgeBasis V H p i).1
  else
    N.cohomologyPushforward (classicalHodgeBasis V H p i).1 = 0

/-- **GENUINE PROJECTIVE DEFECT EQUIVARIANCE.**
On one common atom, actual projective transport carries the classical defect
through the actual cohomology pushforward. -/
theorem defect_projectiveTransport_atom_eq_map
    (f : V.X ⟶ V.X)
    (N : GeometricPushforwardNaturality V H p f)
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p)
    (hT : ProjectiveSheetIntertwines N i x) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (fiberedNativePushforward f (atom V H p i x)) =
      N.cohomologyPushforward
        (fiberedCycleClassDefect (V := V) (H := H) (p := p)
          (atom V H p i x)) := by
  rw [fiberedNativePushforward_atom]
  rw [fiberedCycleClassDefect_atom]
  unfold fiberedCycleClassDefect fiberedNativeCycleClass fiberedHodgeAmbient
  rw [LinearMap.sub_apply]
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rw [nativeFace_transportAtom]
  rw [← smoothProjectiveNativePushforward_point V f p x]
  rw [N.naturality]
  rw [map_sub]
  classical
  by_cases hcod : Order.coheight (f x.1) = p
  · rw [fiberedHodgeClass_transportAtom_of_codim f i x hcod]
    simp only [ProjectiveSheetIntertwines, hcod, dite_true] at hT
    rw [hT]
    rfl
  · rw [fiberedHodgeClass_transportAtom_of_wrong_codim f i x hcod]
    simp only [ProjectiveSheetIntertwines, hcod, dite_false] at hT
    rw [hT]
    rfl

/-- Zero defect is stable under a genuine projective transport satisfying the
sheet intertwining law. -/
theorem defectZero_projectiveTransport_atom
    (f : V.X ⟶ V.X)
    (N : GeometricPushforwardNaturality V H p f)
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p)
    (hT : ProjectiveSheetIntertwines N i x)
    (hzero :
      fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (atom V H p i x) = 0) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (fiberedNativePushforward f (atom V H p i x)) = 0 := by
  rw [defect_projectiveTransport_atom_eq_map f N i x hT, hzero]
  exact N.cohomologyPushforward.map_zero

/-- Elementwise classical form: an actual point-cycle representative remains a
valid representative after geometric transport whenever the selected Hodge
sheet transforms with the geometric residue scalar. -/
theorem projectiveTransport_preserves_classical_landing
    (f : V.X ⟶ V.X)
    (N : GeometricPushforwardNaturality V H p f)
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p)
    (hT : ProjectiveSheetIntertwines N i x)
    (hx :
      H.cycleClass p (codimensionPointCycle V.X p x) =
        (classicalHodgeBasis V H p i).1) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (fiberedNativePushforward f (atom V H p i x)) = 0 := by
  apply defectZero_projectiveTransport_atom f N i x hT
  exact (fiberedCycleClassDefect_atom_eq_zero_iff
    (V := V) (H := H) (p := p) i x).2 hx

#check ProjectiveSheetIntertwines
#check defect_projectiveTransport_atom_eq_map
#check defectZero_projectiveTransport_atom
#check projectiveTransport_preserves_classical_landing

#print axioms defect_projectiveTransport_atom_eq_map
#print axioms defectZero_projectiveTransport_atom
#print axioms projectiveTransport_preserves_classical_landing

end GSTClassicalHodgeProjectiveDefectTransport
