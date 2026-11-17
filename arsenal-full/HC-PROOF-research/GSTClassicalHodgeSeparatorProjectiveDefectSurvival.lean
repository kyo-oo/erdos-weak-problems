import GSTClassicalHodgeProjectiveDefectTransport
import GSTClassicalHodgeFiberedSeparatorDefect

/-!
# GST CLASSICAL HODGE — SEPARATOR DEFECT SURVIVES ORDINARY PROJECTIVE TRANSPORT

A microscopic Hodge separator cannot be extinguished merely by moving a
native point through an ordinary projective self-map while retaining the same
Hodge multiplicity sheet.

Indeed, when codimension is preserved, both faces acquire the same genuine
residue-degree scalar:

* the native face becomes that scalar times the image point-cycle;
* the Hodge face becomes that scalar times the obstructed basis vector.

The separator annihilates every genuine point-cycle class and detects the
basis vector.  Hence its reading on the transported defect is exactly the
negative residue degree times the original nonzero basis reading.  Whenever
the residue degree is nonzero the defect remains nonzero.

This is an important rigidity statement for the externalization attack: plain
projective point transport cannot solve the fixed-weight multiplicity problem.
Any successful native geometry must genuinely mix Hodge sheets (for example
through a richer correspondence/operator construction), not merely relocate
the underlying projective point.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeSeparatorProjectiveDefectSurvival

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiberedCycleClassDefect
open GSTClassicalHodgeFiberedNativeProjectiveTransport
open GSTClassicalHodgeProjectivePointTransport
open GSTClassicalHodgeProjectiveDefectTransport
open GSTClassicalHodgeSingleSheetCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Exact separator reading after a codimension-preserving ordinary projective
transport in the same obstructed Hodge sheet. -/
theorem separator_reads_projective_transport_defect
    {i : ClassicalHodgeBasisIndex V H p}
    (S : BasisAtomicSeparator V H p i)
    (f : V.X ⟶ V.X)
    (x : CodimensionPoint V.X p)
    (hcod : Order.coheight (f x.1) = p) :
    S.detector
      (fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (fiberedNativePushforward f (atom V H p i x))) =
      - pointResidueWeight f x.1 *
        S.detector (classicalHodgeBasis V H p i).1 := by
  rw [fiberedNativePushforward_atom]
  unfold fiberedCycleClassDefect fiberedNativeCycleClass fiberedHodgeAmbient
  rw [LinearMap.sub_apply]
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rw [nativeFace_transportAtom]
  rw [← smoothProjectiveNativePushforward_point V f p x]
  rw [smoothProjectiveNativePushforward_point]
  rw [nativePointPushforward_eq f p x hcod]
  rw [LinearMap.map_sub, LinearMap.map_smul]
  rw [LinearMap.map_smul]
  rw [S.annihilates_atoms ⟨f x.1, hcod⟩]
  rw [fiberedHodgeClass_transportAtom_of_codim f i x hcod]
  simp

/-- Nonzero residue degree makes the separator reading survive projective
transport. -/
theorem separator_detects_projective_transport_defect
    {i : ClassicalHodgeBasisIndex V H p}
    (S : BasisAtomicSeparator V H p i)
    (f : V.X ⟶ V.X)
    (x : CodimensionPoint V.X p)
    (hcod : Order.coheight (f x.1) = p)
    (hdeg : pointResidueWeight f x.1 ≠ 0) :
    S.detector
      (fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (fiberedNativePushforward f (atom V H p i x))) ≠ 0 := by
  rw [separator_reads_projective_transport_defect S f x hcod]
  exact mul_ne_zero (neg_ne_zero.mpr hdeg) S.detects_basis

/-- Hence the transported fibered defect itself remains nonzero. -/
theorem projective_transport_defect_ne_zero
    {i : ClassicalHodgeBasisIndex V H p}
    (S : BasisAtomicSeparator V H p i)
    (f : V.X ⟶ V.X)
    (x : CodimensionPoint V.X p)
    (hcod : Order.coheight (f x.1) = p)
    (hdeg : pointResidueWeight f x.1 ≠ 0) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
      (fiberedNativePushforward f (atom V H p i x)) ≠ 0 := by
  intro hz
  exact separator_detects_projective_transport_defect S f x hcod hdeg (by
    rw [hz]
    simp)

/-- Ordinary codimension-preserving self-transport with nonzero residue degree
therefore cannot turn an obstructed atom into a classical landing state. -/
theorem not_defectZero_after_sameSheet_projective_transport
    {i : ClassicalHodgeBasisIndex V H p}
    (S : BasisAtomicSeparator V H p i)
    (f : V.X ⟶ V.X)
    (x : CodimensionPoint V.X p)
    (hcod : Order.coheight (f x.1) = p)
    (hdeg : pointResidueWeight f x.1 ≠ 0) :
    ¬ fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (fiberedNativePushforward f (atom V H p i x)) = 0 :=
  projective_transport_defect_ne_zero S f x hcod hdeg

#check separator_reads_projective_transport_defect
#check separator_detects_projective_transport_defect
#check projective_transport_defect_ne_zero
#check not_defectZero_after_sameSheet_projective_transport

#print axioms separator_reads_projective_transport_defect
#print axioms separator_detects_projective_transport_defect
#print axioms projective_transport_defect_ne_zero

end GSTClassicalHodgeSeparatorProjectiveDefectSurvival
