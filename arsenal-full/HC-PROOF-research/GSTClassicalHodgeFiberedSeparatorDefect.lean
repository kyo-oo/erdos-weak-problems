import GSTClassicalHodgeFiberedCycleClassDefect
import GSTClassicalHodgeSingleSheetCrown
import GSTClassicalHodgeNormalizedFiberedSpectralAtom
import GSTWorldRecoordinationGroupoid
import GSTClassicalHodgeFiniteSupportArsenalConjugation
import GSTClassicalHodgeFiberedNativeRecoordination

/-!
# GST CLASSICAL HODGE — SINGLE-SHEET SEPARATORS AS FIBERED DEFECT DETECTORS

The single-sheet crown reduces failure of the classical target to one genuine
Hodge basis direction and one rational detector which annihilates every actual
codimension-p point-cycle class while detecting that basis vector.

The fibered cycle-class defect puts the native and classical faces in one
ambient cohomology space.  On a common atom carrying the obstructed basis
label, the detector kills the native face by definition and therefore reads
exactly the negative of its nonzero Hodge-basis value.

Thus a microscopic Hodge failure is already a nonzero event in the same
fibered/limitless common-refinement universe used by the GST projector,
recoordination, Poincare and projective-transport machinery.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFiberedSeparatorDefect

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiberedCycleClassDefect
open GSTClassicalHodgeNormalizedFiberedSpectralAtom
open GSTClassicalHodgeAtomicAnnihilator
open GSTWorldRecoordinationGroupoid
open GSTClassicalHodgeFiniteSupportArsenalConjugation
open GSTClassicalHodgeSingleSheetCrown
open GSTClassicalHodgeFiberedNativeRecoordination

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- An atomic separator evaluates the defect of every common atom in its
obstructed Hodge sheet as minus its nonzero basis reading. -/
theorem separator_reads_atom_defect
    {i : ClassicalHodgeBasisIndex V H p}
    (S : BasisAtomicSeparator V H p i)
    (x : CodimensionPoint V.X p) :
    S.detector
      (fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (atom V H p i x)) =
      - S.detector (classicalHodgeBasis V H p i).1 := by
  rw [fiberedCycleClassDefect_atom]
  rw [map_sub]
  rw [S.annihilates_atoms x]
  simp

/-- Therefore every genuine point atom in the obstructed multiplicity sheet
has nonzero classical defect as seen by the separator. -/
theorem separator_detects_atom_defect
    {i : ClassicalHodgeBasisIndex V H p}
    (S : BasisAtomicSeparator V H p i)
    (x : CodimensionPoint V.X p) :
    S.detector
      (fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (atom V H p i x)) ≠ 0 := by
  rw [separator_reads_atom_defect S x]
  exact neg_ne_zero.mpr S.detects_basis

/-- In particular the defect itself is nonzero on every such common atom. -/
theorem atom_defect_ne_zero_of_separator
    {i : ClassicalHodgeBasisIndex V H p}
    (S : BasisAtomicSeparator V H p i)
    (x : CodimensionPoint V.X p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
      (atom V H p i x) ≠ 0 := by
  intro hz
  exact absurd
    (show S.detector (fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (atom V H p i x)) = 0 by rw [hz]; simp)
    (separator_detects_atom_defect S x)

/-- The same detector identity holds for a normalized GST spectral atom as
soon as that live state is the obstructed basis sheet. -/
theorem separator_reads_normalizedSpectralAtom_defect
    {i : ClassicalHodgeBasisIndex V H p}
    (Sep : BasisAtomicSeparator V H p i)
    (alpha : ClassicalHodgeFiber V H p)
    (W : GSTWorldShape (liveRank alpha))
    (y : ShapeState W)
    (x : CodimensionPoint V.X p)
    (hy : shapedLiveBasisIndex alpha W y = i) :
    Sep.detector
      (fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (normalizedSpectralAtom alpha W y x)) =
      - Sep.detector (classicalHodgeBasis V H p i).1 := by
  rw [normalizedSpectralAtom_defect]
  rw [map_sub]
  rw [Sep.annihilates_atoms x]
  rw [hy]
  simp

/-- Hence a normalized live spectral atom in the obstructed sheet is detected
nontrivially while its native and limitless faces remain the exact unit faces
proved by the normalized spectral crown. -/
theorem separator_detects_normalizedSpectralAtom_defect
    {i : ClassicalHodgeBasisIndex V H p}
    (Sep : BasisAtomicSeparator V H p i)
    (alpha : ClassicalHodgeFiber V H p)
    (W : GSTWorldShape (liveRank alpha))
    (y : ShapeState W)
    (x : CodimensionPoint V.X p)
    (hy : shapedLiveBasisIndex alpha W y = i) :
    Sep.detector
      (fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (normalizedSpectralAtom alpha W y x)) ≠ 0 := by
  rw [separator_reads_normalizedSpectralAtom_defect Sep alpha W y x hy]
  exact neg_ne_zero.mpr Sep.detects_basis

/-- Microscopic failure package inside the common limitless universe. -/
structure FiberedDefectEvent
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H p) where
  separator : BasisAtomicSeparator V H p i
  point : CodimensionPoint V.X p
  state : FiberedNativeAddress V H p := atom V H p i point
  state_eq_atom : state = atom V H p i point := by rfl
  detector_nonzero :
    separator.detector
      (fiberedCycleClassDefect (V := V) (H := H) (p := p) state) ≠ 0

/-- Every basis separator and every genuine codimension-p point canonically
produce a nonzero fibered defect event. -/
noncomputable def defectEventOfSeparator
    {i : ClassicalHodgeBasisIndex V H p}
    (S : BasisAtomicSeparator V H p i)
    (x : CodimensionPoint V.X p) :
    FiberedDefectEvent V H p i where
  separator := S
  point := x
  state := atom V H p i x
  state_eq_atom := rfl
  detector_nonzero := separator_detects_atom_defect S x

/-- A full Stage-2G failure plus one native point in the obstructed weight is
therefore already a nonzero event in the exact fibered defect universe. -/
theorem not_hodge_yields_fibered_defect_event_of_point
    (hnot : ¬ BigradedBettiHodgeStatement V H)
    (choosePoint :
      ∀ p : Nat, ∀ i : ClassicalHodgeBasisIndex V H p,
        Nonempty (CodimensionPoint V.X p)) :
    ∃ p : Nat,
    ∃ i : ClassicalHodgeBasisIndex V H p,
      Nonempty (FiberedDefectEvent V H p i) := by
  obtain ⟨p, i, ⟨Sep⟩⟩ :=
    (not_bigradedBettiHodgeStatement_iff_exists_basis_separator V H).mp hnot
  obtain ⟨x⟩ := choosePoint p i
  exact ⟨p, i, ⟨defectEventOfSeparator Sep x⟩⟩

#check separator_reads_atom_defect
#check separator_detects_atom_defect
#check atom_defect_ne_zero_of_separator
#check separator_reads_normalizedSpectralAtom_defect
#check FiberedDefectEvent
#check defectEventOfSeparator

#print axioms separator_reads_atom_defect
#print axioms separator_detects_atom_defect
#print axioms atom_defect_ne_zero_of_separator
#print axioms separator_reads_normalizedSpectralAtom_defect

end GSTClassicalHodgeFiberedSeparatorDefect
