import GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
import GSTClassicalHodgeSingleSheetCrown

/-!
# GST CLASSICAL HODGE — CLOSED-CORRESPONDENCE GHOST EXTINCTION

The omniversal separator formulation turns a Hodge failure into one detector
that kills every algebraic point-cycle class but sees one genuine Hodge basis
sheet.  The realized closed-correspondence algebra gives a geometry-first way
to attack that detector.

A realized correspondence word preserves the actual atomic cycle-class span
because it comes from a native cycle operator with an exact cycle-class square.
Therefore a separator kills the image of EVERY genuine point atom under EVERY
realized correspondence word.

This yields a sharp microscopic contradiction target.  To eliminate the
separator at sheet j it is enough to find:

* one genuine codimension-p point x;
* one finite rational word W of realized closed correspondences;
* one nonzero scalar c;

such that

  W(cl[x]) = c * basis_j.

No matrix-unit naturality is assumed.  This is an actual geometric reachability
statement.  If it is proved, the target sheet is algebraic by rational
rescaling and the separator is impossible.

The final section reconnects this target to the limitless GST arsenal: if a
GST matrix unit E_ij is reachable by genuine realized correspondence words,
then any genuine algebraic Hodge source with nonzero i-coordinate produces a
closed-correspondence hit on j.  Thus the internal rank-free GST machine is
used as the amplification theorem, while the realization burden stays entirely
in genuine projective geometry.
-/

set_option maxHeartbeats 80000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeClosedCorrespondenceGhostExtinction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeSingleSheetCrown
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Every single-sheet separator kills the image of every genuine point atom
under every realized closed-correspondence word. -/
theorem basisSeparator_kills_realizedWord_point
    {j : ClassicalHodgeBasisIndex V H p}
    (S : BasisAtomicSeparator V H p j)
    (W : RealizedCorrespondenceWord V H p)
    (x : CodimensionPoint V.X p) :
    S.detector
      ((realizedWordPair W).cohomologyOperator
        (H.cycleClass p (codimensionPointCycle V.X p x))) = 0 := by
  have hxAtomic :
      H.cycleClass p (codimensionPointCycle V.X p x) ∈
        pointCycleClassSpan p (H.cycleClass p) := by
    exact Submodule.subset_span ⟨x, rfl⟩
  have himage := realizedWord_atomic_stable W _ hxAtomic
  have hker :
      pointCycleClassSpan p (H.cycleClass p) ≤
        LinearMap.ker S.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      p (H.cycleClass p) S.detector).mp S.annihilates_atoms
  exact hker himage

/-- Concrete geometry-first hit on one Hodge sheet: a genuine point class is
sent by a finite rational word of realized closed correspondences to a nonzero
scalar multiple of that basis sheet. -/
def ClosedCorrespondenceHitsSheet
    (j : ClassicalHodgeBasisIndex V H p) : Prop :=
  ∃ x : CodimensionPoint V.X p,
  ∃ W : RealizedCorrespondenceWord V H p,
  ∃ c : ℚ,
    c ≠ 0 ∧
    (realizedWordPair W).cohomologyOperator
        (H.cycleClass p (codimensionPointCycle V.X p x)) =
      c • (classicalHodgeBasis V H p j).1

/-- A realized closed-correspondence hit constructs the targeted basis sheet
inside the genuine atomic cycle-class span. -/
theorem basis_mem_atomicSpan_of_closedCorrespondenceHit
    (j : ClassicalHodgeBasisIndex V H p)
    (hHit : ClosedCorrespondenceHitsSheet (V := V) (H := H) j) :
    (classicalHodgeBasis V H p j).1 ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  rcases hHit with ⟨x,W,c,hc,hEq⟩
  have hxAtomic :
      H.cycleClass p (codimensionPointCycle V.X p x) ∈
        pointCycleClassSpan p (H.cycleClass p) :=
    Submodule.subset_span ⟨x,rfl⟩
  have hImage :
      (realizedWordPair W).cohomologyOperator
        (H.cycleClass p (codimensionPointCycle V.X p x)) ∈
          pointCycleClassSpan p (H.cycleClass p) :=
    realizedWord_atomic_stable W _ hxAtomic
  rw [hEq] at hImage
  have hscaled :=
    (pointCycleClassSpan p (H.cycleClass p)).smul_mem c⁻¹ hImage
  simpa [hc, smul_smul] using hscaled

/-- Hence one closed-correspondence hit makes a separator at that sheet
impossible. -/
theorem isEmpty_basisAtomicSeparator_of_closedCorrespondenceHit
    (j : ClassicalHodgeBasisIndex V H p)
    (hHit : ClosedCorrespondenceHitsSheet (V := V) (H := H) j) :
    IsEmpty (BasisAtomicSeparator V H p j) :=
  (basis_mem_atomicSpan_iff_no_separator V H p j).mp
    (basis_mem_atomicSpan_of_closedCorrespondenceHit j hHit)

/-- Global geometric-hit criterion for the exact Stage-2G Hodge statement. -/
theorem bigradedBettiHodge_of_closedCorrespondenceHits
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hHit : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        ClosedCorrespondenceHitsSheet (V := V) (H := H) j) :
    BigradedBettiHodgeStatement V H := by
  apply (bigradedBettiHodgeStatement_iff_no_basis_separator V H).mpr
  intro q j
  exact isEmpty_basisAtomicSeparator_of_closedCorrespondenceHit j (hHit q j)

/-! ## Reconnection to the limitless GST matrix-unit arsenal -/

/-- If the GST matrix unit E_ij is realized by a genuine closed-correspondence
word, then any genuine point class whose Hodge representative has nonzero
source i-coordinate hits target sheet j.

The source class is required to be Hodge only so that the rank-free matrix-unit
formula is meaningful; that Hodge property is independently supplied by the
geometric cycle-class spine for actual point cycles. -/
theorem closedCorrespondenceHit_of_matrixUnitReachable_point
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (i j : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p)
    (hi : hodgeCoordinate i
      (⟨H.cycleClass p (codimensionPointCycle V.X p x),
        G.pointClass_is_hodge p x⟩ : ClassicalHodgeFiber V H p) ≠ 0)
    (hReach : MatrixUnitReachableByClosedCorrespondences
      (V := V) (H := H) i j) :
    ClosedCorrespondenceHitsSheet (V := V) (H := H) j := by
  rcases hReach with ⟨W,hW⟩
  let alpha : ClassicalHodgeFiber V H p :=
    ⟨H.cycleClass p (codimensionPointCycle V.X p x),
      G.pointClass_is_hodge p x⟩
  refine ⟨x,W,hodgeCoordinate i alpha,hi,?_⟩
  have h := hW alpha
  rw [hodgeMatrixUnit_apply] at h
  exact h

/-- Therefore, if one genuine point Hodge class has a live source coordinate
and E_ij is geometrically reachable, no separator can survive at j. -/
theorem isEmpty_separator_of_matrixUnitReachable_point
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (i j : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p)
    (hi : hodgeCoordinate i
      (⟨H.cycleClass p (codimensionPointCycle V.X p x),
        G.pointClass_is_hodge p x⟩ : ClassicalHodgeFiber V H p) ≠ 0)
    (hReach : MatrixUnitReachableByClosedCorrespondences
      (V := V) (H := H) i j) :
    IsEmpty (BasisAtomicSeparator V H p j) :=
  isEmpty_basisAtomicSeparator_of_closedCorrespondenceHit j
    (closedCorrespondenceHit_of_matrixUnitReachable_point G i j x hi hReach)

#check basisSeparator_kills_realizedWord_point
#check ClosedCorrespondenceHitsSheet
#check basis_mem_atomicSpan_of_closedCorrespondenceHit
#check isEmpty_basisAtomicSeparator_of_closedCorrespondenceHit
#check bigradedBettiHodge_of_closedCorrespondenceHits
#check closedCorrespondenceHit_of_matrixUnitReachable_point
#check isEmpty_separator_of_matrixUnitReachable_point

#print axioms basisSeparator_kills_realizedWord_point
#print axioms basis_mem_atomicSpan_of_closedCorrespondenceHit
#print axioms bigradedBettiHodge_of_closedCorrespondenceHits
#print axioms isEmpty_separator_of_matrixUnitReachable_point

end GSTClassicalHodgeClosedCorrespondenceGhostExtinction
