import GSTClassicalHodgeFiniteSupportArsenalConjugation
import GSTWorldRecoordinationGroupoid
import GSTClassicalHodgeLiveSheetIntertwining

/-!
# GST CLASSICAL HODGE — RECOORDINATION ARSENAL CROWN

A finite live support of a genuine Hodge class is not tied to one rectangular
GST chart.  Its cardinality `N` is the invariant; any `A x B` presentation
with `A*B=N` is only a recoordination of the same finite state universe.

This module puts the live classical support inside the world-recoordination
groupoid.  Exact code projectors and their spectral polynomials commute with
every recoordination.  Hence the sheet-isolation stage of the full arsenal is
intrinsic to the finite observation, not to the temporary `Fin N` numbering.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiniteSupportArsenalConjugation
open GSTWorldRecoordinationGroupoid
open GSTClassicalHodgeLocalCyclicCriterion

namespace GSTClassicalHodgeRecoordinationArsenalCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Canonical one-row chart of the live finite support. -/
def liveLinearShape (alpha : ClassicalHodgeFiber V H p) :
    GSTWorldShape (liveRank alpha) where
  rows := 1
  cols := liveRank alpha
  area_eq := by simp

/-- A live slot as a state of the canonical one-row GST chart. -/
def liveShapeState
    (alpha : ClassicalHodgeFiber V H p)
    (r : Fin (liveRank alpha)) :
    ShapeState (liveLinearShape alpha) :=
  (⟨0, by simp [liveLinearShape]⟩, r)

@[simp]
theorem liveShapeState_code
    (alpha : ClassicalHodgeFiber V H p)
    (r : Fin (liveRank alpha)) :
    worldCode (liveLinearShape alpha) (liveShapeState alpha r) = r.1 := by
  simp [worldCode_expanded, liveLinearShape, liveShapeState]

/-- Rational live coordinate vector viewed as an integer-independent rational
coefficient field on the canonical shape. -/
def liveShapeCoefQ
    (alpha : ClassicalHodgeFiber V H p) :
    ShapeState (liveLinearShape alpha) → ℚ :=
  fun x => liveCoordinateVector alpha x.2

/-- Rational exact code projector on any shaped live universe. -/
def codeSectorProjQ
    {N : Nat} (S : GSTWorldShape N) (k : Nat)
    (f : ShapeState S → ℚ) : ShapeState S → ℚ :=
  fun x => if worldCode S x = k then f x else 0

/-- Rational coefficient transport through one world recoordination. -/
def transportCoefQ
    {N : Nat} (S T : GSTWorldShape N)
    (f : ShapeState S → ℚ) : ShapeState T → ℚ :=
  fun y => f ((worldRecoordinate S T).symm y)

/-- Recoordination preserves rational code projectors exactly. -/
theorem transportCoefQ_codeSectorProjQ
    {N : Nat} (S T : GSTWorldShape N)
    (k : Nat) (f : ShapeState S → ℚ) :
    transportCoefQ S T (codeSectorProjQ S k f) =
      codeSectorProjQ T k (transportCoefQ S T f) := by
  funext y
  have hcode :
      worldCode S ((worldRecoordinate S T).symm y) = worldCode T y := by
    rw [worldRecoordinate_inverse S T y]
    exact worldRecoordinate_code T S y
  simp only [transportCoefQ, codeSectorProjQ]
  rw [hcode]

/-- The projector for a live classical slot isolates that exact slot in the
canonical live GST chart. -/
theorem live_projector_isolates_slot
    (alpha : ClassicalHodgeFiber V H p)
    (r s : Fin (liveRank alpha)) :
    codeSectorProjQ (liveLinearShape alpha) r.1
        (liveShapeCoefQ alpha) (liveShapeState alpha s) =
      if s = r then liveCoordinateVector alpha r else 0 := by
  by_cases hsr : s = r
  · subst s
    simp only [codeSectorProjQ, liveShapeCoefQ]
    rw [liveShapeState_code, if_pos rfl]
    simp [liveShapeState]
  · have hcode : s.1 ≠ r.1 := by
      intro h
      apply hsr
      exact Fin.ext h
    have hkey : worldCode (liveLinearShape alpha) (liveShapeState alpha s) ≠ r.1 := by
      rw [liveShapeState_code]
      exact hcode
    simp only [codeSectorProjQ, liveShapeCoefQ]
    rw [if_neg hkey, if_neg hsr]

/-- **SHAPE-INDEPENDENT LIVE SHEET ISOLATION.**  Recoordinate the live support
into any equal-cardinality GST world.  Projecting by the invariant state code
and transporting is exactly the same as projecting before recoordination. -/
theorem live_projector_recoordination_natural
    (alpha : ClassicalHodgeFiber V H p)
    (T : GSTWorldShape (liveRank alpha))
    (r : Fin (liveRank alpha)) :
    transportCoefQ (liveLinearShape alpha) T
        (codeSectorProjQ (liveLinearShape alpha) r.1 (liveShapeCoefQ alpha)) =
      codeSectorProjQ T r.1
        (transportCoefQ (liveLinearShape alpha) T (liveShapeCoefQ alpha)) :=
  transportCoefQ_codeSectorProjQ (liveLinearShape alpha) T r.1
    (liveShapeCoefQ alpha)

/-- Every live slot remains nonzero after passage to any recoordination because
its underlying invariant code is unchanged. -/
theorem live_slot_survives_recoordination
    (alpha : ClassicalHodgeFiber V H p)
    (r : Fin (liveRank alpha))
    (T : GSTWorldShape (liveRank alpha)) :
    let y := worldRecoordinate (liveLinearShape alpha) T
      (liveShapeState alpha r)
    transportCoefQ (liveLinearShape alpha) T (liveShapeCoefQ alpha) y ≠ 0 := by
  intro y
  unfold transportCoefQ y
  simp [worldRecoordinate]
  exact liveCoordinateVector_ne_zero_at alpha r

/-- Recoordination crown for one nonzero genuine Hodge state: finite support,
exact live coefficients, sheet projectors and arbitrary world shape are all
compatible. -/
theorem recoordination_arsenal_crown
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    (∃ r : Fin (liveRank alpha), liveCoordinateVector alpha r ≠ 0)
    ∧ (∀ T : GSTWorldShape (liveRank alpha),
      ∀ r : Fin (liveRank alpha),
      transportCoefQ (liveLinearShape alpha) T
          (codeSectorProjQ (liveLinearShape alpha) r.1 (liveShapeCoefQ alpha)) =
        codeSectorProjQ T r.1
          (transportCoefQ (liveLinearShape alpha) T (liveShapeCoefQ alpha))) := by
  have hcard : 0 < liveRank alpha := by
    by_contra h
    have hz : liveRank alpha = 0 := Nat.eq_zero_of_not_pos h
    have hsupp : Fintype.card (HodgeSupportIndex alpha) = 0 := hz
    have hempty : IsEmpty (HodgeSupportIndex alpha) :=
      Fintype.card_eq_zero_iff.mp hsupp
    apply halpha
    apply (classicalHodgeBasis V H p).repr.injective
    apply Finsupp.ext
    intro i
    by_contra hi
    have hzero : ((classicalHodgeBasis V H p).repr alpha) i ≠ 0 := by
      intro h
      exact hi (by simp [h, map_zero])
    have himem : i ∈ ((classicalHodgeBasis V H p).repr alpha).support :=
      Finsupp.mem_support_iff.mpr hzero
    exact isEmptyElim (⟨i, himem⟩ : HodgeSupportIndex alpha)
  let r : Fin (liveRank alpha) := ⟨0, hcard⟩
  exact ⟨⟨r, liveCoordinateVector_ne_zero_at alpha r⟩,
    fun T s => live_projector_recoordination_natural alpha T s⟩

#check liveLinearShape
#check liveShapeState
#check liveShapeState_code
#check codeSectorProjQ
#check transportCoefQ
#check transportCoefQ_codeSectorProjQ
#check live_projector_isolates_slot
#check live_projector_recoordination_natural
#check live_slot_survives_recoordination
#check recoordination_arsenal_crown

#print axioms transportCoefQ_codeSectorProjQ
#print axioms live_projector_recoordination_natural
#print axioms live_slot_survives_recoordination
#print axioms recoordination_arsenal_crown

end GSTClassicalHodgeRecoordinationArsenalCrown
