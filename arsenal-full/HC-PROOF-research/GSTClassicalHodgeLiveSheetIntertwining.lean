import GSTClassicalHodgeSheetSpectralExtraction
import GSTClassicalHodgeLocalCyclicCriterion

/-!
# GST CLASSICAL HODGE — LIVE SHEET INTERTWINING

This file identifies the finite multiplicity-sheet index used by the GST
square/projector machinery with the *actual* live basis-support index of a
genuine classical Hodge class.

For a class `alpha` of weight `p` and a live basis direction `i`:

* `(p,i)` is a live fibered limitless address;
* the canonical finite-support equivalence sends it to one unique `Fin N`
  sheet;
* the rational support-square coefficient at that sheet is exactly the
  original Hodge basis coefficient;
* denominator clearing preserves its nonzeroness;
* the existing integer code-sector projector isolates exactly that nonzero
  integral sheet atom.

Thus the local GST sheet projector is not an anonymous finite-world index: it
is canonically tethered to one concrete live classical Hodge multiplicity
direction.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTDimensionFreeHodgeDiagonal
open GSTWorldRecoordinationGroupoid
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeLocalCyclicCriterion
open GSTClassicalHodgeFiniteSupportChart
open GSTClassicalHodgeSquareStrandLocalization
open GSTClassicalHodgeIntegralSquareLocalization
open GSTClassicalHodgeSheetSpectralExtraction

namespace GSTClassicalHodgeLiveSheetIntertwining

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The total fibered address of one live basis direction. -/
def liveFiberedIndex
    {alpha : ClassicalHodgeFiber V H p}
    (i : HodgeSupportIndex alpha) : FiberedHodgeIndex V H :=
  ⟨p, i.1⟩

/-- A live Hodge basis coordinate remains live after embedding into the total
fibered limitless address universe. -/
theorem liveFiberedIndex_mem_support
    (alpha : ClassicalHodgeFiber V H p)
    (i : HodgeSupportIndex alpha) :
    liveFiberedIndex i ∈
      (fiberedWeightCoordinates V H p alpha).support := by
  rw [Finsupp.mem_support_iff]
  show (Finsupp.embDomain (Function.Embedding.sigmaMk p)
      ((classicalHodgeBasis V H p).repr alpha))
      (Function.Embedding.sigmaMk p i.1) ≠ 0
  rw [Finsupp.embDomain_apply_self]
  exact support_coefficient_ne_zero alpha i

/-- The corresponding live fibered-address subtype element. -/
noncomputable def liveFiberedAddress
    (alpha : ClassicalHodgeFiber V H p)
    (i : HodgeSupportIndex alpha) :
    LiveFiberedAddress (fiberedWeightCoordinates V H p alpha) :=
  ⟨liveFiberedIndex i, liveFiberedIndex_mem_support alpha i⟩

/-- Canonical local GST sheet occupied by one live classical Hodge basis
coordinate. -/
noncomputable def liveSheetIndex
    (alpha : ClassicalHodgeFiber V H p)
    (i : HodgeSupportIndex alpha) :
    Fin (fiberedSupportSize (fiberedWeightCoordinates V H p alpha)) :=
  fiberedSupportEquivFin (fiberedWeightCoordinates V H p alpha)
    (liveFiberedAddress alpha i)

/-- The finite square coefficient at the associated GST sheet is literally
the original genuine Hodge basis coefficient. -/
theorem supportDiagonalWorld_liveSheet
    (alpha : ClassicalHodgeFiber V H p)
    (i : HodgeSupportIndex alpha) :
    supportDiagonalWorld (fiberedWeightCoordinates V H p alpha)
        (liveSheetIndex alpha i, liveSheetIndex alpha i) =
      (classicalHodgeBasis V H p).repr alpha i.1 := by
  rw [supportDiagonalWorld_at_diagonal]
  have haddr : ((fiberedSupportEquivFin
      (fiberedWeightCoordinates V H p alpha)).symm
      (liveSheetIndex alpha i)).1 = liveFiberedIndex i := by
    have h1 := (fiberedSupportEquivFin
      (fiberedWeightCoordinates V H p alpha)).symm_apply_apply
      (liveFiberedAddress alpha i)
    show ((fiberedSupportEquivFin
      (fiberedWeightCoordinates V H p alpha)).symm
      ((fiberedSupportEquivFin
        (fiberedWeightCoordinates V H p alpha))
        (liveFiberedAddress alpha i))).1 = liveFiberedIndex i
    rw [h1]
    rfl
  rw [haddr]
  show (Finsupp.embDomain (Function.Embedding.sigmaMk p)
      ((classicalHodgeBasis V H p).repr alpha))
      (Function.Embedding.sigmaMk p i.1) =
    (classicalHodgeBasis V H p).repr alpha i.1
  rw [Finsupp.embDomain_apply_self]

/-- Every such local sheet coefficient is nonzero. -/
theorem supportDiagonalWorld_liveSheet_ne_zero
    (alpha : ClassicalHodgeFiber V H p)
    (i : HodgeSupportIndex alpha) :
    supportDiagonalWorld (fiberedWeightCoordinates V H p alpha)
        (liveSheetIndex alpha i, liveSheetIndex alpha i) ≠ 0 := by
  rw [supportDiagonalWorld_liveSheet alpha i]
  exact support_coefficient_ne_zero alpha i

/-- Canonical integral pure-square model of the localized genuine Hodge
state. -/
noncomputable def integralHodgeSquare
    (alpha : ClassicalHodgeFiber V H p) :=
  canonicalIntegralPureSquareModel
    (supportDiagonalWorld (fiberedWeightCoordinates V H p alpha))
    (supportDiagonalWorld_isPure
      (fiberedWeightCoordinates V H p alpha))

/-- Denominator clearing does not erase a live Hodge sheet. -/
theorem integralHodgeSquare_liveSheet_ne_zero
    (alpha : ClassicalHodgeFiber V H p)
    (i : HodgeSupportIndex alpha) :
    (integralHodgeSquare alpha).world
      (liveSheetIndex alpha i, liveSheetIndex alpha i) ≠ 0 := by
  intro hz
  have hscaled := (integralHodgeSquare alpha).scaled_eq
    (liveSheetIndex alpha i, liveSheetIndex alpha i)
  have hcast : ((integralHodgeSquare alpha).world
      (liveSheetIndex alpha i, liveSheetIndex alpha i) : ℚ) = 0 := by
    simp [hz]
  have hcombined : ((integralHodgeSquare alpha).scale : ℚ) *
      supportDiagonalWorld (fiberedWeightCoordinates V H p alpha)
        (liveSheetIndex alpha i, liveSheetIndex alpha i) = 0 := by
    rw [← hcast]
    exact hscaled
  have hscale : ((integralHodgeSquare alpha).scale : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (integralHodgeSquare alpha).scale_pos
  exact supportDiagonalWorld_liveSheet_ne_zero alpha i
    ((mul_eq_zero.mp hcombined).resolve_left hscale)

/-- The existing integer GST code-sector projector at the tethered live sheet
is exactly the corresponding nonzero diagonal sheet atom. -/
theorem sheetProjector_integralHodgeSquare_eq_liveAtom
    (alpha : ClassicalHodgeFiber V H p)
    (i : HodgeSupportIndex alpha) :
    sheetSpectralProj (liveSheetIndex alpha i)
        (integralHodgeSquare alpha).world =
      sheetDiagonalAtom (liveSheetIndex alpha i)
        ((integralHodgeSquare alpha).world
          (liveSheetIndex alpha i, liveSheetIndex alpha i)) := by
  exact sheetSpectralProj_pure_eq_atom
    (liveSheetIndex alpha i)
    (integralHodgeSquare alpha).world
    (integralHodgeSquare alpha).world_pure

/-- Consequently the projected GST sheet is nonzero. -/
theorem sheetProjector_integralHodgeSquare_ne_zero
    (alpha : ClassicalHodgeFiber V H p)
    (i : HodgeSupportIndex alpha) :
    sheetSpectralProj (liveSheetIndex alpha i)
      (integralHodgeSquare alpha).world ≠ 0 := by
  rw [sheetProjector_integralHodgeSquare_eq_liveAtom alpha i]
  intro hz
  have hdiag1 : worldDiagonalClass (liveSheetIndex alpha i).2
      (liveSheetIndex alpha i).2
      (liveSheetIndex alpha i, liveSheetIndex alpha i) = 1 := by
    simp [worldDiagonalClass, GSTUniversalAddressBridge.worldBasis]
    rfl
  have hdiag0 : ((integralHodgeSquare alpha).world
      (liveSheetIndex alpha i, liveSheetIndex alpha i)) *
      worldDiagonalClass (liveSheetIndex alpha i).2
        (liveSheetIndex alpha i).2
        (liveSheetIndex alpha i, liveSheetIndex alpha i) = 0 :=
    congrFun hz (liveSheetIndex alpha i, liveSheetIndex alpha i)
  rw [hdiag1, mul_one] at hdiag0
  exact integralHodgeSquare_liveSheet_ne_zero alpha i hdiag0

/-- The tethered projector is an explicit integer spectral polynomial with a
nonzero normalization scalar. -/
theorem liveSheet_projector_is_polynomial
    (alpha : ClassicalHodgeFiber V H p)
    (i : HodgeSupportIndex alpha) :
    ∃ (P : Polynomial ℤ) (c : ℤ), c ≠ 0 ∧
      ∀ (f : ShapeCoef
          (outputShape
            (fiberedSupportSize (fiberedWeightCoordinates V H p alpha))
            (fiberedSupportSize (fiberedWeightCoordinates V H p alpha))))
        (x : ShapeState
          (outputShape
            (fiberedSupportSize (fiberedWeightCoordinates V H p alpha))
            (fiberedSupportSize (fiberedWeightCoordinates V H p alpha)))),
        codePolyOp
          (outputShape
            (fiberedSupportSize (fiberedWeightCoordinates V H p alpha))
            (fiberedSupportSize (fiberedWeightCoordinates V H p alpha)))
          P f x =
          c * sheetSpectralProj (liveSheetIndex alpha i) f x := by
  exact sheetSpectralProj_is_polynomial (liveSheetIndex alpha i)

#check liveFiberedIndex
#check liveFiberedAddress
#check liveSheetIndex
#check supportDiagonalWorld_liveSheet
#check integralHodgeSquare
#check integralHodgeSquare_liveSheet_ne_zero
#check sheetProjector_integralHodgeSquare_eq_liveAtom
#check sheetProjector_integralHodgeSquare_ne_zero
#check liveSheet_projector_is_polynomial

#print axioms supportDiagonalWorld_liveSheet
#print axioms integralHodgeSquare_liveSheet_ne_zero
#print axioms sheetProjector_integralHodgeSquare_eq_liveAtom
#print axioms sheetProjector_integralHodgeSquare_ne_zero
#print axioms liveSheet_projector_is_polynomial

end GSTClassicalHodgeLiveSheetIntertwining
