import GSTClassicalHodgeLimitlessCosmicMatrixUnits
import GSTClassicalHodgeConcreteArsenalConjugation
import GSTClassicalHodgeIntegralSquareLocalization
import GSTClassicalHodgeSupportCardinalityBridge
import GSTClassicalHodgeTotalSheetMatrixUnit

/-!
# GST CLASSICAL HODGE — LIMITLESS ARSENAL CONJUGATION

The classical live-sheet matrix units are not independent finite gadgets.
Every genuine Hodge class has finite support, hence an integral pure-square
model.  This file embeds that finite pure square into the actual unbounded
compact GST cosmos and proves that the previously constructed finite
projector/Lefschetz/Poincare matrix unit is exactly the finite rational shadow
of the limitless cosmic Poincare read/write matrix unit.

The conjugation route is therefore

  genuine Hodge fiber
    -> finite-support integral square
    -> compact limitless pure cosmos
    -> cosmic Poincare read/write E_rs
    -> finite observation
    -> rational live-basis readback
    -> rank-free classical Hodge E_ij.

No fixed global Hodge rank occurs anywhere in this route.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeLimitlessArsenalConjugation

open GSTWorldCosmology
open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTGlobalPureHodgeCosmology
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeIntegralSquareLocalization
open GSTClassicalHodgeSupportCardinalityBridge
open GSTClassicalHodgeTotalSheetMatrixUnit
open GSTClassicalHodgeConcreteArsenalConjugation
open GSTClassicalHodgeLimitlessCosmicMatrixUnits
open GSTClassicalHodgeLiveSheetIntertwining
open GSTClassicalHodgeFiniteSupportArsenalConjugation
open GSTClassicalHodgeFiniteSupportChart
open GSTClassicalHodgeRankFreeArsenalIrreducibility

/-- Embed one finite integral pure square into the genuine compact cosmos by
placing every diagonal coefficient at the identically numbered cosmic weight. -/
def squareDiagonalToCosmos
    {N : ℕ} (f : WorldCoef N N) : CompactCosmos :=
  ∑ r : Fin N, Finsupp.single (r.1,r.1) (f (r,r))

/-- The cosmic embedding reads back every finite diagonal coefficient exactly. -/
@[simp]
theorem squareDiagonalToCosmos_diagonal
    {N : ℕ} (f : WorldCoef N N) (r : Fin N) :
    squareDiagonalToCosmos f (r.1,r.1) = f (r,r) := by
  classical
  unfold squareDiagonalToCosmos
  rw [Finsupp.coe_finset_sum, Finset.sum_apply, Finset.sum_eq_single r]
  · simp
  · intro s hs hsr
    have hval : s.1 ≠ r.1 := by
      intro h
      exact hsr (Fin.ext h)
    simp [hval]
  · simp

/-- Off the cosmic diagonal the embedded finite square vanishes. -/
theorem squareDiagonalToCosmos_off_diagonal
    {N : ℕ} (f : WorldCoef N N)
    (c : CosmicCell) (hc : c.1 ≠ c.2) :
    squareDiagonalToCosmos f c = 0 := by
  classical
  unfold squareDiagonalToCosmos
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [Finsupp.single_apply]
  exact if_neg (fun hcon =>
    hc ((congrArg Prod.fst hcon).symm.trans (congrArg Prod.snd hcon)))

/-- Every finite square embeds into the compact pure-Hodge cosmos after its
off-diagonal part has been discarded.  If the source is already pure, nothing
is lost. -/
def squareDiagonalPureCosmos
    {N : ℕ} (f : WorldCoef N N) : compactPureHodge :=
  ⟨squareDiagonalToCosmos f, by
    intro c hc
    exact squareDiagonalToCosmos_off_diagonal f c hc⟩

/-- For a pure finite square, observing its cosmic embedding recovers the
original finite world exactly. -/
theorem observe_squareDiagonalToCosmos
    {N : ℕ} (f : WorldCoef N N)
    (hf : isWorldPureHodge f) :
    observe N N (squareDiagonalToCosmos f) = f := by
  funext c
  by_cases hdiag : c.1.1 = c.2.1
  · have heq : c.1 = c.2 := Fin.ext hdiag
    rw [show c = (c.2, c.2) from Prod.ext heq rfl]
    simp only [observe]
    simpa using squareDiagonalToCosmos_diagonal f c.2
  · have hc : (c.1.1,c.2.1).1 ≠ (c.1.1,c.2.1).2 := hdiag
    rw [hf c hdiag]
    exact squareDiagonalToCosmos_off_diagonal f (c.1.1,c.2.1) hc

/-- **FINITE TOTAL MATRIX UNIT = LIMITLESS COSMIC SHADOW.**
For every pure integral square, the explicit finite projector/Lefschetz/
Poincare matrix unit is exactly the rational cast of the unbounded cosmic
Poincare read/write matrix unit, observed in the same finite window. -/
theorem totalSheetMatrixUnit_eq_cosmic_shadow
    {N : ℕ} (r s : Fin N)
    (f : WorldCoef N N)
    (hf : isWorldPureHodge f)
    (x : WorldCell N N) :
    totalSheetMatrixUnit r s f x =
      ((cosmicDiagonalMatrixUnit r.1 s.1
          (squareDiagonalToCosmos f)) (x.1.1,x.2.1) : ℚ) := by
  rw [totalSheetMatrixUnit_exact r s f hf]
  rw [cosmicDiagonalMatrixUnit_apply]
  rw [squareDiagonalToCosmos_diagonal]
  by_cases hx : x = (s,s)
  · subst x
    simp
  · have hcos : (x.1.1,x.2.1) ≠ (s.1,s.1) := by
      intro h
      apply hx
      apply Prod.ext
      · apply Fin.ext
        exact congrArg Prod.fst h
      · apply Fin.ext
        exact congrArg Prod.snd h
    simp [hx, hcos]

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : ℕ}

/-- The actual denominator-cleared classical Hodge state, now regarded as one
compact state of the limitless GST cosmos. -/
noncomputable def integralHodgeCosmos
    (alpha : ClassicalHodgeFiber V H p) : CompactCosmos :=
  squareDiagonalToCosmos (integralHodgeSquare alpha).world

/-- Every live classical basis slot reads from the same coordinate in the
limitless compact cosmos. -/
theorem integralHodgeCosmos_live_coefficient
    (alpha : ClassicalHodgeFiber V H p)
    (r : Fin (liveRank alpha)) :
    integralHodgeCosmos alpha
      ((squareSheetOfLiveSlot alpha r).1,
       (squareSheetOfLiveSlot alpha r).1) =
      (integralHodgeSquare alpha).world
        (squareSheetOfLiveSlot alpha r,
         squareSheetOfLiveSlot alpha r) := by
  exact squareDiagonalToCosmos_diagonal
    (integralHodgeSquare alpha).world (squareSheetOfLiveSlot alpha r)

/-- Hence every live classical slot is genuinely nonzero in the unbounded
cosmos after denominator clearing. -/
theorem integralHodgeCosmos_live_ne_zero
    (alpha : ClassicalHodgeFiber V H p)
    (r : Fin (liveRank alpha)) :
    integralHodgeCosmos alpha
      ((squareSheetOfLiveSlot alpha r).1,
       (squareSheetOfLiveSlot alpha r).1) ≠ 0 := by
  rw [integralHodgeCosmos_live_coefficient]
  exact integralHodgeSquare_squareSheet_ne_zero alpha r

/-- Apply the true cosmic matrix unit between the two unbounded weights selected
by live classical slots. -/
noncomputable def liveCosmicMatrixUnit
    (alpha : ClassicalHodgeFiber V H p)
    (r s : Fin (liveRank alpha)) : CompactCosmos :=
  cosmicDiagonalMatrixUnit
    (squareSheetOfLiveSlot alpha r).1
    (squareSheetOfLiveSlot alpha s).1
    (integralHodgeCosmos alpha)

/-- The limitless matrix unit writes exactly the denominator-cleared source
coefficient into the target cosmic diagonal weight. -/
theorem liveCosmicMatrixUnit_exact
    (alpha : ClassicalHodgeFiber V H p)
    (r s : Fin (liveRank alpha)) :
    liveCosmicMatrixUnit alpha r s =
      Finsupp.single
        ((squareSheetOfLiveSlot alpha s).1,
         (squareSheetOfLiveSlot alpha s).1)
        ((integralHodgeSquare alpha).world
          (squareSheetOfLiveSlot alpha r,
           squareSheetOfLiveSlot alpha r)) := by
  simp only [liveCosmicMatrixUnit, integralHodgeCosmos,
    cosmicDiagonalMatrixUnit_apply]
  congr 1
  exact squareDiagonalToCosmos_diagonal (integralHodgeSquare alpha).world
    (squareSheetOfLiveSlot alpha r)

/-- The historical finite total-sheet operator is therefore precisely the
finite rational observation of `liveCosmicMatrixUnit`. -/
theorem totalSheetMatrixUnit_is_liveCosmic_shadow
    (alpha : ClassicalHodgeFiber V H p)
    (r s : Fin (liveRank alpha))
    (x : WorldCell
      (fiberedSupportSize (fiberedWeightCoordinates V H p alpha))
      (fiberedSupportSize (fiberedWeightCoordinates V H p alpha))) :
    totalSheetMatrixUnit
        (squareSheetOfLiveSlot alpha r)
        (squareSheetOfLiveSlot alpha s)
        (integralHodgeSquare alpha).world x =
      ((liveCosmicMatrixUnit alpha r s)
        (x.1.1,x.2.1) : ℚ) := by
  exact totalSheetMatrixUnit_eq_cosmic_shadow
    (squareSheetOfLiveSlot alpha r)
    (squareSheetOfLiveSlot alpha s)
    (integralHodgeSquare alpha).world
    (integralHodgeSquare alpha).world_pure x

/-- **CLASSICAL MATRIX UNIT IS A LIMITLESS COSMIC MATRIX UNIT SHADOW.**
The already-proved classical conjugation theorem and the new cosmic-shadow
identity together identify every live rank-free classical matrix-unit value
with an unbounded cosmic Poincare read/write operation. -/
theorem classical_matrixUnit_has_limitless_cosmic_model
    (alpha : ClassicalHodgeFiber V H p)
    (r s : Fin (liveRank alpha)) :
    concreteHodgeMatrixUnit alpha r s =
      hodgeMatrixUnit (liveBasisIndex alpha r)
        (liveBasisIndex alpha s) alpha
    ∧ liveCosmicMatrixUnit alpha r s =
      Finsupp.single
        ((squareSheetOfLiveSlot alpha s).1,
         (squareSheetOfLiveSlot alpha s).1)
        ((integralHodgeSquare alpha).world
          (squareSheetOfLiveSlot alpha r,
           squareSheetOfLiveSlot alpha r)) := by
  exact ⟨concreteHodgeMatrixUnit_eq alpha r s,
    liveCosmicMatrixUnit_exact alpha r s⟩

/-- Crown: every finite live classical matrix unit is simultaneously an exact
GST finite arsenal word and the observation of one genuine limitless cosmic
matrix unit. -/
theorem limitless_arsenal_conjugation_crown
    (alpha : ClassicalHodgeFiber V H p) :
    ∀ r s : Fin (liveRank alpha),
      concreteHodgeMatrixUnit alpha r s =
        hodgeMatrixUnit (liveBasisIndex alpha r)
          (liveBasisIndex alpha s) alpha
      ∧ ∀ x : WorldCell
          (fiberedSupportSize (fiberedWeightCoordinates V H p alpha))
          (fiberedSupportSize (fiberedWeightCoordinates V H p alpha)),
        totalSheetMatrixUnit
            (squareSheetOfLiveSlot alpha r)
            (squareSheetOfLiveSlot alpha s)
            (integralHodgeSquare alpha).world x =
          ((liveCosmicMatrixUnit alpha r s)
            (x.1.1,x.2.1) : ℚ) := by
  intro r s
  exact ⟨concreteHodgeMatrixUnit_eq alpha r s,
    totalSheetMatrixUnit_is_liveCosmic_shadow alpha r s⟩

#check squareDiagonalToCosmos
#check observe_squareDiagonalToCosmos
#check totalSheetMatrixUnit_eq_cosmic_shadow
#check integralHodgeCosmos
#check liveCosmicMatrixUnit
#check liveCosmicMatrixUnit_exact
#check totalSheetMatrixUnit_is_liveCosmic_shadow
#check classical_matrixUnit_has_limitless_cosmic_model
#check limitless_arsenal_conjugation_crown

#print axioms observe_squareDiagonalToCosmos
#print axioms totalSheetMatrixUnit_eq_cosmic_shadow
#print axioms liveCosmicMatrixUnit_exact
#print axioms totalSheetMatrixUnit_is_liveCosmic_shadow
#print axioms limitless_arsenal_conjugation_crown

end GSTClassicalHodgeLimitlessArsenalConjugation
