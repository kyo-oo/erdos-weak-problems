import GSTClassicalHodgeIntegralSquareLocalization
import GSTClassicalHodgeLefschetzTomography
import GSTClassicalHodgeLimitlessArsenalConjugation
import GSTClassicalHodgeTotalSheetMatrixUnit
import GSTTruncatedWorldCohomologyRing
import GSTWorldPoincareDuality

/-!
# GST CLASSICAL HODGE — OMNIVERSAL FAILURE PACKET

A hypothetical failure of the genuine Stage-2G Hodge target has already been
compressed upstream to one finite integral pure-Hodge square with nonzero
Poincare pairing.  This file pushes that *same* witness through the rest of the
repo-wide cosmology instead of choosing one preferred description.

The packet simultaneously exposes:

* nonzero integral pure coordinates;
* nonzero exact Lefschetz tomography moments;
* the dimension-free truncated cohomology-ring realization of every forward
  tomography coefficient;
* a nonzero explicit projector/Lefschetz/Poincare orbit from one live sheet to
  every target sheet;
* a nonzero embedding of the same square into the limitless compact pure
  cosmos;
* exact identification of every finite total-sheet transfer with the
  corresponding limitless cosmic matrix-unit shadow.

Thus a classical failure cannot hide in an abstract separator.  It must survive
as one coherent nonzero state in the finite world, the cohomology-ring world,
the Poincare/Lefschetz world, and the limitless cosmic world at once.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeOmniversalFailurePacket

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTWorldCosmology
open GSTWorldPoincareDuality
open GSTWorldRecoordinationGroupoid
open GSTGlobalPureHodgeCosmology
open GSTTruncatedWorldCohomologyRing
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeLefschetzTomography
open GSTClassicalHodgeIntegralSquareLocalization
open GSTClassicalHodgeTotalSheetMatrixUnit
open GSTClassicalHodgeLimitlessArsenalConjugation
open GSTClassicalHodgeLimitlessCosmicMatrixUnits

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Rationalization of the complete diagonal coordinate vector of one integral
pure square. -/
def pureCoordinateVectorQ
    {N : Nat} (A : PureWorldHodge N N) : Fin N → ℚ :=
  fun i => (pureCoordinates A.1
    (Fin.castLE (show N ≤ min N N by omega) i) : ℚ)

/-- A nonzero integral pure square has a nonzero rationalized diagonal vector.
No information is lost when passing from the integral world to the exact
Lefschetz-tomography coefficient field. -/
theorem pureCoordinateVectorQ_ne_zero
    {N : Nat} (A : PureWorldHodge N N)
    (hA : A.1 ≠ 0) :
    pureCoordinateVectorQ A ≠ 0 := by
  intro hzero
  apply hA
  have hreassemble := pureReassemble_pureCoordinates A.1 A.2
  rw [← hreassemble]
  funext x
  by_cases hdiag : x.1.1 = x.2.1
  · have h := congrFun hzero (⟨x.1.1, x.1.2⟩ : Fin N)
    rw [Pi.zero_apply] at h
    simp only [pureReassemble, dif_pos hdiag, Pi.zero_apply]
    exact Int.cast_eq_zero.mp h
  · simp [pureReassemble, dif_neg hdiag]

/-- Nonzero pure coordinates have a nonzero exact central-binomial Lefschetz
moment. -/
theorem pureSquare_has_nonzero_tomographyMoment
    {N : Nat} (A : PureWorldHodge N N)
    (hA : A.1 ≠ 0) :
    ∃ q : Fin N,
      lefschetzTomography (pureCoordinateVectorQ A) q ≠ 0 :=
  exists_nonzero_lefschetzMoment
    (pureCoordinateVectorQ A)
    (pureCoordinateVectorQ_ne_zero A hA)

/-- A nonzero pure finite square remains nonzero after embedding its diagonal
into the genuine limitless compact cosmos. -/
theorem squareDiagonalToCosmos_ne_zero_of_pure
    {N : Nat} (A : PureWorldHodge N N)
    (hA : A.1 ≠ 0) :
    squareDiagonalToCosmos A.1 ≠ 0 := by
  intro hzero
  have hobs := observe_squareDiagonalToCosmos A.1 A.2
  rw [hzero] at hobs
  have hzobs : observe N N (0 : CompactCosmos) =
      (0 : ShapeCoef (outputShape N N)) := by
    rfl
  exact hA (hobs.symm.trans hzobs)

/-- A nonzero pure square contains a genuinely live diagonal sheet. -/
theorem exists_live_diagonal
    {N : Nat} (A : PureWorldHodge N N)
    (hA : A.1 ≠ 0) :
    ∃ r : Fin N, A.1 (r,r) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hA
  funext c
  obtain ⟨i, j⟩ := c
  by_cases hdiag : i.1 = j.1
  · have hij : i = j := Fin.ext hdiag
    subst hij
    exact h i
  · exact A.2 (i, j) hdiag

/-- One live source sheet generates a nonzero explicit GST orbit to every
other sheet by projector/Lefschetz/Poincare transport. -/
theorem live_diagonal_saturates_totalSheetOrbit
    {N : Nat} (A : PureWorldHodge N N)
    (r : Fin N) (hr : A.1 (r,r) ≠ 0) :
    ∀ s : Fin N,
      totalSheetMatrixUnit r s A.1 ≠ 0 := by
  intro s
  exact totalSheetMatrixUnit_nonzero r s A.1 A.2 hr

/-- Every member of that finite all-sheet orbit is exactly the finite shadow
of the corresponding limitless cosmic matrix unit. -/
theorem live_diagonal_orbit_is_limitless_shadow
    {N : Nat} (A : PureWorldHodge N N)
    (r s : Fin N)
    (x : WorldCell N N) :
    totalSheetMatrixUnit r s A.1 x =
      ((cosmicDiagonalMatrixUnit r.1 s.1
          (squareDiagonalToCosmos A.1)) (x.1.1,x.2.1) : ℚ) := by
  exact totalSheetMatrixUnit_eq_cosmic_shadow r s A.1 A.2 x

/-- Every forward entry of the finite tomography kernel is literally the
rationalized action of a power of the universal Lefschetz class in the
truncated world cohomology ring. -/
theorem tomographyKernel_is_worldCohomologyAction
    {N : Nat} (i j : Fin N) (hij : i.1 ≤ j.1) :
    multiplicityLefschetzKernel i j =
      (worldAct N N
        ((L N N)^(2 * GSTPureHodgeLefschetzKernel.pureWeightGap
          (Fin.castLE (show N ≤ min N N by omega) i)
          (Fin.castLE (show N ≤ min N N by omega) j)))
        (worldBasis
          (pureDiagonalState
            (Fin.castLE (show N ≤ min N N by omega) i)))
        (pureDiagonalState
          (Fin.castLE (show N ≤ min N N by omega) j)) : ℚ) := by
  exact multiplicityLefschetzKernel_eq_worldAct i j hij

/-- **OMNIVERSAL FAILURE PACKET.**

If the genuine classical Hodge statement fails, then one and the same finite
integral pure-square witness simultaneously has:

* nonzero integral Poincare pairing;
* nonzero left and right pure coordinate vectors;
* nonzero exact Lefschetz moments on both sides;
* nonzero limitless compact-cosmos embeddings;
* one live source sheet whose explicit GST total-sheet words stay nonzero for
  every target sheet;
* exact finite/limitless matrix-unit shadow identification;
* exact world-cohomology realization of every forward tomography coefficient.

No new semantic hypothesis is introduced. -/
theorem not_hodge_yields_omniversal_failure_packet
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ N : Nat,
    ∃ A B : PureWorldHodge N N,
      worldTopPairing A.1 B.1 ≠ 0
      ∧ A.1 ≠ 0
      ∧ B.1 ≠ 0
      ∧ pureCoordinateVectorQ A ≠ 0
      ∧ pureCoordinateVectorQ B ≠ 0
      ∧ (∃ qA : Fin N,
          lefschetzTomography (pureCoordinateVectorQ A) qA ≠ 0)
      ∧ (∃ qB : Fin N,
          lefschetzTomography (pureCoordinateVectorQ B) qB ≠ 0)
      ∧ squareDiagonalToCosmos A.1 ≠ 0
      ∧ squareDiagonalToCosmos B.1 ≠ 0
      ∧ (∃ r : Fin N,
          A.1 (r,r) ≠ 0 ∧
          (∀ s : Fin N, totalSheetMatrixUnit r s A.1 ≠ 0) ∧
          (∀ s : Fin N, ∀ x : WorldCell N N,
            totalSheetMatrixUnit r s A.1 x =
              ((cosmicDiagonalMatrixUnit r.1 s.1
                  (squareDiagonalToCosmos A.1))
                (x.1.1,x.2.1) : ℚ)))
      ∧ (∀ i j : Fin N, i.1 ≤ j.1 →
          multiplicityLefschetzKernel i j =
            (worldAct N N
              ((L N N)^(2 * GSTPureHodgeLefschetzKernel.pureWeightGap
                (Fin.castLE (show N ≤ min N N by omega) i)
                (Fin.castLE (show N ≤ min N N by omega) j)))
              (worldBasis
                (pureDiagonalState
                  (Fin.castLE (show N ≤ min N N by omega) i)))
              (pureDiagonalState
                (Fin.castLE (show N ≤ min N N by omega) j)) : ℚ)) := by
  obtain ⟨N, A0, B0, hA0, hB0, hpair⟩ :=
    not_hodge_yields_nonzero_integralPureSquare_pairing V H hnot
  let A : PureWorldHodge N N := ⟨A0, hA0⟩
  let B : PureWorldHodge N N := ⟨B0, hB0⟩
  have hAne : A.1 ≠ 0 := by
    intro hzero
    apply hpair
    have hA0 : A0 = 0 := hzero
    rw [hA0]
    simp [worldTopPairing]
  have hBne : B.1 ≠ 0 := by
    intro hzero
    apply hpair
    have hB0 : B0 = 0 := hzero
    rw [hB0]
    simp [worldTopPairing]
  have hAcoord := pureCoordinateVectorQ_ne_zero A hAne
  have hBcoord := pureCoordinateVectorQ_ne_zero B hBne
  obtain ⟨qA, hqA⟩ := pureSquare_has_nonzero_tomographyMoment A hAne
  obtain ⟨qB, hqB⟩ := pureSquare_has_nonzero_tomographyMoment B hBne
  have hAcos := squareDiagonalToCosmos_ne_zero_of_pure A hAne
  have hBcos := squareDiagonalToCosmos_ne_zero_of_pure B hBne
  obtain ⟨r, hr⟩ := exists_live_diagonal A hAne
  refine ⟨N, A, B, ?_, hAne, hBne,
    hAcoord, hBcoord, ⟨qA,hqA⟩, ⟨qB,hqB⟩,
    hAcos, hBcos, ?_, ?_⟩
  · exact hpair
  · refine ⟨r, hr, live_diagonal_saturates_totalSheetOrbit A r hr, ?_⟩
    intro s x
    exact live_diagonal_orbit_is_limitless_shadow A r s x
  · intro i j hij
    exact tomographyKernel_is_worldCohomologyAction i j hij

#check pureCoordinateVectorQ
#check pureCoordinateVectorQ_ne_zero
#check pureSquare_has_nonzero_tomographyMoment
#check squareDiagonalToCosmos_ne_zero_of_pure
#check exists_live_diagonal
#check live_diagonal_saturates_totalSheetOrbit
#check live_diagonal_orbit_is_limitless_shadow
#check tomographyKernel_is_worldCohomologyAction
#check not_hodge_yields_omniversal_failure_packet

#print axioms pureCoordinateVectorQ_ne_zero
#print axioms pureSquare_has_nonzero_tomographyMoment
#print axioms squareDiagonalToCosmos_ne_zero_of_pure
#print axioms live_diagonal_saturates_totalSheetOrbit
#print axioms live_diagonal_orbit_is_limitless_shadow
#print axioms not_hodge_yields_omniversal_failure_packet

end GSTClassicalHodgeOmniversalFailurePacket
