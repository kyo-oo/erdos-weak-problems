import GSTClassicalHodgeLimitlessArsenalConjugation
import GSTClassicalHodgeIntegralSquareLocalization
import GSTClassicalHodgeLimitlessCosmicLefschetzPropagation
import GSTDimensionFreeHodgeDiagonal
import GSTUniversalAddressBridge
import GSTTransferBridgeV2

/-!
# GST CLASSICAL HODGE — LIMITLESS FAILURE ORBIT

A failure of the genuine Stage-2G statement already produces, by the existing
separator/localization machinery, a finite integral pure GST square with a
nonzero Poincare pairing.  This file refuses to leave that witness trapped in
a finite chart.

The nonzero pairing contains a nonzero diagonal source coefficient.  Embed the
pure square into the compact unbounded cosmos.  The limitless Poincare
read/write matrix-unit algebra then moves that one coefficient to every
natural Hodge weight.  Under the universal address bridge each of those target
states is the same limitless transfer generator `compactClMono p` up to its
nonzero source scalar.

Thus any classical failure generates a nonzero orbit through every weight of
the limitless Hodge cosmology.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeLimitlessFailureOrbit

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTWorldCosmology
open GSTWorldPoincareDuality
open GSTGlobalPureHodgeCosmology
open GSTClassicalHodgeIntegralSquareLocalization
open GSTClassicalHodgeLimitlessArsenalConjugation
open GSTClassicalHodgeLimitlessCosmicMatrixUnits
open GSTDimensionFreeHodgeDiagonal
open GSTUniversalAddressBridge
open GSTTransferBridgeV2

/-- A nonzero finite Poincare pairing has at least one genuinely nonzero
summand. -/
theorem worldTopPairing_ne_zero_exists_term
    {N : ℕ} (A B : WorldCoef N N)
    (hpair : worldTopPairing A B ≠ 0) :
    ∃ c : WorldCell N N, A c * B (worldDual c) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hpair
  unfold worldTopPairing
  apply Finset.sum_eq_zero
  intro c hc
  exact h c

/-- If the left state is pure, every nonzero pairing summand lies on one
actual diagonal weight. -/
theorem pure_pairing_ne_zero_exists_diagonal
    {N : ℕ} (A B : WorldCoef N N)
    (hA : isWorldPureHodge A)
    (hpair : worldTopPairing A B ≠ 0) :
    ∃ r : Fin N, A (r,r) * B (worldDual (r,r)) ≠ 0 := by
  obtain ⟨c, hc⟩ := worldTopPairing_ne_zero_exists_term A B hpair
  obtain ⟨i, j⟩ := c
  have hAc : A (i, j) ≠ 0 := by
    intro hzero
    exact hc (by simp [hzero])
  have hdiag : i.1 = j.1 := by
    by_contra h
    exact hAc (hA (i, j) h)
  have hfin : i = j := Fin.ext hdiag
  subst hfin
  exact ⟨i, hc⟩

/-- The selected diagonal coefficient is nonzero by itself. -/
theorem pure_pairing_source_ne_zero
    {N : ℕ} (A B : WorldCoef N N)
    (hA : isWorldPureHodge A)
    (hpair : worldTopPairing A B ≠ 0) :
    ∃ r : Fin N, A (r,r) ≠ 0 := by
  obtain ⟨r, hr⟩ := pure_pairing_ne_zero_exists_diagonal A B hA hpair
  refine ⟨r, ?_⟩
  intro hz
  exact hr (by simp [hz])

/-- Once embedded in the compact cosmos, one nonzero source diagonal can be
sent by a true limitless matrix unit to every target Hodge weight. -/
theorem nonzero_pure_square_reaches_every_cosmic_weight
    {N : ℕ} (A : WorldCoef N N)
    (hA : isWorldPureHodge A)
    (r : Fin N) (hr : A (r,r) ≠ 0) :
    ∀ p : ℕ,
      cosmicDiagonalMatrixUnit r.1 p (squareDiagonalToCosmos A) =
        A (r,r) • cosmicDiagonalClass p
      ∧ cosmicDiagonalMatrixUnit r.1 p (squareDiagonalToCosmos A) ≠ 0 := by
  intro p
  constructor
  · rw [cosmicDiagonalMatrixUnit_read_write, cosmicPairing_probe,
      squareDiagonalToCosmos_diagonal]
  · intro hz
    have hread := congrArg (fun f : CompactCosmos => f (p,p)) hz
    simp [cosmicDiagonalMatrixUnit_apply,
      squareDiagonalToCosmos_diagonal, hr, cosmicDiagonalClass] at hread

/-- The universal address of every target in the failure orbit is exactly a
nonzero scalar multiple of the canonical limitless transfer generator. -/
theorem failure_orbit_address_is_transfer_generator
    {N : ℕ} (A : WorldCoef N N)
    (r : Fin N) (p : ℕ) :
    compactAddressEquiv
        (cosmicDiagonalMatrixUnit r.1 p (squareDiagonalToCosmos A)) =
      A (r,r) • compactClMono p := by
  rw [cosmicDiagonalMatrixUnit_read_write, cosmicPairing_probe,
    squareDiagonalToCosmos_diagonal]
  ext i
  simp [compactClMono, compactClCode,
    compactAddressEquiv, cosmicAddressEquiv, cosmicDiagonalClass]

/-- **LIMITLESS FAILURE ORBIT THEOREM.**
Every genuine Stage-2G failure produces one finite integral pure witness whose
single nonzero source sheet generates nonzero cosmic Hodge states at every
natural weight. -/
theorem not_hodge_yields_full_limitless_cosmic_orbit
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ N : ℕ,
    ∃ A B : WorldCoef N N,
    ∃ r : Fin N,
      isWorldPureHodge A
      ∧ isWorldPureHodge B
      ∧ worldTopPairing A B ≠ 0
      ∧ A (r,r) ≠ 0
      ∧ ∀ p : ℕ,
          cosmicDiagonalMatrixUnit r.1 p (squareDiagonalToCosmos A) =
            A (r,r) • cosmicDiagonalClass p
          ∧ cosmicDiagonalMatrixUnit r.1 p (squareDiagonalToCosmos A) ≠ 0 := by
  obtain ⟨N,A,B,hA,hB,hpair⟩ :=
    not_hodge_yields_nonzero_integralPureSquare_pairing V H hnot
  obtain ⟨r,hr⟩ := pure_pairing_source_ne_zero A B hA hpair
  exact ⟨N,A,B,r,hA,hB,hpair,hr,
    nonzero_pure_square_reaches_every_cosmic_weight A hA r hr⟩

/-- Address-form crown: a failure orbit hits every canonical limitless transfer
basis direction by a nonzero scalar. -/
theorem not_hodge_yields_all_transfer_directions
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ N : ℕ, ∃ A : WorldCoef N N, ∃ r : Fin N,
      A (r,r) ≠ 0 ∧
      ∀ p : ℕ,
        compactAddressEquiv
          (cosmicDiagonalMatrixUnit r.1 p (squareDiagonalToCosmos A)) =
            A (r,r) • compactClMono p := by
  obtain ⟨N,A,B,r,hA,hB,hpair,hr,horbit⟩ :=
    not_hodge_yields_full_limitless_cosmic_orbit V H hnot
  exact ⟨N,A,r,hr,fun p => failure_orbit_address_is_transfer_generator A r p⟩

#check worldTopPairing_ne_zero_exists_term
#check pure_pairing_ne_zero_exists_diagonal
#check nonzero_pure_square_reaches_every_cosmic_weight
#check failure_orbit_address_is_transfer_generator
#check not_hodge_yields_full_limitless_cosmic_orbit
#check not_hodge_yields_all_transfer_directions

#print axioms pure_pairing_ne_zero_exists_diagonal
#print axioms nonzero_pure_square_reaches_every_cosmic_weight
#print axioms failure_orbit_address_is_transfer_generator
#print axioms not_hodge_yields_full_limitless_cosmic_orbit
#print axioms not_hodge_yields_all_transfer_directions

end GSTClassicalHodgeLimitlessFailureOrbit
