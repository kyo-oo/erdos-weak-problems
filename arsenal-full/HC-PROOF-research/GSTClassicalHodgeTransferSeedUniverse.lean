import GSTClassicalHodgeFiberedTransferCompletion
import GSTClassicalHodgeFiniteSupportArsenalConjugation
import GSTTransferBridgeV2

/-!
# GST CLASSICAL HODGE — TRANSFER SEED UNIVERSE

The limitless transfer bridge already carries one nonzero compact diagonal
Hodge generator `compactClMono p` at every natural weight.  The fibered
classical completion keeps arbitrary Hodge multiplicity above that base
weight, and every individual multiplicity sheet projects exactly to the same
established cosmic diagonal generator.

This module packages the consequence for a nonzero genuine classical Hodge
state: some live basis coordinate exists; its independent fibered sheet is
nonzero; and after forgetting multiplicity that sheet is exactly the limitless
GST transfer generator at the same weight.  Thus every nonzero classical
Hodge state is tethered to a canonical already-proved GST seed without any
countability or finite-rank assumption.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedTransferCompletion
open GSTClassicalHodgeFiniteSupportArsenalConjugation
open GSTTransferBridgeV2

namespace GSTClassicalHodgeTransferSeedUniverse

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Canonical limitless GST transfer seed at one weight, in the rationalized
(ℚ-world) address universe that `forgetMultiplicityToGST` lands in: the
universal address basis of the diagonal cosmic cell `(p,p)`. -/
noncomputable def cosmicTransferSeed (p : Nat) : RationalCompactGSTAddress :=
  Finsupp.single (GSTUniversalAddressBridge.cosmicAddressEquiv (p, p)) (1 : ℚ)

/-- ℚ-world twin of the compact-address Hodge support condition: the
rationalized seed is supported only at the cosmic diagonal address. -/
def isRationalCompactHodge (p : Nat) (φ : RationalCompactGSTAddress) : Prop :=
  ∀ i : Nat, i ≠ GSTUniversalAddressBridge.cosmicAddressEquiv (p, p) → φ i = 0

/-- The canonical transfer seed is a limitless compact-address Hodge class. -/
theorem cosmicTransferSeed_isHodge (p : Nat) :
    isRationalCompactHodge p (cosmicTransferSeed p) := by
  intro i hi
  simp only [cosmicTransferSeed, Finsupp.single_apply]
  exact if_neg (Ne.symm hi)

/-- The canonical transfer seed is nonzero. -/
theorem cosmicTransferSeed_ne_zero (p : Nat) :
    cosmicTransferSeed p ≠ 0 := by
  intro h
  have hv := congrArg
    (fun φ : RationalCompactGSTAddress =>
      φ (GSTUniversalAddressBridge.cosmicAddressEquiv (p, p))) h
  simp only [cosmicTransferSeed, Finsupp.single_apply, Finsupp.zero_apply] at hv
  exact absurd hv one_ne_zero

/-- Every genuine multiplicity sheet above weight `p` projects to the exact
canonical limitless transfer seed. -/
theorem fiberedSheet_projects_to_transferSeed
    (i : ClassicalHodgeBasisIndex V H p) :
    forgetMultiplicityToGST (fiberedSheetGenerator V H ⟨p,i⟩) =
      cosmicTransferSeed p := by
  rw [fiberedSheet_projects_to_cosmicGenerator V H p i]
  rfl

/-- A nonzero genuine Hodge state has at least one live basis coordinate. -/
theorem exists_live_basis_index
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    ∃ i : ClassicalHodgeBasisIndex V H p,
      (classicalHodgeBasis V H p).repr alpha i ≠ 0 := by
  obtain ⟨i, hi⟩ :=
    GSTClassicalHodgeRankFreeArsenalIrreducibility.exists_nonzero_hodgeCoordinate
      halpha
  exact ⟨i, by simpa [GSTClassicalHodgeRankFreeArsenalIrreducibility.hodgeCoordinate] using hi⟩

/-- **LIVE TRANSFER SEED TETHER.** Every nonzero genuine Hodge class contains
an actual live multiplicity sheet which projects to the already-proved
limitless GST transfer generator of that weight. -/
theorem nonzero_hodge_has_transfer_seed_sheet
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    ∃ i : ClassicalHodgeBasisIndex V H p,
      (classicalHodgeBasis V H p).repr alpha i ≠ 0
      ∧ forgetMultiplicityToGST
          (fiberedSheetGenerator V H ⟨p,i⟩) = cosmicTransferSeed p := by
  obtain ⟨i, hi⟩ := exists_live_basis_index alpha halpha
  exact ⟨i, hi, fiberedSheet_projects_to_transferSeed i⟩

/-- The same live sheet is exactly the corresponding basis vector in the
fibered limitless address universe. -/
theorem nonzero_hodge_has_exact_fibered_transfer_sheet
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    ∃ i : ClassicalHodgeBasisIndex V H p,
      (classicalHodgeBasis V H p).repr alpha i ≠ 0
      ∧ fiberedWeightCoordinates V H p (classicalHodgeBasis V H p i) =
          fiberedSheetGenerator V H ⟨p,i⟩
      ∧ forgetMultiplicityToGST
          (fiberedSheetGenerator V H ⟨p,i⟩) = cosmicTransferSeed p := by
  obtain ⟨i, hi, hproj⟩ := nonzero_hodge_has_transfer_seed_sheet alpha halpha
  exact ⟨i, hi,
    classicalBasis_eq_fiberedSheetGenerator V H p i,
    hproj⟩

/-- Transfer-seed crown: every weight has a nonzero canonical GST Hodge seed,
and every nonzero genuine classical Hodge state contains a live sheet mapping
to that seed. -/
theorem transfer_seed_universe_crown :
    (∀ q : Nat,
      isRationalCompactHodge q (cosmicTransferSeed q) ∧
      cosmicTransferSeed q ≠ 0)
    ∧ (∀ q : Nat, ∀ alpha : ClassicalHodgeFiber V H q,
      alpha ≠ 0 →
      ∃ i : ClassicalHodgeBasisIndex V H q,
        (classicalHodgeBasis V H q).repr alpha i ≠ 0
        ∧ forgetMultiplicityToGST
            (fiberedSheetGenerator V H ⟨q,i⟩) = cosmicTransferSeed q) := by
  exact ⟨
    fun q => ⟨cosmicTransferSeed_isHodge q, cosmicTransferSeed_ne_zero q⟩,
    fun q alpha h => nonzero_hodge_has_transfer_seed_sheet alpha h⟩

#check cosmicTransferSeed
#check cosmicTransferSeed_isHodge
#check cosmicTransferSeed_ne_zero
#check fiberedSheet_projects_to_transferSeed
#check exists_live_basis_index
#check nonzero_hodge_has_transfer_seed_sheet
#check nonzero_hodge_has_exact_fibered_transfer_sheet
#check transfer_seed_universe_crown

#print axioms cosmicTransferSeed_ne_zero
#print axioms fiberedSheet_projects_to_transferSeed
#print axioms nonzero_hodge_has_transfer_seed_sheet
#print axioms transfer_seed_universe_crown

end GSTClassicalHodgeTransferSeedUniverse
