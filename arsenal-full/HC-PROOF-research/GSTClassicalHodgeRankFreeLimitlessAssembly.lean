import GSTClassicalHodgeMicroscopicProjectorCriterion
import GSTClassicalHodgeFiberedTransferCompletion

/-!
# GST CLASSICAL HODGE — RANK-FREE LIMITLESS ASSEMBLY

The historical compact Stage-2 route encoded ambient cohomology in `ℕ →₀ ℚ`.
That countable chart is not part of the mathematics of the limitless Hodge
universe.  The genuine basis index of each rational `(p,p)` fiber is already
the canonical address type, and `Basis.repr` already lands in finite-support
coordinates.

This module removes the artificial natural-number chart completely.  Every
genuine Hodge class is represented directly in its unrestricted basis fiber,
then embedded into the total limitless fibered address universe.  Microscopic
projector certificates produce native algebraic cycles at those exact basis
addresses, and finite-support basis reconstruction produces the cycle of an
arbitrary Hodge class.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedTransferCompletion
open GSTClassicalHodgeMicroscopicProjectorCriterion

namespace GSTClassicalHodgeRankFreeLimitlessAssembly

/-- Canonical rank-free finite-support coordinates of the genuine weight-p
Hodge fiber.  No countability assumption occurs. -/
noncomputable def genuineHodgeAddress
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :
    ClassicalHodgeFiber V H p ≃ₗ[ℚ]
      (ClassicalHodgeBasisIndex V H p →₀ ℚ) :=
  (classicalHodgeBasis V H p).repr

@[simp]
theorem genuineHodgeAddress_basis
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H p) :
    genuineHodgeAddress V H p (classicalHodgeBasis V H p i) =
      Finsupp.single i 1 := by
  simp [genuineHodgeAddress]

/-- The canonical basis address is exactly the fixed-weight slice of the
total limitless fibered Hodge address. -/
theorem genuineAddress_eq_fiberedWeightCoordinates
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    fiberedWeightCoordinates V H p alpha =
      Finsupp.embDomain (weightFiberEmbedding V H p)
        (genuineHodgeAddress V H p alpha) := by
  rfl

/-- A microscopic projector certificate at every genuine basis sheet gives a
native cycle at every rank-free address, with no intermediate `Nat` chart. -/
noncomputable def basisCycle
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (hcert : ∀ i : ClassicalHodgeBasisIndex V H p,
      Nonempty (BasisProjectorCertificate V H p i))
    (i : ClassicalHodgeBasisIndex V H p) :
    codimensionCycles V.X p :=
  (Classical.choice (hcert i)).extractedBasisCycle

@[simp]
theorem basisCycle_spec
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (hcert : ∀ i : ClassicalHodgeBasisIndex V H p,
      Nonempty (BasisProjectorCertificate V H p i))
    (i : ClassicalHodgeBasisIndex V H p) :
    H.cycleClass p (basisCycle V H p hcert i) =
      (classicalHodgeBasis V H p i).1 := by
  exact (Classical.choice (hcert i)).extractedBasisCycle_spec

/-- Extend the rank-free basis-cycle assignment linearly over the whole
rational Hodge fiber. -/
noncomputable def cycleLift
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (hcert : ∀ i : ClassicalHodgeBasisIndex V H p,
      Nonempty (BasisProjectorCertificate V H p i)) :
    ClassicalHodgeFiber V H p →ₗ[ℚ] codimensionCycles V.X p :=
  (classicalHodgeBasis V H p).constr ℚ (basisCycle V H p hcert)

@[simp]
theorem cycleLift_basis
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (hcert : ∀ i : ClassicalHodgeBasisIndex V H p,
      Nonempty (BasisProjectorCertificate V H p i))
    (i : ClassicalHodgeBasisIndex V H p) :
    cycleLift V H p hcert (classicalHodgeBasis V H p i) =
      basisCycle V H p hcert i := by
  simp [cycleLift]

/-- Exact reconstruction: applying the genuine cycle-class map to the
rank-free cycle lift is the inclusion of the Hodge fiber into ambient Betti
cohomology. -/
theorem cycleLift_spec
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (hcert : ∀ i : ClassicalHodgeBasisIndex V H p,
      Nonempty (BasisProjectorCertificate V H p i))
    (alpha : ClassicalHodgeFiber V H p) :
    H.cycleClass p (cycleLift V H p hcert alpha) = alpha.1 := by
  have hmaps :
      (H.cycleClass p).comp (cycleLift V H p hcert) =
        (rationalHodgeSubspace (H.hodgeBigrading p)).subtype := by
    apply (classicalHodgeBasis V H p).ext
    intro i
    simp [cycleLift, basisCycle_spec]
  change ((H.cycleClass p).comp (cycleLift V H p hcert)) alpha = alpha.1
  rw [hmaps]
  rfl

/-- Rank-free limitless reconstruction of an arbitrary genuine `(p,p)` class.
The only basis-level construction used is the microscopic projector cycle. -/
theorem hodgeClass_has_rankFree_cycle
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (hcert : ∀ i : ClassicalHodgeBasisIndex V H p,
      Nonempty (BasisProjectorCertificate V H p i))
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha := by
  let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  exact ⟨cycleLift V H p hcert alphaH,
    by simpa [alphaH] using cycleLift_spec V H p hcert alphaH⟩

/-- The rank-free limitless assembly closes the Stage-2G statement directly;
no `NatHodgeCoordinateChart` or countable ambient address is involved. -/
theorem bigradedBettiHodge_of_rankFree_projectors
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hcert : ∀ p : Nat, ∀ i : ClassicalHodgeBasisIndex V H p,
      Nonempty (BasisProjectorCertificate V H p i)) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  exact hodgeClass_has_rankFree_cycle V H p (hcert p) alpha halpha

/-- Limitless address receipt: every classical basis sheet retains its full
multiplicity coordinate before projecting to the universal cosmic diagonal. -/
theorem rankFree_limitless_address_receipt
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    (∀ p, Function.Injective (genuineHodgeAddress V H p)) ∧
    (∀ p i,
      forgetMultiplicityToGST
        (fiberedWeightCoordinates V H p (classicalHodgeBasis V H p i)) =
      Finsupp.single
        (GSTUniversalAddressBridge.cosmicAddressEquiv (p,p)) 1) := by
  exact ⟨fun p => (genuineHodgeAddress V H p).injective,
    classical_basis_projects_to_cosmic_diagonal V H⟩

#check genuineHodgeAddress
#check basisCycle
#check cycleLift
#check cycleLift_spec
#check hodgeClass_has_rankFree_cycle
#check bigradedBettiHodge_of_rankFree_projectors
#check rankFree_limitless_address_receipt

#print axioms cycleLift_spec
#print axioms hodgeClass_has_rankFree_cycle
#print axioms bigradedBettiHodge_of_rankFree_projectors
#print axioms rankFree_limitless_address_receipt

end GSTClassicalHodgeRankFreeLimitlessAssembly
