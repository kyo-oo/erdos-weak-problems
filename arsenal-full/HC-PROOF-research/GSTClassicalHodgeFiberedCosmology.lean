import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import GSTGeometricRealizationStage2G
import GSTTransferBridgeV2
import GSTGlobalPureHodgeCosmology
import GSTDimensionFreeHodgeDiagonal
import GSTUniversalAddressBridge

/-!
# GST CLASSICAL HODGE FIBERED COSMOLOGY

The limitless GST pure-Hodge universe has one cosmic diagonal cell `(p,p)`
for every natural weight `p`.  An arbitrary classical rational `(p,p)` Hodge
space, however, can have more than one independent class at the same weight.

This module resolves that mismatch without collapsing either side:

* the GST diagonal coordinate is the **base** `p`;
* a genuine basis index of the classical rational Hodge fiber is the
  **multiplicity fiber** above `p`;
* a classical Hodge class has finite support in its basis fiber because
  `Basis.repr` is a `Finsupp`;
* forgetting the multiplicity fiber sends every basis direction above `p`
  to the existing limitless GST generator at the universal cosmic diagonal
  address of `(p,p)`.

No algebraic-cycle representative is assumed or constructed here.  This is
the exact rank-free coordinate bridge needed before attacking algebraicity.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G

namespace GSTClassicalHodgeFiberedCosmology

/-- The genuine rational `(p,p)` Hodge fiber in native rational singular
cohomology. -/
abbrev ClassicalHodgeFiber
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :=
  rationalHodgeSubspace (H.hodgeBigrading p)

/-- Unrestricted basis index of one classical Hodge fiber. -/
abbrev ClassicalHodgeBasisIndex
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :=
  Module.Free.ChooseBasisIndex ℚ (ClassicalHodgeFiber V H p)

/-- A chosen rational basis of one genuine Hodge fiber. -/
noncomputable def classicalHodgeBasis
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :
    Module.Basis (ClassicalHodgeBasisIndex V H p) ℚ
      (ClassicalHodgeFiber V H p) :=
  Module.Free.chooseBasis ℚ (ClassicalHodgeFiber V H p)

/-- The total limitless classical Hodge address universe.  The first
coordinate is the GST weight; the second is an unrestricted basis direction
inside the genuine classical `(p,p)` fiber. -/
abbrev FiberedHodgeIndex
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :=
  Σ p : Nat, ClassicalHodgeBasisIndex V H p

/-- Finite-support addresses on the total fibered Hodge universe. -/
abbrev FiberedHodgeAddress
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :=
  FiberedHodgeIndex V H →₀ ℚ

/-- Embed one fixed-weight basis fiber into the total Hodge address universe. -/
def weightFiberEmbedding
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :
    ClassicalHodgeBasisIndex V H p ↪ FiberedHodgeIndex V H :=
  Function.Embedding.sigmaMk p

/-- Coordinates of one weight-p Hodge class, embedded into the total
fibered universe. -/
noncomputable def fiberedWeightCoordinates
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    FiberedHodgeAddress V H :=
  Finsupp.embDomain (weightFiberEmbedding V H p)
    ((classicalHodgeBasis V H p).repr alpha)

/-- One classical basis vector is one atom in the total fibered universe. -/
@[simp]
theorem fiberedWeightCoordinates_basis
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H p) :
    fiberedWeightCoordinates V H p (classicalHodgeBasis V H p i) =
      Finsupp.single (⟨p, i⟩ : FiberedHodgeIndex V H) 1 := by
  simp [fiberedWeightCoordinates, weightFiberEmbedding]

/-- The weight embedding is injective, so fixed-weight classical coordinates
retain all multiplicity information in the total fibered universe. -/
theorem fiberedWeightCoordinates_injective
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :
    Function.Injective (fiberedWeightCoordinates V H p) := by
  intro a b hab
  apply (classicalHodgeBasis V H p).repr.injective
  apply Finsupp.embDomain_injective
  exact hab

/-- Rationalized limitless GST compact-address carrier. -/
abbrev RationalCompactGSTAddress := Nat →₀ ℚ

/-- Forget only the multiplicity fiber, retaining the GST diagonal weight.
All independent basis directions over the same weight project to the same
cosmic diagonal address. -/
noncomputable def forgetMultiplicityToGST
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (φ : FiberedHodgeAddress V H) : RationalCompactGSTAddress :=
  φ.sum fun s q =>
    Finsupp.single (GSTTransferBridgeV2.compactClCode s.1) q

@[simp]
theorem forgetMultiplicityToGST_single
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H p)
    (q : ℚ) :
    forgetMultiplicityToGST
        (Finsupp.single (⟨p, i⟩ : FiberedHodgeIndex V H) q) =
      Finsupp.single (GSTTransferBridgeV2.compactClCode p) q := by
  simp [forgetMultiplicityToGST]

/-- Every classical basis direction over weight p projects to the historical
limitless GST transfer generator, now with rational coefficients. -/
theorem classical_basis_projects_to_gst_diagonal
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H p) :
    forgetMultiplicityToGST
        (fiberedWeightCoordinates V H p (classicalHodgeBasis V H p i)) =
      Finsupp.single (GSTTransferBridgeV2.compactClCode p) 1 := by
  rw [fiberedWeightCoordinates_basis]
  exact forgetMultiplicityToGST_single V H p i 1

/-- The projected code is literally the universal cosmic address of the GST
weight-p diagonal cell `(p,p)`. -/
theorem classical_basis_projects_to_cosmic_diagonal
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H p) :
    forgetMultiplicityToGST
        (fiberedWeightCoordinates V H p (classicalHodgeBasis V H p i)) =
      Finsupp.single
        (GSTUniversalAddressBridge.cosmicAddressEquiv (p, p)) 1 := by
  rw [classical_basis_projects_to_gst_diagonal V H p i]
  rw [GSTTransferBridgeV2.compactClCode_eq_cosmicAddress]

/-- The base/fiber integration receipt: the unrestricted classical Hodge
multiplicity lives above the already-proved limitless GST diagonal universe,
without changing the GST base coordinate or asserting a false rank-one
classification for the classical fiber. -/
theorem fibered_limitless_hodge_crown
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    (∀ p : Nat,
      Function.Injective (fiberedWeightCoordinates V H p))
    ∧ (∀ p : Nat, ∀ i : ClassicalHodgeBasisIndex V H p,
      forgetMultiplicityToGST
          (fiberedWeightCoordinates V H p (classicalHodgeBasis V H p i)) =
        Finsupp.single
          (GSTUniversalAddressBridge.cosmicAddressEquiv (p, p)) 1) := by
  exact ⟨fiberedWeightCoordinates_injective V H,
    classical_basis_projects_to_cosmic_diagonal V H⟩

#check ClassicalHodgeFiber
#check ClassicalHodgeBasisIndex
#check classicalHodgeBasis
#check FiberedHodgeIndex
#check FiberedHodgeAddress
#check weightFiberEmbedding
#check fiberedWeightCoordinates
#check fiberedWeightCoordinates_basis
#check fiberedWeightCoordinates_injective
#check forgetMultiplicityToGST
#check classical_basis_projects_to_gst_diagonal
#check classical_basis_projects_to_cosmic_diagonal
#check fibered_limitless_hodge_crown

#print axioms fiberedWeightCoordinates_basis
#print axioms fiberedWeightCoordinates_injective
#print axioms classical_basis_projects_to_gst_diagonal
#print axioms classical_basis_projects_to_cosmic_diagonal
#print axioms fibered_limitless_hodge_crown

end GSTClassicalHodgeFiberedCosmology
