import Mathlib.LinearAlgebra.Basis.VectorSpace
import GSTProjectiveOverC
import GSTGeometricRealizationStage2D
import GSTGeometricRealizationStage2F
import GSTGeometricRealizationStage2G

/-!
# HODGE CONJECTURE — BASIS-CYCLE BRIDGE (EARLY MODULE)

Extracted from `HodgeConjecture.lean` (the final landing) so that the
mid-level classical-Hodge lane files can consume the bridge WITHOUT the
circular import: eight files (`GSTClassicalHodgeSynchronizedDefectOrbit`,
`GSTClassicalHodgeFiniteSpineMomentOrbit`, `GSTClassicalHodgeGeometryFirstNativeWord`,
`GSTClassicalHodgeLimitlessDefectOrbitLanding`, `GSTClassicalHodgeNativeWordFromArbitrarySeed`,
`GSTClassicalHodgeOmniversePointStrictRelationFinale`,
`GSTClassicalHodgeOmniverseProjectiveApexSpokes`,
`GSTClassicalHodgeProjectiveWordOrbit`) reference
`HodgeConjecture.HodgeBasisCycleBridge` and
`HodgeConjecture.hodge_class_has_cycle_of_basis_bridge`, which previously
lived only in the final landing module that (transitively) imports them all.

The declarations keep the `HodgeConjecture` namespace, so every existing
fully-qualified reference resolves unchanged.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G

namespace HodgeConjecture

/-! ## Exact limitless coordinates on the genuine Hodge fiber -/

/-- The actual rational `(p,p)` Hodge fiber in degree `2p`. -/
abbrev HodgeFiber
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) : Type :=
  rationalHodgeSubspace (H.hodgeBigrading p)

/-- A completely unrestricted basis index for one classical Hodge fiber. -/
abbrev HodgeBasisIndex
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :=
  Module.Free.ChooseBasisIndex ℚ (HodgeFiber V H p)

/-- A chosen rational basis of the genuine `(p,p)` Hodge fiber. -/
noncomputable def hodgeBasis
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :
    Module.Basis (HodgeBasisIndex V H p) ℚ (HodgeFiber V H p) :=
  Module.Free.chooseBasis ℚ (HodgeFiber V H p)

/-- Limitless finite-support coordinates of a genuine Hodge class. -/
noncomputable def hodgeCoordinates
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :
    HodgeFiber V H p ≃ₗ[ℚ] (HodgeBasisIndex V H p →₀ ℚ) :=
  (hodgeBasis V H p).repr

@[simp]
theorem hodgeCoordinates_basis
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) (i : HodgeBasisIndex V H p) :
    hodgeCoordinates V H p (hodgeBasis V H p i) =
      Finsupp.single i 1 := by
  simp [hodgeCoordinates]

/-- The irreducible geometric datum for one Hodge fiber: every basis vector
has an actual native codimension-`p` algebraic-cycle representative. -/
structure HodgeBasisCycleBridge
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) where
  basisCycle : HodgeBasisIndex V H p → codimensionCycles V.X p
  basisCycle_spec :
    ∀ i : HodgeBasisIndex V H p,
      H.cycleClass p (basisCycle i) = (hodgeBasis V H p i).1

/-- Lift the chosen Hodge basis to native algebraic cycles linearly. -/
noncomputable def hodgeBasisCycleLift
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (R : HodgeBasisCycleBridge V H p) :
    HodgeFiber V H p →ₗ[ℚ] codimensionCycles V.X p :=
  (hodgeBasis V H p).constr ℚ R.basisCycle

@[simp]
theorem hodgeBasisCycleLift_basis
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (R : HodgeBasisCycleBridge V H p)
    (i : HodgeBasisIndex V H p) :
    hodgeBasisCycleLift V H p R (hodgeBasis V H p i) =
      R.basisCycle i := by
  simp [hodgeBasisCycleLift]

/-- Finite-support reconstruction is exact: after applying the genuine
cycle-class map, the basis-cycle lift is precisely the inclusion of the Hodge
subspace into ambient rational singular cohomology. -/
theorem hodgeBasisCycleLift_spec
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (R : HodgeBasisCycleBridge V H p)
    (alpha : HodgeFiber V H p) :
    H.cycleClass p (hodgeBasisCycleLift V H p R alpha) = alpha.1 := by
  have hmaps :
      (H.cycleClass p).comp (hodgeBasisCycleLift V H p R) =
        (rationalHodgeSubspace (H.hodgeBigrading p)).subtype := by
    apply (hodgeBasis V H p).ext
    intro i
    simp [hodgeBasisCycleLift, R.basisCycle_spec]
  change ((H.cycleClass p).comp (hodgeBasisCycleLift V H p R)) alpha = alpha.1
  rw [hmaps]
  rfl

/-- Basis-wise algebraicity therefore produces a native cycle for an
arbitrary rational `(p,p)` class. -/
theorem hodge_class_has_cycle_of_basis_bridge
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    {p : Nat}
    (R : HodgeBasisCycleBridge V H p)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  let alphaH : HodgeFiber V H p := ⟨alpha, halpha⟩
  refine ⟨hodgeBasisCycleLift V H p R alphaH, ?_⟩
  simpa [alphaH] using hodgeBasisCycleLift_spec V H p R alphaH

end HodgeConjecture
