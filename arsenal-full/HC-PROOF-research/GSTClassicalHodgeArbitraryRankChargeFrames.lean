import GSTClassicalHodgeSingleCorrespondenceRankTwo
import GSTClassicalHodgeGeometricMatrixRankLanding
import GSTHodgeChannelFinale

/-!
# Arbitrary-rank GST charged geometric frames

This module is a genuine native-cycle construction for every finite rational
Hodge-fiber rank, upgrading the weight-local two-direction charge wedge.

At weight p let s = cl(Z) be the actual projective spine class and let ell
be a rational linear functional on the Hodge fiber. From a finite family
of actual realized geometric correspondence expressions E(j), define a
native frame of exactly n=finrank(HodgeFiber p) cycles:

  Z_0 := spineNativeTower G p
  Z_j := ell(s) * E(j).cycleOperator (spineNativeTower G p)
          - ell(E(j).cohomologyOperator s) * spineNativeTower G p    (j>0).

Each Z_j is constructed from true native rational algebraic cycles. The
matrix used here is the coordinate matrix of those constructed cycles,
never an arbitrarily selected basis-cycle preimage. If its determinant
is nonzero, existing geometric matrix inversion gives the explicit native
cycle for an arbitrary rational Hodge class.

The purely geometric existence statement "a full rank charged frame
exists" is NOT proved by this module. Rewriting it as an axiom or a law
would hide precisely the universal Hodge difficulty; no such axiom is
added.
-/

set_option maxHeartbeats 20000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
open GSTClassicalHodgeSingleCorrespondenceRankTwo
open GSTClassicalHodgeGeometricMatrixRankLanding

namespace GSTClassicalHodgeArbitraryRankChargeFrames

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A finite actual geometric frame whose first column is the native spine
and remaining columns are explicit geometric charge wedges. -/
noncomputable def nativeChargedFrame
    (G : GeometricCycleClassSpine V H)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (E : Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)) →
      RealizedCorrespondenceExpr V H p)
    (j : Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p))) :
    codimensionCycles V.X p :=
  if j.val = 0 then spineNativeTower G p
  else nativeChargeWedge G ell (E j)

/-- Exact Hodge coordinate matrix of the actual geometric charge frame.
Its size is the *entire* rational Hodge-fiber rank, not an arbitrary
cutoff or internal GST shadow rank. -/
noncomputable def chargedFrameHodgeMatrix
    (G : GeometricCycleClassSpine V H)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (E : Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)) →
      RealizedCorrespondenceExpr V H p) :
    Matrix
      (Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)))
      (Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p))) ℚ :=
  nativeHodgeMatrix G (nativeChargedFrame G ell E)

/-- Explicit native rational algebraic cycle manufactured from the inverse
of the real geometric coordinate matrix and the desired Hodge coordinates. -/
noncomputable def chargedFrameInverseCycle
    (G : GeometricCycleClassSpine V H)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (E : Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)) →
      RealizedCorrespondenceExpr V H p)
    (alpha : ClassicalHodgeFiber V H p) :
    codimensionCycles V.X p :=
  nativeCycleByMatrixInversion G (nativeChargedFrame G ell E)
    (chargedFrameHodgeMatrix G ell E)⁻¹ alpha

/-- Exact cycle-class equality for all rational Hodge states in arbitrary
finite rank, conditional ONLY on the numerical determinant of cycles that
were explicitly built from genuine correspondences. -/
theorem chargedFrameInverseCycle_spec
    (G : GeometricCycleClassSpine V H)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (E : Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)) →
      RealizedCorrespondenceExpr V H p)
    (hdet : (chargedFrameHodgeMatrix G ell E).det ≠ 0)
    (alpha : ClassicalHodgeFiber V H p) :
    H.cycleClass p (chargedFrameInverseCycle G ell E alpha) = alpha.1 := by
  exact hodge_cycle_of_nonzero_geometric_determinant G
    (nativeChargedFrame G ell E) hdet alpha

/-- A charged frame can be tested at one fixed geometric weight by one
explicit scalar determinant; no per-target cycle representatives are
requested as premises. -/
theorem every_hodge_class_of_nonzero_charged_geometric_frame
    (G : GeometricCycleClassSpine V H)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (E : Fin (Module.finrank ℚ (ClassicalHodgeFiber V H p)) →
      RealizedCorrespondenceExpr V H p)
    (hdet : (chargedFrameHodgeMatrix G ell E).det ≠ 0)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha :=
  ⟨chargedFrameInverseCycle G ell E ⟨alpha, halpha⟩,
    chargedFrameInverseCycle_spec G ell E hdet ⟨alpha, halpha⟩⟩

/-- The independently necessary geometric generation condition: in every
weight, some finite collection of genuine correspondences constructs a
charged frame whose actual Hodge matrix is nonsingular. This is a named,
checkable proposition, NOT an axiom or a proven existence theorem. -/
def UniversalGSTChargedGeometricFrameGeneration
    (G : GeometricCycleClassSpine V H)
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H) : Prop :=
  ∀ q : Nat,
    letI : FiniteDimensional ℚ (ClassicalHodgeFiber V H q) := F.finite q
    ∃ ell : ClassicalHodgeFiber V H q →ₗ[ℚ] ℚ,
    ∃ E : Fin (Module.finrank ℚ (ClassicalHodgeFiber V H q)) →
      RealizedCorrespondenceExpr V H q,
      (chargedFrameHodgeMatrix G ell E).det ≠ 0

/-- This is a direct full Stage-2G Hodge theorem IF the universal geometric
frame generation statement has independently been established from scheme
geometry. It is not itself an unconditional proof of that input. -/
theorem exact_hodge_of_universal_charged_geometric_frames
    (G : GeometricCycleClassSpine V H)
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (hframe : UniversalGSTChargedGeometricFrameGeneration G F) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  letI : FiniteDimensional ℚ (ClassicalHodgeFiber V H p) := F.finite p
  obtain ⟨ell, E, hdet⟩ := hframe p
  exact every_hodge_class_of_nonzero_charged_geometric_frame
    G ell E hdet alpha halpha

#check nativeChargedFrame
#check chargedFrameHodgeMatrix
#check chargedFrameInverseCycle
#check chargedFrameInverseCycle_spec
#check every_hodge_class_of_nonzero_charged_geometric_frame
#check UniversalGSTChargedGeometricFrameGeneration
#check exact_hodge_of_universal_charged_geometric_frames

#print axioms chargedFrameInverseCycle_spec
#print axioms exact_hodge_of_universal_charged_geometric_frames

end GSTClassicalHodgeArbitraryRankChargeFrames
