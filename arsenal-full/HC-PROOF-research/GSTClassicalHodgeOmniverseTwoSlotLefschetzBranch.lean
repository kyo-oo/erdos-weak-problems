import GSTClassicalHodgeOmniverseCausalBranchPacket
import GSTClassicalHodgeTwoSlotLefschetzCollapse

/-!
# GST CLASSICAL HODGE — OMNIVERSE ARROWS AS BARE TWO-SLOT LEFSCHETZ

The handwritten Pi/omniverse branch graph reaches an arbitrary Hodge basis
sheet by a rank-one matrix-unit transition.  The universal two-slot GST
calculation proves that no separate rank-one primitive is needed: on the
ordered two-slot chart attached to `(i,j)`, the bare rationalized two-step
Lefschetz operator is already the nonzero forward scalar times that matrix
unit.

Consequently every primitive causal arrow used by the handwritten branch
collapse is literally a normalized local `L^2` firing.  This is the equation
that should be geometrically externalized; source/target projectors and an
independent matrix-unit externalization are unnecessary.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeOmniverseTwoSlotLefschetzBranch

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgePrimitiveArsenalRationalization
open GSTClassicalHodgeExplicitArsenalGeneration
open GSTClassicalHodgeLocalCyclicCriterion
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgeTwoSlotLefschetzCollapse

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The one universal scalar appearing in every ordered two-slot chart. -/
abbrev twoSlotScalar : ℚ :=
  (forwardScalar sourceSlot targetSlot : ℚ)

/-- The scalar is nonzero, hence normalization is legitimate. -/
theorem twoSlotScalar_ne_zero : twoSlotScalar ≠ 0 := by
  exact twoSlot_forwardScalar_ne_zero

/-- Bare `L^2` in the ordered `(i,j)` two-slot chart is exactly the universal
nonzero scalar times the genuine rank-free Hodge matrix unit. -/
theorem localized_L2_eq_scaled_matrixUnit
    (i j : ClassicalHodgeBasisIndex V H p) :
    liftFiniteHodgeOperator (pairBasisIndex i j) (diagonalLefschetzQ 2 2) =
      twoSlotScalar • hodgeMatrixUnit i j := by
  simpa [twoSlotScalar] using
    (lifted_twoSlotLefschetz_eq_scaled_hodgeMatrixUnit
      (V := V) (H := H) (p := p) i j)

/-- Therefore the matrix unit itself is the normalized bare two-step
Lefschetz firing. -/
theorem matrixUnit_eq_normalized_localized_L2
    (i j : ClassicalHodgeBasisIndex V H p) :
    hodgeMatrixUnit i j =
      (twoSlotScalar)⁻¹ •
        liftFiniteHodgeOperator (pairBasisIndex i j) (diagonalLefschetzQ 2 2) := by
  rw [localized_L2_eq_scaled_matrixUnit, smul_smul,
    inv_mul_cancel₀ twoSlotScalar_ne_zero, one_smul]

/-- Elementwise form used directly by the handwritten branch-collapse sum. -/
theorem matrixUnit_apply_eq_normalized_localized_L2
    (i j : ClassicalHodgeBasisIndex V H p)
    (alpha : ClassicalHodgeFiber V H p) :
    hodgeMatrixUnit i j alpha =
      (twoSlotScalar)⁻¹ •
        liftFiniteHodgeOperator (pairBasisIndex i j)
          (diagonalLefschetzQ 2 2) alpha := by
  exact LinearMap.congr_fun
    (matrixUnit_eq_normalized_localized_L2
      (V := V) (H := H) (p := p) i j) alpha

/-- Every primitive omniverse event admits an exact equation in which its
target state is a normalized local two-step Lefschetz firing from one live
source slot to the requested target slot. -/
theorem event_target_eq_normalized_localized_L2
    {x y : HodgeBranchNode (V := V) (H := H) (p := p)}
    (e : HodgeBranchEvent x y) :
    ∃ j : ClassicalHodgeBasisIndex V H p,
      ∃ i : HodgeSupportIndex x.state,
        y.state =
          (twoSlotScalar)⁻¹ •
            liftFiniteHodgeOperator (pairBasisIndex i.1 j)
              (diagonalLefschetzQ 2 2) x.state := by
  rcases e with ⟨j, i, hxy⟩
  refine ⟨j, i, ?_⟩
  rw [hxy]
  rw [GSTClassicalHodgeAugmentedTargetMatrixUnit.augmentedConcreteHodgeMatrixUnit_eq]
  exact matrixUnit_apply_eq_normalized_localized_L2
    (V := V) (H := H) (p := p) i.1 j x.state

/-- The exact handwritten branch-collapse identity rewritten entirely in terms
of normalized local bare `L^2` firings. -/
theorem branch_collapse_via_localized_L2
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    ∃ i : HodgeSupportIndex alpha,
      hodgeCoordinate i.1 alpha ≠ 0 ∧
      alpha =
        ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
          (((classicalHodgeBasis V H p).repr alpha j) *
              (hodgeCoordinate i.1 alpha)⁻¹) •
            ((twoSlotScalar)⁻¹ •
              liftFiniteHodgeOperator (pairBasisIndex i.1 j)
                (diagonalLefschetzQ 2 2) alpha) := by
  obtain ⟨i, hi, hcollapse⟩ :=
    branch_collapse_identity (V := V) (H := H) alpha halpha
  refine ⟨i, hi, ?_⟩
  conv_lhs => rw [hcollapse]
  apply Finset.sum_congr rfl
  intro j hj
  rw [matrixUnit_apply_eq_normalized_localized_L2
    (V := V) (H := H) (p := p) i.1 j alpha]

#check localized_L2_eq_scaled_matrixUnit
#check matrixUnit_eq_normalized_localized_L2
#check event_target_eq_normalized_localized_L2
#check branch_collapse_via_localized_L2

#print axioms localized_L2_eq_scaled_matrixUnit
#print axioms matrixUnit_eq_normalized_localized_L2
#print axioms event_target_eq_normalized_localized_L2
#print axioms branch_collapse_via_localized_L2

end GSTClassicalHodgeOmniverseTwoSlotLefschetzBranch
