import Mathlib.LinearAlgebra.Basis.VectorSpace
import GSTClassicalHodgeFiberedCosmology
import GSTGeometricRealizationStage2G

/-!
# GST CLASSICAL HODGE CYCLE LANDING

This module pushes the classical Hodge reduction through the limitless
fibered GST cosmology all the way to the exact remaining geometric datum.

The unrestricted multiplicity fiber from `GSTClassicalHodgeFiberedCosmology`
keeps a genuine basis of each rational `(p,p)` Hodge space.  Every basis
vector already has a machine-checked projection to the universal cosmic
GST diagonal `(p,p)`.  The only extra datum needed for the classical landing
is therefore an actual native codimension-p algebraic cycle whose supplied
cycle-class equals that basis vector.

No cycle-class surjectivity, Hodge conclusion, realization obligation, or
custom mathematical axiom is assumed below.
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

namespace GSTClassicalHodgeCycleLanding

/-- Native algebraicity data for one genuine basis of one rational `(p,p)`
Hodge fiber.  This is the irreducible classical geometric datum after the
limitless GST coordinate side has been constructed. -/
structure FiberedBasisCycleBridge
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) where
  basisCycle :
    ClassicalHodgeBasisIndex V H p -> codimensionCycles V.X p
  basisCycle_spec :
    forall i : ClassicalHodgeBasisIndex V H p,
      H.cycleClass p (basisCycle i) =
        (classicalHodgeBasis V H p i).1

/-- Extend basis-cycle representatives linearly to every rational `(p,p)`
class in the fixed weight fiber. -/
noncomputable def fiberedBasisCycleLift
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (R : FiberedBasisCycleBridge V H p) :
    ClassicalHodgeFiber V H p →ₗ[ℚ] codimensionCycles V.X p :=
  (classicalHodgeBasis V H p).constr ℚ R.basisCycle

@[simp]
theorem fiberedBasisCycleLift_basis
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (R : FiberedBasisCycleBridge V H p)
    (i : ClassicalHodgeBasisIndex V H p) :
    fiberedBasisCycleLift V H p R (classicalHodgeBasis V H p i) =
      R.basisCycle i := by
  simp [fiberedBasisCycleLift]

/-- The genuine classical cycle-class map of the linear lift is exactly the
subtype inclusion of the Hodge fiber. -/
theorem fiberedBasisCycleLift_spec
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (R : FiberedBasisCycleBridge V H p)
    (alpha : ClassicalHodgeFiber V H p) :
    H.cycleClass p (fiberedBasisCycleLift V H p R alpha) = alpha.1 := by
  have hmaps :
      (H.cycleClass p).comp (fiberedBasisCycleLift V H p R) =
        (rationalHodgeSubspace (H.hodgeBigrading p)).subtype := by
    apply (classicalHodgeBasis V H p).ext
    intro i
    simp [fiberedBasisCycleLift, R.basisCycle_spec]
  change
    ((H.cycleClass p).comp (fiberedBasisCycleLift V H p R)) alpha = alpha.1
  rw [hmaps]
  rfl

/-- Basis-wise algebraicity reconstructs an actual codimension-p cycle for
an arbitrary rational `(p,p)` class by its finite-support basis coordinates. -/
theorem hodge_class_has_cycle_of_fibered_basis_bridge
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    {p : Nat}
    (R : FiberedBasisCycleBridge V H p)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  refine ⟨fiberedBasisCycleLift V H p R alphaH, ?_⟩
  simpa [alphaH] using fiberedBasisCycleLift_spec V H p R alphaH

/-- A basis-cycle bridge in every codimension closes the exact Stage-2G
classical Hodge target. -/
theorem bigraded_hodge_of_fibered_basis_cycle_family
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (R : ∀ p : Nat, FiberedBasisCycleBridge V H p) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  exact hodge_class_has_cycle_of_fibered_basis_bridge V H (R p) alpha halpha

/-- Logical extraction in the reverse direction.  This definition is used
only to establish the exact normal-form equivalence; it is not a constructive
step in the forward proof program. -/
noncomputable def fiberedBasisCycleBridgeOfTarget
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (h : BigradedBettiHodgeStatement V H)
    (p : Nat) :
    FiberedBasisCycleBridge V H p where
  basisCycle i :=
    Classical.choose (show
      ∃ Z : codimensionCycles V.X p,
        H.cycleClass p Z = (classicalHodgeBasis V H p i).1 by
      exact h p (classicalHodgeBasis V H p i).2)
  basisCycle_spec i :=
    Classical.choose_spec (show
      ∃ Z : codimensionCycles V.X p,
        H.cycleClass p Z = (classicalHodgeBasis V H p i).1 by
      exact h p (classicalHodgeBasis V H p i).2)

/-- **FIBERED BASIS NORMAL FORM.**  The classical Hodge target is exactly
basis-wise algebraicity in every genuine rational `(p,p)` multiplicity fiber.
No finite-rank or countability restriction occurs. -/
theorem bigradedBettiHodgeStatement_iff_fibered_basis_cycles
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    BigradedBettiHodgeStatement V H ↔
      ∀ p : Nat, Nonempty (FiberedBasisCycleBridge V H p) := by
  constructor
  · intro h p
    exact ⟨fiberedBasisCycleBridgeOfTarget V H h p⟩
  · intro h
    exact bigraded_hodge_of_fibered_basis_cycle_family V H
      (fun p => Classical.choice (h p))

/-- Every algebraic basis representative in the classical fiber is paired
with the already-proved limitless GST fact that its Hodge basis direction
projects to the universal cosmic diagonal address `(p,p)`. -/
theorem fibered_basis_cycle_projects_to_limitless_cosmos
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (R : FiberedBasisCycleBridge V H p)
    (i : ClassicalHodgeBasisIndex V H p) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = (classicalHodgeBasis V H p i).1 ∧
      forgetMultiplicityToGST
          (fiberedWeightCoordinates V H p
            (classicalHodgeBasis V H p i)) =
        Finsupp.single
          (GSTUniversalAddressBridge.cosmicAddressEquiv (p, p)) 1 := by
  refine ⟨R.basisCycle i, R.basisCycle_spec i, ?_⟩
  exact classical_basis_projects_to_cosmic_diagonal V H p i

/-- The exact remaining GST-to-classical algebraicity proposition.  The
second conjunct is already forced by the limitless cosmology; the first is
precisely the native algebraic-cycle landing. -/
def FiberedGSTAlgebraicityBridge
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) : Prop :=
  ∀ p : Nat, ∀ i : ClassicalHodgeBasisIndex V H p,
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = (classicalHodgeBasis V H p i).1 ∧
      forgetMultiplicityToGST
          (fiberedWeightCoordinates V H p
            (classicalHodgeBasis V H p i)) =
        Finsupp.single
          (GSTUniversalAddressBridge.cosmicAddressEquiv (p, p)) 1

/-- **IRREDUCIBLE GST/CLASSICAL LANDING THEOREM.**  The genuine Stage-2G
Hodge conjecture target is equivalent to the fibered GST algebraicity bridge.
The limitless GST projection half is already a theorem, so all unresolved
mathematical content is concentrated in constructing the native cycles. -/
theorem bigradedBettiHodgeStatement_iff_fibered_gst_algebraicity
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    BigradedBettiHodgeStatement V H ↔ FiberedGSTAlgebraicityBridge V H := by
  constructor
  · intro h p i
    have hmem :
        (classicalHodgeBasis V H p i).1 ∈
          rationalHodgeSubspace (H.hodgeBigrading p) :=
      (classicalHodgeBasis V H p i).2
    rcases h p hmem with ⟨Z, hZ⟩
    refine ⟨Z, hZ, ?_⟩
    exact classical_basis_projects_to_cosmic_diagonal V H p i
  · intro h
    apply bigraded_hodge_of_fibered_basis_cycle_family V H
    intro p
    refine
      { basisCycle := fun i => Classical.choose (h p i)
        basisCycle_spec := ?_ }
    intro i
    exact (Classical.choose_spec (h p i)).1

/-- The fibered limitless coordinate theorem is unconditional: regardless of
algebraicity, every genuine classical basis direction has the correct GST
cosmic base address. -/
theorem fibered_gst_projection_unconditional
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    ∀ p : Nat, ∀ i : ClassicalHodgeBasisIndex V H p,
      forgetMultiplicityToGST
          (fiberedWeightCoordinates V H p
            (classicalHodgeBasis V H p i)) =
        Finsupp.single
          (GSTUniversalAddressBridge.cosmicAddressEquiv (p, p)) 1 := by
  exact classical_basis_projects_to_cosmic_diagonal V H

#check FiberedBasisCycleBridge
#check fiberedBasisCycleLift
#check fiberedBasisCycleLift_basis
#check fiberedBasisCycleLift_spec
#check hodge_class_has_cycle_of_fibered_basis_bridge
#check bigraded_hodge_of_fibered_basis_cycle_family
#check fiberedBasisCycleBridgeOfTarget
#check bigradedBettiHodgeStatement_iff_fibered_basis_cycles
#check fibered_basis_cycle_projects_to_limitless_cosmos
#check FiberedGSTAlgebraicityBridge
#check bigradedBettiHodgeStatement_iff_fibered_gst_algebraicity
#check fibered_gst_projection_unconditional

#print axioms fiberedBasisCycleLift_basis
#print axioms fiberedBasisCycleLift_spec
#print axioms hodge_class_has_cycle_of_fibered_basis_bridge
#print axioms bigraded_hodge_of_fibered_basis_cycle_family
#print axioms bigradedBettiHodgeStatement_iff_fibered_basis_cycles
#print axioms fibered_basis_cycle_projects_to_limitless_cosmos
#print axioms bigradedBettiHodgeStatement_iff_fibered_gst_algebraicity
#print axioms fibered_gst_projection_unconditional

end GSTClassicalHodgeCycleLanding
