import GSTClassicalHodgeLimitlessSpinePropagation

/-!
# GST geometric weight-boundary theorem

Smooth projective varieties have a finite Krull dimension d. In actual
algebraic geometry no codimension-p algebraic cycles exist when p>d.
Any proposed native law requiring nonzero cycle classes for EVERY
natural-number p must therefore respect this boundary.

The repository's NativeMassCycleClassBridge contains a nonzero base mass
and successor transport for all natural p; from it the existing Lean
theorems derive a nonzero native projective spine cycle-class for all p.

The unconditional theorem here proves that the bridge is IMPOSSIBLE on
any carrier admitting a single weight p whose native codimension-p cycle
module is zero. No unrestricted native mass law can be turned into an
axiom without resolving the finite-dimensional support boundary.

This is a constraint on the GST MASS BRIDGE, not a counterexample to
the actual rational Hodge conjecture. Valid versions must be
dimension-bounded or restrict their nonzero claims to demonstrably
active cohomological/geometric weights and use a homology-invariant
intersection/degree measurement.
-/

set_option maxHeartbeats 20000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation

namespace GSTResearchGeometricWeightBoundaryAudit

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- A native zero-cycle module at one weight contradicts a uniformly
nonzero conserved projective spine at ALL weights. -/
theorem no_conserved_charge_when_one_native_weight_vanishes
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hempty : ∀ Z : codimensionCycles V.X p, Z = 0) :
    SpineTowerConservedCharge G → False := by
  intro D
  have hspineZero : spineNativeTower G p = 0 := hempty _
  have hcoh :
      H.cycleClass p (spineNativeTower G p) = 0 := by
    rw [hspineZero]
    simp
  exact (D.cycleClass_spineNativeTower_ne_zero p) hcoh

/-- The stated all-weights native-mass bridge cannot exist if there is
any codimension p where every genuine native cycle vanishes. -/
theorem no_unrestricted_native_mass_bridge_at_empty_weight
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hempty : ∀ Z : codimensionCycles V.X p, Z = 0) :
    NativeMassCycleClassBridge V H → False := by
  intro M
  exact (no_conserved_charge_when_one_native_weight_vanishes
    G p hempty) (M.toConservedCharge G)

#check no_conserved_charge_when_one_native_weight_vanishes
#check no_unrestricted_native_mass_bridge_at_empty_weight

#print axioms no_conserved_charge_when_one_native_weight_vanishes
#print axioms no_unrestricted_native_mass_bridge_at_empty_weight

end GSTResearchGeometricWeightBoundaryAudit
