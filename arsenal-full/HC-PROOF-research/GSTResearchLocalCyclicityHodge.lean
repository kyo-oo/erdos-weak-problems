import GSTResearchUniversalOrbitClosureLaw

/-!
# GST local geometric cyclicity — all-weight Hodge reduction

This removes TWO previously separate demands from the sufficient
hypotheses: no prescribed nonzero zeta measurement and no full
GLOBAL geometric irreducibility. Instead, one native algebraic
cycle at each nonzero rational Hodge weight is required to be
CYCLIC under the actual finite-closed Hodge-compatible
correspondence operators.

The previous unconditional universal MINIMAL ORBIT theorem shows
that this condition is exactly full native geometric orbit
generation from that single chosen seed. Under this condition
each target Hodge class is represented by a native algebraic
cycle obtained from that explicit construction.

Zero Hodge fibers are treated without any seed. This is an
all-varieties, all-weights CONDITIONAL reconstruction result
(not the unconditional classical Hodge conjecture).
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
open GSTClassicalHodgeGeometricMatrixRankLanding
open GSTResearchUniversalOrbitClosureLaw

namespace GSTResearchLocalCyclicityHodge

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- All-weights final landing from a LOCAL geometric cyclic seed in every
nonzero rational Hodge fiber. This is weaker than universally
requiring the entire actual correspondence action to be irreducible;
no zeta scalar and no matrix-unit realization assumptions occur. -/
theorem full_hodge_of_all_active_native_geometric_cyclicities
    (G : GeometricCycleClassSpine V H)
    (hcyclic : ∀ p : Nat,
      (∃ a : ClassicalHodgeFiber V H p, a ≠ 0) →
      ∃ Z : codimensionCycles V.X p,
        SeedCyclicForActualGeometry G Z) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  by_cases hactive :
      ∃ a : ClassicalHodgeFiber V H p, a ≠ 0
  · obtain ⟨Z, hZ⟩ := hcyclic p hactive
    exact hodge_cycles_from_one_geometrically_cyclic_native_seed
      G Z hZ alpha halpha
  · have ha0 : alpha = 0 := by
      by_contra hne
      apply hactive
      refine ⟨⟨alpha, halpha⟩, ?_⟩
      intro hz
      apply hne
      simpa using congrArg Subtype.val hz
    exact ⟨0, by simp [ha0]⟩

#check full_hodge_of_all_active_native_geometric_cyclicities
#print axioms full_hodge_of_all_active_native_geometric_cyclicities

end GSTResearchLocalCyclicityHodge
