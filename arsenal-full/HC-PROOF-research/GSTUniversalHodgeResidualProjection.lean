import Mathlib

/-!
# GST universal constructive Hodge projection and exact residual

For an arbitrary rational Hodge fiber V and its REAL rational native-cycle
space N, let cl : N ->_Q V be the genuine cycle class map. Take any
finite family of actual already constructed native cycles z_i, and
an intersection-dual collection of rational probes ell_i such that

       ell_i(cl(z_j)) = KroneckerDelta(i,j).

This relation can be established from a nondegenerate geometric
intersection Gram independently of unknown Hodge target surjectivity.

For EVERY rational Hodge class alpha, the native algebraic cycle

       Z(alpha) = sum_i ell_i(alpha) z_i

is explicitly defined. The residual

       r(alpha) = alpha - cl(Z(alpha))

is provably invisible to ALL these geometric probes. Thus the
algebraic component is constructed for every target alpha, while
any genuinely missing direction is isolated in an explicit
unrepresented residual.

This construction does NOT assert residual zero. Residual zero
for all alpha would amount to the original Hodge conjecture,
so claiming that without further independent geometry would
simply assume the goal.

The rational-linear algebra is formalized for any finite index set;
the next file specializes N,V to ACTUAL Mathlib native cycles
and the Stage-2G rational Hodge subtype.
-/

set_option maxHeartbeats 4000000
noncomputable section

namespace GSTUniversalHodgeResidualProjection

variable {ι N V : Type*}
  [Fintype ι] [DecidableEq ι]
  [AddCommGroup N] [Module ℚ N]
  [AddCommGroup V] [Module ℚ V]

/-- Genuine native input data, rational-linear class map, and
independently geometric dual intersection detectors.
No target Hodge class representative is supplied. -/
structure GeometricDualCyclePacket
    (ι N V : Type*)
    [Fintype ι] [DecidableEq ι]
    [AddCommGroup N] [Module ℚ N]
    [AddCommGroup V] [Module ℚ V] where
  cycleClass : N →ₗ[ℚ] V
  cycles : ι → N
  detectors : ι → V →ₗ[ℚ] ℚ
  dual : ∀ i j, detectors i (cycleClass (cycles j)) =
    if i = j then 1 else 0

/-- ACTUAL native algebraic output for every rational Hodge input.
The result only uses source cycles built independently of alpha. -/
def projectedNativeCycle
    (P : GeometricDualCyclePacket ι N V) (alpha : V) : N :=
  ∑ i, P.detectors i alpha • P.cycles i

/-- Exact dual intersection values on the projected native cycle. -/
theorem projectedNativeCycle_all_dual_readouts
    (P : GeometricDualCyclePacket ι N V)
    (alpha : V) (j : ι) :
    P.detectors j (P.cycleClass (projectedNativeCycle P alpha)) =
      P.detectors j alpha := by
  classical
  simp [projectedNativeCycle, map_sum, map_smul, P.dual,
    mul_ite, Finset.sum_ite_eq', eq_comm]

/-- The residual Hodge class is canonical relative to this geometric
dual family. It belongs to the common kernel of all native probes. -/
def residualClass
    (P : GeometricDualCyclePacket ι N V) (alpha : V) : V :=
  alpha - P.cycleClass (projectedNativeCycle P alpha)

theorem residual_orthogonal_to_all_geometric_cycles
    (P : GeometricDualCyclePacket ι N V)
    (alpha : V) (j : ι) :
    P.detectors j (residualClass P alpha) = 0 := by
  rw [residualClass, map_sub,
    projectedNativeCycle_all_dual_readouts]
  exact sub_self _

/-- For each target Hodge class, an explicitly constructed native
cycle gives a decomposition into native algebraic plus residual.
No target-algebraicity field is assumed. -/
theorem actual_cycle_plus_residual_equals_target
    (P : GeometricDualCyclePacket ι N V) (alpha : V) :
    P.cycleClass (projectedNativeCycle P alpha) +
      residualClass P alpha = alpha := by
  simp [residualClass]

/-- On one already-constructed source cycle, this projection is
exactly the identity in the true rational Hodge fiber. -/
theorem projected_cycle_recovers_source_generator
    (P : GeometricDualCyclePacket ι N V) (j : ι) :
    projectedNativeCycle P (P.cycleClass (P.cycles j)) = P.cycles j := by
  classical
  simp [projectedNativeCycle, P.dual]

/-- It is mathematically legitimate to claim exact algebraic
representation of alpha from this construction IF the independently
computed residual vanishes, with no witness choice. -/
theorem exact_target_representation_of_zero_residual
    (P : GeometricDualCyclePacket ι N V)
    (alpha : V)
    (hzero : residualClass P alpha = 0) :
    ∃ Z : N, P.cycleClass Z = alpha := by
  refine ⟨projectedNativeCycle P alpha, ?_⟩
  have h := actual_cycle_plus_residual_equals_target P alpha
  rw [hzero, add_zero] at h
  exact h

/-- Conversely, a hypothetical Hodge counterexample MUST have
a nonzero geometrically orthogonal residual. This is an exact
invariant, not an appeal to lack of computational evidence. -/
theorem any_unrepresented_target_has_nonzero_residual
    (P : GeometricDualCyclePacket ι N V)
    (alpha : V)
    (hmissing : alpha ∉ LinearMap.range P.cycleClass) :
    residualClass P alpha ≠ 0 := by
  intro hz
  apply hmissing
  exact exact_target_representation_of_zero_residual P alpha hz

#check projectedNativeCycle_all_dual_readouts
#check residual_orthogonal_to_all_geometric_cycles
#check actual_cycle_plus_residual_equals_target
#check projected_cycle_recovers_source_generator
#check exact_target_representation_of_zero_residual
#check any_unrepresented_target_has_nonzero_residual
#print axioms residual_orthogonal_to_all_geometric_cycles
#print axioms any_unrepresented_target_has_nonzero_residual

end GSTUniversalHodgeResidualProjection
