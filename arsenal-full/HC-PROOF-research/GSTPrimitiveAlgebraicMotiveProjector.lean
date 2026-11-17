import GSTUniversalHodgeResidualProjection

/-!
# GST explicit algebraic primitive motive: geometric projector and complement

For any smooth projective complex X of dimension d, any p with 2p<=d,
and every finite rational basis Z_i of ACTUAL primitive algebraic classes,
Hodge-Riemann gives an invertible rational Gram matrix

     G_ij = (-1)^p ∫_X cl(Z_i) cup cl(Z_j) cup h^(d-2p).

Let G^{-1}=(g^{ij}). The cycle

     Pi_A = sum_(i,j) g^{ij}
       ((-1)^p Z_i·h^(d-2p)) × Z_j

is an ACTUAL rational codimension-d algebraic correspondence on X×X.
The projection formula computes its action on the primitive Hodge fiber:

     Pi_A(v) = sum_i ell_i(v) cl(Z_i).

This file kernel-verifies the EXACT rational-linear projector algebra
using the previously verified dual-cycle packet:
    A²=A; R=(id-A) satisfies R²=R and A R = R A = 0;
    R annihilates every cycle generator and fixes any Hodge direction
    orthogonal to all their intersection detectors.

The fixed residual is therefore the cohomological realization of
the explicit GEOMETRIC COMPLEMENT (Delta_X - Pi_A), once the product,
cup and Gysin comparison is instantiated for the actual X.

The explicit Pi_A cycle itself is a standard valid geometric formula,
but it has NOT been formally constructed inside Mathlib's Chow product
API in this module. Do not infer that R=0: the complement may have
nonzero rational Hodge classes. Idempotence is proved on cohomology;
Chow idempotence modulo rational equivalence is not asserted.
-/

set_option maxHeartbeats 3500000
noncomputable section
open GSTUniversalHodgeResidualProjection

namespace GSTPrimitiveAlgebraicMotiveProjector

variable {ι N V : Type*}
  [Fintype ι] [DecidableEq ι]
  [AddCommGroup N] [Module ℚ N]
  [AddCommGroup V] [Module ℚ V]

noncomputable def nativeAlgebraicProjection
    (P : GeometricDualCyclePacket ι N V) : V →ₗ[ℚ] N where
  toFun := projectedNativeCycle P
  map_add' := by
    intro x y
    simp [projectedNativeCycle, map_add, add_smul,
      Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    simp [projectedNativeCycle, map_smul, smul_smul,
      Finset.smul_sum]

/-- Action of the explicit algebraic Gram correspondence on
cohomology: all values are native algebraic cycle classes. -/
noncomputable def algebraicProjector
    (P : GeometricDualCyclePacket ι N V) : V →ₗ[ℚ] V where
  toFun x := P.cycleClass (projectedNativeCycle P x)
  map_add' := by
    intro x y
    simp [projectedNativeCycle, map_add, add_smul,
      Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    simp [projectedNativeCycle, map_smul, smul_smul,
      Finset.smul_sum]

/-- The true cohomological action of Delta_X - Pi_A. -/
noncomputable def complementProjector
    (P : GeometricDualCyclePacket ι N V) : V →ₗ[ℚ] V :=
  LinearMap.id - algebraicProjector P

theorem algebraicProjector_apply
    (P : GeometricDualCyclePacket ι N V) (x : V) :
    algebraicProjector P x =
      P.cycleClass (projectedNativeCycle P x) := rfl

theorem complementProjector_apply
    (P : GeometricDualCyclePacket ι N V) (x : V) :
    complementProjector P x = residualClass P x := by
  simp [complementProjector, algebraicProjector,
    nativeAlgebraicProjection, residualClass]

/-- Algebraic projector is idempotent: this does NOT require
that the known cycles already cover every rational Hodge class. -/
theorem algebraicProjector_idempotent
    (P : GeometricDualCyclePacket ι N V) :
    (algebraicProjector P).comp (algebraicProjector P) =
      algebraicProjector P := by
  apply LinearMap.ext
  intro x
  have hcoeff :
      projectedNativeCycle P (P.cycleClass (projectedNativeCycle P x)) =
        projectedNativeCycle P x := by
    change (∑ i, P.detectors i (P.cycleClass (projectedNativeCycle P x)) • P.cycles i) =
      ∑ i, P.detectors i x • P.cycles i
    apply Finset.sum_congr rfl
    intro i hi
    rw [projectedNativeCycle_all_dual_readouts P x i]
  change P.cycleClass (projectedNativeCycle P (P.cycleClass (projectedNativeCycle P x))) =
    P.cycleClass (projectedNativeCycle P x)
  rw [hcoeff]

theorem algebraicProjector_fixes_generator
    (P : GeometricDualCyclePacket ι N V) (i : ι) :
    algebraicProjector P (P.cycleClass (P.cycles i)) =
      P.cycleClass (P.cycles i) := by
  rw [algebraicProjector_apply,
    projected_cycle_recovers_source_generator]

/-- The NEW residual correspondence is idempotent as a
cohomological endomorphism. This remains compatible with a
nonzero primitive Hodge residual. -/
theorem complementProjector_idempotent
    (P : GeometricDualCyclePacket ι N V) :
    (complementProjector P).comp (complementProjector P) =
      complementProjector P := by
  apply LinearMap.ext
  intro x
  let A := algebraicProjector P
  have hA : A (A x) = A x := by
    have h := algebraicProjector_idempotent P
    exact congrArg (fun f : V →ₗ[ℚ] V => f x) h
  change (x-A x)-A (x-A x) = x-A x
  rw [map_sub, hA]
  abel

theorem complementProjector_kills_algebraic_generators
    (P : GeometricDualCyclePacket ι N V) (i : ι) :
    complementProjector P (P.cycleClass (P.cycles i)) = 0 := by
  rw [complementProjector_apply, residualClass,
    projected_cycle_recovers_source_generator]
  exact sub_self _

theorem complementProjector_fixes_all_orthogonal_directions
    (P : GeometricDualCyclePacket ι N V)
    (x : V)
    (horth : ∀ i, P.detectors i x = 0) :
    complementProjector P x = x := by
  rw [complementProjector_apply, residualClass]
  have hz : projectedNativeCycle P x = 0 := by
    classical
    simp [projectedNativeCycle, horth]
  rw [hz, map_zero, sub_zero]

/-- Any hypothetical missing Hodge class yields a NONZERO fixed
point of the algebraic complement correspondence. In particular,
algebraicity of Delta-Pi_A alone cannot force zero residual. -/
theorem nonrepresented_target_survives_algebraic_complement
    (P : GeometricDualCyclePacket ι N V)
    (x : V)
    (hmissing : x ∉ LinearMap.range P.cycleClass) :
    complementProjector P x ≠ 0 := by
  rw [complementProjector_apply]
  exact any_unrepresented_target_has_nonzero_residual P x hmissing

#check algebraicProjector_idempotent
#check complementProjector_idempotent
#check complementProjector_kills_algebraic_generators
#check complementProjector_fixes_all_orthogonal_directions
#check nonrepresented_target_survives_algebraic_complement
#print axioms complementProjector_idempotent

end GSTPrimitiveAlgebraicMotiveProjector
