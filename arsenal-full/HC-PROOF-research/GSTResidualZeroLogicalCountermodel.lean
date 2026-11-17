import GSTUniversalHodgeResidualProjection

/-!
# Mathbox: exact logical countermodel for the universal zero-energy jump

This is NOT a counterexample to the Hodge conjecture on an actual
smooth projective complex variety.

It is an exact RATIONAL LINEAR-ALGEBRA countermodel to an alleged
logical implication of the existing GST assumptions alone:

  1. a rational native-cycle space N;
  2. a rational Hodge vector space V with positive scalar product Q;
  3. a genuine linear native class map N -> V;
  4. finitely many independent native algebraic cycle generators;
  5. intersection-dual rational probes;
  6. orthogonality of the residual to all those algebraic sources.

The example has V=Q^2, N=Q, class(z)=(z,0), and
alpha=(0,1). Its algebraic projector is zero; the residual
is (0,1), has nonzero Q-energy 1, and is killed by the
native detector x |-> x.1.

This proves there is NO derivation of universal residual zero
from just the algebraic projection, positivity, and the known
duality/naturality axioms; genuinely new geometric information
specific to actual smooth projective varieties is mandatory.

Do NOT classify this as a genuine geometric Hodge counterexample:
the example is not supplied as a geometric variety. The original
Hodge conjecture stays unresolved.
-/

set_option maxHeartbeats 2500000
noncomputable section

open GSTUniversalHodgeResidualProjection

namespace GSTResidualZeroLogicalCountermodel

/-- Rational native cycle-class map for the minimal test model. -/
def rationalNativeClass : ℚ →ₗ[ℚ] (ℚ × ℚ) where
  toFun z := (z, 0)
  map_add' := by
    intro x y
    ext <;> simp
  map_smul' := by
    intro c x
    ext <;> simp

/-- Exact native-algebraic pairing detector. -/
def firstCoordinate : (ℚ × ℚ) →ₗ[ℚ] ℚ where
  toFun x := x.1
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

/-- All GST dual-cycle assumptions hold for this one-dimensional
native source, even though the ambient rational target has dimension two. -/
def nativeDualPacket :
    GeometricDualCyclePacket PUnit ℚ (ℚ × ℚ) where
  cycleClass := rationalNativeClass
  cycles := fun _ => 1
  detectors := fun _ => firstCoordinate
  dual := by
    intro i j
    cases i
    cases j
    norm_num [firstCoordinate, rationalNativeClass]

def unrepresentedTarget : ℚ × ℚ := (0, 1)

/-- Every known native projection coefficient is zero on the
transverse rational target; this is the actual target of the
zero-energy inference, not an arbitrary postulated ghost. -/
theorem native_projection_zero :
    projectedNativeCycle nativeDualPacket unrepresentedTarget = 0 := by
  simp [projectedNativeCycle, nativeDualPacket,
    unrepresentedTarget, firstCoordinate]

theorem residual_is_nonzero_second_direction :
    residualClass nativeDualPacket unrepresentedTarget = (0, 1) := by
  rw [residualClass, native_projection_zero]
  simp [nativeDualPacket, rationalNativeClass, unrepresentedTarget]

/-- The exact positive rational inner-product norm. -/
def positiveQuadraticNorm (v : ℚ × ℚ) : ℚ :=
  v.1 ^ 2 + v.2 ^ 2

/-- The claimed universal conclusion is FALSE in the exact model
of all existing rational-linear GST residual machinery. -/
theorem residual_energy_eq_one :
    positiveQuadraticNorm
        (residualClass nativeDualPacket unrepresentedTarget) = 1 := by
  rw [residual_is_nonzero_second_direction]
  norm_num [positiveQuadraticNorm]

theorem residual_energy_ne_zero :
    positiveQuadraticNorm
        (residualClass nativeDualPacket unrepresentedTarget) ≠ 0 := by
  rw [residual_energy_eq_one]
  norm_num

/-- Minimal explicit test refuting the unsupported universal
linear-algebra zero-energy implication. This is not a model
of the additional, genuine scheme and Hodge geometry of X. -/
theorem existing_dual_projection_axioms_do_not_force_zero_energy :
    ¬ ∀ (P : GeometricDualCyclePacket PUnit ℚ (ℚ × ℚ))
        (alpha : ℚ × ℚ),
        positiveQuadraticNorm (residualClass P alpha) = 0 := by
  intro h
  exact residual_energy_ne_zero
    (h nativeDualPacket unrepresentedTarget)

#check residual_energy_eq_one
#check existing_dual_projection_axioms_do_not_force_zero_energy
#print axioms residual_energy_eq_one
#print axioms existing_dual_projection_axioms_do_not_force_zero_energy

end GSTResidualZeroLogicalCountermodel
