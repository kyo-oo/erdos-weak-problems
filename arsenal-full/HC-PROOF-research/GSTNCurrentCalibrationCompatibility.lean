import waves.GSTNCohomologyV3
import GSTClassicalHodgeNativeCycleCosmicShadow

/-!
# N-cohomology V3 combined with actual GST Hodge native mass

This is the first honest interface between the strengthened N-hole coordinate
module and the existing GST native cycle / Hodge mass framework. The original
research goal remains the all-variety fixed-homology integral current sequence.

An actual rectifiable-current mass is nonnegative on every orientation of an
integral current and is not rational-linear on signed cycles. The Hodge code's
nativeCycleMass is a rational-linear functional on native algebraic cycles.

We PROVE the mismatch on the ACTUAL native algebraic cycle type:
1. If nativeCycleMass were nonnegative on every signed cycle, it would vanish.
2. Any nonzero nativeCycleMass necessarily takes a negative value on some
   signed algebraic cycle.

Therefore N-cohomology cannot use this linear mass to establish a geometric
integral-current calibration bound. The separate geometric mass functional,
integer rectifiability and a class-preserving cycle realization are needed.

This is a correctness-preserving upgrade/combination, not a new Hodge axiom
or a proof of unconditionally existing almost-calibrated currents.
-/

set_option maxHeartbeats 10000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTGeometricRealizationStage2D
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTNCohomologyV3

namespace GSTNCurrentCalibrationCompatibility

variable {V : SmoothProjectiveComplexScheme}
variable {p : Nat}

/-- Nonnegative linear native mass on EVERY signed native algebraic cycle
collapses to zero identically. This is not true for geometric mass on
integral currents, which is intentionally nonlinear. -/
theorem native_linear_mass_nonnegative_implies_zero
    (hnonnegative : ∀ Z : codimensionCycles V.X p,
      0 ≤ nativeCycleMass V p Z) :
    ∀ Z : codimensionCycles V.X p,
      nativeCycleMass V p Z = 0 := by
  intro Z
  exact nonnegative_linear_native_mass_must_vanish
    (nativeCycleMass V p) hnonnegative Z

/-- In the original GST native algebraic cycle class, a nonzero native mass
forces a signed cycle with NEGATIVE linear mass. Thus no global
nonnegative geometric mass can equal it on all signed cycles. -/
theorem nonzero_native_linear_mass_has_negative_signed_cycle
    (K : codimensionCycles V.X p)
    (hK : nativeCycleMass V p K ≠ 0) :
    ∃ Z : codimensionCycles V.X p,
      nativeCycleMass V p Z < 0 := by
  rcases nonzero_linear_mass_has_negative_orientation
    (nativeCycleMass V p) K hK with hn | hn
  · exact ⟨K, hn⟩
  · exact ⟨-K, hn⟩

/-- Direct incompatibility with any proposed pointwise nonnegative
integral-current mass identification on the complete rational signed
native-cycle group. -/
theorem nonzero_native_linear_mass_not_globally_nonnegative
    (K : codimensionCycles V.X p)
    (hK : nativeCycleMass V p K ≠ 0) :
    ¬ ∀ Z : codimensionCycles V.X p, 0 ≤ nativeCycleMass V p Z := by
  intro hpos
  exact hK (native_linear_mass_nonnegative_implies_zero hpos K)

#check native_linear_mass_nonnegative_implies_zero
#check nonzero_native_linear_mass_has_negative_signed_cycle
#check nonzero_native_linear_mass_not_globally_nonnegative

#print axioms native_linear_mass_nonnegative_implies_zero
#print axioms nonzero_native_linear_mass_has_negative_signed_cycle

end GSTNCurrentCalibrationCompatibility
