import waves.GSTNCohomologyV3

/-!
# Mathbox: finite integral calibration obstruction inside N-channel geometry

Goal being attacked (unchanged): fixed-integral-homology closed integral
currents of vanishing absolute Kähler calibration defect for every rational
Hodge class on every smooth projective complex variety.

This file pinpoints a subtle missing INTEGRAL step in attempts to upgrade
rational N-channel coordinates to genuine integral currents. It is a finite
arithmetical model, NOT a smooth-projective Hodge counterexample.

Take two channels whose periods are 2 and 3, and ask for homology class 1.
A closed integral signed chain exists: (-1,1) has period 1.
A rational nonnegative chain exists: (1/2,0) has period 1 and
mass-period defect 0.
But NO integral nonnegative chain represents period 1, and EVERY
integral signed chain of this period has calibration defect >= 4.
Thus rational positivity + integral total period + existence of
integral cycles does not, by itself, supply fixed-class integer
almost-calibrated approximants.

For genuine projective varieties, the user-requested bridge must supply
new geometry forbidding this integrality gap for shifted Hodge classes.
The example does NOT show that the gap occurs in genuine Hodge geometry.
-/

namespace GSTNIntegralCalibrationGap

/-- Integral two-channel period, analogy for integer homology. -/
def period (a b : ℤ) : ℤ := 2 * a + 3 * b

/-- Absolute mass, analogue of a nonnegative nonlinear current mass. -/
def mass (a b : ℤ) : ℤ := 2 * |a| + 3 * |b|

/-- Absolute calibration defect (always nonnegative). -/
def defect (a b : ℤ) : ℤ := mass a b - period a b

theorem integral_class_one_exists : period (-1) 1 = 1 := by
  norm_num [period]

/-- The missing saturated-effective-monoid property already fails for a
two-channel integer lattice, though it holds over rational coefficients. -/
theorem no_nonnegative_integral_carrier_for_period_one
    (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    period a b ≠ 1 := by
  unfold period
  omega

/-- Exact positive integrality gap; no INTEGER signed cycle with period
one can be made arbitrarily close to the calibrated cone. -/
theorem every_integral_carrier_has_defect_at_least_four
    (a b : ℤ) (hperiod : period a b = 1) :
    4 ≤ defect a b := by
  unfold period at hperiod
  unfold defect mass period
  by_cases ha : a < 0
  · by_cases hb : b < 0
    · omega
    · have hba : 0 ≤ b := le_of_not_gt hb
      rw [abs_of_neg ha, abs_of_nonneg hba]
      omega
  · have haa : 0 ≤ a := le_of_not_gt ha
    by_cases hb : b < 0
    · rw [abs_of_nonneg haa, abs_of_neg hb]
      omega
    · have hba : 0 ≤ b := le_of_not_gt hb
      omega

/-- The lower bound 4 is sharp. -/
theorem sharp_integral_carrier_defect :
    period (-1) 1 = 1 ∧ defect (-1) 1 = 4 := by
  constructor <;> norm_num [period, defect, mass]

/-- Zero-defect rational effective carrier for the SAME period one. -/
theorem rational_carrier_is_calibrated :
    (2 : ℚ) * (1/2) + 3 * 0 = 1 ∧
    (2 : ℚ) * |(1/2 : ℚ)| + 3 * |(0 : ℚ)| = 1 := by
  constructor <;> norm_num

/-- Even an arbitrary fixed-homology INTEGER sequence has a persistent
positive lower bound on every element's calibration defect. -/
theorem no_integral_fixed_class_defect_vanishing
    (T : ℕ → ℤ × ℤ)
    (hclass : ∀ n, period (T n).1 (T n).2 = 1) :
    ∀ n, 4 ≤ defect (T n).1 (T n).2 := by
  intro n
  exact every_integral_carrier_has_defect_at_least_four
    (T n).1 (T n).2 (hclass n)

#check no_nonnegative_integral_carrier_for_period_one
#check every_integral_carrier_has_defect_at_least_four
#check rational_carrier_is_calibrated
#check no_integral_fixed_class_defect_vanishing
#print axioms every_integral_carrier_has_defect_at_least_four

end GSTNIntegralCalibrationGap
