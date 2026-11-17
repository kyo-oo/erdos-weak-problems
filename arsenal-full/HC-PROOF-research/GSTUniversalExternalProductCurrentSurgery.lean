import GSTNPrimitiveGeometricSurgery

/-!
# GST universal external-product geometric surgery: exact defect transport

Original target: produce, for EVERY smooth projective complex X and
EVERY primitive rational Hodge class, an integral homology preserving
replacement current with absolute Kähler calibration defect tending to 0.

On ANY smooth projective X of any dimension, let S be a closed integral
2q-current. On P¹xP¹ there is the genuine integral homology relation
    [anti-holomorphic graph Γ]+[holomorphic diagonal Δ]
      = 2 [holomorphic ruling fiber F].

External product with S makes an ACTUAL closed integral boundary surgery
on XxP¹xP¹, for every X and any integral current S:
   S x (Γ+Δ) --> 2 (S x F).

With product Kähler metric, the full geometric mass/period identities
for integer rectifiable products are:
   Mass(S x (Γ+Δ)) = 4 Mass(S),
   Period(S x (Γ+Δ)) = 2 Period(S);
   Mass(2 S x F) = 2 Mass(S),
   Period(2 S x F) = 2 Period(S).
The base Γ and Δ have disjoint sheets in 2-dimensional measure.
These identities show exact lowering of mass by 2 Mass(S).

CRITICAL: The OUTPUT defect is 2 * Defect(S), hence vanishes
ONLY IF S already was calibrated. This explicitly tests and REJECTS
a possible inference that universal product-based GST surgery
eliminates arbitrary primitive Hodge defects on X.

Lean verifies the exact universal mass/period arithmetic and the
base integer homology identity, not the analytic external-product
theorems of geometric measure theory. No all-X Hodge assertion occurs.
-/

namespace GSTUniversalExternalProductCurrentSurgery

open GSTNPrimitiveGeometricSurgery

/-- Mass and Kähler period of an arbitrary oriented closed integer current
S on an arbitrary smooth projective X. This numerical projection
does not assert S has an algebraic representative. -/
structure PrimitiveCurrentNumerics where
  mass : ℚ
  period : ℚ
  mass_nonnegative : 0 ≤ mass
  calibrated_bound : period ≤ mass

/-- Absolute Wirtinger calibration defect of the original primitive carrier. -/
def primitiveDefect (S : PrimitiveCurrentNumerics) : ℚ :=
  S.mass - S.period

/-- External-product mass and period for the initial anti-graph+diagonal
packet on XxP¹xP¹. -/
def inputMass (S : PrimitiveCurrentNumerics) : ℚ := 4 * S.mass
def inputPeriod (S : PrimitiveCurrentNumerics) : ℚ := 2 * S.period
def inputDefect (S : PrimitiveCurrentNumerics) : ℚ :=
  inputMass S - inputPeriod S

/-- External-product mass and period for its homologous replacement
by two ruling fibers. -/
def outputMass (S : PrimitiveCurrentNumerics) : ℚ := 2 * S.mass
def outputPeriod (S : PrimitiveCurrentNumerics) : ℚ := 2 * S.period
def outputDefect (S : PrimitiveCurrentNumerics) : ℚ :=
  outputMass S - outputPeriod S

/-- The genuine P¹xP¹ factor surgery preserves the integer homology
signature exactly. -/
theorem base_homology_preserved :
    homology calibratedReplacement = homology badPrimitiveAmple :=
  explicit_surgery_preserves_homology

theorem external_surgery_preserves_calibration_period
    (S : PrimitiveCurrentNumerics) :
    inputPeriod S = outputPeriod S := by
  rfl

/-- A GLOBAL all-X mass lowering operation (on the product XxP¹xP¹),
not a primitive Hodge mass-vanishing theorem. -/
theorem external_surgery_exact_mass_drop
    (S : PrimitiveCurrentNumerics) :
    inputMass S - outputMass S = 2 * S.mass := by
  simp [inputMass, outputMass]
  ring

/-- The defect strictly improves if S has positive mass. -/
theorem external_surgery_exact_defect_drop
    (S : PrimitiveCurrentNumerics) :
    inputDefect S - outputDefect S = 2 * S.mass := by
  simp [inputDefect, outputDefect, inputMass, inputPeriod,
        outputMass, outputPeriod]
  ring

/-- Crucial all-X quantitative obstruction: the remaining primitive
defect is not destroyed by GST tensor surgery but exactly doubled. -/
theorem external_surgery_retains_primitive_defect
    (S : PrimitiveCurrentNumerics) :
    outputDefect S = 2 * primitiveDefect S := by
  simp [outputDefect, outputMass, outputPeriod, primitiveDefect]
  ring

theorem external_surgery_zero_defect_iff_original_calibrated
    (S : PrimitiveCurrentNumerics) :
    outputDefect S = 0 ↔ primitiveDefect S = 0 := by
  rw [external_surgery_retains_primitive_defect]
  constructor
  · intro h
    linarith
  · intro h
    rw [h]
    ring

theorem external_surgery_output_nonnegative
    (S : PrimitiveCurrentNumerics) :
    0 ≤ outputDefect S := by
  rw [external_surgery_retains_primitive_defect]
  unfold primitiveDefect
  linarith [S.calibrated_bound]

#check base_homology_preserved
#check external_surgery_exact_defect_drop
#check external_surgery_zero_defect_iff_original_calibrated
#print axioms external_surgery_zero_defect_iff_original_calibrated


/-! ## Sharp tensor calibration rigidity for every positive holomorphic factor

The old packet was a special case with factor Kähler volume 2.
For ANY positive calibrated product factor of volume v>0,
the remaining primitive defect is exactly v·D(S).
Neither tensor stabilization nor repeating factor surgeries can
turn a noncalibrated primitive carrier into a calibrated current.
This is a quantitative arithmetic identity; its geometric
application assumes the standard mass/period multiplicativity
of external products, not an unverified universal GST functor.
-/

/-- Full arbitrary auxiliary factor mass and calibration period. -/
def generalTensorDefect
    (S : PrimitiveCurrentNumerics) (factorMass factorPeriod : ℚ) : ℚ :=
  S.mass * factorMass - S.period * factorPeriod

/-- Exact separation into a primitive defect term and a factor defect
term, without assuming the original primitive current is holomorphic. -/
theorem general_tensor_defect_decomposition
    (S : PrimitiveCurrentNumerics) (factorMass factorPeriod : ℚ) :
    generalTensorDefect S factorMass factorPeriod =
      factorMass * primitiveDefect S +
      (factorMass - factorPeriod) * S.period := by
  unfold generalTensorDefect primitiveDefect
  ring

/-- Tensoring with ANY calibrated factor of volume v transports the
primitive defect faithfully; it does NOT destroy it. -/
theorem calibrated_tensor_exact_residual
    (S : PrimitiveCurrentNumerics) (v : ℚ) :
    generalTensorDefect S v v = v * primitiveDefect S := by
  rw [general_tensor_defect_decomposition]
  ring

theorem calibrated_tensor_zero_iff_original
    (S : PrimitiveCurrentNumerics) (v : ℚ) (hv : 0 < v) :
    generalTensorDefect S v v = 0 ↔ primitiveDefect S = 0 := by
  rw [calibrated_tensor_exact_residual]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h0 | h0
    · exact False.elim ((ne_of_gt hv) h0)
    · exact h0
  · intro h
    rw [h]
    ring

theorem calibrated_tensor_positive_gap
    (S : PrimitiveCurrentNumerics) (v : ℚ)
    (hv : 0 < v) (hD : 0 < primitiveDefect S) :
    0 < generalTensorDefect S v v := by
  rw [calibrated_tensor_exact_residual]
  exact mul_pos hv hD

/-- Even arbitrarily many tensor-stabilizing moves retain the
original defect scaled by the product of positive volumes. -/
theorem repeated_calibrated_tensor_rigidity
    (S : PrimitiveCurrentNumerics) (v : ℚ) (hv : 0 < v) (n : ℕ) :
    v ^ n * primitiveDefect S = 0 ↔ primitiveDefect S = 0 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hpow | hdef
    · exact False.elim ((ne_of_gt (pow_pos hv n)) hpow)
    · exact hdef
  · intro h
    rw [h]
    ring

#check general_tensor_defect_decomposition
#check calibrated_tensor_zero_iff_original
#check repeated_calibrated_tensor_rigidity
#print axioms repeated_calibrated_tensor_rigidity


/-! ## Rigidity even for noncalibrated auxiliary tensor factors

A calibrated tensor factor was not essential to the nonvanishing
argument. If both Kähler periods are positive, and the factor obeys
the calibration inequality, a zero tensor defect forces BOTH
factors to be individually calibrated. This is an exact numerical
obstruction to all product-only primitive-defect elimination. -/

/-- Any semipositive auxiliary factor preserves nonnegativity of
the total numerical Wirtinger defect. -/
theorem semipositive_tensor_defect_nonnegative
    (S : PrimitiveCurrentNumerics) (a b : ℚ)
    (ha : 0 ≤ a) (hb : b ≤ a) (hp : 0 ≤ S.period) :
    0 ≤ generalTensorDefect S a b := by
  rw [general_tensor_defect_decomposition]
  have hs : 0 ≤ primitiveDefect S := by
    unfold primitiveDefect
    linarith [S.calibrated_bound]
  exact add_nonneg (mul_nonneg ha hs)
    (mul_nonneg (sub_nonneg.mpr hb) hp)

/-- Two positive-period factors have vanishing product defect if
and only if both factors independently saturate calibration. -/
theorem zero_tensor_defect_iff_both_factors_calibrated
    (S : PrimitiveCurrentNumerics) (a b : ℚ)
    (ha : 0 < a) (hb : b ≤ a) (hp : 0 < S.period) :
    generalTensorDefect S a b = 0 ↔
      primitiveDefect S = 0 ∧ a = b := by
  constructor
  · intro hz
    have hs : 0 ≤ primitiveDefect S := by
      unfold primitiveDefect
      linarith [S.calibrated_bound]
    have hfirst : 0 ≤ a * primitiveDefect S :=
      mul_nonneg (le_of_lt ha) hs
    have hsecond : 0 ≤ (a-b) * S.period :=
      mul_nonneg (sub_nonneg.mpr hb) (le_of_lt hp)
    rw [general_tensor_defect_decomposition] at hz
    have hfirstzero : a * primitiveDefect S = 0 := by linarith
    have hsecondzero : (a-b) * S.period = 0 := by linarith
    have hS : primitiveDefect S = 0 := by
      rcases mul_eq_zero.mp hfirstzero with h | h
      · exact False.elim ((ne_of_gt ha) h)
      · exact h
    have hfactor : a = b := by
      rcases mul_eq_zero.mp hsecondzero with h | h
      · linarith
      · exact False.elim ((ne_of_gt hp) h)
    exact ⟨hS, hfactor⟩
  · rintro ⟨hS, hfactor⟩
    rw [general_tensor_defect_decomposition, hS, hfactor]
    ring

#check semipositive_tensor_defect_nonnegative
#check zero_tensor_defect_iff_both_factors_calibrated
#print axioms zero_tensor_defect_iff_both_factors_calibrated


/-! ## GST rigidity under arbitrary finite calibrated stabilizations

The factor volumes may all DIFFER. This rules out a hidden
calibration collapse from composing several independent positive-volume
product surgeries. A factor of volume at least one cannot improve
the original absolute defect. These are exact numerical implications
of genuine geometric mass/period product laws, not a universal
algebraic-cycle realization claim.
-/

open scoped BigOperators

/-- No positive calibrated tensor factor with volume at least one
can decrease the original absolute primitive calibration defect. -/
theorem calibrated_tensor_defect_nondecreasing_at_integral_volume
    (S : PrimitiveCurrentNumerics) (v : ℚ) (hv : 1 ≤ v) :
    primitiveDefect S ≤ generalTensorDefect S v v := by
  rw [calibrated_tensor_exact_residual]
  have hD : 0 ≤ primitiveDefect S := by
    unfold primitiveDefect
    linarith [S.calibrated_bound]
  nlinarith

/-- For an arbitrary FINITE family of different positive calibrated
factors, a tensor product has zero defect if and only if the original
current has zero defect. No fixed-volume or equal-factor assumption. -/
theorem arbitrary_finite_calibrated_tensor_rigidity
    {ι : Type*} (s : Finset ι) (v : ι → ℚ)
    (hv : ∀ i ∈ s, 0 < v i)
    (S : PrimitiveCurrentNumerics) :
    generalTensorDefect S (∏ i ∈ s, v i) (∏ i ∈ s, v i) = 0 ↔
      primitiveDefect S = 0 := by
  classical
  have hprod : 0 < ∏ i ∈ s, v i := by
    apply Finset.prod_pos
    intro i hi
    exact hv i hi
  exact calibrated_tensor_zero_iff_original S _ hprod

#check calibrated_tensor_defect_nondecreasing_at_integral_volume
#check arbitrary_finite_calibrated_tensor_rigidity
#print axioms arbitrary_finite_calibrated_tensor_rigidity

end GSTUniversalExternalProductCurrentSurgery
