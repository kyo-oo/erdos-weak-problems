import waves.GSTNCohomologyV3

/-!
# GST N-cohomology: constructive integral ample-shift saturation in ALL finite ranks

Original research goal: construct fixed-integral-homology almost-calibrated
currents on EVERY smooth projective complex variety for every rational Hodge
class. This file proves an exact N-channel integer model mechanism relevant to
that goal. It is NOT a theorem constructing geometric currents on arbitrary X.

Unlike the two-channel result, this works for any finite N-shape, any signed
integer coefficient vector, any positive integer ample vector b, and any
nonnegative integer channel masses/periods w.

The explicit budget M=sum_i |a_i| produces nonnegative integer coordinates
c_i=a_i+M*b_i. Its weighted homology period is exactly period(a)+M*period(b)
and nonlinear absolute-multiplicity mass equals its period exactly.
Therefore the constant integer sequence of c has calibration defect zero.

To apply this to a genuine complex projective variety, an independently proved
geometric cycle-class realization must identify EVERY rational Hodge direction
with integer combinations of ACTUAL calibrated holomorphic cycles. That
surjectivity is not assumed or proved here.
-/

set_option maxHeartbeats 10000000
noncomputable section

namespace GSTNAllChannelAmpleSaturation

open GSTNCohomology
open scoped BigOperators

/-- Signed integer N-channel coefficients, with N coming from GST N-shapes. -/
abbrev IntegerChannels (s : NShape) := Fin s.holes → ℤ

/-- Explicit single ample-shift budget, valid for arbitrary finite N. -/
def shiftBudget (s : NShape) (a : IntegerChannels s) : ℤ :=
  ∑ i : Fin s.holes, |a i|

/-- Shift along any strictly positive integer channel-vector b. -/
def shiftedChannels (s : NShape) (a b : IntegerChannels s) :
    IntegerChannels s :=
  fun i => a i + shiftBudget s a * b i

theorem shiftBudget_nonnegative (s : NShape) (a : IntegerChannels s) :
    0 ≤ shiftBudget s a := by
  unfold shiftBudget
  exact Finset.sum_nonneg (fun i hi => abs_nonneg (a i))

theorem shiftBudget_dominates_coordinate
    (s : NShape) (a : IntegerChannels s) (i : Fin s.holes) :
    |a i| ≤ shiftBudget s a := by
  classical
  unfold shiftBudget
  exact Finset.single_le_sum
    (fun j hj => abs_nonneg (a j)) (Finset.mem_univ i)

/-- The constructive ALL-N saturation theorem. There are no existential
witnesses hidden in the proof: shiftedChannels is an explicit formula. -/
theorem shiftedChannels_nonnegative
    (s : NShape) (a b : IntegerChannels s)
    (hb : ∀ i, 1 ≤ b i) :
    ∀ i, 0 ≤ shiftedChannels s a b i := by
  intro i
  have hs := shiftBudget_dominates_coordinate s a i
  have hm := shiftBudget_nonnegative s a
  have hb_i := hb i
  have habs : -|a i| ≤ a i := neg_abs_le (a i)
  unfold shiftedChannels
  nlinarith [mul_nonneg hm (show 0 ≤ b i - 1 by omega)]

/-- Weighted integer homology period in an abstract N-channel lattice. -/
def period (s : NShape) (w a : IntegerChannels s) : ℤ :=
  ∑ i : Fin s.holes, w i * a i

/-- Nonnegative but NONLINEAR multiplicity mass. -/
def currentMass (s : NShape) (w a : IntegerChannels s) : ℤ :=
  ∑ i : Fin s.holes, w i * |a i|

def calibrationDefect (s : NShape) (w a : IntegerChannels s) : ℤ :=
  currentMass s w a - period s w a

theorem period_shifted
    (s : NShape) (w a b : IntegerChannels s) :
    period s w (shiftedChannels s a b) =
      period s w a + shiftBudget s a * period s w b := by
  unfold period shiftedChannels
  calc
    (∑ i : Fin s.holes, w i * (a i + shiftBudget s a * b i)) =
      (∑ i : Fin s.holes, w i * a i) +
        (∑ i : Fin s.holes, shiftBudget s a * (w i * b i)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i : Fin s.holes, w i * a i) +
        shiftBudget s a * (∑ i : Fin s.holes, w i * b i) := by
      rw [Finset.mul_sum]

theorem mass_shifted_eq_period
    (s : NShape) (w a b : IntegerChannels s)
    (hb : ∀ i, 1 ≤ b i) :
    currentMass s w (shiftedChannels s a b) =
      period s w (shiftedChannels s a b) := by
  unfold currentMass period
  apply Finset.sum_congr rfl
  intro i hi
  rw [abs_of_nonneg (shiftedChannels_nonnegative s a b hb i)]

theorem shifted_zero_defect
    (s : NShape) (w a b : IntegerChannels s)
    (hb : ∀ i, 1 ≤ b i) :
    calibrationDefect s w (shiftedChannels s a b) = 0 := by
  unfold calibrationDefect
  rw [mass_shifted_eq_period s w a b hb]
  exact sub_self _

/-- A *single fixed shifted integer homology period* at every sequence
index, with absolute (not normalized) calibration defect exactly zero,
in the all-N integer-channel model. -/
def integerCalibratedSequence
    (s : NShape) (a b : IntegerChannels s) : ℕ → IntegerChannels s :=
  fun _ => shiftedChannels s a b

theorem all_N_integral_fixed_period_calibrated_sequence
    (s : NShape) (w a b : IntegerChannels s)
    (hb : ∀ i, 1 ≤ b i) :
    (∀ k : ℕ,
      period s w (integerCalibratedSequence s a b k) =
        period s w a + shiftBudget s a * period s w b) ∧
    (∀ k : ℕ,
      calibrationDefect s w (integerCalibratedSequence s a b k) = 0) := by
  constructor
  · intro k
    exact period_shifted s w a b
  · intro k
    exact shifted_zero_defect s w a b hb

#check all_N_integral_fixed_period_calibrated_sequence
#print axioms all_N_integral_fixed_period_calibrated_sequence


/-! ## Exact positivity-cone semantics for ALL N-window channels

The construction above only supplied a sufficient positive ample shift.
These results prove NECESSITY as well: whenever every channel has
strictly positive integer mass weight, abstract zero calibration defect
is equivalent to coordinatewise nonnegativity. This is a complete
integer-effective cone, not a claim that X has a realized algebraic
cycle for every coordinate direction.
-/

/-- A canonical expression of N-channel defect as a sum of weighted
negative-part penalties, valid WITHOUT sign assumptions. -/
theorem defect_as_weighted_negative_part
    (s : NShape) (w a : IntegerChannels s) :
    calibrationDefect s w a =
      ∑ i : Fin s.holes, w i * (|a i| - a i) := by
  unfold calibrationDefect currentMass period
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- For arbitrary nonnegative integer weights, the N-channel
nonlinear defect is globally nonnegative, just like actual
Kähler calibration defect (but only inside this coordinate model). -/
theorem defect_nonnegative
    (s : NShape) (w a : IntegerChannels s)
    (hw : ∀ i, 0 ≤ w i) :
    0 ≤ calibrationDefect s w a := by
  rw [defect_as_weighted_negative_part]
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hw i) (sub_nonneg.mpr (le_abs_self (a i)))

/-- Exact all-N classification of zero-defect integer packets:
under strictly positive weights there are no hidden signed
calibrated directions, and the earlier ample shift lands in
precisely the entire integral nonnegative cone. -/
theorem defect_zero_iff_all_coordinates_nonnegative
    (s : NShape) (w a : IntegerChannels s)
    (hw : ∀ i, 1 ≤ w i) :
    calibrationDefect s w a = 0 ↔
      ∀ i : Fin s.holes, 0 ≤ a i := by
  constructor
  · intro hz i
    by_contra hnot
    have hneg : a i < 0 := lt_of_not_ge hnot
    have hweights : ∀ j ∈ Finset.univ,
        0 ≤ w j * (|a j| - a j) := by
      intro j hj
      exact mul_nonneg (by have h := hw j; omega)
        (sub_nonneg.mpr (le_abs_self (a j)))
    have hpositive : 0 < w i * (|a i| - a i) := by
      have hwi : 0 < w i := by have h := hw i; omega
      have hai : 0 < |a i| - a i := by
        rw [abs_of_neg hneg]
        omega
      exact mul_pos hwi hai
    have hle :
        w i * (|a i| - a i) ≤
          ∑ j : Fin s.holes, w j * (|a j| - a j) :=
      Finset.single_le_sum
        (fun j hj => hweights j (Finset.mem_univ j))
        (Finset.mem_univ i)
    rw [defect_as_weighted_negative_part] at hz
    omega
  · intro ha
    rw [defect_as_weighted_negative_part]
    apply Finset.sum_eq_zero
    intro i hi
    rw [abs_of_nonneg (ha i)]
    ring

/-- The earlier explicit GST ample-shift operation is now a
constructive witness for the complete zero-defect cone. -/
theorem shifted_lands_in_complete_zero_defect_cone
    (s : NShape) (w a b : IntegerChannels s)
    (hw : ∀ i, 1 ≤ w i)
    (hb : ∀ i, 1 ≤ b i) :
    calibrationDefect s w (shiftedChannels s a b) = 0 ∧
      (∀ i : Fin s.holes, 0 ≤ shiftedChannels s a b i) := by
  have h := shiftedChannels_nonnegative s a b hb
  exact ⟨(defect_zero_iff_all_coordinates_nonnegative s w
    (shiftedChannels s a b) hw).2 h, h⟩

#check defect_zero_iff_all_coordinates_nonnegative
#print axioms defect_zero_iff_all_coordinates_nonnegative



/-! ## Sharp GST N-window ample shift: the LEAST integral coefficient

Previous ample-shift budget was sum_i |a_i|, which may grossly
overshoot the integer effective cone. The new law uses the LEAST
nonnegative integer shift, not merely any sufficient one. No Hodge
surjectivity or imaginary geometric cycle is introduced.
-/

/-- An actual candidate integer shift works in every N channel. -/
def IsFeasibleAmpleShift
    (s : NShape) (a b : IntegerChannels s) (k : ℕ) : Prop :=
  ∀ i : Fin s.holes, 0 ≤ a i + (k : ℤ) * b i

theorem feasible_ample_shift_exists
    (s : NShape) (a b : IntegerChannels s)
    (hb : ∀ i, 1 ≤ b i) :
    ∃ k : ℕ, IsFeasibleAmpleShift s a b k := by
  have hbudget := shiftBudget_nonnegative s a
  refine ⟨(shiftBudget s a).toNat, ?_⟩
  intro i
  have h := shiftedChannels_nonnegative s a b hb i
  have hcast : (((shiftBudget s a).toNat : ℕ) : ℤ) =
      shiftBudget s a := by omega
  change 0 ≤ a i + (((shiftBudget s a).toNat : ℕ) : ℤ) * b i
  rw [hcast]
  exact h

/-- Exact minimal integer ample shift over ALL feasible natural shifts. -/
noncomputable def leastAmpleShift
    (s : NShape) (a b : IntegerChannels s)
    (hb : ∀ i, 1 ≤ b i) : ℕ := by
  classical
  exact Nat.find (feasible_ample_shift_exists s a b hb)

theorem leastAmpleShift_feasible
    (s : NShape) (a b : IntegerChannels s)
    (hb : ∀ i, 1 ≤ b i) :
    IsFeasibleAmpleShift s a b (leastAmpleShift s a b hb) := by
  classical
  exact Nat.find_spec (feasible_ample_shift_exists s a b hb)

/-- The new value is OPTIMAL, not merely a large positivity bound. -/
theorem leastAmpleShift_minimal
    (s : NShape) (a b : IntegerChannels s)
    (hb : ∀ i, 1 ≤ b i)
    (k : ℕ) (hk : IsFeasibleAmpleShift s a b k) :
    leastAmpleShift s a b hb ≤ k := by
  classical
  exact Nat.find_min' (feasible_ample_shift_exists s a b hb) hk

/-- At the exact LEAST shift, all nonnegative and all strictly positive
weight choices have zero absolute N-channel calibration defect. -/
theorem leastAmpleShift_calibrates_all_positive_weights
    (s : NShape) (w a b : IntegerChannels s)
    (hw : ∀ i, 1 ≤ w i)
    (hb : ∀ i, 1 ≤ b i) :
    calibrationDefect s w
      (fun i => a i + ((leastAmpleShift s a b hb : ℕ) : ℤ) * b i) = 0 := by
  apply (defect_zero_iff_all_coordinates_nonnegative s w _ hw).2
  exact leastAmpleShift_feasible s a b hb

/-- Strong necessity: EVERY zero-defect positive-weight integer shift
must be at least this sharp minimum. -/
theorem leastAmpleShift_optimal_for_zero_defect
    (s : NShape) (w a b : IntegerChannels s)
    (hw : ∀ i, 1 ≤ w i)
    (hb : ∀ i, 1 ≤ b i)
    (k : ℕ)
    (hk : calibrationDefect s w (fun i => a i + (k : ℤ) * b i) = 0) :
    leastAmpleShift s a b hb ≤ k := by
  apply leastAmpleShift_minimal s a b hb k
  exact (defect_zero_iff_all_coordinates_nonnegative s w _ hw).1 hk

#check leastAmpleShift_calibrates_all_positive_weights
#check leastAmpleShift_optimal_for_zero_defect
#print axioms leastAmpleShift_optimal_for_zero_defect


/-! ## Exact all-N transition: the first calibrated integer shift

The earlier law constructs the optimal shift. This upgrade classifies
EVERY integer shift on both sides of that threshold, for arbitrary
positive weights and nonuniform integral ample directions. It is a
complete finite-lattice effective-cone phase transition.
-/

/-- Every smaller integer shift has strictly positive absolute
calibration defect in the N-channel integer model. -/
theorem positive_defect_before_least_ample_shift
    (s : NShape) (w a b : IntegerChannels s)
    (hw : ∀ i, 1 ≤ w i) (hb : ∀ i, 1 ≤ b i)
    (k : ℕ) (hk : k < leastAmpleShift s a b hb) :
    0 < calibrationDefect s w (fun i => a i + (k : ℤ) * b i) := by
  have hnonneg : 0 ≤ calibrationDefect s w
      (fun i => a i + (k : ℤ) * b i) :=
    defect_nonnegative s w _ (fun i => by have h := hw i; omega)
  by_contra hnot
  have hz : calibrationDefect s w
      (fun i => a i + (k : ℤ) * b i) = 0 := by omega
  have hmin := leastAmpleShift_optimal_for_zero_defect
    s w a b hw hb k hz
  omega

/-- At and above the sharp first ample shift, every coordinate
is nonnegative, hence the EXACT integer defect is zero. -/
theorem zero_defect_at_every_larger_ample_shift
    (s : NShape) (w a b : IntegerChannels s)
    (hw : ∀ i, 1 ≤ w i) (hb : ∀ i, 1 ≤ b i)
    (k : ℕ) (hk : leastAmpleShift s a b hb ≤ k) :
    calibrationDefect s w (fun i => a i + (k : ℤ) * b i) = 0 := by
  apply (defect_zero_iff_all_coordinates_nonnegative s w _ hw).2
  intro i
  have hbase : 0 ≤ a i +
      ((leastAmpleShift s a b hb : ℕ) : ℤ) * b i :=
    leastAmpleShift_feasible s a b hb i
  have hki : ((leastAmpleShift s a b hb : ℕ) : ℤ) ≤ (k : ℤ) :=
    Int.ofNat_le.mpr hk
  have hbi : 0 ≤ b i := by have h := hb i; omega
  have hmul : 0 ≤ ((k : ℤ) -
      ((leastAmpleShift s a b hb : ℕ) : ℤ)) * b i :=
    mul_nonneg (sub_nonneg.mpr hki) hbi
  nlinarith

/-- The exact sharp quantifier-free CALIBRATION THRESHOLD:
there is no hidden interval or fractionally calibrated integer packet. -/
theorem all_N_zero_defect_iff_integer_shift_at_least_minimal
    (s : NShape) (w a b : IntegerChannels s)
    (hw : ∀ i, 1 ≤ w i) (hb : ∀ i, 1 ≤ b i)
    (k : ℕ) :
    calibrationDefect s w (fun i => a i + (k : ℤ) * b i) = 0 ↔
      leastAmpleShift s a b hb ≤ k := by
  constructor
  · exact leastAmpleShift_optimal_for_zero_defect s w a b hw hb k
  · exact zero_defect_at_every_larger_ample_shift s w a b hw hb k

#check all_N_zero_defect_iff_integer_shift_at_least_minimal
#print axioms all_N_zero_defect_iff_integer_shift_at_least_minimal


/-! ## Complete weight invariance and positivity detection

Strictly positive weights alter the numerical size of defect but not
its ZERO LOCUS or the presence of signed non-effective channels.
This makes the GST integer effective cone intrinsic to the channels,
not to an arbitrarily chosen positive detector. -/

/-- The zero-calibration locus is independent of which strictly
positive rational-integer channel weights are chosen. -/
theorem all_N_zero_defect_independent_of_positive_weights
    (s : NShape) (w v a : IntegerChannels s)
    (hw : ∀ i, 1 ≤ w i) (hv : ∀ i, 1 ≤ v i) :
    calibrationDefect s w a = 0 ↔ calibrationDefect s v a = 0 := by
  rw [defect_zero_iff_all_coordinates_nonnegative s w a hw,
      defect_zero_iff_all_coordinates_nonnegative s v a hv]

/-- The exact support obstruction: positive weights produce
strict defect precisely when at least one integer channel has
negative multiplicity. Valid in ALL finite N-shapes. -/
theorem all_N_positive_defect_iff_negative_channel
    (s : NShape) (w a : IntegerChannels s)
    (hw : ∀ i, 1 ≤ w i) :
    0 < calibrationDefect s w a ↔
      ∃ i : Fin s.holes, a i < 0 := by
  have hnonneg : 0 ≤ calibrationDefect s w a :=
    defect_nonnegative s w a (fun i => by have h := hw i; omega)
  constructor
  · intro hpositive
    by_contra hn
    have hall : ∀ i : Fin s.holes, 0 ≤ a i := by
      intro i
      by_contra hi
      exact hn ⟨i, by omega⟩
    have hz :=
      (defect_zero_iff_all_coordinates_nonnegative s w a hw).2 hall
    omega
  · rintro ⟨i, hi⟩
    have hnotzero : calibrationDefect s w a ≠ 0 := by
      intro hz
      have hall :=
        (defect_zero_iff_all_coordinates_nonnegative s w a hw).1 hz
      have hcoord := hall i
      omega
    omega

#check all_N_zero_defect_independent_of_positive_weights
#check all_N_positive_defect_iff_negative_channel
#print axioms all_N_positive_defect_iff_negative_channel


/-! ## Arbitrary-rank integral scaling law for the exact GST defect

Unlike a merely sufficient positivity estimate, this is an EXACT
homogeneity identity for every N-shape and every signed integer
channel vector. It rules out eliminating a nonzero lattice defect by
clearing denominators or multiplying every existing channel by a
nonzero positive integer. It does not equate formal integer channels
with actual projective algebraic cycles.
-/

/-- Positive integer rescaling preserves the full value of the
N-cohomology absolute calibration defect up to the same factor. -/
theorem all_N_calibration_defect_integer_homogeneity
    (s : NShape) (w a : IntegerChannels s) (k : ℕ) :
    calibrationDefect s w (fun i => (k : ℤ) * a i) =
      (k : ℤ) * calibrationDefect s w a := by
  simp only [defect_as_weighted_negative_part, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hk : 0 ≤ (k : ℤ) := by omega
  rw [abs_mul, abs_of_nonneg hk]
  ring

/-- A nonzero positive integral change of multiplicity cannot
turn an uncalibrated N-channel packet into a calibrated one. -/
theorem all_N_calibration_zero_iff_positive_integer_scaling
    (s : NShape) (w a : IntegerChannels s)
    (k : ℕ) (hk : 0 < k) :
    calibrationDefect s w (fun i => (k : ℤ) * a i) = 0 ↔
      calibrationDefect s w a = 0 := by
  rw [all_N_calibration_defect_integer_homogeneity]
  have hk0 : (k : ℤ) ≠ 0 := by omega
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hk0
  · intro h
    rw [h]
    ring

#check all_N_calibration_defect_integer_homogeneity
#check all_N_calibration_zero_iff_positive_integer_scaling
#print axioms all_N_calibration_zero_iff_positive_integer_scaling

end GSTNAllChannelAmpleSaturation
