import GSTNIntegralCalibrationGap

/-!
# Mathbox: Ample shifts can heal N-channel integrality gaps

Original all-X goal is the existence of integral fixed-homology
almost-calibrated currents for arbitrary rational Hodge classes.

An earlier two-channel test proved the UNshifted integer period 1
has integral calibration defect at least 4, despite a rational
nonnegative solution. This is NOT a proof of obstruction after
adding a sufficiently ample class. We correct that analysis by
constructing an explicit integer calibrated representative after
a POSITIVE interior shift.

Two integral positive generators have periods 2,3; their interior
ample class 12 = 2*3 + 3*2. For arbitrary integer n, choose
a(n)=-n+3*|n|, b(n)=n+2*|n|.
Both are nonnegative, with period n+12*|n| and defect zero.
Therefore a constant closed integral sequence is available
for every shifted class in THIS finite N-channel toy geometry.

This is an honest finite lattice/calibration result, not
a claimed all-X Chow cycle or proof of the Hodge conjecture.
For actual X a proof requires independently geometric generators
whose rational Hodge classes span the target, which is precisely
the missing, nontrivial geometric realization.
-/

set_option maxHeartbeats 4000000

namespace GSTNAmpleShiftIntegralRealization

open GSTNIntegralCalibrationGap

/-- Explicit integral coordinates after a sufficiently ample shift. -/
def ampleA (n : ℤ) : ℤ := -n + 3 * |n|
def ampleB (n : ℤ) : ℤ := n + 2 * |n|

theorem ampleA_nonnegative (n : ℤ) : 0 ≤ ampleA n := by
  unfold ampleA
  rcases le_total 0 n with hn | hn
  · rw [abs_of_nonneg hn]
    omega
  · rw [abs_of_nonpos hn]
    omega

theorem ampleB_nonnegative (n : ℤ) : 0 ≤ ampleB n := by
  unfold ampleB
  rcases le_total 0 n with hn | hn
  · rw [abs_of_nonneg hn]
    omega
  · rw [abs_of_nonpos hn]
    omega

/-- The integral combination has exactly the original integer class
plus an explicit positive ample-class multiple. -/
theorem amplePeriod (n : ℤ) :
    period (ampleA n) (ampleB n) = n + 12 * |n| := by
  unfold period ampleA ampleB
  ring

/-- The constructed current coefficients are integer and nonnegative,
so their nonlinear absolute mass equals their fixed homology period. -/
theorem ampleDefect_zero (n : ℤ) :
    defect (ampleA n) (ampleB n) = 0 := by
  unfold defect mass
  rw [abs_of_nonneg (ampleA_nonnegative n),
      abs_of_nonneg (ampleB_nonnegative n)]
  unfold period
  ring

/-- A genuine integer fixed-class zero-calibration-defect sequence in
the finite N-channel model, with NO irrational or rational-weight
multiplicities. This does not create integral currents on arbitrary X. -/
def ampleSequence (n : ℤ) : ℕ → ℤ × ℤ :=
  fun _ => (ampleA n, ampleB n)

theorem integral_fixed_class_calibrated_sequence_in_model (n : ℤ) :
    (∀ k : ℕ,
      period (ampleSequence n k).1 (ampleSequence n k).2 =
        n + 12 * |n|) ∧
    (∀ k : ℕ,
      defect (ampleSequence n k).1 (ampleSequence n k).2 = 0) := by
  constructor
  · intro k
    exact amplePeriod n
  · intro k
    exact ampleDefect_zero n

/-- The prior period-one gap disappears after a single interior shift:
period 13 = 2*5+3*1, all integer and fully calibrated. -/
theorem concrete_period_one_shift :
    period 5 1 = 13 ∧ defect 5 1 = 0 := by
  constructor <;> norm_num [period, defect, mass]

#check ampleA_nonnegative
#check ampleB_nonnegative
#check amplePeriod
#check ampleDefect_zero
#check integral_fixed_class_calibrated_sequence_in_model
#print axioms integral_fixed_class_calibrated_sequence_in_model

end GSTNAmpleShiftIntegralRealization
