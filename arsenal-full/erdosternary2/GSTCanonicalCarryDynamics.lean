import GSTCanonicalTailStateIso

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTCanonicalCarryDynamics

open GSTCanonicalTailStateIso

/-- Every physical x4 carry is strictly below four once the ternary modulus is positive. -/
theorem carry4_lt_four (R p : Nat) : carry4 R p < 4 := by
  unfold carry4
  have hM : 0 < 3^p := Nat.pow_pos (by decide)
  have hr : R % 3^p < 3^p := Nat.mod_lt _ hM
  exact (Nat.div_lt_iff_lt_mul hM).2 (by nlinarith)

/-- Exact one-column x4/base-3 carry regeneration law. -/
theorem carry4_forward_exact (R p : Nat) :
    carry4 R (p+1) = (carry4 R p + 4 * digit3 R p) / 3 := by
  unfold carry4 digit3
  rw [Nat.pow_succ]
  rw [Nat.mod_mul]
  rw [← Nat.div_div_eq_div_mul]
  have hM : 0 < 3^p := Nat.pow_pos (by decide)
  have hshape :
      4 * (R % 3^p + 3^p * (R / 3^p % 3)) =
        4 * (R % 3^p) + 3^p * (4 * (R / 3^p % 3)) := by
    ring
  rw [hshape, Nat.add_mul_div_left _ _ hM]

end GSTCanonicalCarryDynamics
