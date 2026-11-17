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

/-- Emitted ternary residue of one canonical x4 carry transition. -/
def carry4Emit (R p : Nat) : Nat :=
  (carry4 R p + 4*digit3 R p) % 3

/-- **EXACT CARRY STATE DECOMPOSITION.**
One physical transition is completely reconstructed from the next carry and
its emitted ternary residue. -/
theorem carry4_state_decomposition
    (R p : Nat) :
    carry4 R p + 4*digit3 R p =
      3*carry4 R (p+1) + carry4Emit R p := by
  unfold carry4Emit
  rw [carry4_forward_exact]
  simpa [Nat.add_comm] using
    (Nat.mod_add_div (carry4 R p + 4*digit3 R p) 3).symm

/-- The emitted transition residue is always a genuine ternary digit. -/
theorem carry4Emit_lt_three
    (R p : Nat) :
    carry4Emit R p < 3 := by
  unfold carry4Emit
  exact Nat.mod_lt _ (by decide)

/-- The pair (next carry, emitted trit) uniquely encodes the transition
numerator. -/
theorem carry4_transition_packet
    (R p : Nat) :
    (carry4 R (p+1), carry4Emit R p) =
      ((carry4 R p + 4*digit3 R p) / 3,
       (carry4 R p + 4*digit3 R p) % 3) := by
  rw [carry4_forward_exact]
  rfl

#check carry4Emit
#check carry4_state_decomposition
#check carry4Emit_lt_three
#check carry4_transition_packet
#print axioms carry4_state_decomposition
#print axioms carry4_transition_packet

end GSTCanonicalCarryDynamics
