import GSTFourPowerDirectResidue

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerDirectAdditionCarry

open GSTFourPowerDirectResidue

/-- Exact multiplication-by-four carry below ternary row `p`. -/
def directCarry4 (R p : Nat) : Nat :=
  (4 * (R % 3^p)) / 3^p

/-- For positive rows, the four-valued multiplication carry splits into the
previous source ternary digit plus a single binary addition-carry bit. -/
def binaryCarry (R p : Nat) : Nat :=
  directCarry4 R p - digit3 R (p-1)

/-- Every ternary digit is in `{0,1,2}`. -/
theorem digit3_lt_three (R p : Nat) : digit3 R p < 3 := by
  unfold digit3
  exact Nat.mod_lt _ (by decide)

/-- Multiplication by four has carry strictly below four at every row. -/
theorem directCarry4_lt_four (R p : Nat) : directCarry4 R p < 4 := by
  unfold directCarry4
  have hM : 0 < (3^p : Nat) := by positivity
  have hr : R % 3^p < 3^p := Nat.mod_lt _ hM
  apply (Nat.div_lt_iff_lt_mul hM).2
  nlinarith

/-- Exact ternary carry recurrence for multiplication by four. -/
theorem directCarry4_forward_exact_all (R p : Nat) :
    directCarry4 R (p+1) =
      (directCarry4 R p + 4 * digit3 R p) / 3 := by
  simp only [directCarry4, digit3, Nat.pow_succ]
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  have hsplit :
      R % (3^p * 3) = R % 3^p + 3^p * (R / 3^p % 3) := by
    rw [Nat.mod_mul]
  rw [hsplit, Nat.mul_add]
  rw [show 4 * (3^p * (R / 3^p % 3)) =
      3^p * (4 * (R / 3^p % 3)) by ac_rfl]
  rw [← Nat.div_div_eq_div_mul]
  rw [Nat.add_mul_div_left _ _ hp]

/-- One recurrence step lies between the current digit and one above it. -/
theorem carry_step_between_digit_and_succ
    (c d : Nat) (hc : c < 4) (hd : d < 3) :
    d ≤ (c + 4*d) / 3 ∧ (c + 4*d) / 3 ≤ d+1 := by
  interval_cases c <;> interval_cases d <;> norm_num

/-- At every positive row the four-valued carry is exactly the previous
ternary digit plus the binary carry bit. -/
theorem directCarry4_eq_prev_digit_add_binary
    (R p : Nat) (hp : 1 ≤ p) :
    directCarry4 R p = digit3 R (p-1) + binaryCarry R p := by
  have hshape : (p-1)+1 = p := by omega
  have hrec := directCarry4_forward_exact_all R (p-1)
  rw [hshape] at hrec
  have hb := carry_step_between_digit_and_succ
    (directCarry4 R (p-1)) (digit3 R (p-1))
    (directCarry4_lt_four R (p-1)) (digit3_lt_three R (p-1))
  rw [← hrec] at hb
  unfold binaryCarry
  omega

/-- The residual addition carry is genuinely binary. -/
theorem binaryCarry_lt_two
    (R p : Nat) (hp : 1 ≤ p) : binaryCarry R p < 2 := by
  have hshape : (p-1)+1 = p := by omega
  have hrec := directCarry4_forward_exact_all R (p-1)
  rw [hshape] at hrec
  have hb := carry_step_between_digit_and_succ
    (directCarry4 R (p-1)) (digit3 R (p-1))
    (directCarry4_lt_four R (p-1)) (digit3_lt_three R (p-1))
  rw [← hrec] at hb
  unfold binaryCarry
  omega

/-- Exact quotient decomposition behind `4R = R + 3R`. -/
theorem four_mul_div_decomposition (R p : Nat) :
    (4*R) / 3^p = directCarry4 R p + 4 * (R / 3^p) := by
  unfold directCarry4
  have hM : 0 < 3^p := Nat.pow_pos (by decide)
  have hdiv : R = 3^p * (R / 3^p) + R % 3^p :=
    (Nat.div_add_mod R (3^p)).symm
  have hmul :
      4 * R = 4 * (3^p * (R / 3^p) + R % 3^p) :=
    congrArg (fun x : Nat => 4 * x) hdiv
  rw [hmul, Nat.mul_add]
  rw [show 4 * (3^p * (R / 3^p)) + 4 * (R % 3^p) =
      4 * (R % 3^p) + 3^p * (4 * (R / 3^p)) by ac_rfl]
  rw [Nat.add_mul_div_left _ _ hM]

/-- The target ternary digit is source digit plus multiplication carry mod 3. -/
theorem digit3_four_mul (R p : Nat) :
    digit3 (4*R) p = (digit3 R p + directCarry4 R p) % 3 := by
  unfold digit3
  rw [four_mul_div_decomposition]
  simp [Nat.add_mod, Nat.mul_mod, Nat.add_comm]

/-- Positive-row target digit in the binary-carry normal form. -/
theorem digit3_four_mul_binary
    (R p : Nat) (hp : 1 ≤ p) :
    digit3 (4*R) p =
      (digit3 R p + digit3 R (p-1) + binaryCarry R p) % 3 := by
  rw [digit3_four_mul]
  rw [directCarry4_eq_prev_digit_add_binary R p hp]
  simp [Nat.add_assoc]

/-- Finite arithmetic classifier for the two source states that turn a current
source digit `2` into a target digit `2`. -/
theorem two_shift_eq_two_iff_forbidden_edges
    (prev bit : Nat) (hprev : prev < 3) (hbit : bit < 2) :
    (2 + prev + bit) % 3 = 2 ↔
      ((prev = 0 ∧ bit = 0) ∨ (prev = 2 ∧ bit = 1)) := by
  interval_cases prev <;> interval_cases bit <;> norm_num

/-- Exact common-two classifier at a positive row.  A common digit `2` occurs
iff the binary automaton takes one of exactly two forbidden edges. -/
theorem common_two_row_iff_forbidden_edges
    (R p : Nat) (hp : 1 ≤ p) :
    (digit3 R p = 2 ∧ digit3 (4*R) p = 2) ↔
      (digit3 R p = 2 ∧
        ((digit3 R (p-1) = 0 ∧ binaryCarry R p = 0) ∨
         (digit3 R (p-1) = 2 ∧ binaryCarry R p = 1))) := by
  have hprev := digit3_lt_three R (p-1)
  have hbit := binaryCarry_lt_two R p hp
  constructor
  · intro h
    have hformula := digit3_four_mul_binary R p hp
    rw [h.1] at hformula
    have ht :
        (2 + digit3 R (p-1) + binaryCarry R p) % 3 = 2 :=
      hformula.symm.trans h.2
    exact ⟨h.1,
      (two_shift_eq_two_iff_forbidden_edges
        (digit3 R (p-1)) (binaryCarry R p) hprev hbit).1 ht⟩
  · rintro ⟨hs, hedge⟩
    refine ⟨hs, ?_⟩
    rw [digit3_four_mul_binary R p hp, hs]
    exact (two_shift_eq_two_iff_forbidden_edges
      (digit3 R (p-1)) (binaryCarry R p) hprev hbit).2 hedge

/-- Arithmetic identity for updating the residual binary carry. -/
theorem binary_step_arithmetic
    (d prev bit : Nat)
    (hd : d < 3) (hprev : prev < 3) (hbit : bit < 2) :
    (prev + bit + 4*d) / 3 - d = (d + prev + bit) / 3 := by
  interval_cases d <;> interval_cases prev <;> interval_cases bit <;> norm_num

/-- The binary carry evolves by a two-state deterministic automaton. -/
theorem binaryCarry_forward_exact
    (R p : Nat) (hp : 1 ≤ p) :
    binaryCarry R (p+1) =
      (digit3 R p + digit3 R (p-1) + binaryCarry R p) / 3 := by
  change directCarry4 R (p+1) - digit3 R (p+1-1) =
    (digit3 R p + digit3 R (p-1) + binaryCarry R p) / 3
  rw [show p+1-1 = p by omega]
  rw [directCarry4_forward_exact_all]
  rw [directCarry4_eq_prev_digit_add_binary R p hp]
  exact binary_step_arithmetic
    (digit3 R p) (digit3 R (p-1)) (binaryCarry R p)
    (digit3_lt_three R p) (digit3_lt_three R (p-1))
    (binaryCarry_lt_two R p hp)

/-- Powers of four start the positive-row automaton in state `(1,0)`. -/
theorem pow4_binary_initial_state (K : Nat) :
    digit3 (4^K) 0 = 1 ∧ binaryCarry (4^K) 1 = 0 := by
  have hmod := pow4_mod3_one K
  constructor
  · simpa [digit3] using hmod
  · unfold binaryCarry directCarry4 digit3
    simp [hmod]

#check directCarry4
#check binaryCarry
#check directCarry4_forward_exact_all
#check directCarry4_eq_prev_digit_add_binary
#check binaryCarry_lt_two
#check digit3_four_mul_binary
#check common_two_row_iff_forbidden_edges
#check binaryCarry_forward_exact
#check pow4_binary_initial_state
#print axioms directCarry4_forward_exact_all
#print axioms directCarry4_eq_prev_digit_add_binary
#print axioms binaryCarry_lt_two
#print axioms digit3_four_mul_binary
#print axioms common_two_row_iff_forbidden_edges
#print axioms binaryCarry_forward_exact
#print axioms pow4_binary_initial_state

end GSTFourPowerDirectAdditionCarry
