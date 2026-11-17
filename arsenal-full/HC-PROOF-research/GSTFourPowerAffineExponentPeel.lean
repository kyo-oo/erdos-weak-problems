import GSTFourPowerAffineOrbit

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineExponentPeel

open GSTFourPowerDirectResidue
open GSTFourPowerAffineOrbit

/-- Tail polynomial when the next ternary exponent trit is `0`. -/
def peel0 (x : Nat) : Nat := x + 3*x^2 + 3*x^3

/-- Tail polynomial when the next ternary exponent trit is `1`. -/
def peel1 (x : Nat) : Nat := 4*x + 12*x^2 + 12*x^3

/-- Tail polynomial when the next ternary exponent trit is `2`. -/
def peel2 (x : Nat) : Nat := 1 + 16*x + 48*x^2 + 48*x^3

/-- Exact exponent-trit peel for the `0` branch. -/
theorem affineOrbit_three_mul (q : Nat) :
    affineOrbit (3*q) = 3 * peel0 (affineOrbit q) := by
  let x := affineOrbit q
  have h :
      1 + 3 * affineOrbit (3*q) = (1 + 3*x)^3 := by
    calc
      1 + 3 * affineOrbit (3*q) = 4^(3*q) :=
        (four_pow_eq_one_plus_three_affineOrbit (3*q)).symm
      _ = (4^q)^3 := by
        rw [show 3*q = q*3 by omega, pow_mul]
      _ = (1 + 3*x)^3 := by
        rw [four_pow_eq_one_plus_three_affineOrbit q]
  dsimp [peel0, x] at h ⊢
  nlinarith [h]

/-- Exact exponent-trit peel for the `1` branch. -/
theorem affineOrbit_three_mul_add_one (q : Nat) :
    affineOrbit (3*q + 1) = 1 + 3 * peel1 (affineOrbit q) := by
  rw [show 3*q + 1 = (3*q) + 1 by omega, affineOrbit_succ,
    affineOrbit_three_mul]
  unfold peel0 peel1
  ring

/-- Exact exponent-trit peel for the `2` branch. -/
theorem affineOrbit_three_mul_add_two (q : Nat) :
    affineOrbit (3*q + 2) = 2 + 3 * peel2 (affineOrbit q) := by
  rw [show 3*q + 2 = (3*q + 1) + 1 by omega, affineOrbit_succ,
    affineOrbit_three_mul_add_one]
  unfold peel1 peel2
  ring

/-- After consuming exponent trit `0`, all higher affine-orbit digits are the
    digits of the exact polynomial tail `peel0`. -/
theorem digit_peel_zero (q j : Nat) :
    digit3 (affineOrbit (3*q)) (j+1) =
      digit3 (peel0 (affineOrbit q)) j := by
  rw [affineOrbit_three_mul]
  have h := GSTCanonicalTailStateIso.prefix_slice_digit_exact
    1 0 (peel0 (affineOrbit q)) j (by norm_num : 0 < 3^1)
  simpa [GSTCanonicalTailStateIso.digit3, GSTFourPowerDirectResidue.digit3,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- After consuming exponent trit `1`, all higher affine-orbit digits are the
    digits of the exact polynomial tail `peel1`. -/
theorem digit_peel_one (q j : Nat) :
    digit3 (affineOrbit (3*q + 1)) (j+1) =
      digit3 (peel1 (affineOrbit q)) j := by
  rw [affineOrbit_three_mul_add_one]
  have h := GSTCanonicalTailStateIso.prefix_slice_digit_exact
    1 1 (peel1 (affineOrbit q)) j (by norm_num : 1 < 3^1)
  simpa [GSTCanonicalTailStateIso.digit3, GSTFourPowerDirectResidue.digit3,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- After consuming exponent trit `2`, all higher affine-orbit digits are the
    digits of the exact polynomial tail `peel2`. -/
theorem digit_peel_two (q j : Nat) :
    digit3 (affineOrbit (3*q + 2)) (j+1) =
      digit3 (peel2 (affineOrbit q)) j := by
  rw [affineOrbit_three_mul_add_two]
  have h := GSTCanonicalTailStateIso.prefix_slice_digit_exact
    1 2 (peel2 (affineOrbit q)) j (by norm_num : 2 < 3^1)
  simpa [GSTCanonicalTailStateIso.digit3, GSTFourPowerDirectResidue.digit3,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- The least ternary digit of the affine orbit literally records exponent trit `0`. -/
theorem affineOrbit_low_trit_zero (q : Nat) :
    digit3 (affineOrbit (3*q)) 0 = 0 := by
  rw [affineOrbit_three_mul]
  simp [GSTFourPowerDirectResidue.digit3]

/-- The least ternary digit of the affine orbit literally records exponent trit `1`. -/
theorem affineOrbit_low_trit_one (q : Nat) :
    digit3 (affineOrbit (3*q+1)) 0 = 1 := by
  rw [affineOrbit_three_mul_add_one]
  simp [GSTFourPowerDirectResidue.digit3]

/-- The least ternary digit of the affine orbit literally records exponent trit `2`. -/
theorem affineOrbit_low_trit_two (q : Nat) :
    digit3 (affineOrbit (3*q+2)) 0 = 2 := by
  rw [affineOrbit_three_mul_add_two]
  simp [GSTFourPowerDirectResidue.digit3]

/-- The three tail polynomials form two consecutive affine steps after the common cubic core. -/
theorem peel1_eq_four_peel0 (x : Nat) : peel1 x = 4 * peel0 x := by
  unfold peel0 peel1
  ring

/-- The `2` tail is the next affine iterate after the `1` tail. -/
theorem peel2_eq_four_peel1_add_one (x : Nat) :
    peel2 x = 4 * peel1 x + 1 := by
  unfold peel1 peel2
  ring

/-- Closing identity needed by the `r = 2` exponent branch. -/
theorem peel0_affine_succ (x : Nat) :
    peel0 (4*x + 1) = 4 * peel2 x + 3 := by
  unfold peel0 peel2
  ring


/-! ## Exact exponent/affine trit conjugacy -/

/-- **LOW-TRIT CONJUGACY.**  The least ternary digit of the affine orbit is
not merely classified on three named branches: it is exactly the least
ternary digit of the exponent itself.  Thus the exponent shift and affine
state are synchronized at the first ternary coordinate for every `K`. -/
theorem affineOrbit_low_trit_exact (K : Nat) :
    digit3 (affineOrbit K) 0 = K % 3 := by
  have hlt : K % 3 < 3 := Nat.mod_lt K (by decide)
  have hsplit := Nat.mod_add_div K 3
  have hcases : K % 3 = 0 ∨ K % 3 = 1 ∨ K % 3 = 2 := by
    omega
  rcases hcases with h0 | h1 | h2
  · have hK : K = 3 * (K / 3) := by omega
    calc
      digit3 (affineOrbit K) 0 =
          digit3 (affineOrbit (3 * (K / 3))) 0 :=
        congrArg (fun e : Nat => digit3 (affineOrbit e) 0) hK
      _ = 0 := affineOrbit_low_trit_zero (K / 3)
      _ = K % 3 := h0.symm
  · have hK : K = 3 * (K / 3) + 1 := by omega
    calc
      digit3 (affineOrbit K) 0 =
          digit3 (affineOrbit (3 * (K / 3) + 1)) 0 :=
        congrArg (fun e : Nat => digit3 (affineOrbit e) 0) hK
      _ = 1 := affineOrbit_low_trit_one (K / 3)
      _ = K % 3 := h1.symm
  · have hK : K = 3 * (K / 3) + 2 := by omega
    calc
      digit3 (affineOrbit K) 0 =
          digit3 (affineOrbit (3 * (K / 3) + 2)) 0 :=
        congrArg (fun e : Nat => digit3 (affineOrbit e) 0) hK
      _ = 2 := affineOrbit_low_trit_two (K / 3)
      _ = K % 3 := h2.symm

/-- Equality tests on the first affine-orbit trit are literally equality
tests on the exponent trit.  This is the branch-free classifier interface. -/
theorem affineOrbit_low_trit_eq_iff (K r : Nat) :
    digit3 (affineOrbit K) 0 = r ↔ K % 3 = r := by
  rw [affineOrbit_low_trit_exact]

/-- The three explicit peel branches are exhaustive for every exponent. -/
theorem affineOrbit_exponent_trichotomy (K : Nat) :
    (K % 3 = 0 ∧ digit3 (affineOrbit K) 0 = 0) ∨
    (K % 3 = 1 ∧ digit3 (affineOrbit K) 0 = 1) ∨
    (K % 3 = 2 ∧ digit3 (affineOrbit K) 0 = 2) := by
  have hlt : K % 3 < 3 := Nat.mod_lt K (by decide)
  have hcases : K % 3 = 0 ∨ K % 3 = 1 ∨ K % 3 = 2 := by
    omega
  rcases hcases with h0 | h1 | h2
  · exact Or.inl ⟨h0, by simpa [affineOrbit_low_trit_exact, h0]⟩
  · exact Or.inr (Or.inl ⟨h1, by simpa [affineOrbit_low_trit_exact, h1]⟩)
  · exact Or.inr (Or.inr ⟨h2, by simpa [affineOrbit_low_trit_exact, h2]⟩)

#check affineOrbit_low_trit_exact
#check affineOrbit_low_trit_eq_iff
#check affineOrbit_exponent_trichotomy
#print axioms affineOrbit_low_trit_exact

end GSTFourPowerAffineExponentPeel
