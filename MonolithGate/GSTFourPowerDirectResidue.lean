import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerDirectResidue

/-- Pure ternary digit, deliberately independent of every Graph-V2 module. -/
def digit3 (R p : Nat) : Nat := R / 3^p % 3

/-- Exact quotient in `4^(3^r) = 1 + 3^(r+1) * lteCoeff r`.
Kept here so the direct proof spine has no dependency on the Graph-V2
exponential/relocation tower. -/
def lteCoeff : Nat → Nat
  | 0 => 1
  | r+1 =>
      let c := lteCoeff r
      c + 3^(r+1) * c^2 + 3^(2*r+1) * c^3

/-- Exact power-of-four LTE identity at every ternary scale. -/
theorem pow4_three_power_lte_exact : ∀ r : Nat,
    4^(3^r) = 1 + 3^(r+1) * lteCoeff r
  | 0 => by norm_num [lteCoeff]
  | r+1 => by
      have ih := pow4_three_power_lte_exact r
      calc
        4^(3^(r+1)) = (4^(3^r))^3 := by
          rw [Nat.pow_succ, Nat.pow_mul]
        _ = (1 + 3^(r+1) * lteCoeff r)^3 := by rw [ih]
        _ = 1 + 3^((r+1)+1) * lteCoeff (r+1) := by
          simp only [lteCoeff]
          rw [show (r+1)+1 = r+2 by omega]
          have h1 : 3^(r+1) = 3^r * 3 := by
            rw [Nat.pow_succ]
          have h2 : 3^(2*r+1) = (3^r)^2 * 3 := by
            calc
              3^(2*r+1) = 3^((r+r)+1) := by congr 1 <;> omega
              _ = 3^(r+r) * 3 := by rw [Nat.pow_succ]
              _ = (3^r * 3^r) * 3 := by rw [Nat.pow_add]
              _ = (3^r)^2 * 3 := by ring
          have h3 : 3^(r+2) = 3^r * 9 := by
            calc
              3^(r+2) = 3^((r+1)+1) := by congr 1 <;> omega
              _ = 3^(r+1) * 3 := by rw [Nat.pow_succ]
              _ = 3^r * 9 := by rw [h1]; ring
          rw [h3, h1, h2]
          ring

/-- The exact LTE quotient is always one modulo three. -/
theorem lteCoeff_mod3_one : ∀ r : Nat, lteCoeff r % 3 = 1
  | 0 => by decide
  | r+1 => by
      have ih := lteCoeff_mod3_one r
      simp only [lteCoeff]
      have hpow1 : 3^(r+1) % 3 = 0 := by
        rw [Nat.pow_succ]
        simp
      have hpow2 : 3^(2*r+1) % 3 = 0 := by
        rw [Nat.pow_succ]
        simp
      simp [Nat.add_mod, Nat.mul_mod, hpow1, hpow2, ih]

/-- Any multiple of the scale exponent is one modulo the next ternary cut. -/
theorem pow4_scaled_mod_next (r u : Nat) :
    4^(3^r * u) % 3^(r+1) = 1 := by
  have hA := pow4_three_power_lte_exact r
  rw [Nat.pow_mul, hA, Nat.pow_mod]
  have hMgt1 : 1 < 3^(r+1) := by
    have h3 : 3^1 ≤ 3^(r+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    norm_num at h3 ⊢
  have hbase : (1 + 3^(r+1) * lteCoeff r) % 3^(r+1) = 1 := by
    simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hMgt1]
  simpa [hbase, Nat.mod_eq_of_lt hMgt1]

/-- A ternary digit at row `p` is determined by the residue modulo `3^(p+1)`. -/
theorem digit3_eq_of_mod_next
    (R S p : Nat)
    (hmod : R % 3^(p+1) = S % 3^(p+1)) :
    digit3 R p = digit3 S p := by
  unfold digit3
  have hpow : 3^(p+1) = 3^p * 3 := by
    rw [Nat.pow_succ]
  have hfull : R % (3^p * 3) = S % (3^p * 3) := by
    simpa [hpow] using hmod
  have hR : R % (3^p * 3) =
      R % 3^p + 3^p * (R / 3^p % 3) := by
    rw [Nat.mod_mul]
  have hS : S % (3^p * 3) =
      S % 3^p + 3^p * (S / 3^p % 3) := by
    rw [Nat.mod_mul]
  have hdvd : 3^p ∣ 3^(p+1) := Nat.pow_dvd_pow 3 (by omega)
  have hRlow := Nat.mod_mod_of_dvd R hdvd
  have hSlow := Nat.mod_mod_of_dvd S hdvd
  have hlow : R % 3^p = S % 3^p := by
    calc
      R % 3^p = (R % 3^(p+1)) % 3^p := hRlow.symm
      _ = (S % 3^(p+1)) % 3^p := by rw [hmod]
      _ = S % 3^p := hSlow
  rw [hR, hS, hlow] at hfull
  have hmul : 3^p * (R / 3^p % 3) =
      3^p * (S / 3^p % 3) := by omega
  exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 3^p) hmul

/-- Row `p` of `4^K` is periodic in `K` with exponent period `3^p`. -/
theorem pow4_digit_period
    (p K u : Nat) :
    digit3 (4^(K + 3^p*u)) p = digit3 (4^K) p := by
  apply digit3_eq_of_mod_next
  rw [Nat.pow_add, Nat.mul_mod]
  rw [pow4_scaled_mod_next p u]
  simp

/-- Every power of four is one modulo three. -/
theorem pow4_mod3_one (m : Nat) : 4^m % 3 = 1 := by
  rw [Nat.pow_mod]
  norm_num

/-- Adding one exponent trit at scale `3^p` shifts row `p+1` by one modulo 3. -/
theorem pow4_exponent_lift_one_digit
    (p m c : Nat)
    (hA : 4^(3^p) = 1 + 3^(p+1)*c)
    (hc : c % 3 = 1) :
    digit3 (4^(m + 3^p)) (p+1) =
      (digit3 (4^m) (p+1) + 1) % 3 := by
  let L := 3^(p+1)
  have hL : 0 < L := by
    dsimp [L]
    exact Nat.pow_pos (by decide)
  have hpow : 4^(m + 3^p) = 4^m * (1 + L*c) := by
    rw [Nat.pow_add, hA]
  have hshape : 4^m * (1 + L*c) = 4^m + L * (4^m*c) := by ring
  unfold digit3
  rw [show 3^(p+1) = L by rfl, hpow, hshape]
  rw [Nat.add_mul_div_left _ _ hL]
  rw [Nat.add_mod, Nat.mul_mod, pow4_mod3_one, hc]

/-- Adding exponent trit two shifts row `p+1` by two modulo 3. -/
theorem pow4_exponent_lift_two_digit
    (p m c : Nat)
    (hA : 4^(3^p) = 1 + 3^(p+1)*c)
    (hc : c % 3 = 1) :
    digit3 (4^(m + 2*3^p)) (p+1) =
      (digit3 (4^m) (p+1) + 2) % 3 := by
  have h1 := pow4_exponent_lift_one_digit p m c hA hc
  have h2 := pow4_exponent_lift_one_digit p (m + 3^p) c hA hc
  have hexp : m + 2*3^p = (m + 3^p) + 3^p := by omega
  rw [hexp]
  rw [h2, h1]
  have hd : digit3 (4^m) (p+1) < 3 := by
    unfold digit3
    exact Nat.mod_lt _ (by decide)
  omega

/-- Canonical ternary-exponent digit lift. -/
theorem pow4_exponent_trit_lift_digit
    (p m a : Nat)
    (ha : a < 3) :
    digit3 (4^(m + a*3^p)) (p+1) =
      (digit3 (4^m) (p+1) + a) % 3 := by
  have hA := pow4_three_power_lte_exact p
  have hc := lteCoeff_mod3_one p
  have haCases : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases haCases with h0 | h1 | h2
  · subst a
    simp only [Nat.zero_mul, Nat.add_zero]
    have hd : digit3 (4^m) (p+1) < 3 := by
      unfold digit3
      exact Nat.mod_lt _ (by decide)
    omega
  · subst a
    simpa using pow4_exponent_lift_one_digit p m (lteCoeff p) hA hc
  · subst a
    simpa using pow4_exponent_lift_two_digit p m (lteCoeff p) hA hc

/-- Exponent residues five and six modulo nine have a shared row-two digit 2. -/
theorem row_two_overlap_of_mod9_five_or_six
    (L : Nat) (hres : L % 9 = 5 ∨ L % 9 = 6) :
    digit3 (4^L) 2 = 2 ∧ digit3 (4^(L+1)) 2 = 2 := by
  rcases hres with h5 | h6
  · have hs := Nat.mod_add_div L 9
    rw [h5] at hs
    have hshape : L = 5 + 9 * (L / 9) := by
      simpa [Nat.add_comm, Nat.mul_comm] using hs.symm
    have hshape1 : L+1 = 6 + 9 * (L / 9) := by omega
    constructor
    · rw [hshape]
      calc
        digit3 (4 ^ (5 + 9 * (L / 9))) 2 = digit3 (4^5) 2 :=
          pow4_digit_period 2 5 (L/9)
        _ = 2 := by norm_num [digit3]
    · rw [hshape1]
      calc
        digit3 (4 ^ (6 + 9 * (L / 9))) 2 = digit3 (4^6) 2 :=
          pow4_digit_period 2 6 (L/9)
        _ = 2 := by norm_num [digit3]
  · have hs := Nat.mod_add_div L 9
    rw [h6] at hs
    have hshape : L = 6 + 9 * (L / 9) := by
      simpa [Nat.add_comm, Nat.mul_comm] using hs.symm
    have hshape1 : L+1 = 7 + 9 * (L / 9) := by omega
    constructor
    · rw [hshape]
      calc
        digit3 (4 ^ (6 + 9 * (L / 9))) 2 = digit3 (4^6) 2 :=
          pow4_digit_period 2 6 (L/9)
        _ = 2 := by norm_num [digit3]
    · rw [hshape1]
      calc
        digit3 (4 ^ (7 + 9 * (L / 9))) 2 = digit3 (4^7) 2 :=
          pow4_digit_period 2 7 (L/9)
        _ = 2 := by norm_num [digit3]

/-- Exact row-two residue classification. -/
theorem row_two_overlap_iff_mod9_five_or_six
    (L : Nat) :
    (digit3 (4^L) 2 = 2 ∧ digit3 (4^(L+1)) 2 = 2) ↔
      (L % 9 = 5 ∨ L % 9 = 6) := by
  constructor
  · intro hov
    let r := L % 9
    have hr : r < 9 := by
      dsimp [r]
      exact Nat.mod_lt _ (by norm_num)
    have hs := Nat.mod_add_div L 9
    have hshape : L = r + 9 * (L / 9) := by
      dsimp [r]
      omega
    have hshape1 : L + 1 = (r + 1) + 9 * (L / 9) := by
      omega
    have h0 : digit3 (4^r) 2 = 2 := by
      have h := hov.1
      rw [hshape] at h
      have hperiod := pow4_digit_period 2 r (L / 9)
      norm_num at hperiod
      rw [hperiod] at h
      exact h
    have h1 : digit3 (4^(r+1)) 2 = 2 := by
      have h := hov.2
      rw [hshape1] at h
      have hperiod := pow4_digit_period 2 (r+1) (L / 9)
      norm_num at hperiod
      rw [hperiod] at h
      exact h
    have hres : r = 5 ∨ r = 6 := by
      interval_cases r <;> norm_num [digit3] at *
    simpa [r] using hres
  · exact row_two_overlap_of_mod9_five_or_six L

/-- Direct obstruction: global common-two failure excludes both row-two classes. -/
theorem no_common_two_forbids_mod9_five_six
    (K : Nat)
    (hNo : ¬ ∃ p : Nat, 1 ≤ p ∧
      digit3 (4^K) p = 2 ∧ digit3 (4^(K+1)) p = 2) :
    K % 9 ≠ 5 ∧ K % 9 ≠ 6 := by
  constructor
  · intro h5
    apply hNo
    refine ⟨2, by norm_num, ?_⟩
    exact row_two_overlap_of_mod9_five_or_six K (Or.inl h5)
  · intro h6
    apply hNo
    refine ⟨2, by norm_num, ?_⟩
    exact row_two_overlap_of_mod9_five_or_six K (Or.inr h6)

#check digit3
#check pow4_three_power_lte_exact
#check lteCoeff_mod3_one
#check pow4_scaled_mod_next
#check digit3_eq_of_mod_next
#check pow4_digit_period
#check pow4_exponent_trit_lift_digit
#check row_two_overlap_of_mod9_five_or_six
#check row_two_overlap_iff_mod9_five_or_six
#check no_common_two_forbids_mod9_five_six
#print axioms pow4_three_power_lte_exact
#print axioms lteCoeff_mod3_one
#print axioms pow4_scaled_mod_next
#print axioms digit3_eq_of_mod_next
#print axioms pow4_digit_period
#print axioms pow4_exponent_trit_lift_digit
#print axioms row_two_overlap_of_mod9_five_or_six
#print axioms row_two_overlap_iff_mod9_five_or_six
#print axioms no_common_two_forbids_mod9_five_six

end GSTFourPowerDirectResidue