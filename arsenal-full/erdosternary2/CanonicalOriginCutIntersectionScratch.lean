import PrefixOneOriginPhaseRecursionScratch
import InformationDescentScratch
import GSTNavigationCore

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- Monolith Navigation is the canonical origin-energy map used by the copied
prefix/residue stack. -/
theorem gst_navigation_constant_origin_energyS :
    GSTCanonicalOriginEnergyS gstNavigationConstant := by
  exact gst_navigation_core_origin_energyS

/-- The canonical suffix term is divisible by the physical cut modulus, so the
carry at cut k depends only on the finite origin prefix a. -/
theorem gst_canonical_origin_cut_carryS
    (s a k m : Nat) (hs : 1 ≤ s) :
    gstCarryS (gstNavigationConstant s (a + 3^k*m)) k =
      gstCarryS (gstNavigationConstant s a) k := by
  have hrec0 := gst_canonical_prefix_recurrenceS
    gstNavigationConstant gst_navigation_constant_origin_energyS
    s a k m hs
  have hrec :
      gstNavigationConstant s (a + 3^k*m) =
        gstNavigationConstant s a +
          3^k * (4^(3^s*a) * gstNavigationConstant (s+k) m) := by
    rw [hrec0]
    ring
  unfold gstCarryS
  rw [hrec]
  have hmod :
      (gstNavigationConstant s a +
          3^k * (4^(3^s*a) * gstNavigationConstant (s+k) m)) % 3^k =
        gstNavigationConstant s a % 3^k := by
    rw [Nat.add_mod]
    have hzero :
        (3^k * (4^(3^s*a) * gstNavigationConstant (s+k) m)) % 3^k = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      exact Nat.dvd_mul_right (3^k)
        (4^(3^s*a) * gstNavigationConstant (s+k) m)
    rw [hzero, Nat.add_zero, Nat.mod_mod]
  rw [hmod]

/-- The power multiplier in every canonical origin cut is one modulo three. -/
theorem gst_canonical_origin_cut_multiplier_mod3S
    (s a : Nat) :
    4^(3^s*a) % 3 = 1 := by
  rw [Nat.pow_mod]
  norm_num

/-- Canonical Navigation retains the origin's least ternary trit at every
positive level, including divisible-by-three and zero tails. -/
theorem gst_navigation_constant_mod3_allS
    (s m : Nat) (hs : 1 ≤ s) :
    gstNavigationConstant s m % 3 = m % 3 := by
  exact gst_navigation_core_mod3_allS s m hs

/-- The physical digit exposed at cut k is the finite-prefix digit shifted by
the next origin trit m%3. -/
theorem gst_canonical_origin_cut_digitS
    (s a k m : Nat) (hs : 1 ≤ s) :
    gstDigitS (gstNavigationConstant s (a + 3^k*m)) k =
      (gstDigitS (gstNavigationConstant s a) k + m % 3) % 3 := by
  have hrec0 := gst_canonical_prefix_recurrenceS
    gstNavigationConstant gst_navigation_constant_origin_energyS
    s a k m hs
  have hrec :
      gstNavigationConstant s (a + 3^k*m) =
        gstNavigationConstant s a +
          3^k * (4^(3^s*a) * gstNavigationConstant (s+k) m) := by
    rw [hrec0]
    ring
  have hkpos : 0 < 3^k := Nat.pow_pos (by decide)
  have hQm3 : gstNavigationConstant (s+k) m % 3 = m % 3 :=
    gst_navigation_constant_mod3_allS (s+k) m (by omega)
  have hA3 : 4^(3^s*a) % 3 = 1 :=
    gst_canonical_origin_cut_multiplier_mod3S s a
  unfold gstDigitS
  rw [hrec]
  rw [Nat.add_mul_div_left _ _ hkpos]
  rw [Nat.add_mod, Nat.mul_mod, hA3, hQm3]
  simp only [Nat.one_mul, Nat.mod_mod]

/-- If the finite prefix has a good GST carry at cut k and the next origin trit
shifts the exposed digit to two, the full canonical Navigation value has a
physical witness at that cut. -/
theorem gst_canonical_origin_cut_witnessS
    (s a k m : Nat) (hs : 1 ≤ s)
    (hcarry :
      gstCarryS (gstNavigationConstant s a) k = 0 ∨
      gstCarryS (gstNavigationConstant s a) k = 3)
    (hdigit :
      (gstDigitS (gstNavigationConstant s a) k + m % 3) % 3 = 2) :
    GSTNavigationWitness (gstNavigationConstant s (a + 3^k*m)) := by
  have hc := gst_canonical_origin_cut_carryS s a k m hs
  have hd := gst_canonical_origin_cut_digitS s a k m hs
  have hfullCarry :
      gstCarryS (gstNavigationConstant s (a + 3^k*m)) k = 0 ∨
      gstCarryS (gstNavigationConstant s (a + 3^k*m)) k = 3 := by
    rw [hc]
    exact hcarry
  have hfullDigit :
      gstDigitS (gstNavigationConstant s (a + 3^k*m)) k = 2 := by
    rw [hd, hdigit]
  rcases hfullCarry with h0 | h3
  · exact gst_navigation_core_witness_of_digit_carry_zeroS
      (gstNavigationConstant s (a + 3^k*m)) k
      (by simpa [gstDigitS, gstDigit] using hfullDigit)
      (by simpa [gstCarryS, gstCarry] using h0)
  · exact gst_navigation_core_witness_of_digit_carry_threeS
      (gstNavigationConstant s (a + 3^k*m)) k
      (by simpa [gstDigitS, gstDigit] using hfullDigit)
      (by simpa [gstCarryS, gstCarry] using h3)

/-- Badness forbids exactly the next-origin trit that would shift a good prefix
carry into digit two at this cut. -/
theorem gst_canonical_bad_forbids_cut_shiftS
    (s a k m : Nat) (hs : 1 ≤ s)
    (hno : ¬ GSTNavigationWitness
      (gstNavigationConstant s (a + 3^k*m)))
    (hcarry :
      gstCarryS (gstNavigationConstant s a) k = 0 ∨
      gstCarryS (gstNavigationConstant s a) k = 3) :
    (gstDigitS (gstNavigationConstant s a) k + m % 3) % 3 ≠ 2 := by
  intro hd
  exact hno (gst_canonical_origin_cut_witnessS
    s a k m hs hcarry hd)

/-! ## Live prefix-one cut transplant

These are the exact formulas used by the final monolith hard branch.  They
retain every preceding zero origin trit through the arbitrary cut `k`; no
replacement of `1 + 3^k*m` by the one-trit case is made. -/

/-- Exact arbitrary-k prefix-one Navigation decomposition. -/
theorem gst_prefix_one_navigation_cut_decompositionS
    (s k m : Nat) (hs : 1 ≤ s) :
    gstNavigationConstant s (1 + 3^k*m) =
      gstNavigationConstant s 1 +
        3^k * 4^(3^s) * gstNavigationConstant (s+k) m := by
  simpa using
    (gst_canonical_prefix_recurrenceS
      gstNavigationConstant gst_navigation_constant_origin_energyS
      s 1 k m hs)

/-- The level-one unit prefix is the literal integer seven. -/
theorem gst_level_one_navigation_unit_sevenS :
    gstNavigationConstant 1 1 = 7 := by
  have h := gst_navigation_constant_origin_energyS 1 1 (by decide)
  norm_num at h
  omega

/-- At level one the arbitrary-k parent is exactly `7 + 3^k*64*Q`. -/
theorem gst_level_one_prefix_one_cut_decompositionS
    (k m : Nat) :
    gstNavigationConstant 1 (1 + 3^k*m) =
      7 + 3^k * 64 * gstNavigationConstant (1+k) m := by
  have h := gst_prefix_one_navigation_cut_decompositionS 1 k m (by decide)
  rw [gst_level_one_navigation_unit_sevenS] at h
  norm_num at h ⊢
  simpa [Nat.add_assoc, Nat.mul_assoc] using h

/-- Once `k≥2`, the complete low prefix at the cut is exactly seven. -/
theorem gst_level_one_prefix_one_cut_residueS
    (k m : Nat) (hk : 2 ≤ k) :
    gstNavigationConstant 1 (1 + 3^k*m) % 3^k = 7 := by
  rw [gst_level_one_prefix_one_cut_decompositionS]
  have h9 : 9 ≤ 3^k := by
    rw [show (9 : Nat) = 3^2 by decide]
    exact Nat.pow_le_pow_of_le (by decide : 1 < 3) hk
  have h7 : 7 < 3^k := by omega
  simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt h7]

/-- The high tail after the arbitrary prefix-one cut is literally `64*Q`. -/
theorem gst_level_one_prefix_one_cut_tailS
    (k m : Nat) (hk : 2 ≤ k) :
    gstNavigationConstant 1 (1 + 3^k*m) / 3^k =
      64 * gstNavigationConstant (1+k) m := by
  rw [gst_level_one_prefix_one_cut_decompositionS]
  have hp : 0 < 3^k := Nat.pow_pos (by decide)
  have h9 : 9 ≤ 3^k := by
    rw [show (9 : Nat) = 3^2 by decide]
    exact Nat.pow_le_pow_of_le (by decide : 1 < 3) hk
  have h7 : 7 < 3^k := by omega
  have hshape :
      7 + 3^k * 64 * gstNavigationConstant (1+k) m =
        7 + 3^k * (64 * gstNavigationConstant (1+k) m) := by ring
  rw [hshape, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt h7,
    Nat.zero_add]

/-- Exact seeded carry generated by the retained low prefix seven. -/
theorem gst_level_one_prefix_one_cut_carryS
    (k m : Nat) (hk : 2 ≤ k) :
    gstCarryS (gstNavigationConstant 1 (1 + 3^k*m)) k =
      28 / 3^k := by
  unfold gstCarryS
  rw [gst_level_one_prefix_one_cut_residueS k m hk]

/-- In the hard origin-one family the first exposed parent digit at the cut is
one; the child origin trit is retained exactly rather than discarded. -/
theorem gst_level_one_prefix_one_cut_digit_oneS
    (k m : Nat) (hk : 2 ≤ k) (hm1 : m % 3 = 1) :
    gstDigitS (gstNavigationConstant 1 (1 + 3^k*m)) k = 1 := by
  unfold gstDigitS
  rw [gst_level_one_prefix_one_cut_tailS k m hk]
  rw [Nat.mul_mod]
  have hQ := gst_navigation_constant_mod3_allS (1+k) m (by omega)
  rw [hQ, hm1]
