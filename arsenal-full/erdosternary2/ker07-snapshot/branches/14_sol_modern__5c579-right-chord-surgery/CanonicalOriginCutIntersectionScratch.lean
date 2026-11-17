/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1019 / 1132
/-    Path         : branches/sol_5c579-right-chord-surgery/CanonicalOriginCutIntersectionScratch.lean
/-    Ref          : origin/sol/5c579-right-chord-surgery
/-    First-commit : 2026-08-17 11:13:39 +0530  (f14277b)
/-    Last-commit  : 2026-08-17 11:15:11 +0530  (45307f7)
/-    Total commits: 3
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/3] 2026-08-17 11:13:39 +0530  f14277b  (ker07-dev)
/-        Add canonical origin-cut physical intersection
/- [02/3] 2026-08-17 11:14:11 +0530  1178560  (ker07-dev)
/-        Harden canonical origin-cut intersection
/- [03/3] 2026-08-17 11:15:11 +0530  45307f7  (ker07-dev)
/-        Generalize canonical origin-cut intersection to all trits
/- ====================================================================== -/

import ResidualNullPrefixFourCutScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Canonical origin-prefix / physical-cut intersection

This is the reusable arithmetic bridge behind the locked residual proof.
For the canonical Navigation map, an origin decomposition

  b = a + 3^k*m

has two exact consequences at physical ternary cut k:

* the GST carry is determined entirely by the finite prefix a;
* the exposed digit is the prefix digit plus the next origin trit m%3.

No alternate-space re-coordinate is promoted to physical transport here: both
statements are literal consequences of the canonical perfect-power recurrence.
-/

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

/-- The power multiplier in every canonical origin cut is a unit one modulo
three. -/
theorem gst_canonical_origin_cut_multiplier_mod3S
    (s a : Nat) :
    4^(3^s*a) % 3 = 1 := by
  rw [Nat.pow_mod]
  norm_num

/-- The canonical Navigation value retains the origin's least ternary trit at
every positive level, including the divisible-by-three and zero cases. -/
theorem gst_navigation_constant_mod3_allS
    (s m : Nat) (hs : 1 ≤ s) :
    gstNavigationConstant s m % 3 = m % 3 := by
  by_cases hm0 : m = 0
  · subst m
    have hQ0 := gst_canonical_origin_zeroS
      gstNavigationConstant gst_navigation_constant_origin_energyS s hs
    rw [hQ0]
    decide
  by_cases hm3 : m % 3 = 0
  · have hmshape : m = 3 * (m / 3) := by
      have h := Nat.mod_add_div m 3
      rw [hm3] at h
      omega
    rw [hmshape, gst_navigation_constant_mul3 s (m/3) hs]
    simp
  · exact gstNavigationConstant_mod3 s m hs (by omega) hm3

/-- For every remaining origin m, including a zero or divisible-by-three tail,
the physical digit exposed at cut k is exactly the prefix digit shifted by the
next origin trit m%3. -/
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

/-- Physical intersection constructor.  If the finite prefix has a good GST
carry at cut k and the next origin trit shifts the exposed digit to two, then
the full canonical Navigation value has a genuine physical Navigation witness
at exactly that cut. -/
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
  · exact gstNavigationWitness_of_digit_carry_zero
      (gstNavigationConstant s (a + 3^k*m)) k
      (by simpa [gstDigitS, gstDigit] using hfullDigit)
      (by simpa [gstCarryS, gstCarry] using h0)
  · exact gstNavigationWitness_of_digit_carry_three
      (gstNavigationConstant s (a + 3^k*m)) k
      (by simpa [gstDigitS, gstDigit] using hfullDigit)
      (by simpa [gstCarryS, gstCarry] using h3)

/-- Badness therefore forbids the unique next-origin trit that would shift a
good prefix carry into digit two at this physical cut.  This exact exclusion
also applies when the remaining origin tail has already become zero. -/
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
