/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0550 / 1132
/-    Path         : branches/sol_5c579-right-chord-surgery/GSTExponentLiftScratch.lean
/-    Ref          : origin/sol/5c579-right-chord-surgery
/-    First-commit : 2026-08-16 02:25:06 +0530  (eaddb30)
/-    Last-commit  : 2026-08-16 02:57:02 +0530  (b00e2a3)
/-    Total commits: 3
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/3] 2026-08-16 02:25:06 +0530  eaddb30  (ker07-dev)
/-        Add pure-power exponent trit lift graph
/- [02/3] 2026-08-16 02:47:04 +0530  48ab484  (ker07-dev)
/-        simplify exponent-trit lift proof
/- [03/3] 2026-08-16 02:57:02 +0530  b00e2a3  (ker07-dev)
/-        remove redundant closed-goal tactics
/- ====================================================================== -/

import InformationDescentScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
Pure-power exponent-residue graph.

This is the canonical component absent from arbitrary affine T. If one
3-adic exponent trit is changed at level p, the exact LTE block
4^(3^p)=1+3^(p+1)c with c == 1 (mod 3) determines the newly exposed power
digit one level higher.
-/

/-- Powers of four are one modulo three. -/
theorem gst_pow4_mod3_oneS (m : Nat) : 4^m % 3 = 1 := by
  rw [Nat.pow_mod]
  norm_num

/-- Adding one exponent trit `3^p` shifts the newly exposed ternary power digit
by exactly one. -/
theorem gst_pow4_exponent_lift_one_digitS
    (p m c : Nat)
    (hA : 4^(3^p) = 1 + 3^(p+1)*c)
    (hc : c % 3 = 1) :
    gstDigitS (4^(m + 3^p)) (p+1) =
      (gstDigitS (4^m) (p+1) + 1) % 3 := by
  let L := 3^(p+1)
  have hL : 0 < L := by
    dsimp [L]
    exact Nat.pow_pos (by decide)
  have hpow : 4^(m + 3^p) = 4^m * (1 + L*c) := by
    rw [Nat.pow_add, hA]
  have hshape :
      4^m * (1 + L*c) = 4^m + L * (4^m*c) := by ring
  unfold gstDigitS
  rw [show 3^(p+1) = L by rfl, hpow, hshape]
  rw [Nat.add_mul_div_left _ _ hL]
  rw [Nat.add_mod, Nat.mul_mod, gst_pow4_mod3_oneS, hc]

/-- Adding exponent trit `2*3^p` shifts the newly exposed ternary power digit
by exactly two.  This is obtained by applying the exact one-trit lift twice,
so no separate nonlinear modular normalization is needed. -/
theorem gst_pow4_exponent_lift_two_digitS
    (p m c : Nat)
    (hA : 4^(3^p) = 1 + 3^(p+1)*c)
    (hc : c % 3 = 1) :
    gstDigitS (4^(m + 2*3^p)) (p+1) =
      (gstDigitS (4^m) (p+1) + 2) % 3 := by
  have h1 := gst_pow4_exponent_lift_one_digitS p m c hA hc
  have h2 := gst_pow4_exponent_lift_one_digitS p (m + 3^p) c hA hc
  have hexp : m + 2*3^p = (m + 3^p) + 3^p := by omega
  rw [hexp]
  rw [h2, h1]
  have hd : gstDigitS (4^m) (p+1) < 3 := by
    unfold gstDigitS
    exact Nat.mod_lt _ (by decide)
  omega

/-- Unified exponent-trit lift for a in {0,1,2}. -/
theorem gst_pow4_exponent_trit_lift_digitS
    (p m c a : Nat)
    (ha : a < 3)
    (hA : 4^(3^p) = 1 + 3^(p+1)*c)
    (hc : c % 3 = 1) :
    gstDigitS (4^(m + a*3^p)) (p+1) =
      (gstDigitS (4^m) (p+1) + a) % 3 := by
  have haCases : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases haCases with h0 | h1 | h2
  · subst a
    simp only [Nat.zero_mul, Nat.add_zero]
    have hd : gstDigitS (4^m) (p+1) < 3 := by
      unfold gstDigitS
      exact Nat.mod_lt _ (by decide)
    omega
  · subst a
    simpa using gst_pow4_exponent_lift_one_digitS p m c hA hc
  · subst a
    simpa using gst_pow4_exponent_lift_two_digitS p m c hA hc
