/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1018 / 1132
/-    Path         : branches/sol_right-chord-firepower-base/ResidualNullPrefixFourCutScratch.lean
/-    Ref          : origin/sol/right-chord-firepower-base
/-    First-commit : 2026-08-17 11:08:42 +0530  (4179389)
/-    Last-commit  : 2026-08-17 11:08:42 +0530  (4179389)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 11:08:42 +0530  4179389  (ker07-dev)
/-        Eliminate second-trit one in NULL residual
/- ====================================================================== -/

import ResidualNullTerminalScratch
import NavigationResidueCutScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Locked NULL branch: canonical prefix-four cut

If n = 3u+1, then the parent origin is 1+3n = 4+9u.  At levels s>=2,
Q_s(4) has residue 10 mod 27.  Therefore a next origin trit u%3=1 lifts the
parent Navigation constant to residue 19 mod 27, which is a NULL Happy Gate at
position two.
-/

/-- Q_s(4) has the stable residue 10 modulo 27 from level two onward. -/
theorem gst_navigation_constant_four_mod27S
    (s : Nat) (hs : 2 ≤ s) :
    gstNavigationConstant s 4 % 27 = 10 := by
  by_cases hs2 : s = 2
  · subst s
    decide
  by_cases hs3 : s = 3
  · subst s
    decide
  · have h243 := gst_navigation_constant_four_mod243_stableS s (by omega)
    have h := Nat.mod_mod_of_dvd (gstNavigationConstant s 4)
      (by decide : 27 ∣ 243)
    rw [h243] at h
    norm_num at h ⊢
    exact h.symm

/-- Prefix-four origin lift: if u%3=1, Q_s(4+9u) is residue 19 mod 27. -/
theorem gst_navigation_prefix_four_next_one_mod27S
    (s u : Nat) (hs : 2 ≤ s) (hu : 1 ≤ u) (hu1 : u % 3 = 1) :
    gstNavigationConstant s (4 + 9*u) % 27 = 19 := by
  have hrec := gst_canonical_prefix_recurrenceS
    gstNavigationConstant gst_navigation_constant_origin_energyS
    s 4 2 u (by omega)
  norm_num at hrec

  have hQ4 : gstNavigationConstant s 4 % 27 = 10 :=
    gst_navigation_constant_four_mod27S s hs
  have hQu3 : gstNavigationConstant (s+2) u % 3 = 1 := by
    simpa [hu1] using
      (gstNavigationConstant_mod3 (s+2) u (by omega) hu (by omega))
  have hA3 : 4^(3^s * 4) % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have hprod3 :
      (4^(3^s * 4) * gstNavigationConstant (s+2) u) % 3 = 1 := by
    rw [Nat.mul_mod, hA3, hQu3]
    decide
  have hprodDecomp :
      4^(3^s * 4) * gstNavigationConstant (s+2) u =
        1 + 3 * ((4^(3^s * 4) * gstNavigationConstant (s+2) u) / 3) := by
    have h := Nat.mod_add_div
      (4^(3^s * 4) * gstNavigationConstant (s+2) u) 3
    rw [hprod3] at h
    omega
  have hterm :
      (9 * 4^(3^s * 4) * gstNavigationConstant (s+2) u) % 27 = 9 := by
    have hshape :
        9 * 4^(3^s * 4) * gstNavigationConstant (s+2) u =
          9 * (4^(3^s * 4) * gstNavigationConstant (s+2) u) := by ring
    rw [hshape, hprodDecomp]
    have hshape2 :
        9 * (1 + 3 * ((4^(3^s * 4) *
          gstNavigationConstant (s+2) u) / 3)) =
          9 + 27 * ((4^(3^s * 4) *
            gstNavigationConstant (s+2) u) / 3) := by ring
    rw [hshape2, Nat.add_mod, Nat.mul_mod]
    norm_num

  rw [hrec, Nat.add_mod, hQ4, hterm]
  decide

/-- In the true NULL residual n=3u+1, a second origin trit one contradicts the
complete parent Omega bad trace. -/
theorem gst_residual_null_second_trit_one_impossibleS
    (s n : Nat) (hs : 2 ≤ s) (hn : 1 ≤ n)
    (hn1 : n % 3 = 1)
    (hu1 : (n/3) % 3 = 1)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) : False := by
  let u := n / 3
  have hu : 1 ≤ u := gst_residual_null_bad_forces_deeper_originS
    s n (by omega) hn hn1 hBad
  have hnshape : n = 3*u + 1 := by
    dsimp [u]
    have h := Nat.mod_add_div n 3
    omega
  have hparentOrigin : 1 + 3*n = 4 + 9*u := by
    rw [hnshape]
    ring
  have hmod : gstNavigationConstant s (1 + 3*n) % 27 = 19 := by
    rw [hparentOrigin]
    exact gst_navigation_prefix_four_next_one_mod27S s u hs hu (by simpa [u] using hu1)

  have hgateS := gst_residue19_is_null_gate2S
    (gstNavigationConstant s (1 + 3*n)) hmod
  have hd : gstDigit (gstNavigationConstant s (1 + 3*n)) 2 = 2 := by
    simpa [gstDigitS, gstDigit] using hgateS.1
  have hc : gstCarry (gstNavigationConstant s (1 + 3*n)) 2 = 0 := by
    simpa [gstCarryS, gstCarry] using hgateS.2

  have hprojection := gst_omega_parent_projection s 1 n 1 (by omega)
  have homegaDigit : (gstOmega s 1 n 1).parentDigit = 2 := by
    have hd' : gstDigit (gstNavigationConstant s (1 + 3^1*n)) (1+1) = 2 := by
      simpa using hd
    rw [hprojection.1] at hd'
    exact hd'
  have homegaCarry : (gstOmega s 1 n 1).parentCarry = 0 := by
    have hc' : gstCarry (gstNavigationConstant s (1 + 3^1*n)) (1+1) = 0 := by
      simpa using hc
    rw [hprojection.2] at hc'
    exact hc'
  have hzero : GSTOmegaGatePolynomial (gstOmega s 1 n 1) = 0 :=
    (gst_omega_gate_polynomial_zero_iff (gstOmega s 1 n 1)).2
      ⟨homegaDigit, Or.inl homegaCarry⟩
  exact (hBad 1) hzero

/-- Therefore, at levels s>=2, a completely bad NULL residual with first trit
one and positive remaining origin can only have second trit zero or two. -/
theorem gst_residual_null_second_trit_zero_or_twoS
    (s n : Nat) (hs : 2 ≤ s) (hn : 1 ≤ n)
    (hn1 : n % 3 = 1)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    (n/3) % 3 = 0 ∨ (n/3) % 3 = 2 := by
  have hlt : (n/3) % 3 < 3 := Nat.mod_lt _ (by decide)
  have hcases : (n/3) % 3 = 0 ∨ (n/3) % 3 = 1 ∨ (n/3) % 3 = 2 := by
    omega
  rcases hcases with h0 | h1 | h2
  · exact Or.inl h0
  · exact False.elim
      (gst_residual_null_second_trit_one_impossibleS s n hs hn hn1 h1 hBad)
  · exact Or.inr h2
