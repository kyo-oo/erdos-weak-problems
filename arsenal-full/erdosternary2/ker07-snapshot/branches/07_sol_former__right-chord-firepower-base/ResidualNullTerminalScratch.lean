/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1006 / 1132
/-    Path         : branches/sol_right-chord-firepower-base/ResidualNullTerminalScratch.lean
/-    Ref          : origin/sol/right-chord-firepower-base
/-    First-commit : 2026-08-17 10:57:21 +0530  (9d900e3)
/-    Last-commit  : 2026-08-17 11:06:51 +0530  (4ffc57c)
/-    Total commits: 4
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/4] 2026-08-17 10:57:21 +0530  9d900e3  (ker07-dev)
/-        Prove stable NULL terminal residue base
/- [02/4] 2026-08-17 10:57:58 +0530  69e7560  (ker07-dev)
/-        Harden stable NULL terminal digit proof
/- [03/4] 2026-08-17 11:01:37 +0530  2aebc7a  (ker07-dev)
/-        Force deeper origin in stable NULL branch
/- [04/4] 2026-08-17 11:06:51 +0530  4ffc57c  (ker07-dev)
/-        Close all finite NULL terminal base levels
/- ====================================================================== -/

import ResidualNullBranchReductionScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Terminal base for the locked residual NULL branch

For residual origin n=1, the first NULL regeneration turns the hard parent tail
into the exact suffix (Q_s(4)-1)/9.  The stable levels s>=4 are discharged by
canonical c-tower residues; s=1,2,3 are explicit kernel-decidable base cases.
-/

/-- At stable levels the canonical block multiplier is one modulo 81. -/
theorem gst_canonical_block_mod81_oneS
    (s : Nat) (hs : 4 ≤ s) :
    4^(3^s) % 81 = 1 := by
  rw [lte_identity s (by omega), Nat.add_mod, Nat.mul_mod]
  have hp : 3^(s+1) % 81 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    rw [show (81:Nat) = 3^4 by decide]
    exact Nat.pow_dvd_pow 3 (by omega)
  rw [hp]
  norm_num

/-- Stable low residue of the actual parent Navigation constant Q_s(4). -/
theorem gst_navigation_constant_four_mod243_stableS
    (s : Nat) (hs : 4 ≤ s) :
    gstNavigationConstant s 4 % 243 = 226 := by
  have hrec := gst_navigation_constant_general_recurrence s 1 1 (by omega)
  norm_num at hrec
  rw [gstNavigationConstant_one (s+1) (by omega)] at hrec

  have hc243 : c s % 243 = 178 := c_mod243_stable s hs
  have hA81 : 4^(3^s) % 81 = 1 :=
    gst_canonical_block_mod81_oneS s hs
  have hcNext81 : c (s+1) % 81 = 16 :=
    c_mod81_stable (s+1) (by omega)
  have hprod81 : (4^(3^s) * c (s+1)) % 81 = 16 := by
    rw [Nat.mul_mod, hA81, hcNext81]
    decide
  have hprodDecomp :
      4^(3^s) * c (s+1) =
        16 + 81 * ((4^(3^s) * c (s+1)) / 81) := by
    have h := Nat.mod_add_div (4^(3^s) * c (s+1)) 81
    rw [hprod81] at h
    omega
  have hterm :
      (3 * 4^(3^s) * c (s+1)) % 243 = 48 := by
    have hshape :
        3 * 4^(3^s) * c (s+1) =
          3 * (4^(3^s) * c (s+1)) := by ring
    rw [hshape, hprodDecomp]
    have hshape2 :
        3 * (16 + 81 * ((4^(3^s) * c (s+1)) / 81)) =
          48 + 243 * ((4^(3^s) * c (s+1)) / 81) := by ring
    rw [hshape2, Nat.add_mod, Nat.mul_mod]
    norm_num

  rw [hrec, Nat.add_mod, hc243, hterm]
  decide

/-- Exact regenerated terminal word after the forced prefix and NULL row. -/
def gstResidualNullTerminalS (s : Nat) : Nat :=
  (gstNavigationConstant s 4 - 1) / 9

/-- The stable terminal word is exactly 25 modulo 27 = 221_3. -/
theorem gst_residual_null_terminal_mod27S
    (s : Nat) (hs : 4 ≤ s) :
    gstResidualNullTerminalS s % 27 = 25 := by
  have hQ : gstNavigationConstant s 4 % 243 = 226 :=
    gst_navigation_constant_four_mod243_stableS s hs
  have hdecomp :
      gstNavigationConstant s 4 =
        226 + 243 * (gstNavigationConstant s 4 / 243) := by
    have h := Nat.mod_add_div (gstNavigationConstant s 4) 243
    rw [hQ] at h
    omega
  unfold gstResidualNullTerminalS
  rw [hdecomp]
  have hshape :
      226 + 243 * (gstNavigationConstant s 4 / 243) - 1 =
        9 * (25 + 27 * (gstNavigationConstant s 4 / 243)) := by
    omega
  rw [hshape]
  simp [Nat.add_mod, Nat.mul_mod]

/-- The stable terminal NULL suffix has a physical Happy Gate at position two. -/
theorem gst_residual_null_terminal_happyS
    (s : Nat) (hs : 4 ≤ s) :
    gstDigitS (gstResidualNullTerminalS s) 2 = 2 ∧
      (gstAffineMulCarryS 4 0 (gstResidualNullTerminalS s) 2 = 0 ∨
       gstAffineMulCarryS 4 0 (gstResidualNullTerminalS s) 2 = 3) := by
  have h27 := gst_residual_null_terminal_mod27S s hs
  have h9 : gstResidualNullTerminalS s % 9 = 7 := by
    have h := Nat.mod_mod_of_dvd (gstResidualNullTerminalS s)
      (by decide : 9 ∣ 27)
    rw [h27] at h
    norm_num at h ⊢
    exact h.symm
  constructor
  · unfold gstDigitS
    have hsplit :
        gstResidualNullTerminalS s % 27 =
          gstResidualNullTerminalS s % 9 +
            9 * (gstResidualNullTerminalS s / 9 % 3) := by
      rw [show (27:Nat) = 9 * 3 by decide, Nat.mod_mul]
    rw [h27, h9] at hsplit
    norm_num at hsplit
    omega
  · right
    unfold gstAffineMulCarryS
    rw [show (3:Nat)^2 = 9 by decide, h9]
    decide

/-- Explicit low-level NULL terminal gates.  These are finite kernel checks,
not bounded searches used as a universal theorem. -/
theorem gst_residual_null_terminal_happy_s1S :
    gstDigitS (gstResidualNullTerminalS 1) 6 = 2 ∧
      (gstAffineMulCarryS 4 0 (gstResidualNullTerminalS 1) 6 = 0 ∨
       gstAffineMulCarryS 4 0 (gstResidualNullTerminalS 1) 6 = 3) := by
  decide

theorem gst_residual_null_terminal_happy_s2S :
    gstDigitS (gstResidualNullTerminalS 2) 7 = 2 ∧
      (gstAffineMulCarryS 4 0 (gstResidualNullTerminalS 2) 7 = 0 ∨
       gstAffineMulCarryS 4 0 (gstResidualNullTerminalS 2) 7 = 3) := by
  decide

theorem gst_residual_null_terminal_happy_s3S :
    gstDigitS (gstResidualNullTerminalS 3) 5 = 2 ∧
      (gstAffineMulCarryS 4 0 (gstResidualNullTerminalS 3) 5 = 0 ∨
       gstAffineMulCarryS 4 0 (gstResidualNullTerminalS 3) 5 = 3) := by
  decide

/-- Every positive canonical level has an explicit terminal NULL gate. -/
theorem gst_residual_null_terminal_happy_allS
    (s : Nat) (hs : 1 ≤ s) :
    ∃ p,
      gstDigitS (gstResidualNullTerminalS s) p = 2 ∧
        (gstAffineMulCarryS 4 0 (gstResidualNullTerminalS s) p = 0 ∨
         gstAffineMulCarryS 4 0 (gstResidualNullTerminalS s) p = 3) := by
  by_cases hs1 : s = 1
  · subst s
    exact ⟨6, gst_residual_null_terminal_happy_s1S⟩
  by_cases hs2 : s = 2
  · subst s
    exact ⟨7, gst_residual_null_terminal_happy_s2S⟩
  by_cases hs3 : s = 3
  · subst s
    exact ⟨5, gst_residual_null_terminal_happy_s3S⟩
  · exact ⟨2, gst_residual_null_terminal_happyS s (by omega)⟩

/-- The NULL-reduced n=1 expression is exactly the canonical terminal word. -/
theorem gst_residual_null_origin_one_terminal_eqS
    (s : Nat) (hs : 1 ≤ s) :
    (gstCanonicalPrefixOffsetS s + GSTCanonicalBlockS s) / 3 +
        GSTCanonicalBlockS s *
          GSTHardPrefixOneTailS
            gstNavigationConstant gstCanonicalPrefixOffsetS (s+1) 0 =
      gstResidualNullTerminalS s := by
  have hparent := gst_hard_tail_parent_navigationS
    gstNavigationConstant gst_navigation_constant_origin_energyS
    gstCanonicalPrefixOffsetS gst_navigation_constant_unit_prefixS
    s 1 hs
  have hdiv := gst_hard_tail_origin_one_div3S
    gstNavigationConstant gst_navigation_constant_origin_energyS
    gstCanonicalPrefixOffsetS gst_navigation_constant_unit_prefixS
    s 0 hs
  norm_num at hdiv
  have hterm :
      gstResidualNullTerminalS s =
        GSTHardPrefixOneTailS
          gstNavigationConstant gstCanonicalPrefixOffsetS s 1 / 3 := by
    unfold gstResidualNullTerminalS
    rw [hparent]
    have hshape :
        1 + 3 * GSTHardPrefixOneTailS
          gstNavigationConstant gstCanonicalPrefixOffsetS s 1 - 1 =
          3 * GSTHardPrefixOneTailS
            gstNavigationConstant gstCanonicalPrefixOffsetS s 1 := by
      omega
    rw [hshape, show (9:Nat) = 3 * 3 by decide,
      ← Nat.div_div_eq_div_mul]
    simp
  rw [hterm, hdiv]

/-- Complete terminal base for every positive canonical level. -/
theorem gst_residual_null_origin_one_bad_impossible_allS
    (s : Nat) (hs : 1 ≤ s)
    (hBad : GSTOmegaInfiniteBadTrace s 1 1) : False := by
  have hred := gst_residual_null_branch_reductionS
    s 1 hs (by decide) (by decide) hBad
  dsimp only at hred
  have hbad := hred.2.1
  have heq := gst_residual_null_origin_one_terminal_eqS s hs
  rw [heq] at hbad
  obtain ⟨p, hhappy⟩ := gst_residual_null_terminal_happy_allS s hs
  exact (hbad p) hhappy

/-- NULL forcing step: a completely bad residual origin in the n mod 3 = 1
branch cannot terminate at this trit.  Therefore its remaining origin n/3 is
positive, at every positive canonical level. -/
theorem gst_residual_null_bad_forces_deeper_originS
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hn1 : n % 3 = 1)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    1 ≤ n / 3 := by
  by_contra hnot
  have hu0 : n / 3 = 0 := by omega
  have hnEq : n = 1 := by
    have h := Nat.mod_add_div n 3
    rw [hn1, hu0] at h
    omega
  subst n
  exact False.elim (gst_residual_null_origin_one_bad_impossible_allS s hs hBad)
