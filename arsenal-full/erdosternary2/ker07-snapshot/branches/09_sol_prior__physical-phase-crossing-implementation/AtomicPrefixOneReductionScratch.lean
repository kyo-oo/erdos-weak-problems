/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0617 / 1132
/-    Path         : branches/sol_physical-phase-crossing-implementation/AtomicPrefixOneReductionScratch.lean
/-    Ref          : origin/sol/physical-phase-crossing-implementation
/-    First-commit : 2026-08-16 15:43:03 +0530  (76ad5a6)
/-    Last-commit  : 2026-08-16 15:43:03 +0530  (76ad5a6)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-16 15:43:03 +0530  76ad5a6  (ker07-dev)
/-        Add atomic prefix-one residual reduction helpers
/- ====================================================================== -/

import ErdosTernary2

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- Prefix-one Omega badness rules out every parent Navigation witness.
    Position zero is excluded by the exact prefix-one residue modulo three;
    every positive parent gate projects to an Omega gate-polynomial zero. -/
theorem gst_prefix_one_no_parent_navigation_of_omega_bad_atomic
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    ¬ GSTNavigationWitness (gstNavigationConstant s (1+3*n)) := by
  intro hnav
  obtain ⟨p, hp⟩ := hnav
  have hQmod : gstNavigationConstant s (1+3*n) % 3 = 1 := by
    calc
      gstNavigationConstant s (1+3*n) % 3 = (1+3*n) % 3 :=
        gstNavigationConstant_mod3 s (1+3*n) hs (by omega) (by omega)
      _ = 1 := by omega
  have hp0 : p ≠ 0 := by
    intro hpz
    subst p
    have hd0 : gstDigit (gstNavigationConstant s (1+3*n)) 0 = 1 := by
      change gstNavigationConstant s (1+3*n) / 1 % 3 = 1
      simpa using hQmod
    rw [hd0] at hp
    omega
  have hp1 : 1 ≤ p := by omega
  let j := p - 1
  have hpj : p = 1 + j := by
    dsimp [j]
    omega
  have hparentDigit :
      gstDigit (gstNavigationConstant s (1+3*n)) (1+j) = 2 := by
    rw [← hpj]
    exact hp.1
  have hcarryMod : gstCarry (gstNavigationConstant s (1+3*n)) p % 3 = 0 :=
    gstGoodSpace_carry_mod3_zero _ p hp.2
  have hcarryLt : gstCarry (gstNavigationConstant s (1+3*n)) p < 4 :=
    gstCarry_lt_four _ p hp1
  have hparentCarryP :
      gstCarry (gstNavigationConstant s (1+3*n)) p = 0 ∨
      gstCarry (gstNavigationConstant s (1+3*n)) p = 3 := by
    omega
  have hparentCarry :
      gstCarry (gstNavigationConstant s (1+3*n)) (1+j) = 0 ∨
      gstCarry (gstNavigationConstant s (1+3*n)) (1+j) = 3 := by
    rw [← hpj]
    exact hparentCarryP
  have hprojection := gst_omega_parent_projection s 1 n j hs
  have hOmegaDigit : (gstOmega s 1 n j).parentDigit = 2 := by
    rw [← hprojection.1]
    simpa [Nat.pow_one] using hparentDigit
  have hOmegaCarry :
      (gstOmega s 1 n j).parentCarry = 0 ∨
      (gstOmega s 1 n j).parentCarry = 3 := by
    rcases hparentCarry with h0 | h3
    · left
      rw [← hprojection.2]
      simpa [Nat.pow_one] using h0
    · right
      rw [← hprojection.2]
      simpa [Nat.pow_one] using h3
  have hzero : GSTOmegaGatePolynomial (gstOmega s 1 n j) = 0 :=
    (gst_omega_gate_polynomial_zero_iff (gstOmega s 1 n j)).2
      ⟨hOmegaDigit, hOmegaCarry⟩
  have hnonzero := hBad j
  change GSTOmegaGatePolynomial (gstOmega s 1 n j) ≠ 0 at hnonzero
  exact hnonzero hzero

/-- A Navigation witness of `3*R` cannot occur at position zero and shifts
    exactly back to a Navigation witness of `R`. -/
theorem gstNavigationWitness_of_mul_three_atomic
    (R : Nat) (h : GSTNavigationWitness (3*R)) :
    GSTNavigationWitness R := by
  obtain ⟨p, hd, hspace⟩ := h
  cases p with
  | zero =>
      have hz : gstDigit (3*R) 0 = 0 := by
        simp [gstDigit]
      rw [hz] at hd
      omega
  | succ j =>
      have hd' : gstDigit (3*R) (j+1) = 2 := by
        simpa [Nat.succ_eq_add_one] using hd
      have hspace' :
          gstSpaceAt (3*R) (j+1) = .gstPlus ∨
          gstSpaceAt (3*R) (j+1) = .null := by
        simpa [Nat.succ_eq_add_one] using hspace
      refine ⟨j, ?_, ?_⟩
      · rw [← gstDigit_mul_three_shift R j]
        exact hd'
      · rw [← gstSpace_mul_three_shift R j]
        exact hspace'

/-- Iterated inverse shift through a forced ternary zero prefix. -/
theorem gstNavigationWitness_of_mul_three_pow_atomic
    (r R : Nat) (h : GSTNavigationWitness (3^r * R)) :
    GSTNavigationWitness R := by
  induction r generalizing R with
  | zero =>
      simpa using h
  | succ r ih =>
      have hscaled : GSTNavigationWitness (3^r * (3*R)) := by
        simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          using h
      have hthree : GSTNavigationWitness (3*R) := ih (R := 3*R) hscaled
      exact gstNavigationWitness_of_mul_three_atomic R hthree

/-- Exact iterated canonical zero-origin scaling. -/
theorem gst_navigation_constant_mul3_pow_atomic
    (s r m : Nat) (hs : 1 ≤ s) :
    gstNavigationConstant s (3^r * m) =
      3^r * gstNavigationConstant (s+r) m := by
  induction r generalizing s with
  | zero => simp
  | succ r ih =>
      have harg : 3^(r+1) * m = 3 * (3^r * m) := by
        rw [Nat.pow_succ]
        ac_rfl
      rw [harg, gst_navigation_constant_mul3 s (3^r*m) hs]
      rw [ih (s := s+1) (by omega)]
      have hidx : (s+1)+r = s+(r+1) := by omega
      rw [hidx, Nat.pow_succ]
      ac_rfl
