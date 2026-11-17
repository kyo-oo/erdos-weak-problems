/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0423 / 1132
/-    Path         : branches/sol_physical-phase-crossing-surgery-plan/CanonicalCausalityScratch.lean
/-    Ref          : origin/sol/physical-phase-crossing-surgery-plan
/-    First-commit : 2026-08-15 20:27:28 +0530  (91309e8)
/-    Last-commit  : 2026-08-15 20:27:28 +0530  (91309e8)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-15 20:27:28 +0530  91309e8  (ker07-dev)
/-        Formalize exact GST state causality from finite origin prefixes
/- ====================================================================== -/

import CanonicalPrefixScratch
import InformationDescentScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- A ternary digit is exactly the corresponding one-trit quotient of the
    prefix residue through that digit. -/
theorem gstDigitS_eq_prefix_residue_divS (R j : Nat) :
    gstDigitS R j = (R % 3^(j+1)) / 3^j := by
  unfold gstDigitS
  rw [Nat.pow_succ]
  rw [Nat.mod_mul]
  have hp : 0 < 3^j := Nat.pow_pos (by decide)
  rw [Nat.add_mul_div_left _ _ hp]
  have hr : R % 3^j < 3^j := Nat.mod_lt _ hp
  rw [Nat.div_eq_of_lt hr]
  simp

/-- Equality through ternary depth j+1 preserves the complete GST vertex at j:
    both the input digit and the incoming multiply-by-four carry. -/
theorem gst_state_eq_of_prefix_residueS
    (R S j : Nat)
    (hres : R % 3^(j+1) = S % 3^(j+1)) :
    gstDigitS R j = gstDigitS S j ∧
      gstCarryS R j = gstCarryS S j := by
  constructor
  · rw [gstDigitS_eq_prefix_residue_divS,
        gstDigitS_eq_prefix_residue_divS, hres]
  · have hdvd : 3^j ∣ 3^(j+1) :=
      Nat.pow_dvd_pow 3 (by omega)
    have hlow : R % 3^j = S % 3^j := by
      calc
        R % 3^j = (R % 3^(j+1)) % 3^j := by
          rw [Nat.mod_mod_of_dvd R hdvd]
        _ = (S % 3^(j+1)) % 3^j := by rw [hres]
        _ = S % 3^j := Nat.mod_mod_of_dvd S hdvd
    unfold gstCarryS
    rw [hlow]

/-- Canonical origin causality at one exact GST vertex: the state at position j
    depends only on n modulo 3^(j+1). -/
theorem gst_canonical_state_from_origin_prefixS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t n j : Nat) (ht : 1 ≤ t) :
    let a := n % 3^(j+1)
    gstDigitS (Q t n) j = gstDigitS (Q t a) j ∧
      gstCarryS (Q t n) j = gstCarryS (Q t a) j := by
  dsimp only
  apply gst_state_eq_of_prefix_residueS
  exact gst_canonical_prefix_residueS Q hQ t n (j+1) ht

/-- A canonical child Happy Gate is already present in the finite origin prefix
    that ends exactly at the gate's causal depth. -/
theorem gst_canonical_gate_from_origin_prefixS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t n j : Nat) (ht : 1 ≤ t)
    (hgate : gstDigitS (Q t n) j = 2 ∧
      (gstCarryS (Q t n) j = 0 ∨ gstCarryS (Q t n) j = 3)) :
    let a := n % 3^(j+1)
    gstDigitS (Q t a) j = 2 ∧
      (gstCarryS (Q t a) j = 0 ∨ gstCarryS (Q t a) j = 3) := by
  dsimp only
  have hs := gst_canonical_state_from_origin_prefixS Q hQ t n j ht
  constructor
  · rw [← hs.1]
    exact hgate.1
  · rcases hgate.2 with h0 | h3
    · left
      rw [← hs.2]
      exact h0
    · right
      rw [← hs.2]
      exact h3
