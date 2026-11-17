/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0569 / 1132
/-    Path         : branches/sol_phase-crossing-red-test/NavigationResidueCutScratch.lean
/-    Ref          : origin/sol/phase-crossing-red-test
/-    First-commit : 2026-08-16 03:39:00 +0530  (0ee2a2c)
/-    Last-commit  : 2026-08-16 03:39:00 +0530  (0ee2a2c)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-16 03:39:00 +0530  0ee2a2c  (ker07-dev)
/-        add canonical mod27 navigation cut scratch
/- ====================================================================== -/

import CanonicalPrefixScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
A direct canonical Navigation cut missing from the old origin classifier.
The argument is abstract in the canonical map Q and uses only exact origin
energy plus three low residues of Q(t,1).
-/

/-- At level at least two, the canonical block multiplier is one modulo 9. -/
theorem gst_canonical_block_unit_mod9S
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t : Nat) (ht : 2 ≤ t) :
    4^(3^t) % 9 = 1 := by
  have h := hQ t 1 (by omega)
  simp only [Nat.mul_one] at h
  rw [h, Nat.add_mod, Nat.mul_mod]
  have hdiv : 3^(t+1) % 9 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    rw [show (9:Nat) = 3^2 by decide]
    exact Nat.pow_dvd_pow 3 (by omega)
  rw [hdiv]
  norm_num

/-- The residue-one block multiplier is one modulo 3. -/
theorem gst_canonical_block_unit_mod3S
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t : Nat) (ht : 1 ≤ t) :
    4^(3^t) % 3 = 1 := by
  have h := hQ t 1 ht
  simp only [Nat.mul_one] at h
  rw [h, Nat.add_mod, Nat.mul_mod]
  have hdiv : 3^(t+1) % 3 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact Nat.dvd_pow_self 3 (by omega)
  rw [hdiv]
  norm_num

/-- The nested origin 4=1+3*1 has residue one modulo 9. -/
theorem gst_canonical_Q4_mod9S
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t : Nat) (ht : 2 ≤ t)
    (hQ1_9 : Q t 1 % 9 = 7)
    (hQnext1_3 : Q (t+1) 1 % 3 = 1) :
    Q t 4 % 9 = 1 := by
  have hrec := gst_canonical_prefix_recurrenceS Q hQ t 1 1 1 (by omega)
  norm_num at hrec ⊢
  rw [hrec, Nat.add_mod, Nat.mul_mod, hQ1_9]
  have hA3 : 4^(3^t) % 3 = 1 :=
    gst_canonical_block_unit_mod3S Q hQ t (by omega)
  have hthree :
      (3 * 4^(3^t) * Q (t+1) 1) % 9 = 3 := by
    have hAq3 : (4^(3^t) * Q (t+1) 1) % 3 = 1 := by
      rw [Nat.mul_mod, hA3, hQnext1_3]
      decide
    have hfactor :
        (3 * 4^(3^t) * Q (t+1) 1) % 9 =
          3 * ((4^(3^t) * Q (t+1) 1) % 3) := by
      omega
    rw [hfactor, hAq3]
  rw [hthree]
  decide

/-- The exact origin 13=1+3*4 has canonical residue 19 modulo 27. -/
theorem gst_canonical_Q13_mod27S
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (s : Nat) (hs : 2 ≤ s)
    (hQ1_27 : Q s 1 % 27 = 16)
    (hQnext1_9 : Q (s+1) 1 % 9 = 7)
    (hQnext2_3 : Q (s+2) 1 % 3 = 1) :
    Q s 13 % 27 = 19 := by
  have hQ4 : Q (s+1) 4 % 9 = 1 :=
    gst_canonical_Q4_mod9S Q hQ (s+1) (by omega)
      hQnext1_9 hQnext2_3
  have hrec := gst_canonical_prefix_recurrenceS Q hQ s 1 1 4 (by omega)
  norm_num at hrec ⊢
  rw [hrec, Nat.add_mod, Nat.mul_mod, hQ1_27]
  have hA9 : 4^(3^s) % 9 = 1 :=
    gst_canonical_block_unit_mod9S Q hQ s hs
  have hterm :
      (3 * 4^(3^s) * Q (s+1) 4) % 27 = 3 := by
    have hAq9 : (4^(3^s) * Q (s+1) 4) % 9 = 1 := by
      rw [Nat.mul_mod, hA9, hQ4]
      decide
    have hfactor :
        (3 * 4^(3^s) * Q (s+1) 4) % 27 =
          3 * ((4^(3^s) * Q (s+1) 4) % 9) := by
      omega
    rw [hfactor, hAq9]
  rw [hterm]
  decide

/-- Canonical origin causality extends the residue-13 calculation to the full
class b == 13 (mod 27). -/
theorem gst_canonical_mod27_13_residueS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (s b : Nat) (hs : 2 ≤ s)
    (hb13 : b % 27 = 13)
    (hQ1_27 : Q s 1 % 27 = 16)
    (hQnext1_9 : Q (s+1) 1 % 9 = 7)
    (hQnext2_3 : Q (s+2) 1 % 3 = 1) :
    Q s b % 27 = 19 := by
  have hprefix := gst_canonical_prefix_residueS Q hQ s b 3 (by omega)
  norm_num at hprefix
  rw [hb13] at hprefix
  exact hprefix.trans
    (gst_canonical_Q13_mod27S Q hQ s hs hQ1_27 hQnext1_9 hQnext2_3)

/-- Residue 19 modulo 27 is a fixed NULL Happy Gate at ternary position two. -/
theorem gst_residue19_is_null_gate2S
    (R : Nat) (hR : R % 27 = 19) :
    gstDigitS R 2 = 2 ∧ gstCarryS R 2 = 0 := by
  constructor
  · unfold gstDigitS
    have hdiv : R / 9 % 3 = (R % 27) / 9 := by
      omega
    rw [hdiv, hR]
    decide
  · unfold gstCarryS
    have hmod9 : R % 9 = 1 := by
      have h := Nat.mod_mod_of_dvd R (by decide : 9 ∣ 27)
      rw [hR] at h
      norm_num at h ⊢
      exact h.symm
    rw [hmod9]
    decide
