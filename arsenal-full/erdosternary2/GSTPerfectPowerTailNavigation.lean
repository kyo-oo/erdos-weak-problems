import GSTCanonicalTailStateIso
import GSTCanonicalTailLTE

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTPerfectPowerTailNavigation

open GSTCanonicalTailStateIso
open GSTCanonicalTailLTE

/-- The canonical GST quotient below the forced `s+1` ternary prefix. -/
def canonicalTail (s b : Nat) : Nat :=
  4^(3^s * b) / 3^(s+1)

/-- Exact perfect-power decomposition `4^(3^s b) = 1 + 3^(s+1) Q_s(b)`. -/
theorem canonical_tail_decomposition (s b : Nat) :
    4^(3^s * b) = 1 + 3^(s+1) * canonicalTail s b := by
  have hmod : 4^(3^s * b) % 3^(s+1) = 1 :=
    pow4_scaled_mod_next s b
  have hsplit := Nat.mod_add_div (4^(3^s * b)) (3^(s+1))
  rw [hmod] at hsplit
  simpa [canonicalTail] using hsplit.symm

/-- The ternary digit at `p` is determined by the residue modulo the next place. -/
theorem digit3_eq_next_residue_div (R p : Nat) :
    digit3 R p = (R % 3^(p+1)) / 3^p := by
  unfold digit3
  rw [Nat.pow_succ]
  rw [Nat.mod_mul]
  have hM : 0 < 3^p := Nat.pow_pos (by decide)
  rw [Nat.add_mul_div_left _ _ hM]
  rw [Nat.div_eq_of_lt (Nat.mod_lt _ hM), Nat.zero_add]

/-- The forced prefix `1,0,...,0` below a canonical cut contains no Happy gate. -/
theorem forced_prefix_not_happy
    (cut Q p : Nat) (hcut : 2 ≤ cut) (hp : p < cut) :
    ¬ HappyCell
        (carry4 (1 + 3^cut * Q) p)
        (digit3 (1 + 3^cut * Q) p) := by
  intro hHappy
  have hd : digit3 (1 + 3^cut * Q) p = 2 := hHappy.1
  have hbig : 1 < 3^cut := (one_prefix_bounds cut hcut).1
  have hmodCut : (1 + 3^cut * Q) % 3^cut = 1 := by
    simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hbig]
  have hdvd : 3^(p+1) ∣ 3^cut :=
    Nat.pow_dvd_pow 3 (by omega)
  have hsmall : 1 < 3^(p+1) := by
    have h3 : 3 ≤ 3^(p+1) := by
      simpa using (Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (show 1 ≤ p+1 by omega))
    omega
  have hm := Nat.mod_mod_of_dvd (1 + 3^cut * Q) hdvd
  rw [hmodCut, Nat.mod_eq_of_lt hsmall] at hm
  have hmodSmall : (1 + 3^cut * Q) % 3^(p+1) = 1 := hm.symm
  rw [digit3_eq_next_residue_div, hmodSmall] at hd
  by_cases hp0 : p = 0
  · subst p
    norm_num at hd
  · have hp1 : 1 ≤ p := by omega
    have h3p : 3 ≤ 3^p := by
      simpa using (Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat)) hp1)
    have hdiv0 : 1 / 3^p = 0 := Nat.div_eq_of_lt (by omega)
    rw [hdiv0] at hd
    norm_num at hd

/-- Every Happy witness of a canonical perfect power lies at or above its GST cut. -/
theorem perfect_power_happy_position_ge_cut
    (s b p : Nat) (hs : 1 ≤ s)
    (hHappy : HappyCell
      (carry4 (4^(3^s * b)) p)
      (digit3 (4^(3^s * b)) p)) :
    s + 1 ≤ p := by
  by_contra hnot
  have hp : p < s+1 := by omega
  have h := hHappy
  rw [canonical_tail_decomposition s b] at h
  exact forced_prefix_not_happy (s+1) (canonicalTail s b) p (by omega) hp h

/-- Canonical Tail Projection Theorem.
Navigation of the full perfect power projects exactly to Navigation of `Q_s(b)`. -/
theorem canonical_tail_projection
    (s b : Nat) (hs : 1 ≤ s)
    (hNav : Navigation (4^(3^s * b))) :
    Navigation (canonicalTail s b) := by
  obtain ⟨p, hHappy⟩ := hNav
  have hpge : s+1 ≤ p :=
    perfect_power_happy_position_ge_cut s b p hs hHappy
  let j := p - (s+1)
  have hpEq : p = s+1+j := by
    dsimp [j]
    omega
  refine ⟨j, ?_⟩
  apply (canonical_tail_happy_iff (s+1) (canonicalTail s b) j (by omega)).1
  have h := hHappy
  rw [canonical_tail_decomposition s b] at h
  rw [hpEq] at h
  exact h

end GSTPerfectPowerTailNavigation
