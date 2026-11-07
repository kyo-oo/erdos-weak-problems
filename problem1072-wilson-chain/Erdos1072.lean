import Erdos1072_Data
import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 262144

/-! # Erdős #1072 — THE WILSON-PAIR LAW (Kill candidate, S033)

**Problem (Erdős–Hardy–Subbarao).** f(p) = least n with n! ≡ −1 (mod p).
Open: infinitude of the Wilson-only primes (f(p) = p−1); f(p)/p → 0 a.e.

**THIS KERNEL — THE PAIRING LAW (the structure theorem for the solution
set of n! ≡ −1 (mod p)), all unconditional:**

**THEOREM (Wilson-free pairing identity, `erdos1072_pair_law`).** For every
p ≥ 2 (p = 2 or odd) and n ≤ p−1:
    n! · (p−1−n)! ≡ (−1)^{p−1−n} · (p−1)!  (mod p).
Pure induction — Wilson's theorem is NOT used.

**THEOREM (the classic Wilson-pair law, `erdos1072_wilson_pair_classic`).**
If n! ≡ −1 (mod p) and (p−1)! ≡ −1 (mod p) (the Wilson receipt), then
    (p−1−n)! ≡ (−1)^{p−1−n}  (mod p).
The solution set of n! ≡ −1 (mod p) is closed under the involution
n ↦ p−1−n with the sign law.

**Applications:** the eleven first extra-solution primes (7,3), (11,5),
(19,9), (23,14), (29,18), (43,21), (47,23), (59,15), (61,8), (67,18),
(71,7) — each a term-mode application of the general corollary with the
decide-verified receipts. The full census (2,694 instances over the 1,227
primes 5 ≤ p < 10^4, 465 Wilson-only, ZERO pair-law violations) is the
battery (battery1072.py). -/

namespace Erdos1072

/-! ## §1 The modeq toolkit (core-safe). -/
theorem addmul (x p m : Nat) : (x + p * m) ≡ x [MOD p] := by
  show (x + p * m) % p = x % p
  exact Nat.add_mul_mod_self_right x p m

theorem fm_modeq (p j : Nat) : fm p (j + 1) ≡ (j + 1) * fm p j [MOD p] := by
  show ((j + 1) * fm p j) % p % p = ((j + 1) * fm p j) % p
  exact Nat.mod_modeq _ _

theorem tm_modeq (p m : Nat) : tm p (m + 1) ≡ (p - 1 - m) * tm p m [MOD p] := by
  show ((p - 1 - m) * tm p m) % p % p = ((p - 1 - m) * tm p m) % p
  exact Nat.mod_modeq _ _

theorem modeq_eq (p a b : Nat) (ha : a < p) (hb : b < p) (h : a ≡ b [MOD p]) : a = b := by
  have h' : a % p = b % p := h
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'
  exact h'

theorem fm_lt (p : Nat) (hp : 2 ≤ p) : ∀ j, fm p j < p := by
  intro j
  induction j with
  | zero => show 1 < p; omega
  | succ j _ => show ((j + 1) * fm p j) % p < p; exact Nat.mod_lt _ (by omega : 0 < p)

theorem sgn_lt (p m : Nat) (hp : 2 ≤ p) : sgn p m < p := by
  unfold sgn
  cases Nat.mod_two_eq_zero_or_one m with
  | inl h => rw [h]; show 1 < p; omega
  | inr h => rw [h]; show p - 1 < p; omega

/-! ## §2 The sign algebra. -/
theorem sgn_sum (p m : Nat) (hp : 1 ≤ p) : sgn p m + sgn p (m + 1) = p := by
  unfold sgn
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · have h2 : (m + 1) % 2 = 1 := by omega
    rw [h, h2]
    have e1 : (if (0:Nat) = 0 then 1 else p - 1) = 1 := if_pos rfl
    have e2 : (if (1:Nat) = 0 then 1 else p - 1) = p - 1 := if_neg (by decide)
    rw [e1, e2]; omega
  · have h2 : (m + 1) % 2 = 0 := by omega
    rw [h, h2]
    have e1 : (if (1:Nat) = 0 then 1 else p - 1) = p - 1 := if_neg (by decide)
    have e2 : (if (0:Nat) = 0 then 1 else p - 1) = 1 := if_pos rfl
    rw [e1, e2]; omega

/-! ## §3 The sign-carry congruence (the engine of the tail law). -/
theorem sgn_carry (p m : Nat) (hp : 2 ≤ p) (hm : m + 1 ≤ p) :
    (p - 1 - m) * sgn p m ≡ sgn p (m + 1) * (m + 1) [MOD p] := by
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · -- m even: sgn m = 1, sgn (m+1) = p − 1
    have h1 : sgn p m = 1 := by unfold sgn; rw [h]; exact if_pos rfl
    have h2 : sgn p (m + 1) = p - 1 := by
      unfold sgn; rw [show (m + 1) % 2 = 1 by omega]; exact if_neg (by decide)
    rw [h1, h2, Nat.mul_one]
    have heq : (p - 1) * (m + 1) = (p - 1 - m) + p * m := by
      have s1 : (p - 1) * (m + 1) = (p - 1) * m + (p - 1) * 1 := Nat.mul_add (p - 1) m 1
      have s2 : (p - 1) * m + m = p * m := by
        rw [← Nat.add_mul, Nat.sub_add_cancel (by omega : 1 ≤ p)]
      rw [Nat.mul_one] at s1
      omega
    exact ((addmul (p - 1 - m) p m).symm).trans (Nat.modeq_of_eq heq)
  · -- m odd
    have h1 : sgn p m = p - 1 := by
      unfold sgn; rw [h]; exact if_neg (by decide)
    rcases Nat.eq_or_lt_of_le hm with hm2 | hm2
    · -- m + 1 = p: both sides ≡ 0
      have hm3 : m = p - 1 := by omega
      rw [hm2, hm3]
      have hz : p - 1 - (p - 1) = 0 := by omega
      rw [hz, Nat.zero_mul]
      show (0:Nat) % p = sgn p p * p % p
      rw [Nat.zero_mod, Nat.mul_mod_self_left]
    · -- m + 1 < p, i.e. m ≤ p − 2: sgn (m+1) = 1
      have h2 : sgn p (m + 1) = 1 := by
        unfold sgn; rw [show (m + 1) % 2 = 0 by omega]; exact if_pos rfl
      rw [h1, h2, Nat.one_mul]
      have heq : (p - 1 - m) * (p - 1) = (m + 1) + p * (p - m - 2) := by
        have hA : p - 1 - m + (m + 1) = p := by omega
        have hA2 : p - m - 2 = (p - 1 - m) - 1 := by omega
        have s1 : p * (p - m - 2) + p = p * (p - 1 - m) := by
          rw [hA2, Nat.mul_sub, Nat.mul_one]; omega
        have s2 : (p - 1 - m) * (p - 1) + (p - 1 - m) = (p - 1 - m) * p := by
          rw [Nat.mul_sub, Nat.mul_one]; omega
        have s3 : p * (p - 1 - m) = (p - 1 - m) * p := Nat.mul_comm _ _
        omega
      exact ((addmul (m + 1) p (p - m - 2)).symm).trans (Nat.modeq_of_eq heq)

/-! ## §4 THE TAIL LAW: tm p m ≡ sgn p m · m! (mod p), by induction. -/
theorem tail_law (p : Nat) (hp : 2 ≤ p) :
    ∀ m, m ≤ p - 1 → tm p m ≡ sgn p m * fm p m [MOD p] := by
  intro m
  induction m with
  | zero =>
    intro _
    show (1:Nat) ≡ 1 * 1 [MOD p]
    exact Nat.modeq_of_eq (by simp [fm, tm, sgn])
  | succ m ih =>
    intro hm
    have hm' : m ≤ p - 1 := by omega
    have IH := ih hm'
    have sc := sgn_carry p m hp (by omega)
    calc tm p (m + 1) ≡ (p - 1 - m) * tm p m [MOD p] := tm_modeq p m
      _ ≡ (p - 1 - m) * (sgn p m * fm p m) [MOD p] := IH.mul_left _
      _ ≡ (sgn p (m + 1) * (m + 1)) * fm p m [MOD p] :=
          (Nat.modeq_of_eq (Nat.mul_assoc _ _ _)).trans (sc.mul_right (fm p m))
      _ ≡ sgn p (m + 1) * fm p (m + 1) [MOD p] :=
          (Nat.modeq_of_eq (by ring)).trans (fm_modeq p m).symm

/-! ## §5 THE SPLIT LAW: n! · (tail of length p−1−n) ≡ (p−1)!. -/
theorem split_law (p : Nat) (hp : 2 ≤ p) (hpar : p = 2 ∨ p % 2 = 1) :
    ∀ n, n ≤ p - 1 → fm p n * tm p (p - 1 - n) ≡ fm p (p - 1) [MOD p] := by
  have hsgn1 : sgn p (p - 1) = 1 := by
    rcases hpar with h | h
    · subst h; simp [sgn]
    · have e : (p - 1) % 2 = 0 := by omega
      simp [sgn, e]
  intro n
  induction n with
  | zero =>
    intro _
    show (1:Nat) * tm p (p - 1) ≡ fm p (p - 1) [MOD p]
    rw [Nat.one_mul]
    calc tm p (p - 1) ≡ sgn p (p - 1) * fm p (p - 1) [MOD p] :=
          tail_law p hp (p - 1) (by omega)
      _ ≡ 1 * fm p (p - 1) [MOD p] := Nat.modeq_of_eq (by rw [hsgn1])
      _ ≡ fm p (p - 1) [MOD p] := Nat.modeq_of_eq (Nat.one_mul _)
  | succ n ih =>
    intro hn
    have hn' : n ≤ p - 1 := by omega
    have IH := ih hn'
    have hidx : p - 1 - n = (p - 2 - n) + 1 := by omega
    have hidx2 : p - 1 - (p - 2 - n) = n + 1 := by omega
    have htm : tm p (p - 1 - n) ≡ (n + 1) * tm p (p - 2 - n) [MOD p] := by
      have h0 := tm_modeq p (p - 2 - n)
      rw [hidx2] at h0
      rw [hidx]
      exact h0
    calc fm p (n + 1) * tm p (p - 2 - n)
        ≡ (n + 1) * fm p n * tm p (p - 2 - n) [MOD p] := (fm_modeq p n).mul_right _
      _ ≡ fm p n * ((n + 1) * tm p (p - 2 - n)) [MOD p] := Nat.modeq_of_eq (by ring)
      _ ≡ fm p n * tm p (p - 1 - n) [MOD p] := htm.mul_left _
      _ ≡ fm p (p - 1) [MOD p] := IH

/-! ## §6 THE (p−1)² ≡ 1 lemma. -/
theorem sqn (p : Nat) (hp : 2 ≤ p) : (p - 1) * (p - 1) ≡ 1 [MOD p] := by
  have he : (p - 1) * (p - 1) = p * (p - 2) + 1 := by
    have s1 : (p - 1) * (p - 1) = (p - 1) * p - (p - 1) * 1 := Nat.mul_sub (p - 1) p 1
    have s2 : (p - 1) * p = p * (p - 1) := Nat.mul_comm _ _
    have s3 : p * (p - 1) = p * (p - 2) + p * 1 := by
      rw [show p - 1 = (p - 2) + 1 by omega, Nat.mul_add, Nat.mul_one]
    rw [Nat.mul_one] at s1
    omega
  show ((p - 1) * (p - 1)) % p = (1:Nat) % p
  rw [he, Nat.add_comm, Nat.add_mul_mod_self_right]

/-! ## §7 THE MAIN THEOREM — the Wilson-free pairing identity. -/
theorem erdos1072_pair_law (p n : Nat) (hp : 2 ≤ p) (hpar : p = 2 ∨ p % 2 = 1)
    (hn : n ≤ p - 1) :
    fm p n * fm p (p - 1 - n) ≡ sgn p (p - 1 - n) * fm p (p - 1) [MOD p] := by
  have hsplit := split_law p hp hpar n hn
  have htail := tail_law p hp (p - 1 - n) (by omega)
  have key : sgn p (p - 1 - n) * (fm p n * fm p (p - 1 - n))
      ≡ fm p (p - 1) [MOD p] :=
    ((Nat.modeq_of_eq (by ring)).trans (htail.mul_left (fm p n)).symm).trans hsplit
  rcases Nat.mod_two_eq_zero_or_one (p - 1 - n) with hq | hq
  · have hs : sgn p (p - 1 - n) = 1 := by unfold sgn; rw [hq]; exact if_pos rfl
    rw [hs, Nat.one_mul] at key ⊢
    exact key
  · have hs : sgn p (p - 1 - n) = p - 1 := by
      unfold sgn; rw [hq]; exact if_neg (by decide)
    rw [hs] at key ⊢
    have hX : fm p n * fm p (p - 1 - n)
        ≡ (p - 1) * (p - 1) * (fm p n * fm p (p - 1 - n)) [MOD p] :=
      (((sqn p hp).mul_right _).trans (Nat.modeq_of_eq (Nat.one_mul _))).symm
    have hstep := key.mul_left (p - 1)
    exact hX.trans ((Nat.modeq_of_eq (by ring)).trans hstep)

/-! ## §8 THE CLASSIC COROLLARY — the Wilson-pair law. -/
theorem erdos1072_wilson_pair_classic (p n : Nat) (hp : 2 ≤ p)
    (hpar : p = 2 ∨ p % 2 = 1) (hn : n + 1 ≤ p - 1)
    (hW : fm p (p - 1) = p - 1) (h : fm p n = p - 1) :
    fm p (p - 1 - n) = sgn p (p - 1 - n) := by
  have hpair := erdos1072_pair_law p n hp hpar (by omega)
  rw [h, hW] at hpair
  rcases Nat.mod_two_eq_zero_or_one (p - 1 - n) with hq | hq
  · have hs : sgn p (p - 1 - n) = 1 := by unfold sgn; rw [hq]; exact if_pos rfl
    rw [hs, Nat.one_mul] at hpair
    have hY : fm p (p - 1 - n)
        ≡ (p - 1) * (p - 1) * fm p (p - 1 - n) [MOD p] :=
      (((sqn p hp).mul_right _).trans (Nat.modeq_of_eq (Nat.one_mul _))).symm
    have h2 : (p - 1) * (p - 1) * fm p (p - 1 - n)
        ≡ (p - 1) * (p - 1) [MOD p] :=
      (Nat.modeq_of_eq (by ring)).trans (hpair.mul_left (p - 1))
    have hfinal : fm p (p - 1 - n) ≡ 1 [MOD p] := (hY.trans h2).trans (sqn p hp)
    exact modeq_eq p _ _ (fm_lt p hp _) (by omega) hfinal
  · have hs : sgn p (p - 1 - n) = p - 1 := by
      unfold sgn; rw [hq]; exact if_neg (by decide)
    rw [hs, Nat.one_mul] at hpair
    have hY : fm p (p - 1 - n)
        ≡ (p - 1) * (p - 1) * fm p (p - 1 - n) [MOD p] :=
      (((sqn p hp).mul_right _).trans (Nat.modeq_of_eq (Nat.one_mul _))).symm
    have h2 : (p - 1) * (p - 1) * fm p (p - 1 - n)
        ≡ (p - 1) * (p - 1) * (p - 1) [MOD p] :=
      (Nat.modeq_of_eq (by ring)).trans (hpair.mul_left (p - 1))
    have h3 : (p - 1) * (p - 1) * (p - 1) ≡ (p - 1) [MOD p] :=
      ((Nat.modeq_of_eq (by ring)).trans (sqn p hp).mul_right (p - 1)).trans
        (Nat.modeq_of_eq (Nat.one_mul _))
    exact modeq_eq p _ _ (fm_lt p hp _) (sgn_lt p _ hp) ((hY.trans h2).trans h3)

/-! ## §9 THE NAMED APPLICATIONS (term-mode, receipts from Data). -/
theorem erdos1072_pair_7   : fm 7 3   = sgn 7 3   := by
  simpa using erdos1072_wilson_pair_classic 7 3 (by norm_num) (by decide)
    (by norm_num) Erdos1072Data.wilson_7 Erdos1072Data.inst_7_3
theorem erdos1072_pair_11  : fm 11 5  = sgn 11 5  := by
  simpa using erdos1072_wilson_pair_classic 11 5 (by norm_num) (by decide)
    (by norm_num) Erdos1072Data.wilson_11 Erdos1072Data.inst_11_5
theorem erdos1072_pair_19  : fm 19 9  = sgn 19 9  := by
  simpa using erdos1072_wilson_pair_classic 19 9 (by norm_num) (by decide)
    (by norm_num) Erdos1072Data.wilson_19 Erdos1072Data.inst_19_9
theorem erdos1072_pair_23  : fm 23 8  = sgn 23 8  := by
  simpa using erdos1072_wilson_pair_classic 23 14 (by norm_num) (by decide)
    (by norm_num) Erdos1072Data.wilson_23 Erdos1072Data.inst_23_14
theorem erdos1072_pair_29  : fm 29 10 = sgn 29 10 := by
  simpa using erdos1072_wilson_pair_classic 29 18 (by norm_num) (by decide)
    (by norm_num) Erdos1072Data.wilson_29 Erdos1072Data.inst_29_18
theorem erdos1072_pair_43  : fm 43 21 = sgn 43 21 := by
  simpa using erdos1072_wilson_pair_classic 43 21 (by norm_num) (by decide)
    (by norm_num) Erdos1072Data.wilson_43 Erdos1072Data.inst_43_21
theorem erdos1072_pair_47  : fm 47 23 = sgn 47 23 := by
  simpa using erdos1072_wilson_pair_classic 47 23 (by norm_num) (by decide)
    (by norm_num) Erdos1072Data.wilson_47 Erdos1072Data.inst_47_23
theorem erdos1072_pair_59  : fm 59 43 = sgn 59 43 := by
  simpa using erdos1072_wilson_pair_classic 59 15 (by norm_num) (by decide)
    (by norm_num) Erdos1072Data.wilson_59 Erdos1072Data.inst_59_15
theorem erdos1072_pair_61  : fm 61 52 = sgn 61 52 := by
  simpa using erdos1072_wilson_pair_classic 61 8 (by norm_num) (by decide)
    (by norm_num) Erdos1072Data.wilson_61 Erdos1072Data.inst_61_8
theorem erdos1072_pair_67  : fm 67 48 = sgn 67 48 := by
  simpa using erdos1072_wilson_pair_classic 67 18 (by norm_num) (by decide)
    (by norm_num) Erdos1072Data.wilson_67 Erdos1072Data.inst_67_18
theorem erdos1072_pair_71  : fm 71 63 = sgn 71 63 := by
  simpa using erdos1072_wilson_pair_classic 71 7 (by norm_num) (by decide)
    (by norm_num) Erdos1072Data.wilson_71 Erdos1072Data.inst_71_7

/-! ## §10 THE ARSENAL BRIDGE (erdosternary2 + HC-PROOF applied to the
census primes' own ternary profiles). -/
theorem erdos1072_arsenal_bridge :
    [71 % 3, (71 / 3) % 3, (71 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    carryAtPos 61 1 < 4 ∧ carryAtPos 67 2 < 4 ∧
    v2r (3 ^ 1 * 24) = v2r 24 :=
  ⟨by decide, carryAtPos_bound 61 1, carryAtPos_bound 67 2,
    CardinalWorldsV2.v2r_ternary_scaling 1 24⟩

#eval "ERDOS1072_KERNEL_GREEN"
#print axioms erdos1072_pair_law
#print axioms erdos1072_wilson_pair_classic
#print axioms erdos1072_pair_7
#print axioms erdos1072_pair_23
#print axioms erdos1072_pair_71
#print axioms erdos1072_arsenal_bridge

end Erdos1072
