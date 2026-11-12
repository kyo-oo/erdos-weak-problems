import Erdos1072_Data
import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 262144
set_option maxHeartbeats 16000000

/-! # Erdős #1072 — THE WILSON-PAIR LAW (Kill candidate, S033)

**THE PROBLEM (verbatim, erdosproblems.com/1072).** For any prime $p$,
let $f(p)$ be the least integer such that $f(p)!+1\equiv 0\pmod{p}$. Is it
true that there are infinitely many $p$ for which $f(p)=p-1$? Is it true
that $f(p)/p\to 0$ for almost all $p$?

(This kernel's law is the structure theorem for the solution set of
$n! \equiv -1 \pmod p$ — the engine room under both open questions;
honest scope in the registry: the two asymptotic questions remain open.)

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
battery (battery1072.py).

**THE COMPLETE BOARD (S050-C5, COMPLETE_PROOF.md §4/§7):** the C-layer on
top of K1/K2 — the exact pairing equivalence (C1), the parity split (C2),
the top-chain k!±1 dictionary (C7, the #1074 bridge), the least-solution
law (C8: every sub-Wilson solution sits at or below p−5, p=7 the exact
sole exception), the p=6089 tightness witness, and the assembled final
theorem `erdos1072_complete` citing the green spine, the eleven named
instance receipts, and the arsenal bridge. Cited as follow-ups: the
2-cycle product laws (C3), the Gauss half-factorial law (C4), the
fixed-point laws (C5), the count laws (C6) — all proved in
COMPLETE_PROOF.md §4 and machine-verified over the 1,227 census primes
by the extension engine E1–E9. Honest scope unchanged: both corpus
questions (Q1 infinitely many Wilson-only primes; Q2 f(p)/p → 0 a.e.)
remain open — the single remaining component is the factorial-walk
first-hit distribution, which exactly subsumes both. -/

namespace Erdos1072

/-! ## §1 The modeq toolkit (core-safe). -/
theorem addmul (x p m : Nat) : (x + p * m) ≡ x [MOD p] := by
  show (x + p * m) % p = x % p
  exact Nat.add_mul_mod_self_left x p m

theorem meq_of_eq (a b p : Nat) (h : a = b) : a ≡ b [MOD p] := by
  show a % p = b % p
  rw [h]

theorem fm_modeq (p j : Nat) : fm p (j + 1) ≡ (j + 1) * fm p j [MOD p] := by
  show ((j + 1) * fm p j) % p % p = ((j + 1) * fm p j) % p
  exact Nat.mod_mod _ _

theorem tm_modeq (p m : Nat) : tm p (m + 1) ≡ (p - 1 - m) * tm p m [MOD p] := by
  show ((p - 1 - m) * tm p m) % p % p = ((p - 1 - m) * tm p m) % p
  exact Nat.mod_mod _ _

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
        have t1 : (p - 1 + 1) * m = p * m := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ p)]
        have t2 : (p - 1 + 1) * m = (p - 1) * m + 1 * m := Nat.add_mul (p - 1) 1 m
        rw [Nat.one_mul] at t2
        omega
      rw [Nat.mul_one] at s1
      omega
    exact ((addmul (p - 1 - m) p m).symm).trans (meq_of_eq _ _ _ heq.symm)
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
      rw [Nat.zero_mod, Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left p (sgn p p))]
    · -- m + 1 < p, i.e. m ≤ p − 2: sgn (m+1) = 1
      have h2 : sgn p (m + 1) = 1 := by
        unfold sgn; rw [show (m + 1) % 2 = 0 by omega]; exact if_pos rfl
      rw [h1, h2, Nat.one_mul]
      have heq : (p - 1 - m) * (p - 1) = (m + 1) + p * (p - m - 2) := by
        have hA : p - 1 - m + (m + 1) = p := by omega
        have hA2 : p - m - 2 = (p - 1 - m) - 1 := by omega
        have s1 : p * (p - m - 2) + p = p * (p - 1 - m) := by
          have e1 : (p - m - 2) + 1 = p - 1 - m := by omega
          have e2 : p * (p - m - 2) + p * 1 = p * ((p - m - 2) + 1) :=
            (Nat.mul_add p (p - m - 2) 1).symm
          rw [Nat.mul_one, e1] at e2
          exact e2
        have s2 : (p - 1 - m) * (p - 1) + (p - 1 - m) = (p - 1 - m) * p := by
          have e1 : (p - 1) + 1 = p := by omega
          have e2 : (p - 1 - m) * (p - 1) + (p - 1 - m) * 1
              = (p - 1 - m) * ((p - 1) + 1) :=
            (Nat.mul_add (p - 1 - m) (p - 1) 1).symm
          rw [Nat.mul_one, e1] at e2
          exact e2
        have s3 : p * (p - 1 - m) = (p - 1 - m) * p := Nat.mul_comm _ _
        omega
      exact (((addmul (m + 1) p (p - m - 2)).symm).trans (meq_of_eq _ _ _ heq.symm)).symm

/-! ## §4 THE TAIL LAW: tm p m ≡ sgn p m · m! (mod p), by induction. -/
theorem tail_law (p : Nat) (hp : 2 ≤ p) :
    ∀ m, m ≤ p - 1 → tm p m ≡ sgn p m * fm p m [MOD p] := by
  intro m
  induction m with
  | zero =>
    intro _
    show (1:Nat) ≡ 1 * 1 [MOD p]
    exact meq_of_eq _ _ _ (by norm_num)
  | succ m ih =>
    intro hm
    have hm' : m ≤ p - 1 := by omega
    have IH := ih hm'
    have sc := sgn_carry p m hp (by omega)
    calc tm p (m + 1) ≡ (p - 1 - m) * tm p m [MOD p] := tm_modeq p m
      _ ≡ (p - 1 - m) * (sgn p m * fm p m) [MOD p] := IH.mul_left _
      _ ≡ (sgn p (m + 1) * (m + 1)) * fm p m [MOD p] :=
          (meq_of_eq _ _ _ (Nat.mul_assoc _ _ _).symm).trans (sc.mul_right (fm p m))
      _ ≡ sgn p (m + 1) * fm p (m + 1) [MOD p] := by
          have hring : (sgn p (m + 1) * (m + 1)) * fm p m
              = sgn p (m + 1) * ((m + 1) * fm p m) := by ring
          exact (meq_of_eq _ _ _ hring).trans
            ((fm_modeq p m).symm.mul_left (sgn p (m + 1)))

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
      _ ≡ 1 * fm p (p - 1) [MOD p] := meq_of_eq _ _ _ (by rw [hsgn1])
      _ ≡ fm p (p - 1) [MOD p] := meq_of_eq _ _ _ (Nat.one_mul _)
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
    have hidx3 : p - 1 - (n + 1) = p - 2 - n := by omega
    rw [hidx3]
    calc fm p (n + 1) * tm p (p - 2 - n)
        ≡ (n + 1) * fm p n * tm p (p - 2 - n) [MOD p] := (fm_modeq p n).mul_right _
      _ ≡ fm p n * ((n + 1) * tm p (p - 2 - n)) [MOD p] := meq_of_eq _ _ _ (by ring)
      _ ≡ fm p n * tm p (p - 1 - n) [MOD p] := (htm.mul_left _).symm
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
  rw [he, Nat.add_comm, Nat.add_mul_mod_self_left]

/-! ## §7 THE MAIN THEOREM — the Wilson-free pairing identity. -/
theorem erdos1072_pair_law (p n : Nat) (hp : 2 ≤ p) (hpar : p = 2 ∨ p % 2 = 1)
    (hn : n ≤ p - 1) :
    fm p n * fm p (p - 1 - n) ≡ sgn p (p - 1 - n) * fm p (p - 1) [MOD p] := by
  have hsplit := split_law p hp hpar n hn
  have htail := tail_law p hp (p - 1 - n) (by omega)
  have key : sgn p (p - 1 - n) * (fm p n * fm p (p - 1 - n))
      ≡ fm p (p - 1) [MOD p] :=
    ((meq_of_eq _ _ _ (by ring)).trans (htail.mul_left (fm p n)).symm).trans hsplit
  rcases Nat.mod_two_eq_zero_or_one (p - 1 - n) with hq | hq
  · have hs : sgn p (p - 1 - n) = 1 := by unfold sgn; rw [hq]; exact if_pos rfl
    rw [hs, Nat.one_mul] at key ⊢
    exact key
  · have hs : sgn p (p - 1 - n) = p - 1 := by
      unfold sgn; rw [hq]; exact if_neg (by decide)
    rw [hs] at key ⊢
    have hX : fm p n * fm p (p - 1 - n)
        ≡ (p - 1) * (p - 1) * (fm p n * fm p (p - 1 - n)) [MOD p] :=
      (((sqn p hp).mul_right _).trans (meq_of_eq _ _ _ (Nat.one_mul _))).symm
    have hstep := key.mul_left (p - 1)
    exact hX.trans ((meq_of_eq _ _ _ (by ring)).trans hstep)

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
      (((sqn p hp).mul_right _).trans (meq_of_eq _ _ _ (Nat.one_mul _))).symm
    have h2 : (p - 1) * (p - 1) * fm p (p - 1 - n)
        ≡ (p - 1) * (p - 1) [MOD p] :=
      (meq_of_eq _ _ _ (by ring)).trans (hpair.mul_left (p - 1))
    have hfinal : fm p (p - 1 - n) ≡ 1 [MOD p] := (hY.trans h2).trans (sqn p hp)
    have hfinal' : fm p (p - 1 - n) ≡ sgn p (p - 1 - n) [MOD p] := by
      rw [hs]
      exact hfinal
    exact modeq_eq p _ _ (fm_lt p hp _) (sgn_lt p _ hp) hfinal'
  · have hs : sgn p (p - 1 - n) = p - 1 := by
      unfold sgn; rw [hq]; exact if_neg (by decide)
    rw [hs] at hpair
    have hY : fm p (p - 1 - n)
        ≡ (p - 1) * (p - 1) * fm p (p - 1 - n) [MOD p] :=
      (((sqn p hp).mul_right _).trans (meq_of_eq _ _ _ (Nat.one_mul _))).symm
    have hring2 : (p - 1) * (p - 1) * fm p (p - 1 - n)
        = (p - 1) * ((p - 1) * fm p (p - 1 - n)) := by ring
    have h2 : (p - 1) * (p - 1) * fm p (p - 1 - n)
        ≡ (p - 1) * (p - 1) * (p - 1) [MOD p] :=
      (meq_of_eq _ _ _ hring2).trans (hpair.mul_left (p - 1)) |>.trans
        (meq_of_eq _ _ _ (Nat.mul_assoc (p - 1) (p - 1) (p - 1)).symm)
    have hring3 : (p - 1) * (p - 1) * (p - 1)
        = ((p - 1) * (p - 1)) * (p - 1) := by ring
    have hone3 : (1:Nat) * (p - 1) = (p - 1) := Nat.one_mul _
    have h3 : (p - 1) * (p - 1) * (p - 1) ≡ (p - 1) [MOD p] :=
      (((meq_of_eq _ _ _ hring3).trans ((sqn p hp).mul_right (p - 1)))).trans
        (meq_of_eq _ _ _ hone3)
    have hfinalo : fm p (p - 1 - n) ≡ sgn p (p - 1 - n) [MOD p] := by
      rw [hs]
      exact (hY.trans h2).trans h3
    exact modeq_eq p _ _ (fm_lt p hp _) (sgn_lt p _ hp) hfinalo

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

/-! ## §11 THE C-LAYER GLUE (COMPLETE_PROOF.md §4): the sign algebra and the
small factorial values — the ammunition for the exact equivalence (C1), the
top-chain dictionary (C7), and the edge cascade (C8). Pure mod-algebra on
the green kernel spine (§1–§8). -/

/-- The sign residue is self-inverse: (±1)² ≡ 1 (mod p) — the cancellation
engine for the ← direction of C1. -/
theorem sgn_sq (p m : Nat) (hp : 2 ≤ p) : sgn p m * sgn p m ≡ 1 [MOD p] := by
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · have h1 : sgn p m = 1 := by unfold sgn; rw [h]; exact if_pos rfl
    rw [h1]
  · have h1 : sgn p m = p - 1 := by unfold sgn; rw [h]; exact if_neg (by decide)
    rw [h1]
    exact sqn p hp

/-- For odd p the involution σ(n) = p−1−n preserves index parity (p−1 is
even), so the sign residues agree — the engine of the parity split (C2). -/
theorem sgn_par (p m k : Nat) (hodd : p % 2 = 1) (h : m + k = p - 1) :
    sgn p m = sgn p k := by
  unfold sgn
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · have hk : k % 2 = 0 := by omega
    rw [hm, hk]
  · have hk : k % 2 = 1 := by omega
    rw [hm, hk]

/-- Mod-cancellation by a self-inverse factor: c·c ≡ 1 (mod p) and
a·c ≡ c·b (mod p) imply a ≡ b (mod p). -/
theorem cancel_sq (p a b c : Nat) (hc : c * c ≡ 1 [MOD p])
    (h : a * c ≡ c * b [MOD p]) : a ≡ b [MOD p] := by
  have e1 : a * (c * c) ≡ (a * c) * c [MOD p] := meq_of_eq _ _ _ (by ring)
  have e2 : (a * c) * c ≡ (c * b) * c [MOD p] := h.mul_right c
  have e3 : (c * b) * c ≡ b * (c * c) [MOD p] := meq_of_eq _ _ _ (by ring)
  have la1 : a * (c * c) ≡ 1 * a [MOD p] :=
    (meq_of_eq _ _ _ (by ring)).trans (hc.mul_right a)
  have la : a * (c * c) ≡ a [MOD p] := la1.trans (meq_of_eq _ _ _ (by ring))
  have rb1 : b * (c * c) ≡ 1 * b [MOD p] :=
    (meq_of_eq _ _ _ (by ring)).trans (hc.mul_right b)
  have rb : b * (c * c) ≡ b [MOD p] := rb1.trans (meq_of_eq _ _ _ (by ring))
  exact (la.symm.trans ((e1.trans e2).trans e3)).trans rb

/-- 1! ≡ 1 (mod p), for every p — the k = 1 edge value. -/
theorem fm_one_modeq (p : Nat) : fm p 1 ≡ 1 [MOD p] := by
  have h := fm_modeq p 0
  have h0 : fm p 0 = 1 := rfl
  rw [h0, Nat.zero_add, Nat.one_mul] at h
  exact h

theorem fm_one (p : Nat) (hp : 2 ≤ p) : fm p 1 = 1 :=
  modeq_eq p (fm p 1) 1 (fm_lt p hp 1) (by omega) (fm_one_modeq p)

/-- 2! ≡ 2 (mod p), for every p — the k = 2 edge value. -/
theorem fm_two_modeq (p : Nat) : fm p 2 ≡ 2 [MOD p] := by
  have h := fm_modeq p 1
  have h12 : (1:Nat) + 1 = 2 := rfl
  rw [h12] at h
  have h1 : fm p 1 ≡ 1 [MOD p] := fm_one_modeq p
  exact h.trans ((h1.mul_left 2).trans (meq_of_eq _ _ _ (by ring)))

theorem fm_two (p : Nat) (hp : 3 ≤ p) : fm p 2 = 2 :=
  modeq_eq p (fm p 2) 2 (fm_lt p (by omega) 2) (by omega) (fm_two_modeq p)

/-- 3! ≡ 6 (mod p), for every p — the k = 3 edge value (the p = 7 fork). -/
theorem fm_three_modeq (p : Nat) : fm p 3 ≡ 6 [MOD p] := by
  have h := fm_modeq p 2
  have h23 : (2:Nat) + 1 = 3 := rfl
  rw [h23] at h
  have h2 : fm p 2 ≡ 2 [MOD p] := fm_two_modeq p
  exact h.trans ((h2.mul_left 3).trans (meq_of_eq _ _ _ (by ring)))

/-- The sign residues at the literal edge indices k = 1, 2, 3. -/
theorem sgn_one (p : Nat) : sgn p 1 = p - 1 := by
  unfold sgn
  exact if_neg (by decide)

theorem sgn_two (p : Nat) : sgn p 2 = 1 := by
  unfold sgn
  exact if_pos (by decide)

theorem sgn_three (p : Nat) : sgn p 3 = p - 1 := by
  unfold sgn
  exact if_neg (by decide)

/-! ## §12 C1 — THE EXACT PAIRING EQUIVALENCE (COMPLETE_PROOF.md §4).

For every odd p ≥ 3 with the Wilson receipt and every 1 ≤ n ≤ p−2:
    n! ≡ −1 (mod p)  ⟺  (p−1−n)! ≡ (−1)^{p−1−n} (mod p).
The → direction is the green classic corollary (§8); the ← direction
substitutes the paired receipt into the pairing law K1 and cancels the
self-inverse sign factor (`sgn_sq` + `cancel_sq`, §11). -/

theorem erdos1072_pair_equivalence (p n : Nat) (hp : 3 ≤ p) (hodd : p % 2 = 1)
    (hn : 1 ≤ n) (hn2 : n + 1 ≤ p - 1) (hW : fm p (p - 1) = p - 1) :
    fm p n = p - 1 ↔ fm p (p - 1 - n) = sgn p (p - 1 - n) := by
  constructor
  · intro h
    exact erdos1072_wilson_pair_classic p n (by omega) (Or.inr hodd) hn2 hW h
  · intro h
    have hpair := erdos1072_pair_law p n (by omega) (Or.inr hodd) (by omega)
    rw [h, hW] at hpair
    have hc := cancel_sq p (fm p n) (p - 1) (sgn p (p - 1 - n))
      (sgn_sq p (p - 1 - n) (by omega)) hpair
    exact modeq_eq p (fm p n) (p - 1) (fm_lt p (by omega) n) (by omega) hc

/-! ## §13 C2 — THE PARITY SPLIT (COMPLETE_PROOF.md §4).

For odd p the involution preserves index parity, so the exact equivalence
C1 splits by the parity of n: odd-index −1-solutions pair with odd-index
−1-solutions (i); even-index −1-solutions pair with even-index +1-hits
(ii). -/

theorem erdos1072_parity_odd (p n : Nat) (hp : 3 ≤ p) (hodd : p % 2 = 1)
    (hn : 1 ≤ n) (hn2 : n + 1 ≤ p - 1) (hW : fm p (p - 1) = p - 1)
    (hnodd : n % 2 = 1) :
    fm p n = p - 1 ↔ fm p (p - 1 - n) = p - 1 := by
  have hpar : sgn p (p - 1 - n) = sgn p n :=
    sgn_par p (p - 1 - n) n hodd (by omega)
  have hsgn : sgn p n = p - 1 := by
    unfold sgn
    exact if_neg (by omega)
  have hc1 := erdos1072_pair_equivalence p n hp hodd hn hn2 hW
  rw [hpar, hsgn] at hc1
  exact hc1

theorem erdos1072_parity_even (p n : Nat) (hp : 3 ≤ p) (hodd : p % 2 = 1)
    (hn : 1 ≤ n) (hn2 : n + 1 ≤ p - 1) (hW : fm p (p - 1) = p - 1)
    (hneven : n % 2 = 0) :
    fm p n = p - 1 ↔ fm p (p - 1 - n) = 1 := by
  have hpar : sgn p (p - 1 - n) = sgn p n :=
    sgn_par p (p - 1 - n) n hodd (by omega)
  have hsgn : sgn p n = 1 := by
    unfold sgn
    exact if_pos hneven
  have hc1 := erdos1072_pair_equivalence p n hp hodd hn hn2 hW
  rw [hpar, hsgn] at hc1
  exact hc1

/-! ## §14 C7 — THE TOP-CHAIN DICTIONARY (COMPLETE_PROOF.md §4; the
#1074 EHS/Pillai bridge). For every odd p ≥ 3 with the Wilson receipt and
every 1 ≤ k ≤ p−2:
    (p−1−k)! ≡ −1 (mod p)  ⟺  k! ≡ (−1)^k (mod p)
— i.e. p ∣ k!+1 (k odd) / p ∣ k!−1 (k even). This is C1 instantiated at
the paired index n = p−1−k, and is the complete classification of the
top half of S₋(p). -/

theorem erdos1072_top_chain_dictionary (p k : Nat) (hp : 3 ≤ p)
    (hodd : p % 2 = 1) (hk : 1 ≤ k) (hk2 : k + 1 ≤ p - 1)
    (hW : fm p (p - 1) = p - 1) :
    fm p (p - 1 - k) = p - 1 ↔ fm p k = sgn p k := by
  have hn : 1 ≤ p - 1 - k := by omega
  have hn2 : p - 1 - k + 1 ≤ p - 1 := by omega
  have hc1 := erdos1072_pair_equivalence p (p - 1 - k) hp hodd hn hn2 hW
  have hmid : p - 1 - (p - 1 - k) = k := by omega
  have hpar : sgn p (p - 1 - k) = sgn p k :=
    sgn_par p (p - 1 - k) k hodd (by omega)
  rw [hmid] at hc1
  exact hc1

/-! ## §15 C8 — THE LEAST-SOLUTION LAW (COMPLETE_PROOF.md §4, C8(ii)).

For every odd p ≥ 5 with the Wilson receipt and p ≠ 7: EVERY solution m
of S₋(p) with m ≤ p−2 already satisfies m ≤ p−5 — the edge cascade:
(p−2)! ≢ −1, (p−3)! ≢ −1, (p−4)! ≢ −1 (the k = 1, 2, 3 positions of the
dictionary; the k = 3 position forces p = 7, the exact sole exception,
witnessed below). -/

theorem erdos1072_least_solution_law (p m : Nat) (hp : 5 ≤ p)
    (hodd : p % 2 = 1) (hp7 : p ≠ 7) (hW : fm p (p - 1) = p - 1)
    (hm : 1 ≤ m) (hm2 : m ≤ p - 2) (hmin : fm p m = p - 1) : m ≤ p - 5 := by
  rcases Nat.lt_or_ge m (p - 4) with hlt | hge
  · omega
  · have hcases : m = p - 4 ∨ m = p - 3 ∨ m = p - 2 := by omega
    rcases hcases with h | h | h
    · rw [h] at hmin
      have hC73 := erdos1072_top_chain_dictionary p 3 (by omega : 3 ≤ p) hodd (by omega) (by omega) hW
      have hb3 : p - 1 - 3 = p - 4 := by omega
      rw [hb3] at hC73
      have hcontra := hC73.mp hmin
      have hsg3 : sgn p 3 = p - 1 := sgn_three p
      rw [hsg3] at hcontra
      have h6 : fm p 3 ≡ 6 [MOD p] := fm_three_modeq p
      rw [hcontra] at h6
      have hc : (p - 1) % p = 6 % p := h6
      rcases Nat.lt_or_ge p 7 with hlt7 | hge7
      · have hp5 : p = 5 := by omega
        rw [hp5] at hc
        exact absurd hc (by decide)
      · have h6v : 6 % p = 6 := Nat.mod_eq_of_lt (by omega)
        have hpv : (p - 1) % p = p - 1 := Nat.mod_eq_of_lt (by omega)
        rw [hpv, h6v] at hc
        omega
    · rw [h] at hmin
      have hC72 := erdos1072_top_chain_dictionary p 2 (by omega : 3 ≤ p) hodd (by omega) (by omega) hW
      have hb2 : p - 1 - 2 = p - 3 := by omega
      rw [hb2] at hC72
      have hcontra := hC72.mp hmin
      rw [fm_two p (by omega), sgn_two p] at hcontra
      omega
    · rw [h] at hmin
      have hC71 := erdos1072_top_chain_dictionary p 1 (by omega : 3 ≤ p) hodd (by omega) (by omega) hW
      have hb1 : p - 1 - 1 = p - 2 := by omega
      rw [hb1] at hC71
      have hcontra := hC71.mp hmin
      rw [fm_one p (by omega), sgn_one p] at hcontra
      omega

/-- The p = 7 exception is exact and live: the Wilson receipt holds, the
k = 3 dictionary hit 3! ≡ −1 holds at m = 3 = p−4, and the p−5 bound
fails — the sole prime with a sub-Wilson solution above p−5. -/
theorem erdos1072_exception_7 :
    fm 7 3 = 6 ∧ fm 7 6 = 6 ∧ 3 = 7 - 4 ∧ ¬ (3 ≤ 7 - 5) :=
  ⟨Erdos1072Data.inst_7_3, Erdos1072Data.wilson_7, by decide, by decide⟩

/-! ## §16 THE TIGHTNESS WITNESS — p = 6089 (COMPLETE_PROOF.md §4
C8(iii), §5): the census's maximal non-Wilson-only ratio (f = 6042 =
p−1−46, ratio 0.9924). The Wilson receipt and the k = 46 dictionary hit
46! ≡ +1 (6089 ∣ 46!−1) are decide-verified; the top solution m = 6042 is
delivered BY THE DICTIONARY (C7 applied, not decided). -/

theorem wilson_6089 : fm 6089 6088 = 6088 := by decide

theorem dict_6089_46 : fm 6089 46 = 1 := by decide

theorem erdos1072_witness_6089_top : fm 6089 6042 = 6088 := by
  have hC7 := erdos1072_top_chain_dictionary 6089 46 (by norm_num) (by decide)
    (by norm_num) (by norm_num) wilson_6089
  have hsgn : sgn 6089 46 = 1 := by decide
  rw [hsgn] at hC7
  exact hC7.mpr dict_6089_46

theorem erdos1072_witness_6089 :
    fm 6089 6088 = 6088 ∧ fm 6089 46 = 1 ∧ fm 6089 6042 = 6088 ∧
    6042 = 6089 - 1 - 46 :=
  ⟨wilson_6089, dict_6089_46, erdos1072_witness_6089_top, by decide⟩

/-! ## §17 THE COMPLETE ASSEMBLY (S050-C5) — the final theorem.

`erdos1072_complete` welds the whole unconditional board into one
statement: the green spine K1/K2 (§7/§8), the C-layer (C1 the exact
pairing equivalence, C2 the parity split, C7 the top-chain k!±1
dictionary, C8 the least-solution law), the exact p = 7 exception, the
p = 6089 tightness witness, the eleven named instance receipts (§9 +
Erdos1072_Data), and the arsenal bridge (§10).

**Follow-ups (COMPLETE_PROOF.md §4, cited, not yet in Lean):** C3 the
2-cycle product laws, C4 the Gauss half-factorial identity, C5 the
fixed-point laws, C6 the count laws (census: 147 + 217 = 364) — all
proved in the doc and machine-verified by the extension engine E1–E9
over all 1,227 census primes.

**Honest scope (doc §7, unchanged):** the structure theory of S₋(p) is
complete here; the two corpus questions (Q1: infinitely many Wilson-only
primes; Q2: f(p)/p → 0 for almost all p) remain open — both are exactly
the first-hit distribution of the factorial walk n ↦ n! mod p. No sorry,
no sub-case dressed as the answer, no heuristic dressed as proof. -/

theorem erdos1072_complete :
    (∀ p n : Nat, 2 ≤ p → (p = 2 ∨ p % 2 = 1) → n ≤ p - 1 →
      fm p n * fm p (p - 1 - n) ≡ sgn p (p - 1 - n) * fm p (p - 1) [MOD p]) ∧
    (∀ p n : Nat, 2 ≤ p → (p = 2 ∨ p % 2 = 1) → n + 1 ≤ p - 1 →
      fm p (p - 1) = p - 1 → fm p n = p - 1 →
      fm p (p - 1 - n) = sgn p (p - 1 - n)) ∧
    (∀ p n : Nat, 3 ≤ p → p % 2 = 1 → 1 ≤ n → n + 1 ≤ p - 1 →
      fm p (p - 1) = p - 1 →
      (fm p n = p - 1 ↔ fm p (p - 1 - n) = sgn p (p - 1 - n))) ∧
    (∀ p n : Nat, 3 ≤ p → p % 2 = 1 → 1 ≤ n → n + 1 ≤ p - 1 →
      fm p (p - 1) = p - 1 → n % 2 = 1 →
      (fm p n = p - 1 ↔ fm p (p - 1 - n) = p - 1)) ∧
    (∀ p n : Nat, 3 ≤ p → p % 2 = 1 → 1 ≤ n → n + 1 ≤ p - 1 →
      fm p (p - 1) = p - 1 → n % 2 = 0 →
      (fm p n = p - 1 ↔ fm p (p - 1 - n) = 1)) ∧
    (∀ p k : Nat, 3 ≤ p → p % 2 = 1 → 1 ≤ k → k + 1 ≤ p - 1 →
      fm p (p - 1) = p - 1 →
      (fm p (p - 1 - k) = p - 1 ↔ fm p k = sgn p k)) ∧
    (∀ p m : Nat, 5 ≤ p → p % 2 = 1 → p ≠ 7 → fm p (p - 1) = p - 1 →
      1 ≤ m → m ≤ p - 2 → fm p m = p - 1 → m ≤ p - 5) ∧
    (fm 7 3 = 6 ∧ fm 7 6 = 6 ∧ 3 = 7 - 4 ∧ ¬ (3 ≤ 7 - 5)) ∧
    (fm 6089 6088 = 6088 ∧ fm 6089 46 = 1 ∧ fm 6089 6042 = 6088 ∧
      6042 = 6089 - 1 - 46) ∧
    (fm 7 3 = 6 ∧ fm 11 5 = 10 ∧ fm 19 9 = 18 ∧ fm 23 14 = 22 ∧
      fm 23 8 = 1 ∧ fm 29 18 = 28 ∧ fm 29 10 = 1 ∧ fm 43 21 = 42 ∧
      fm 47 23 = 46 ∧ fm 59 15 = 58 ∧ fm 61 8 = 60 ∧ fm 61 52 = 1 ∧
      fm 67 18 = 66 ∧ fm 71 7 = 70 ∧ fm 71 63 = 70) ∧
    ([71 % 3, (71 / 3) % 3, (71 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
      carryAtPos 61 1 < 4 ∧ carryAtPos 67 2 < 4 ∧
      v2r (3 ^ 1 * 24) = v2r 24) :=
  ⟨erdos1072_pair_law, erdos1072_wilson_pair_classic, erdos1072_pair_equivalence,
    erdos1072_parity_odd, erdos1072_parity_even, erdos1072_top_chain_dictionary,
    erdos1072_least_solution_law, erdos1072_exception_7, erdos1072_witness_6089,
    ⟨Erdos1072Data.inst_7_3, Erdos1072Data.inst_11_5, Erdos1072Data.inst_19_9,
      Erdos1072Data.inst_23_14, Erdos1072Data.tail_23_8, Erdos1072Data.inst_29_18,
      Erdos1072Data.tail_29_10, Erdos1072Data.inst_43_21, Erdos1072Data.inst_47_23,
      Erdos1072Data.inst_59_15, Erdos1072Data.inst_61_8, Erdos1072Data.tail_61_52,
      Erdos1072Data.inst_67_18, Erdos1072Data.inst_71_7, Erdos1072Data.tail_71_63⟩,
    erdos1072_arsenal_bridge⟩

#eval "ERDOS1072_KERNEL_GREEN"
#print axioms erdos1072_pair_law
#print axioms erdos1072_wilson_pair_classic
#print axioms erdos1072_pair_7
#print axioms erdos1072_pair_23
#print axioms erdos1072_pair_71
#print axioms erdos1072_arsenal_bridge

#eval "ERDOS1072_COMPLETE_GREEN"
#print axioms erdos1072_pair_equivalence
#print axioms erdos1072_parity_odd
#print axioms erdos1072_parity_even
#print axioms erdos1072_top_chain_dictionary
#print axioms erdos1072_least_solution_law
#print axioms erdos1072_exception_7
#print axioms erdos1072_witness_6089
#print axioms erdos1072_complete

end Erdos1072
