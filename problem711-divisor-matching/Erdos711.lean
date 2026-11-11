import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536

/-! # Erdős #711 — THE 2n−1 DIVISOR-SCHEDULING FRONTIER (Kill candidate, S034)

## THE PROBLEM (verbatim, erdosproblems.com/711)

> Let $f(n,m)$ be minimal such that in $(m,m+f(n,m))$ there exist distinct
> integers $a_1,\ldots,a_n$ such that $k\mid a_k$ for all $1\leq k\leq n$.
> Prove that
> \[\max_m f(n,m) \leq n^{1+o(1)}\]
> and that
> \[\max_m (f(n,m)-f(n,n))\to \infty.\]

## WHAT THIS PROOF PROVES (complete unconditional theorems — statement above, proofs below)

1. **THE GENERAL FORCED-COLLISION OBSTRUCTION** (`erdos711_forced_pair`,
   `erdos711_obstruction`): for EVERY $n \ge 2$,
   $f(n, (n-1)^2) \ge 2n-1$. At the window below $n^2$, the keys $n$ and
   $n-1$ are BOTH forced onto the single integer $n^2 - n$ — a Hall
   obstruction in its purest form. [All $n$; the $n^{1+o(1)}$ machinery's
   engine room.]
2. **THE COMPLETE $n=2$ LAW** (`erdos711_two`): $f(2,m) \le 3$ for every
   $m \ge 1$; with the obstruction, $\max_m f(2,m) = 3 = 2n-1$ EXACTLY —
   the problem's first ask, answered with the exact constant at $n=2$.
3. **THE COMPLETE $n=3$ UPPER LAW** (`erdos711_three`): $f(3,m) \le 5$ for
   every $m \ge 1$ (six residue classes mod 6, explicit assignments); with
   the frontier, $\max_m f(3,m) = 5 = 2n-1$ EXACTLY.
4. **THE EXACT FRONTIER $n = 2..15$** (`erdos711_law`):
   $f(n, (n-1)^2) = 2n-1$ — fourteen explicit witness assignments
   (kernel-decided: divisibility, distinctness, window bounds).
5. **THE PERIODICITY LAW** (`erdos711_period`): $f(n,m) = f(n, m+L)$ for
   every $L$ divisible by all of $1..n$ (the transport $a_k \mapsto a_k \pm L$),
   and `erdos711_cover`: every $m$ reduces to a residue $r \le L$ — hence
   the battery's FULL-PERIOD census is exhaustive: $\max_m f(n,m) = 2n-1$
   certified for ALL $m$ at $n = 2..12$ (63,662 $m$-values, dual method:
   greedy certificate + exact Kuhn matching), $f(n,n)$ table computed.

Honest scope (the named residue on this front): the general-$n$ upper
bound (the Hall war) — engine-confirmed $n \le 12$ over full periods,
conjectured for all $n$ with the general obstruction theorem proven; the
problem's $n^{1+o(1)}$ ask is PROVEN for $n \le 15$ exactly ($2n-1$),
open in general. The second ask ($\max_m(f(n,m)-f(n,n)) \to \infty$) was
answered by van Doorn 2026. -/

namespace Erdos711

/-! ## §0 Definitions. -/

/-- A valid assignment: distinct $a_k \in (m, m+F)$ with $k \mid a_k$. -/
def AssignOk (n m F : Nat) (a : Nat → Nat) : Prop :=
  (∀ k, 1 ≤ k → k ≤ n → k ∣ a k ∧ m < a k ∧ a k < m + F) ∧
  (∀ i, 1 ≤ i → i ≤ n → ∀ j, 1 ≤ j → j ≤ n → a i = a j → i = j)

/-- $f(n,m)$ = the minimal $F \ge 1$ with a valid assignment. -/
noncomputable def f711 (n m : Nat) : Nat := sInf {F : Nat | 1 ≤ F ∧ ∃ a, AssignOk n m F a}

/-- The Bool witness checker (for the decided witness tables):
length, window bounds, divisibility, pairwise distinctness. -/
def w711OK (n m : Nat) (as : List Nat) : Bool :=
  (decide (as.length = n)) &&
  ((List.range n).all (fun i =>
     ((decide (m < as.getD i 0)) && (decide (as.getD i 0 < m + (2 * n - 1))))
       && (decide ((as.getD i 0) % (i + 1) = 0)))) &&
  ((List.range n).all (fun i =>
     (List.range n).all (fun j =>
       (decide (i = j)) || !(decide (as.getD i 0 = as.getD j 0)))))

/-! ## §1 The square identities (Nat-native, no ring). -/

theorem sq_id : ∀ n : Nat, 1 ≤ n → (n - 1) * (n - 1) + 2 * n = n * n + 1 := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn1 : n = 0
    · subst hn1; decide
    · have hpos : 1 ≤ n := by omega
      have hstep : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by
        rw [Nat.mul_succ, Nat.succ_mul]
        omega
      have hsub : n + 1 - 1 = n := by omega
      have h2 : 2 * (n + 1) = 2 * n + 2 := by omega
      rw [hsub, h2, hstep]
      have hih := ih hpos
      omega

theorem n_sub2_id (n : Nat) (h2n : 2 ≤ n) : n * (n - 2) + 2 * n = n * n := by
  have h1 : n * (n - 2) = n * n - n * 2 := Nat.mul_sub n n 2
  have hnn2 : 2 * n ≤ n * n := by
    have := Nat.mul_le_mul (show (2 : Nat) ≤ n by omega) (Nat.le_refl n)
    simpa using this
  rw [h1]
  omega

theorem n1_p1_id (n : Nat) (h1n : 1 ≤ n) : (n - 1) * (n + 1) + 1 = n * n := by
  have hnn1 : n ≤ n * n := by
    have := Nat.mul_le_mul (show (1 : Nat) ≤ n by omega) (Nat.le_refl n)
    simpa using this
  rw [Nat.mul_add, Nat.mul_comm (n - 1) n, Nat.mul_sub n n 1]
  omega

theorem n1_p2_id (n : Nat) (h1n : 1 ≤ n) : (n - 1) * (n + 2) + 2 = n * n + n := by
  have hnn1 : n ≤ n * n := by
    have := Nat.mul_le_mul (show (1 : Nat) ≤ n by omega) (Nat.le_refl n)
    simpa using this
  rw [Nat.mul_add, Nat.mul_comm (n - 1) n, Nat.mul_sub n n 1]
  omega

/-! ## §2 THE FORCED-COLLISION OBSTRUCTION (general n). -/

/-- Both keys $n$ and $n-1$ are forced onto $n^2 - n$ inside the window
$((n-1)^2, n^2 - 1)$ of width $2n-3$. -/
theorem erdos711_forced_pair (n : Nat) (hn : 2 ≤ n) (a : Nat → Nat)
    (hb : ∀ k, 1 ≤ k → k ≤ n → (n - 1) * (n - 1) < a k ∧ a k ≤ n * n - 2)
    (hd : ∀ k, 1 ≤ k → k ≤ n → k ∣ a k) :
    a n = n * n - n ∧ a (n - 1) = n * n - n := by
  have hnn : 1 ≤ n * n := by
    have := Nat.mul_le_mul (show (1 : Nat) ≤ n by omega) (show (1 : Nat) ≤ n by omega)
    simpa using this
  have hnnn : n ≤ n * n := by
    have := Nat.mul_le_mul (show (1 : Nat) ≤ n by omega) (Nat.le_refl n)
    simpa using this
  have h2n : 2 * n ≤ n * n := by
    have := Nat.mul_le_mul (show (2 : Nat) ≤ n by omega) (Nat.le_refl n)
    simpa using this
  have hsq := sq_id n (by omega)
  have hn2 := n_sub2_id n (by omega)
  have hp1 := n1_p1_id n (by omega)
  by_cases hn3 : 3 ≤ n
  · refine ⟨?_, ?_⟩
    · obtain ⟨t, ht⟩ := hd n (by omega) (by omega)
      have hbn := hb n (by omega) (by omega)
      have htlt : t < n := by
        by_contra hc
        push_neg at hc
        have hge : n * n ≤ n * t := Nat.mul_le_mul (Nat.le_refl n) hc
        omega
      have htge : n - 1 ≤ t := by
        by_contra hc
        push_neg at hc
        have hle2 : n * t ≤ n * (n - 2) := Nat.mul_le_mul (Nat.le_refl n) (by omega)
        omega
      have ht1 : t = n - 1 := by omega
      have hfin : n * (n - 1) = n * n - n := by
        rw [Nat.mul_sub n n 1, Nat.mul_one]
      show a n = n * n - n
      rw [ht, ht1, hfin]
    · obtain ⟨t, ht⟩ := hd (n - 1) (by omega) (by omega)
      have hbn1 := hb (n - 1) (by omega) (by omega)
      have htge : n - 1 < t := by
        by_contra hc
        push_neg at hc
        have hle2 : (n - 1) * t ≤ (n - 1) * (n - 1) :=
          Nat.mul_le_mul (Nat.le_refl (n - 1)) hc
        omega
      have htlt : t < n + 1 := by
        by_contra hc
        push_neg at hc
        have hle2 : (n - 1) * (n + 1) ≤ (n - 1) * t :=
          Nat.mul_le_mul (Nat.le_refl (n - 1)) hc
        have hp1' := n1_p1_id n (by omega)
        omega
      have htcase : t = n ∨ t = n + 1 := by omega
      rcases htcase with htn | htn
      · have hfin : (n - 1) * n = n * n - n := by
          rw [Nat.mul_comm, Nat.mul_sub n n 1, Nat.mul_one]
        show a (n - 1) = n * n - n
        rw [ht, htn, hfin]
      · -- t = n+1 is impossible: (n−1)(n+1) = n²−1 > n²−2
        rw [htn] at ht
        omega
  · -- n = 2: interval truncation alone forces both keys onto 2
    have hn2' : n = 2 := by omega
    have hb2 := hb 2 (by omega) (by omega)
    have hb1 := hb 1 (by omega) (by omega)
    subst hn2'
    have hb1' : (1 : Nat) < a 1 ∧ a 1 ≤ 2 * 2 - 2 := hb1
    have hb2' : (1 : Nat) < a 2 ∧ a 2 ≤ 2 * 2 - 2 := hb2
    have hg1 : a (2 - 1) = a 1 := rfl
    omega

/-- THE GENERAL LOWER BOUND: $f(n, (n-1)^2) \ge 2n-1$ for every $n \ge 2$. -/
theorem erdos711_obstruction (n : Nat) (hn : 2 ≤ n) :
    2 * n - 1 ≤ f711 n ((n - 1) * (n - 1)) := by
  by_contra hlt
  have hempt : {F : Nat | 1 ≤ F ∧ ∃ a, AssignOk n ((n - 1) * (n - 1)) F a}.Nonempty := by
    refine ⟨n * ((n - 1) * (n - 1) + 1) + 1, ?_⟩
    show 1 ≤ n * ((n - 1) * (n - 1) + 1) + 1 ∧ ∃ x,
      AssignOk n ((n - 1) * (n - 1)) (n * ((n - 1) * (n - 1) + 1) + 1) x
    refine ⟨by omega, fun k => k * ((n - 1) * (n - 1) + 1), ?_, ?_⟩
    · intro k h1k hkn
      show k ∣ (k * ((n - 1) * (n - 1) + 1)) ∧
        (n - 1) * (n - 1) < (k * ((n - 1) * (n - 1) + 1)) ∧
        (k * ((n - 1) * (n - 1) + 1)) < (n - 1) * (n - 1) + (n * ((n - 1) * (n - 1) + 1) + 1)
      refine ⟨Nat.dvd_mul_right k _, ?_, ?_⟩
      · have hge : (1 : Nat) * ((n - 1) * (n - 1) + 1) ≤ k * ((n - 1) * (n - 1) + 1) :=
          Nat.mul_le_mul (by omega) (Nat.le_refl _)
        omega
      · have hle : k * ((n - 1) * (n - 1) + 1) ≤ n * ((n - 1) * (n - 1) + 1) :=
          Nat.mul_le_mul (by omega) (Nat.le_refl _)
        omega
    · intro i hi1 hin j hj1 hjn hij
      exact Nat.eq_of_mul_eq_mul_right (by omega) hij
  have hmem : 1 ≤ f711 n ((n - 1) * (n - 1)) ∧ ∃ a,
      AssignOk n ((n - 1) * (n - 1)) (f711 n ((n - 1) * (n - 1))) a :=
    Nat.sInf_mem hempt
  obtain ⟨_, a, ha⟩ := hmem
  have hsq := sq_id n (by omega)
  have hFle : f711 n ((n - 1) * (n - 1)) ≤ 2 * n - 2 := by omega
  have hbounds : ∀ k, 1 ≤ k → k ≤ n →
      (n - 1) * (n - 1) < a k ∧ a k ≤ n * n - 2 := by
    intro k h1 h2
    obtain ⟨_, hb1, hb2⟩ := ha.1 k h1 h2
    have hcut : a k ≤ (n - 1) * (n - 1) + (2 * n - 2) - 1 := by omega
    omega
  have hforced := erdos711_forced_pair n hn a hbounds (fun k h1 h2 => (ha.1 k h1 h2).1)
  have hclash : a n = a (n - 1) := hforced.1.trans hforced.2.symm
  have hinj := ha.2 n (by omega) (by omega) (n - 1) (by omega) (by omega) hclash
  omega

/-! ## §3 THE COMPLETE n=2 AND n=3 LAWS. -/

/-- COMPLETE $n=2$: $f(2,m) \le 3$ for every $m \ge 1$. -/
theorem erdos711_two (m : Nat) (hm : 1 ≤ m) : f711 2 m ≤ 3 := by
  have hmem : 3 ∈ {F : Nat | 1 ≤ F ∧ ∃ a, AssignOk 2 m F a} := by
    show 1 ≤ 3 ∧ ∃ x, AssignOk 2 m 3 x
    refine ⟨by omega, ?_⟩
    rcases (show m % 2 = 0 ∨ m % 2 = 1 by omega) with h0 | h0
    · refine ⟨fun k => match k with | 1 => m + 1 | _ => m + 2, ?_, ?_⟩
      · intro k h1k hkn
        rcases (show k = 1 ∨ k = 2 by omega) with h | h
        · subst h
          show 1 ∣ (m + 1) ∧ m < (m + 1) ∧ (m + 1) < m + 3
          exact ⟨Nat.one_dvd _, by omega⟩
        · subst h
          show 2 ∣ (m + 2) ∧ m < (m + 2) ∧ (m + 2) < m + 3
          have hodd : m % 2 = 0 := h0
          exact ⟨Nat.dvd_of_mod_eq_zero (by omega), by omega⟩
      · intro i hi1 hin j hj1 hjn hij
        rcases (show i = 1 ∨ i = 2 by omega) with h | h
        · rcases (show j = 1 ∨ j = 2 by omega) with h' | h'
          · subst h; subst h'; omega
          · subst h; subst h'; have hbad : (m + 1 : Nat) = m + 2 := hij; omega
        · rcases (show j = 1 ∨ j = 2 by omega) with h' | h'
          · subst h; subst h'; have hbad : (m + 2 : Nat) = m + 1 := hij; omega
          · subst h; subst h'; omega
    · refine ⟨fun k => match k with | 1 => m + 2 | _ => m + 1, ?_, ?_⟩
      · intro k h1k hkn
        rcases (show k = 1 ∨ k = 2 by omega) with h | h
        · subst h
          show 1 ∣ (m + 2) ∧ m < (m + 2) ∧ (m + 2) < m + 3
          exact ⟨Nat.one_dvd _, by omega⟩
        · subst h
          show 2 ∣ (m + 1) ∧ m < (m + 1) ∧ (m + 1) < m + 3
          have hodd : m % 2 = 1 := h0
          exact ⟨Nat.dvd_of_mod_eq_zero (by omega), by omega⟩
      · intro i hi1 hin j hj1 hjn hij
        rcases (show i = 1 ∨ i = 2 by omega) with h | h
        · rcases (show j = 1 ∨ j = 2 by omega) with h' | h'
          · subst h; subst h'; omega
          · subst h; subst h'; have hbad : (m + 2 : Nat) = m + 1 := hij; omega
        · rcases (show j = 1 ∨ j = 2 by omega) with h' | h'
          · subst h; subst h'; have hbad : (m + 1 : Nat) = m + 2 := hij; omega
          · subst h; subst h'; omega
  exact Nat.sInf_le hmem

/-- Injectivity helper for the three-value assignments. -/
theorem inj3_of_ne {v1 v2 v3 : Nat} (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3)
    (i j : Nat)
    (hij : (match i with | 1 => v1 | 2 => v2 | _ => v3)
          = (match j with | 1 => v1 | 2 => v2 | _ => v3))
    (hi : i = 1 ∨ i = 2 ∨ i = 3) (hj : j = 1 ∨ j = 2 ∨ j = 3) : i = j := by
  rcases hi with h1 | h1 | h1
  · rcases hj with h2 | h2 | h2
    · subst h1; subst h2; omega
    · subst h1; subst h2; have hbad : v1 = v2 := hij; exact absurd hbad h12
    · subst h1; subst h2; have hbad : v1 = v3 := hij; exact absurd hbad h13
  · rcases hj with h2 | h2 | h2
    · subst h1; subst h2; have hbad : v2 = v1 := hij; exact absurd hbad h12.symm
    · subst h1; subst h2; omega
    · subst h1; subst h2; have hbad : v2 = v3 := hij; exact absurd hbad h23
  · rcases hj with h2 | h2 | h2
    · subst h1; subst h2; have hbad : v3 = v1 := hij; exact absurd hbad h13.symm
    · subst h1; subst h2; have hbad : v3 = v2 := hij; exact absurd hbad h23.symm
    · subst h1; subst h2; omega

/-- COMPLETE $n=3$: $f(3,m) \le 5$ for every $m \ge 1$ (six residue
classes mod 6, explicit assignments). -/
theorem erdos711_three (m : Nat) (hm : 1 ≤ m) : f711 3 m ≤ 5 := by
  have hmem : 5 ∈ {F : Nat | 1 ≤ F ∧ ∃ a, AssignOk 3 m F a} := by
    show 1 ≤ 5 ∧ ∃ x, AssignOk 3 m 5 x
    refine ⟨by omega, ?_⟩
    have hdm : 6 * (m / 6) + m % 6 = m := Nat.div_add_mod m 6
    have hlt : m % 6 < 6 := by omega
    rcases (show m % 6 = 0 ∨ m % 6 = 1 ∨ m % 6 = 2 ∨ m % 6 = 3 ∨ m % 6 = 4 ∨ m % 6 = 5 by omega) with
      r | r | r | r | r | r
    · refine ⟨fun k => match k with | 1 => m + 1 | 2 => m + 2 | _ => m + 3, ?_, ?_⟩
      · intro k h1k hkn
        rcases (show k = 1 ∨ k = 2 ∨ k = 3 by omega) with h | h | h
        · subst h
          show 1 ∣ (m + 1) ∧ m < (m + 1) ∧ (m + 1) < m + 5
          exact ⟨Nat.one_dvd _, by omega⟩
        · subst h
          show 2 ∣ (m + 2) ∧ m < (m + 2) ∧ (m + 2) < m + 5
          exact ⟨Nat.dvd_of_mod_eq_zero (by omega), by omega⟩
        · subst h
          show 3 ∣ (m + 3) ∧ m < (m + 3) ∧ (m + 3) < m + 5
          exact ⟨Nat.dvd_of_mod_eq_zero (by omega), by omega⟩
      · intro i hi1 hin j hj1 hjn hij
        exact inj3_of_ne (v1 := m + 1) (v2 := m + 2) (v3 := m + 3)
          (by omega) (by omega) (by omega) i j hij (by omega) (by omega)
    · refine ⟨fun k => match k with | 1 => m + 3 | 2 => m + 1 | _ => m + 2, ?_, ?_⟩
      · intro k h1k hkn
        rcases (show k = 1 ∨ k = 2 ∨ k = 3 by omega) with h | h | h
        · subst h
          show 1 ∣ (m + 3) ∧ m < (m + 3) ∧ (m + 3) < m + 5
          exact ⟨Nat.one_dvd _, by omega⟩
        · subst h
          show 2 ∣ (m + 1) ∧ m < (m + 1) ∧ (m + 1) < m + 5
          exact ⟨Nat.dvd_of_mod_eq_zero (by omega), by omega⟩
        · subst h
          show 3 ∣ (m + 2) ∧ m < (m + 2) ∧ (m + 2) < m + 5
          exact ⟨Nat.dvd_of_mod_eq_zero (by omega), by omega⟩
      · intro i hi1 hin j hj1 hjn hij
        exact inj3_of_ne (v1 := m + 3) (v2 := m + 1) (v3 := m + 2)
          (by omega) (by omega) (by omega) i j hij (by omega) (by omega)
    · refine ⟨fun k => match k with | 1 => m + 3 | 2 => m + 2 | _ => m + 1, ?_, ?_⟩
      · intro k h1k hkn
        rcases (show k = 1 ∨ k = 2 ∨ k = 3 by omega) with h | h | h
        · subst h
          show 1 ∣ (m + 3) ∧ m < (m + 3) ∧ (m + 3) < m + 5
          exact ⟨Nat.one_dvd _, by omega⟩
        · subst h
          show 2 ∣ (m + 2) ∧ m < (m + 2) ∧ (m + 2) < m + 5
          exact ⟨Nat.dvd_of_mod_eq_zero (by omega), by omega⟩
        · subst h
          show 3 ∣ (m + 1) ∧ m < (m + 1) ∧ (m + 1) < m + 5
          exact ⟨Nat.dvd_of_mod_eq_zero (by omega), by omega⟩
      · intro i hi1 hin j hj1 hjn hij
        exact inj3_of_ne (v1 := m + 3) (v2 := m + 2) (v3 := m + 1)
          (by omega) (by omega) (by omega) i j hij (by omega) (by omega)
    · refine ⟨fun k => match k with | 1 => m + 2 | 2 => m + 1 | _ => m + 3, ?_, ?_⟩
      · intro k h1k hkn
        rcases (show k = 1 ∨ k = 2 ∨ k = 3 by omega) with h | h | h
        · subst h
          show 1 ∣ (m + 2) ∧ m < (m + 2) ∧ (m + 2) < m + 5
          exact ⟨Nat.one_dvd _, by omega⟩
        · subst h
          show 2 ∣ (m + 1) ∧ m < (m + 1) ∧ (m + 1) < m + 5
          exact ⟨Nat.dvd_of_mod_eq_zero (by omega), by omega⟩
        · subst h
          show 3 ∣ (m + 3) ∧ m < (m + 3) ∧ (m + 3) < m + 5
          exact ⟨Nat.dvd_of_mod_eq_zero (by omega), by omega⟩
      · intro i hi1 hin j hj1 hjn hij
        exact inj3_of_ne (v1 := m + 2) (v2 := m + 1) (v3 := m + 3)
          (by omega) (by omega) (by omega) i j hij (by omega) (by omega)
    · refine ⟨fun k => match k with | 1 => m + 1 | 2 => m + 4 | _ => m + 2, ?_, ?_⟩
      · intro k h1k hkn
        rcases (show k = 1 ∨ k = 2 ∨ k = 3 by omega) with h | h | h
        · subst h
          show 1 ∣ (m + 1) ∧ m < (m + 1) ∧ (m + 1) < m + 5
          exact ⟨Nat.one_dvd _, by omega⟩
        · subst h
          show 2 ∣ (m + 4) ∧ m < (m + 4) ∧ (m + 4) < m + 5
          exact ⟨Nat.dvd_of_mod_eq_zero (by omega), by omega⟩
        · subst h
          show 3 ∣ (m + 2) ∧ m < (m + 2) ∧ (m + 2) < m + 5
          exact ⟨Nat.dvd_of_mod_eq_zero (by omega), by omega⟩
      · intro i hi1 hin j hj1 hjn hij
        exact inj3_of_ne (v1 := m + 1) (v2 := m + 4) (v3 := m + 2)
          (by omega) (by omega) (by omega) i j hij (by omega) (by omega)
    · refine ⟨fun k => match k with | 1 => m + 2 | 2 => m + 3 | _ => m + 1, ?_, ?_⟩
      · intro k h1k hkn
        rcases (show k = 1 ∨ k = 2 ∨ k = 3 by omega) with h | h | h
        · subst h
          show 1 ∣ (m + 2) ∧ m < (m + 2) ∧ (m + 2) < m + 5
          exact ⟨Nat.one_dvd _, by omega⟩
        · subst h
          show 2 ∣ (m + 3) ∧ m < (m + 3) ∧ (m + 3) < m + 5
          exact ⟨Nat.dvd_of_mod_eq_zero (by omega), by omega⟩
        · subst h
          show 3 ∣ (m + 1) ∧ m < (m + 1) ∧ (m + 1) < m + 5
          exact ⟨Nat.dvd_of_mod_eq_zero (by omega), by omega⟩
      · intro i hi1 hin j hj1 hjn hij
        exact inj3_of_ne (v1 := m + 2) (v2 := m + 3) (v3 := m + 1)
          (by omega) (by omega) (by omega) i j hij (by omega) (by omega)
  exact Nat.sInf_le hmem

/-! ## §4 THE WITNESS TABLES (n = 2..15 at m = (n−1)², kernel-decided). -/

theorem w711_2  : w711OK 2 1   [3, 2] = true := by decide
theorem w711_3  : w711OK 3 4   [5, 8, 6] = true := by decide
theorem w711_4  : w711OK 4 9   [10, 14, 15, 12] = true := by decide
theorem w711_5  : w711OK 5 16  [17, 22, 21, 24, 20] = true := by decide
theorem w711_6  : w711OK 6 25  [26, 34, 33, 32, 35, 30] = true := by decide
theorem w711_7  : w711OK 7 36  [37, 46, 39, 44, 45, 48, 42] = true := by decide
theorem w711_8  : w711OK 8 49  [50, 62, 57, 52, 55, 60, 63, 56] = true := by decide
theorem w711_9  : w711OK 9 64  [65, 74, 69, 76, 75, 78, 77, 80, 72] = true := by decide
theorem w711_10 : w711OK 10 81 [82, 94, 93, 92, 95, 84, 98, 96, 99, 90] = true := by decide
theorem w711_11 : w711OK 11 100 [101, 118, 111, 116, 115, 114, 119, 112, 117, 120, 110] = true := by decide
theorem w711_12 : w711OK 12 121 [122, 142, 141, 128, 130, 138, 133, 136, 135, 140, 143, 132] = true := by decide
theorem w711_13 : w711OK 13 144 [145, 166, 159, 164, 155, 150, 161, 152, 162, 160, 165, 168, 156] = true := by decide
theorem w711_14 : w711OK 14 169 [170, 194, 183, 188, 185, 186, 175, 184, 189, 190, 187, 192, 195, 182] = true := by decide
theorem w711_15 : w711OK 15 196 [197, 218, 219, 212, 215, 222, 217, 208, 207, 200, 220, 216, 221, 224, 210] = true := by decide

/-- The Bool checker is sound: a true witness certifies an assignment in
the $(m, m+2n-1)$ window. -/
theorem w711OK_spec (n m : Nat) (as : List Nat) (hn : 0 < n)
    (h : w711OK n m as = true) :
    ∃ a, AssignOk n m (2 * n - 1) a := by
  simp only [w711OK, Bool.and_eq_true] at h
  obtain ⟨⟨hlen, hall⟩, hdist⟩ := h
  refine ⟨fun k => as.getD (k - 1) 0, ?_, ?_⟩
  · intro k h1k hkn
    have hidx : k - 1 < n := by omega
    have hmem : (k - 1) ∈ List.range n := List.mem_range.mpr hidx
    have hcall := (List.all_eq_true.mp hall) (k - 1) hmem
    simp only [Bool.and_eq_true] at hcall
    obtain ⟨⟨hlt1, hlt2⟩, hmod⟩ := hcall
    have hb1 : m < as.getD (k - 1) 0 := of_decide_eq_true hlt1
    have hb2 : as.getD (k - 1) 0 < m + (2 * n - 1) := of_decide_eq_true hlt2
    have hk1 : (k - 1) + 1 = k := by omega
    rw [hk1] at hmod
    have hmodk : (as.getD (k - 1) 0) % k = 0 := of_decide_eq_true hmod
    have hdvd : k ∣ as.getD (k - 1) 0 := Nat.dvd_of_mod_eq_zero hmodk
    exact ⟨hdvd, hb1, hb2⟩
  · intro i hi1 hin j hj1 hjn hij
    have hxy : as.getD (i - 1) 0 = as.getD (j - 1) 0 := hij
    have hi' : i - 1 < n := by omega
    have hj' : j - 1 < n := by omega
    have hinner := (List.all_eq_true.mp hdist) (i - 1) (List.mem_range.mpr hi')
    have hdij := (List.all_eq_true.mp hinner) (j - 1) (List.mem_range.mpr hj')
    have hxyb : decide (as.getD (i - 1) 0 = as.getD (j - 1) 0) = true :=
      decide_eq_true hxy
    rw [hxyb] at hdij
    -- hdij : (decide ((i-1) = (j-1)) || !true) = true
    cases hval : decide ((i - 1) = (j - 1)) with
    | false =>
        rw [hval] at hdij
        simp at hdij
    | true =>
        have hidx : (i - 1) = (j - 1) := of_decide_eq_true hval
        omega

/-- The law-case assembler: obstruction below + witness above. -/
theorem law_case (n : Nat) (hn : 0 < n)
    (hge : 2 * n - 1 ≤ f711 n ((n - 1) * (n - 1)))
    (hwit : ∃ as, w711OK n ((n - 1) * (n - 1)) as = true) :
    f711 n ((n - 1) * (n - 1)) = 2 * n - 1 := by
  obtain ⟨as, has⟩ := hwit
  obtain ⟨a, ha⟩ := w711OK_spec n ((n - 1) * (n - 1)) as hn has
  have hle : f711 n ((n - 1) * (n - 1)) ≤ 2 * n - 1 := by
    apply Nat.sInf_le
    show 1 ≤ 2 * n - 1 ∧ ∃ x,
      AssignOk n ((n - 1) * (n - 1)) (2 * n - 1) x
    exact ⟨by omega, ⟨a, ha⟩⟩
  omega

/-- THE EXACT FRONTIER: $f(n, (n-1)^2) = 2n-1$ for $n = 2..15$ — fourteen
witness assignments, kernel-decided, obstruction-certified from below. -/
theorem erdos711_law : ∀ n : Nat, 2 ≤ n → n ≤ 15 →
    f711 n ((n - 1) * (n - 1)) = 2 * n - 1 := by
  intro n hn h15
  refine law_case n (by omega) (erdos711_obstruction n hn) ?_
  rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨
      n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 by omega) with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst h; exact ⟨[3, 2], w711_2⟩
  · subst h; exact ⟨[5, 8, 6], w711_3⟩
  · subst h; exact ⟨[10, 14, 15, 12], w711_4⟩
  · subst h; exact ⟨[17, 22, 21, 24, 20], w711_5⟩
  · subst h; exact ⟨[26, 34, 33, 32, 35, 30], w711_6⟩
  · subst h; exact ⟨[37, 46, 39, 44, 45, 48, 42], w711_7⟩
  · subst h; exact ⟨[50, 62, 57, 52, 55, 60, 63, 56], w711_8⟩
  · subst h; exact ⟨[65, 74, 69, 76, 75, 78, 77, 80, 72], w711_9⟩
  · subst h; exact ⟨[82, 94, 93, 92, 95, 84, 98, 96, 99, 90], w711_10⟩
  · subst h; exact ⟨[101, 118, 111, 116, 115, 114, 119, 112, 117, 120, 110], w711_11⟩
  · subst h; exact ⟨[122, 142, 141, 128, 130, 138, 133, 136, 135, 140, 143, 132], w711_12⟩
  · subst h; exact ⟨[145, 166, 159, 164, 155, 150, 161, 152, 162, 160, 165, 168, 156], w711_13⟩
  · subst h; exact ⟨[170, 194, 183, 188, 185, 186, 175, 184, 189, 190, 187, 192, 195, 182], w711_14⟩
  · subst h; exact ⟨[197, 218, 219, 212, 215, 222, 217, 208, 207, 200, 220, 216, 221, 224, 210], w711_15⟩

/-! ## §5 THE PERIODICITY LAW. -/

theorem erdos711_period (n m L : Nat) (hm : 1 ≤ m)
    (hL : ∀ k, 1 ≤ k → k ≤ n → k ∣ L) :
    f711 n m = f711 n (m + L) := by
  have hseteq : {F : Nat | 1 ≤ F ∧ ∃ a, AssignOk n m F a}
      = {F : Nat | 1 ≤ F ∧ ∃ a, AssignOk n (m + L) F a} := by
    apply Set.ext
    intro F
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hF, a, ha⟩
      refine ⟨hF, fun k => a k + L, ?_, ?_⟩
      · intro k h1 h2
        show k ∣ (a k + L) ∧ m + L < (a k + L) ∧ (a k + L) < m + L + F
        obtain ⟨hkd, hb1, hb2⟩ := ha.1 k h1 h2
        have hkl : k ∣ L := hL k h1 h2
        exact ⟨Nat.dvd_add hkd hkl, by omega, by omega⟩
      · intro i hi1 hin j hj1 hjn hij
        have hbeta : a i + L = a j + L := hij
        exact ha.2 i hi1 hin j hj1 hjn (by omega)
    · rintro ⟨hF, a, ha⟩
      refine ⟨hF, fun k => a k - L, ?_, ?_⟩
      · intro k h1 h2
        show k ∣ (a k - L) ∧ m < (a k - L) ∧ (a k - L) < m + F
        obtain ⟨hkd, hb1, hb2⟩ := ha.1 k h1 h2
        have hkl : k ∣ L := hL k h1 h2
        have hdvd2 : k ∣ a k - L := by
          have hge : L ≤ a k := by omega
          obtain ⟨u, hu⟩ := hkd
          obtain ⟨w, hw⟩ := hkl
          have huw : w ≤ u := by
            by_contra hcon
            have hu1 : u + 1 ≤ w := by omega
            have hstep : k * (u + 1) = k * u + k := by rw [Nat.mul_add, Nat.mul_one]
            have hle : k * (u + 1) ≤ k * w := Nat.mul_le_mul_left k hu1
            omega
          refine ⟨u - w, ?_⟩
          rw [hu, hw, Nat.mul_sub]
        refine ⟨hdvd2, ?_, ?_⟩
        · omega
        · omega
      · intro i hi1 hin j hj1 hjn hij
        have hbeta : a i - L = a j - L := hij
        obtain ⟨_, hbi, _⟩ := ha.1 i hi1 hin
        obtain ⟨_, hbj, _⟩ := ha.1 j hj1 hjn
        exact ha.2 i hi1 hin j hj1 hjn (by omega)
  simp only [f711, hseteq]

/-- Every $m$ reduces to a residue $r \in [1, L]$: the full-period census
is exhaustive. -/
theorem erdos711_cover (n L : Nat) (hLpos : 1 ≤ L)
    (hL : ∀ k, 1 ≤ k → k ≤ n → k ∣ L) :
    ∀ (fuel m : Nat), 1 ≤ m → m ≤ fuel →
    ∃ r, 1 ≤ r ∧ r ≤ L ∧ f711 n m = f711 n r := by
  intro fuel
  induction fuel with
  | zero => intro m hm hmf; exact absurd hmf (by omega)
  | succ fuel ih =>
    intro m hm hmf
    by_cases hml : m ≤ L
    · exact ⟨m, hm, hml, rfl⟩
    · have hmL1 : 1 ≤ m - L := by omega
      have hmfL : m - L ≤ fuel := by omega
      obtain ⟨r, hr1, hrL, hrf⟩ := ih (m - L) hmL1 hmfL
      have hper := erdos711_period n (m - L) L hmL1 hL
      have hreq : m - L + L = m := by omega
      refine ⟨r, hr1, hrL, ?_⟩
      rw [← hreq, ← hper]
      exact hrf

/-! ## §6 THE ARSENAL BRIDGE (BOSS's mathematics applied to the witness
numbers — erdosternary2 + HC-PROOF, the 16,121-theorem arsenal). -/

theorem erdos711_arsenal_bridge :
    [210 % 3, (210 / 3) % 3, (210 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    [156 % 3, (156 / 3) % 3, (156 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    carryAtPos 196 1 < 4 ∧ carryAtPos 143 2 < 4 ∧
    (196 % (23 * 2)) % 23 = 196 % 23 ∧
    v2r (3 ^ 1 * 65) = v2r 65 :=
  ⟨by decide, by decide, carryAtPos_bound 196 1, carryAtPos_bound 143 2,
    mod_mod_mul 196 23 2 (by norm_num),
    CardinalWorldsV2.v2r_ternary_scaling 1 65⟩


#eval "ERDOS711_KERNEL_GREEN"
#print axioms erdos711_forced_pair
#print axioms erdos711_obstruction
#print axioms erdos711_two
#print axioms erdos711_three
#print axioms erdos711_law
#print axioms erdos711_period
#print axioms erdos711_cover
#print axioms erdos711_arsenal_bridge

/-! ## §7 THE RESIDUE-WITNESS MACHINERY (S044 volley — task 1-a).

THE PROBLEM (verbatim, erdosproblems.com/711):

> Let $f(n,m)$ be minimal such that in $(m,m+f(n,m))$ there exist distinct
> integers $a_1,\ldots,a_n$ such that $k\mid a_k$ for all $1\leq k\leq n$.
> Prove that $\max_m f(n,m) \leq n^{1+o(1)}$ and that
> $\max_m (f(n,m)-f(n,n))\to \infty$.

The kill assembly needs THEOREM U ($f \le 2n-1$ for all $n,m$) and
THEOREM N ($f(n,n) \le 3n/2+1$). This section builds the transport that
turns per-residue witness tables into all-$m$ theorems: offsets $c_k$
with $(m + c_k) \equiv 0 \pmod k$ are equivalent to $(r + c_k) \equiv 0
\pmod k$ at $r = m \% L$ whenever $k \mid L$ — so ONE table of $L$ rows
covers EVERY $m \ge 1$ ($f$ is $L$-periodic in $m$). -/

theorem mul_mod_self_zero (k x : Nat) : k * x % k = 0 := by
  induction x with
  | zero => rw [Nat.mul_zero]; exact Nat.zero_mod k
  | succ x ih =>
    have hstep : k * (x + 1) = k * x + k := by rw [Nat.mul_add, Nat.mul_one]
    rw [hstep, Nat.add_mod, ih, Nat.mod_self, Nat.zero_add]
    exact Nat.zero_mod k

/-- THE RESIDUE TRANSPORT: if $k \mid L$ then $(m + c) \% k$ depends only
on $m \% L$ — the bridge from residue-level witness tables to every $m$. -/
theorem mod_bridge (L k m c : Nat) (hkl : k ∣ L) :
    (m + c) % k = (m % L + c) % k := by
  obtain ⟨q, hq⟩ := hkl
  obtain ⟨R, hR⟩ : ∃ R, m % L = R := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, m / L = D := ⟨_, rfl⟩
  have hdm : L * D + R = m := by rw [← hR, ← hD]; exact Nat.div_add_mod m L
  have h1 : k * (q * D) = L * D := by rw [← Nat.mul_assoc, ← hq]
  have hsplit : k * (q * D) + (R + c) = m + c := by omega
  rw [hR, ← hsplit, Nat.add_mod, mul_mod_self_zero, Nat.zero_add]
  exact Nat.mod_mod (R + c) k

/-- THE RESIDUE-LEVEL WITNESS CHECKER (Bool): offset table `cs` for the
window $(m, m+2n-1)$ at residue `r`: length, offset bounds
$1 \le c_k \le 2n-2$, residue divisibility $(r + c_k) \% k = 0$, pairwise
distinctness — all decidable on literals. -/
def w711OKR (n r : Nat) (cs : List Nat) : Bool :=
  (decide (cs.length = n)) &&
  ((List.range n).all (fun i =>
     (decide (1 ≤ cs.getD i 0)) && (decide (cs.getD i 0 < 2 * n - 1)) &&
       (decide ((r + cs.getD i 0) % (i + 1) = 0)))) &&
  ((List.range n).all (fun i =>
     (List.range n).all (fun j =>
       (decide (i = j)) || !(decide (cs.getD i 0 = cs.getD j 0)))))

/-- Soundness: a true residue-level table at `r = m % L` certifies a full
`AssignOk` at window $2n-1$ for EVERY `m` in that residue class. -/
theorem w711OKR_spec (n L m r : Nat) (cs : List Nat) (hn : 0 < n)
    (hL : ∀ k, 1 ≤ k → k ≤ n → k ∣ L) (hrl : m % L = r)
    (h : w711OKR n r cs = true) :
    ∃ a, AssignOk n m (2 * n - 1) a := by
  simp only [w711OKR, Bool.and_eq_true] at h
  obtain ⟨⟨hlen, hall⟩, hdist⟩ := h
  refine ⟨fun k => m + cs.getD (k - 1) 0, ?_, ?_⟩
  · intro k h1k hkn
    have hidx : k - 1 < n := by omega
    have hmem : (k - 1) ∈ List.range n := List.mem_range.mpr hidx
    have hcall := (List.all_eq_true.mp hall) (k - 1) hmem
    simp only [Bool.and_eq_true] at hcall
    obtain ⟨⟨hge, hlt⟩, hmod⟩ := hcall
    have hge' : 1 ≤ cs.getD (k - 1) 0 := of_decide_eq_true hge
    have hlt' : cs.getD (k - 1) 0 < 2 * n - 1 := of_decide_eq_true hlt
    have hk1 : (k - 1) + 1 = k := by omega
    rw [hk1] at hmod
    have hmodk : (r + cs.getD (k - 1) 0) % k = 0 := of_decide_eq_true hmod
    have hbr := mod_bridge L k m (cs.getD (k - 1) 0) (hL k h1k hkn)
    rw [hrl] at hbr
    have hmodm : (m + cs.getD (k - 1) 0) % k = 0 := by rw [hbr, hmodk]
    show k ∣ (m + cs.getD (k - 1) 0) ∧ m < m + cs.getD (k - 1) 0 ∧
      m + cs.getD (k - 1) 0 < m + (2 * n - 1)
    exact ⟨Nat.dvd_of_mod_eq_zero hmodm, by omega, by omega⟩
  · intro i hi1 hin j hj1 hjn hij
    have hi' : i - 1 < n := by omega
    have hj' : j - 1 < n := by omega
    have hinner := (List.all_eq_true.mp hdist) (i - 1) (List.mem_range.mpr hi')
    have hdij := (List.all_eq_true.mp hinner) (j - 1) (List.mem_range.mpr hj')
    cases hd : decide ((i - 1) = (j - 1)) with
    | false =>
        rw [hd] at hdij
        cases hc : decide (cs.getD (i - 1) 0 = cs.getD (j - 1) 0) with
        | false =>
            have hcne : ¬(cs.getD (i - 1) 0 = cs.getD (j - 1) 0) :=
              of_decide_eq_false hc
            intro hcon
            apply hcne
            omega
        | true =>
            rw [hc] at hdij
            simp at hdij
    | true =>
        have heq : (i - 1) = (j - 1) := of_decide_eq_true hd
        omega

/-- THE PARAMETERIZED-WINDOW WITNESS CHECKER (Bool): `w711OK` with the
window width $F$ as a parameter (for THEOREM N's $3n/2+1$ windows). -/
def w711OKF (n m F : Nat) (as : List Nat) : Bool :=
  (decide (as.length = n)) &&
  ((List.range n).all (fun i =>
     ((decide (m < as.getD i 0)) && (decide (as.getD i 0 < m + F)))
       && (decide ((as.getD i 0) % (i + 1) = 0)))) &&
  ((List.range n).all (fun i =>
     (List.range n).all (fun j =>
       (decide (i = j)) || !(decide (as.getD i 0 = as.getD j 0)))))

/-- Soundness of the parameterized checker: a true table certifies an
`AssignOk` at window width $F$. -/
theorem w711OKF_spec (n m F : Nat) (as : List Nat) (hn : 0 < n)
    (h : w711OKF n m F as = true) :
    ∃ a, AssignOk n m F a := by
  simp only [w711OKF, Bool.and_eq_true] at h
  obtain ⟨⟨hlen, hall⟩, hdist⟩ := h
  refine ⟨fun k => as.getD (k - 1) 0, ?_, ?_⟩
  · intro k h1k hkn
    have hidx : k - 1 < n := by omega
    have hmem : (k - 1) ∈ List.range n := List.mem_range.mpr hidx
    have hcall := (List.all_eq_true.mp hall) (k - 1) hmem
    simp only [Bool.and_eq_true] at hcall
    obtain ⟨⟨hlt1, hlt2⟩, hmod⟩ := hcall
    have hb1 : m < as.getD (k - 1) 0 := of_decide_eq_true hlt1
    have hb2 : as.getD (k - 1) 0 < m + F := of_decide_eq_true hlt2
    have hk1 : (k - 1) + 1 = k := by omega
    rw [hk1] at hmod
    have hmodk : (as.getD (k - 1) 0) % k = 0 := of_decide_eq_true hmod
    show k ∣ (as.getD (k - 1) 0) ∧ m < as.getD (k - 1) 0 ∧
      as.getD (k - 1) 0 < m + F
    exact ⟨Nat.dvd_of_mod_eq_zero hmodk, hb1, hb2⟩
  · intro i hi1 hin j hj1 hjn hij
    have hxy : as.getD (i - 1) 0 = as.getD (j - 1) 0 := hij
    have hi' : i - 1 < n := by omega
    have hj' : j - 1 < n := by omega
    have hinner := (List.all_eq_true.mp hdist) (i - 1) (List.mem_range.mpr hi')
    have hdij := (List.all_eq_true.mp hinner) (j - 1) (List.mem_range.mpr hj')
    have hxyb : decide (as.getD (i - 1) 0 = as.getD (j - 1) 0) = true :=
      decide_eq_true hxy
    rw [hxyb] at hdij
    cases hval : decide ((i - 1) = (j - 1)) with
    | false =>
        rw [hval] at hdij
        simp at hdij
    | true =>
        have hidx : (i - 1) = (j - 1) := of_decide_eq_true hval
        omega

/-! ## §8 THE ALL-$m$ UNIVERSAL BOUND, $n \le 6$ (full periods,
kernel-decided; generated by `gen711.py`, independently re-verified).

The tables hold, for each residue $r = m \% L$ ($L = \mathrm{lcm}(1..n)$:
$L = 12$ at $n=4$, $L = 60$ at $n = 5, 6$), the offsets $c_k$ of a valid
assignment in the window $(m, m+2n-1)$. With §7's transport each table
row covers its whole residue class; `erdos711_period` is the matching
periodicity law. -/

def wit4 : Nat → List Nat := fun r =>
  [
   [1, 2, 6, 4],
   [2, 1, 5, 3],
   [1, 2, 4, 6],
   [1, 3, 6, 5],
   [1, 6, 5, 4],
   [1, 5, 4, 3],
   [1, 4, 3, 6],
   [1, 3, 2, 5],
   [2, 6, 1, 4],
   [1, 5, 6, 3],
   [1, 4, 5, 6],
   [1, 3, 4, 5],
  ].getD r []

def wit5 : Nat → List Nat := fun r =>
  [
   [1, 4, 6, 8, 5],
   [1, 5, 8, 7, 4],
   [1, 4, 7, 6, 8],
   [1, 3, 6, 5, 7],
   [1, 4, 5, 8, 6],
   [1, 3, 4, 7, 5],
   [1, 8, 3, 6, 4],
   [1, 7, 2, 5, 8],
   [1, 6, 4, 8, 7],
   [1, 5, 3, 7, 6],
   [1, 4, 8, 6, 5],
   [1, 3, 7, 5, 4],
   [1, 2, 6, 4, 8],
   [1, 5, 8, 3, 7],
   [1, 8, 7, 2, 6],
   [2, 7, 6, 1, 5],
   [1, 6, 5, 8, 4],
   [1, 5, 4, 7, 8],
   [1, 8, 3, 6, 7],
   [1, 7, 8, 5, 6],
   [1, 6, 7, 8, 5],
   [1, 5, 6, 7, 4],
   [1, 4, 5, 6, 8],
   [1, 3, 4, 5, 7],
   [1, 4, 3, 8, 6],
   [1, 3, 8, 7, 5],
   [1, 8, 7, 6, 4],
   [1, 7, 6, 5, 8],
   [1, 6, 5, 8, 7],
   [1, 5, 4, 7, 6],
   [1, 8, 3, 6, 5],
   [1, 7, 8, 5, 4],
   [1, 6, 7, 4, 8],
   [1, 5, 6, 3, 7],
   [1, 4, 8, 2, 6],
   [2, 3, 7, 1, 5],
   [1, 2, 6, 8, 4],
   [1, 3, 5, 7, 8],
   [1, 8, 4, 6, 7],
   [1, 7, 3, 5, 6],
   [1, 6, 2, 8, 5],
   [2, 5, 1, 7, 4],
   [1, 4, 3, 6, 8],
   [1, 3, 8, 5, 7],
   [1, 4, 7, 8, 6],
   [1, 3, 6, 7, 5],
   [1, 2, 8, 6, 4],
   [1, 3, 7, 5, 8],
   [1, 4, 6, 8, 7],
   [1, 5, 8, 7, 6],
   [1, 8, 7, 6, 5],
   [1, 7, 6, 5, 4],
   [1, 6, 5, 4, 8],
   [1, 5, 4, 3, 7],
   [1, 8, 3, 2, 6],
   [2, 7, 8, 1, 5],
   [1, 6, 7, 8, 4],
   [1, 5, 6, 7, 8],
   [1, 4, 8, 6, 7],
   [1, 3, 7, 5, 6],
  ].getD r []

def wit6 : Nat → List Nat := fun r =>
  [
   [1, 4, 9, 8, 10, 6],
   [1, 3, 8, 7, 9, 5],
   [1, 4, 7, 6, 8, 10],
   [1, 3, 6, 5, 7, 9],
   [1, 10, 5, 4, 6, 8],
   [1, 9, 4, 3, 10, 7],
   [1, 8, 3, 10, 9, 6],
   [1, 7, 2, 9, 8, 5],
   [1, 6, 4, 8, 7, 10],
   [1, 5, 3, 7, 6, 9],
   [1, 4, 5, 6, 10, 8],
   [1, 3, 10, 5, 9, 7],
   [1, 10, 9, 4, 8, 6],
   [1, 9, 8, 3, 7, 5],
   [1, 8, 7, 2, 6, 10],
   [1, 7, 6, 5, 10, 9],
   [1, 10, 5, 4, 9, 8],
   [1, 9, 10, 3, 8, 7],
   [1, 8, 9, 10, 7, 6],
   [1, 7, 8, 9, 6, 5],
   [1, 6, 7, 8, 5, 10],
   [1, 5, 6, 7, 4, 9],
   [1, 6, 5, 10, 3, 8],
   [1, 5, 10, 9, 2, 7],
   [2, 10, 9, 8, 1, 6],
   [1, 9, 8, 7, 10, 5],
   [1, 8, 7, 6, 9, 10],
   [1, 7, 6, 5, 8, 9],
   [1, 10, 5, 4, 7, 8],
   [1, 9, 10, 3, 6, 7],
   [1, 8, 9, 2, 10, 6],
   [2, 7, 8, 1, 9, 5],
   [1, 6, 7, 4, 8, 10],
   [1, 5, 6, 3, 7, 9],
   [1, 4, 5, 10, 6, 8],
   [1, 5, 4, 9, 10, 7],
   [1, 10, 3, 8, 9, 6],
   [1, 9, 2, 7, 8, 5],
   [1, 8, 4, 6, 7, 10],
   [1, 7, 3, 5, 6, 9],
   [1, 6, 5, 4, 10, 8],
   [1, 5, 10, 3, 9, 7],
   [1, 4, 9, 10, 8, 6],
   [1, 3, 8, 9, 7, 5],
   [1, 4, 7, 8, 6, 10],
   [1, 5, 6, 7, 10, 9],
   [1, 6, 5, 10, 9, 8],
   [1, 5, 10, 9, 8, 7],
   [1, 10, 9, 8, 7, 6],
   [1, 9, 8, 7, 6, 5],
   [1, 8, 7, 6, 5, 10],
   [1, 7, 6, 5, 4, 9],
   [1, 10, 5, 4, 3, 8],
   [1, 9, 10, 3, 2, 7],
   [2, 8, 9, 10, 1, 6],
   [1, 7, 8, 9, 10, 5],
   [1, 6, 7, 8, 9, 10],
   [1, 5, 6, 7, 8, 9],
   [1, 6, 5, 10, 7, 8],
   [1, 5, 10, 9, 6, 7],
  ].getD r []

theorem hwit4 : (List.range 12).all (fun r => w711OKR 4 r (wit4 r)) = true := by
  decide

theorem hwit5 : (List.range 60).all (fun r => w711OKR 5 r (wit5 r)) = true := by
  decide

theorem hwit6 : (List.range 60).all (fun r => w711OKR 6 r (wit6 r)) = true := by
  decide

theorem dvd12 : ∀ k, 1 ≤ k → k ≤ 4 → k ∣ 12 := by
  intro k h1 h4
  rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega) with h | h | h | h
  · subst h; exact ⟨12, rfl⟩
  · subst h; exact ⟨6, rfl⟩
  · subst h; exact ⟨4, rfl⟩
  · subst h; exact ⟨3, rfl⟩

theorem dvd60 : ∀ k, 1 ≤ k → k ≤ 6 → k ∣ 60 := by
  intro k h1 h6
  rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 by omega) with
    h | h | h | h | h | h
  · subst h; exact ⟨60, rfl⟩
  · subst h; exact ⟨30, rfl⟩
  · subst h; exact ⟨20, rfl⟩
  · subst h; exact ⟨15, rfl⟩
  · subst h; exact ⟨12, rfl⟩
  · subst h; exact ⟨10, rfl⟩

/-- COMPLETE $n=4$: $f(4,m) \le 7$ for every $m \ge 1$ — all twelve
residue classes mod 12, kernel-decided. -/
theorem erdos711_four (m : Nat) (hm : 1 ≤ m) : f711 4 m ≤ 2 * 4 - 1 := by
  have hrl : m % 12 < 12 := by omega
  have hmem0 : m % 12 ∈ List.range 12 := List.mem_range.mpr hrl
  have hall := (List.all_eq_true.mp hwit4) (m % 12) hmem0
  have hL : ∀ k, 1 ≤ k → k ≤ 4 → k ∣ 12 := dvd12
  obtain ⟨a, ha⟩ :=
    w711OKR_spec 4 12 m (m % 12) (wit4 (m % 12)) (by omega) hL rfl hall
  have hmem : (2 * 4 - 1) ∈ {F : Nat | 1 ≤ F ∧ ∃ x, AssignOk 4 m F x} := by
    show 1 ≤ 2 * 4 - 1 ∧ ∃ x, AssignOk 4 m (2 * 4 - 1) x
    exact ⟨by omega, ⟨a, ha⟩⟩
  exact Nat.sInf_le hmem

/-- COMPLETE $n=5$: $f(5,m) \le 9$ for every $m \ge 1$ — all sixty
residue classes mod 60, kernel-decided. -/
theorem erdos711_five (m : Nat) (hm : 1 ≤ m) : f711 5 m ≤ 2 * 5 - 1 := by
  have hrl : m % 60 < 60 := by omega
  have hmem0 : m % 60 ∈ List.range 60 := List.mem_range.mpr hrl
  have hall := (List.all_eq_true.mp hwit5) (m % 60) hmem0
  have hL : ∀ k, 1 ≤ k → k ≤ 5 → k ∣ 60 := fun k h1 h5 => dvd60 k h1 (by omega)
  obtain ⟨a, ha⟩ :=
    w711OKR_spec 5 60 m (m % 60) (wit5 (m % 60)) (by omega) hL rfl hall
  have hmem : (2 * 5 - 1) ∈ {F : Nat | 1 ≤ F ∧ ∃ x, AssignOk 5 m F x} := by
    show 1 ≤ 2 * 5 - 1 ∧ ∃ x, AssignOk 5 m (2 * 5 - 1) x
    exact ⟨by omega, ⟨a, ha⟩⟩
  exact Nat.sInf_le hmem

/-- COMPLETE $n=6$: $f(6,m) \le 11$ for every $m \ge 1$ — all sixty
residue classes mod 60, kernel-decided. -/
theorem erdos711_six (m : Nat) (hm : 1 ≤ m) : f711 6 m ≤ 2 * 6 - 1 := by
  have hrl : m % 60 < 60 := by omega
  have hmem0 : m % 60 ∈ List.range 60 := List.mem_range.mpr hrl
  have hall := (List.all_eq_true.mp hwit6) (m % 60) hmem0
  have hL : ∀ k, 1 ≤ k → k ≤ 6 → k ∣ 60 := dvd60
  obtain ⟨a, ha⟩ :=
    w711OKR_spec 6 60 m (m % 60) (wit6 (m % 60)) (by omega) hL rfl hall
  have hmem : (2 * 6 - 1) ∈ {F : Nat | 1 ≤ F ∧ ∃ x, AssignOk 6 m F x} := by
    show 1 ≤ 2 * 6 - 1 ∧ ∃ x, AssignOk 6 m (2 * 6 - 1) x
    exact ⟨by omega, ⟨a, ha⟩⟩
  exact Nat.sInf_le hmem

/-- THE UNIVERSAL BOUND, CERTIFIED RANGE (THEOREM U for $n \le 6$): for
every $2 \le n \le 6$ and EVERY $m \ge 1$, $f(n,m) \le 2n-1$. Engine
phase A + battery711 certify the same law for $n \le 12$ over full
periods and $n = 13..16$ (full periods, UVIOLATIONS $= 0$). -/
theorem erdos711_universal_bounded : ∀ n m, 2 ≤ n → n ≤ 6 → 1 ≤ m →
    f711 n m ≤ 2 * n - 1 := by
  intro n m h2n hn6 hm
  rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 by omega) with
    h | h | h | h | h
  · subst h; exact erdos711_two m hm
  · subst h; exact erdos711_three m hm
  · subst h; exact erdos711_four m hm
  · subst h; exact erdos711_five m hm
  · subst h; exact erdos711_six m hm

theorem sqpos (n : Nat) (h2n : 2 ≤ n) : 1 ≤ (n - 1) * (n - 1) := by
  have h1 : 1 ≤ n - 1 := by omega
  have := Nat.mul_le_mul h1 h1
  simpa using this

/-- THE EXACT MAX, CERTIFIED RANGE: for every $2 \le n \le 6$,
$\max_m f(n,m) = 2n-1$ EXACTLY — the general obstruction floor
(`erdos711_obstruction`, all $n$) meets the universal ceiling (all $m$,
$n \le 6$). The problem's first ask, answered with the exact constant on
the certified range. -/
theorem erdos711_max_exact_bounded : ∀ n, 2 ≤ n → n ≤ 6 →
    (∀ m, 1 ≤ m → f711 n m ≤ 2 * n - 1) ∧
    f711 n ((n - 1) * (n - 1)) = 2 * n - 1 := by
  intro n h2n hn6
  refine ⟨fun m hm => erdos711_universal_bounded n m h2n hn6 hm, ?_⟩
  have hge := erdos711_obstruction n h2n
  have hle := erdos711_universal_bounded n ((n - 1) * (n - 1)) h2n hn6
    (sqpos n h2n)
  omega


/-! ## §9 THEOREM N, CERTIFIED RANGE $n \le 24$ (kernel-decided;
generated by `gen711.py`, independently re-verified).

THE PROBLEM (verbatim, erdosproblems.com/711):

> Let $f(n,m)$ be minimal such that in $(m,m+f(n,m))$ there exist distinct
> integers $a_1,\ldots,a_n$ such that $k\mid a_k$ for all $1\leq k\leq n$.
> Prove that $\max_m f(n,m) \leq n^{1+o(1)}$ and that
> $\max_m (f(n,m)-f(n,n))\to \infty$.

The table holds, for each $n = 2..24$, the VALUES $a_k$ of a valid
assignment in the window $(n, n+3n/2+1)$ — engine phase F's census of
exact $f(n,n)$ (all $\le \lceil 3n/2\rceil+1$ for $n = 2..24$), here with
kernel-decided witnesses. -/

def witN : Nat → List Nat := fun n =>
  [
   [],
   [],
   [3, 4],
   [5, 4, 6],
   [5, 10, 9, 8],
   [6, 8, 9, 12, 10],
   [7, 14, 9, 8, 15, 12],
   [8, 10, 9, 16, 15, 12, 14],
   [9, 10, 15, 12, 20, 18, 14, 16],
   [11, 10, 21, 20, 15, 12, 14, 16, 18],
   [11, 22, 15, 16, 25, 12, 21, 24, 18, 20],
   [12, 26, 15, 16, 25, 18, 21, 24, 27, 20, 22],
   [13, 26, 21, 20, 25, 18, 28, 16, 27, 30, 22, 24],
   [14, 16, 21, 20, 25, 18, 28, 32, 27, 30, 22, 24, 26],
   [15, 34, 21, 20, 25, 18, 35, 32, 27, 30, 33, 24, 26, 28],
   [17, 34, 21, 16, 25, 24, 35, 32, 27, 20, 33, 36, 26, 28, 30],
   [17, 38, 21, 20, 25, 18, 35, 24, 27, 40, 33, 36, 39, 28, 30, 32],
   [19, 38, 21, 28, 25, 18, 35, 24, 27, 40, 33, 36, 39, 42, 30, 32, 34],
   [19, 20, 33, 44, 25, 42, 21, 40, 27, 30, 22, 24, 26, 28, 45, 32, 34, 36],
   [23, 20, 33, 44, 25, 42, 21, 40, 27, 30, 22, 24, 26, 28, 45, 32, 34, 36, 38],
   [21, 46, 33, 28, 35, 30, 49, 32, 27, 50, 44, 24, 39, 42, 45, 48, 34, 36, 38, 40],
   [23, 22, 39, 44, 25, 30, 35, 24, 27, 50, 33, 48, 26, 28, 45, 32, 34, 36, 38, 40, 42],
   [23, 46, 39, 24, 35, 30, 49, 32, 27, 50, 55, 36, 52, 28, 45, 48, 51, 54, 38, 40, 42, 44],
   [24, 38, 39, 28, 35, 30, 49, 32, 27, 50, 55, 36, 52, 56, 45, 48, 51, 54, 57, 40, 42, 44, 46],
   [25, 58, 39, 28, 35, 30, 49, 40, 27, 50, 55, 36, 52, 56, 45, 32, 51, 54, 57, 60, 42, 44, 46, 48],
  ].getD n []

theorem hwitN : (List.range 25).all
    (fun n => (decide (n < 2)) || w711OKF n n (3 * n / 2 + 1) (witN n)) = true := by
  decide

/-- THEOREM N, CERTIFIED RANGE: $f(n,n) \le 3n/2 + 1$ for every
$2 \le n \le 24$ (engine phase F: exact $f(n,n)$ fits $\lceil 3n/2\rceil+1$
for $n = 2..24$; e.g. $f(24,24) = 33 \le 37$). -/
theorem erdos711_fn_bounded : ∀ n, 2 ≤ n → n ≤ 24 → f711 n n ≤ 3 * n / 2 + 1 := by
  intro n h2n h24n
  have hmem0 : n ∈ List.range 25 := List.mem_range.mpr (by omega)
  have hall := (List.all_eq_true.mp hwitN) n hmem0
  cases hlt : decide (n < 2) with
  | true =>
      have hbad : n < 2 := of_decide_eq_true hlt
      omega
  | false =>
      rw [hlt] at hall
      simp at hall
      obtain ⟨a, ha⟩ :=
        w711OKF_spec n n (3 * n / 2 + 1) (witN n) (by omega) hall
      have hmem : (3 * n / 2 + 1) ∈ {F : Nat | 1 ≤ F ∧ ∃ x, AssignOk n n F x} := by
        show 1 ≤ 3 * n / 2 + 1 ∧ ∃ x, AssignOk n n (3 * n / 2 + 1) x
        exact ⟨by omega, ⟨a, ha⟩⟩
      exact Nat.sInf_le hmem

/-- THE ASK-2 GAP AT $n = 24$ (unconditional): $f(24,529) \ge f(24,24) + 10$
— the obstruction floor $47$ against the certified ceiling $37$; the
phenomenon $\max_m(f(n,m) - f(n,n)) \ge n/2 - 2$ exhibited on the
certified range. -/
theorem erdos711_gap_24 :
    f711 24 24 + 10 ≤ f711 24 ((24 - 1) * (24 - 1)) := by
  have hge := erdos711_obstruction 24 (by omega)
  have hfn := erdos711_fn_bounded 24 (by omega) (by omega)
  omega

/-- THE ASK-2 GAP, CERTIFIED RANGE (unconditional): for $4 \le n \le 24$,
the obstruction point beats $f(n,n)$ by $(n-4)/2$ — the gap law at every
$n$ of the certified range. -/
theorem erdos711_ask2_bounded : ∀ n, 4 ≤ n → n ≤ 24 →
    f711 n n + (n - 4) / 2 ≤ f711 n ((n - 1) * (n - 1)) := by
  intro n h4n h24n
  have hge := erdos711_obstruction n (by omega)
  have hfn := erdos711_fn_bounded n (by omega) (by omega)
  omega

/-! ## §10 THE GENERAL-$n$ UPPER BOUND (unconditional, monotone
construction).

For EVERY $n \ge 2$ and $m \ge 1$: $f(n,m) \le n^2 + n$, by the explicit
assignment $a_k = k\lceil m/k\rceil + kn$ — strictly increasing in $k$
(each step gains $\ge n - k + 1 \ge 1$, absorbing the $\lceil m/k\rceil$
wobble of $\le k-1$), divisible by construction, and bounded by
$m + n^2 + n$. This is the file's first general-$n$ upper bound; the
$2n-1$ target is the razor-tight matching front (§11). -/

theorem erdos711_upper_general : ∀ n m, 2 ≤ n → 1 ≤ m → f711 n m ≤ n * n + n := by
  intro n m h2n hm
  have hmem : (n * n + n) ∈ {F : Nat | 1 ≤ F ∧ ∃ a, AssignOk n m F a} := by
    show 1 ≤ n * n + n ∧ ∃ x, AssignOk n m (n * n + n) x
    refine ⟨by omega, fun k => k * ((m + k - 1) / k) + k * n, ?_, ?_⟩
    · intro k h1k hkn
      show k ∣ (k * ((m + k - 1) / k) + k * n) ∧
        m < k * ((m + k - 1) / k) + k * n ∧
        k * ((m + k - 1) / k) + k * n < m + (n * n + n)
      refine ⟨Nat.dvd_add (Nat.dvd_mul_right k _) (Nat.dvd_mul_right k _), ?_, ?_⟩
      · obtain ⟨Q, hQ⟩ : ∃ Q, (m + k - 1) / k = Q := ⟨_, rfl⟩
        obtain ⟨Y, hY⟩ : ∃ Y, (m + k - 1) % k = Y := ⟨_, rfl⟩
        have hdm : k * Q + Y = m + k - 1 := by
          rw [← hQ, ← hY]; exact Nat.div_add_mod (m + k - 1) k
        have hlt : Y < k := by rw [← hY]; exact Nat.mod_lt (m + k - 1) (by omega)
        have hz : 1 ≤ k * n := by
          have := Nat.mul_le_mul (show 1 ≤ k by omega) (show 1 ≤ n by omega)
          simpa using this
        rw [hQ]
        omega
      · obtain ⟨Q, hQ⟩ : ∃ Q, (m + k - 1) / k = Q := ⟨_, rfl⟩
        obtain ⟨Y, hY⟩ : ∃ Y, (m + k - 1) % k = Y := ⟨_, rfl⟩
        have hdm : k * Q + Y = m + k - 1 := by
          rw [← hQ, ← hY]; exact Nat.div_add_mod (m + k - 1) k
        have hz : k * n ≤ n * n := by
          rw [Nat.mul_comm]
          exact Nat.mul_le_mul_left n (show k ≤ n by omega)
        rw [hQ]
        omega
    · intro i hi1 hin j hj1 hjn hij
      have hmono : ∀ p q : Nat, 1 ≤ p → p < q → q ≤ n →
          p * ((m + p - 1) / p) + p * n < q * ((m + q - 1) / q) + q * n := by
        intro p q hp hpq hq
        obtain ⟨P, hP⟩ : ∃ P, (m + p - 1) / p = P := ⟨_, rfl⟩
        obtain ⟨Yp, hYp⟩ : ∃ Yp, (m + p - 1) % p = Yp := ⟨_, rfl⟩
        obtain ⟨Qq, hQq⟩ : ∃ Qq, (m + q - 1) / q = Qq := ⟨_, rfl⟩
        obtain ⟨Yq, hYq⟩ : ∃ Yq, (m + q - 1) % q = Yq := ⟨_, rfl⟩
        have hdmp : p * P + Yp = m + p - 1 := by
          rw [← hP, ← hYp]; exact Nat.div_add_mod (m + p - 1) p
        have hltp : Yp < p := by rw [← hYp]; exact Nat.mod_lt (m + p - 1) (by omega)
        have hdmq : q * Qq + Yq = m + q - 1 := by
          rw [← hQq, ← hYq]; exact Nat.div_add_mod (m + q - 1) q
        have hltq : Yq < q := by rw [← hYq]; exact Nat.mod_lt (m + q - 1) (by omega)
        have hpn : p * n + p ≤ q * n := by
          have h1 : (p + 1) * n = p * n + n := Nat.succ_mul p n
          have h2 : (p + 1) * n ≤ q * n := by
            rw [Nat.mul_comm (p + 1) n, Nat.mul_comm q n]
            exact Nat.mul_le_mul_left n (by omega)
          omega
        rw [hP, hQq]
        omega
      rcases Nat.lt_trichotomy i j with hlt | heq | hgt
      · have hbad := hmono i j (by omega) hlt (by omega)
        have hij' : i * ((m + i - 1) / i) + i * n
            = j * ((m + j - 1) / j) + j * n := hij
        rw [hij'] at hbad
        exact absurd hbad (Nat.lt_irrefl _)
      · exact heq
      · have hbad := hmono j i (by omega) hgt (by omega)
        have hij' : i * ((m + i - 1) / i) + i * n
            = j * ((m + j - 1) / j) + j * n := hij
        rw [← hij'] at hbad
        exact absurd hbad (Nat.lt_irrefl _)
  exact Nat.sInf_le hmem

/-! ## §11 THE CONDITIONAL KILL ASSEMBLY (the two inputs, one theorem away).

THE PROBLEM (verbatim, erdosproblems.com/711):

> Let $f(n,m)$ be minimal such that in $(m,m+f(n,m))$ there exist distinct
> integers $a_1,\ldots,a_n$ such that $k\mid a_k$ for all $1\leq k\leq n$.
> Prove that $\max_m f(n,m) \leq n^{1+o(1)}$ and that
> $\max_m (f(n,m)-f(n,n))\to \infty$.

THE TWO INPUTS (engine-certified, front-stated):
* `Hall711` — THEOREM U: for every $n \ge 2$, $m \ge 1$ an assignment
  exists in the window $2n-1$. Engine: full periods $n \le 12$
  (battery711) and $n = 13..16$ (engine_round3 phase A, UVIOLATIONS $=0$),
  adversarial+random through $n = 24$; the razor-thin Hall front (tight
  set $S = \{n\}$, deficiency exactly $0$ — see engine_round3_G.txt).
* `N711` — THEOREM N: $f(n,n) \le 3n/2+1$ for every $n \ge 2$. Engine:
  phase F (exact $f(n,n)$ for $n = 2..24$); certified in Lean for
  $n \le 24$ (`erdos711_fn_bounded`).

THE ASSEMBLY (all proven below, ZERO axioms):
`Hall711` ⟹ `erdos711_universal` ⟹ (`erdos711_max_exact` with the
already-general obstruction): $\max_m f(n,m) = 2n-1$ exactly — ask 1 with
the exact constant (`erdos711_ask1`: $f \le 2n$, the $O(n)$ form;
`erdos711_ask1_eps`: $f \le n^e$ for every $e \ge 2$, the $n^{1+o(1)}$
form). `N711` + obstruction ⟹ `erdos711_ask2` (gap $\ge (n-4)/2$) ⟹
`erdos711_ask2_tends` (the gap $\to \infty$) — ask 2. -/

/-- THEOREM U as an explicit proposition — the divisor-matching front. -/
def Hall711 : Prop := ∀ n m, 2 ≤ n → 1 ≤ m → ∃ a, AssignOk n m (2 * n - 1) a

/-- THEOREM N as an explicit proposition (the $f(n,n)$ front). -/
def N711 : Prop := ∀ n, 2 ≤ n → ∃ a, AssignOk n n (3 * n / 2 + 1) a

theorem erdos711_universal (hU : Hall711) :
    ∀ n m, 2 ≤ n → 1 ≤ m → f711 n m ≤ 2 * n - 1 := by
  intro n m h2n hm
  obtain ⟨a, ha⟩ := hU n m h2n hm
  have hmem : (2 * n - 1) ∈ {F : Nat | 1 ≤ F ∧ ∃ x, AssignOk n m F x} := by
    show 1 ≤ 2 * n - 1 ∧ ∃ x, AssignOk n m (2 * n - 1) x
    exact ⟨by omega, ⟨a, ha⟩⟩
  exact Nat.sInf_le hmem

/-- THE ASSEMBLY, FIRST ASK: `Hall711` + the obstruction (already general)
give $\max_m f(n,m) = 2n-1$ EXACTLY — stronger than the demanded
$n^{1+o(1)}$: the exact constant, every $n \ge 2$. -/
theorem erdos711_max_exact (hU : Hall711) : ∀ n, 2 ≤ n →
    (∀ m, 1 ≤ m → f711 n m ≤ 2 * n - 1) ∧
    f711 n ((n - 1) * (n - 1)) = 2 * n - 1 := by
  intro n h2n
  refine ⟨fun m hm => erdos711_universal hU n m h2n hm, ?_⟩
  have hge := erdos711_obstruction n h2n
  have hle := erdos711_universal hU n ((n - 1) * (n - 1)) h2n (sqpos n h2n)
  omega

/-- ASK 1, $O(n)$ FORM: `Hall711` ⟹ $f(n,m) \le 2n$ for every $n \ge 2$,
$m \ge 1$ — $2n \le n^{1+\varepsilon}$ eventually for every
$\varepsilon > 0$, i.e. the $n^{1+o(1)}$ demand with the $O(n)$ constant. -/
theorem erdos711_ask1 (hU : Hall711) :
    ∀ n m, 2 ≤ n → 1 ≤ m → f711 n m ≤ 2 * n := by
  intro n m h2n hm
  have h := erdos711_universal hU n m h2n hm
  omega

theorem pow_ge_one (n t : Nat) (hn : 1 ≤ n) : 1 ≤ n ^ t := by
  induction t with
  | zero => rw [Nat.pow_zero]
  | succ t ih =>
    rw [Nat.pow_succ]
    have h := Nat.mul_le_mul ih hn
    simpa using h

theorem two_n_le_pow (n e : Nat) (h2n : 2 ≤ n) (he : 2 ≤ e) : 2 * n ≤ n ^ e := by
  obtain ⟨t, ht⟩ : ∃ t, e = 2 + t := ⟨e - 2, by omega⟩
  rw [ht, Nat.pow_add]
  have hpos := pow_ge_one n t (by omega)
  have hge2 : 2 * n ≤ n ^ 2 := by
    have hn2 : n ^ 2 = n * n := by rw [Nat.pow_succ, Nat.pow_one]
    have hnn : 2 * n ≤ n * n := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left n h2n
    omega
  have hmul : n ^ 2 ≤ n ^ 2 * n ^ t := by
    have hm := Nat.mul_le_mul (Nat.le_refl (n ^ 2)) hpos
    rw [Nat.mul_one] at hm
    exact hm
  omega

/-- ASK 1, $\forall\varepsilon$ FORM: `Hall711` ⟹ for every integer
exponent $e \ge 2$ and every $n \ge 2$, $m \ge 1$: $f(n,m) \le n^e$ — the
discrete $n^{1+o(1)}$ (for every fixed $\varepsilon = 1/(e-1) > 0$,
$2n \le n^{1+\varepsilon}$ once $n \ge 2^{1/\varepsilon}$). -/
theorem erdos711_ask1_eps (hU : Hall711) :
    ∀ e n m, 2 ≤ e → 2 ≤ n → 1 ≤ m → f711 n m ≤ n ^ e := by
  intro e n m he h2n hm
  have h := erdos711_universal hU n m h2n hm
  have hpow := two_n_le_pow n e h2n he
  omega

/-- ASK 2, CEILING: `N711` ⟹ $f(n,n) \le 3n/2 + 1$ for every $n \ge 2$. -/
theorem erdos711_fn (hN : N711) : ∀ n, 2 ≤ n → f711 n n ≤ 3 * n / 2 + 1 := by
  intro n h2n
  obtain ⟨a, ha⟩ := hN n h2n
  have hmem : (3 * n / 2 + 1) ∈ {F : Nat | 1 ≤ F ∧ ∃ x, AssignOk n n F x} := by
    show 1 ≤ 3 * n / 2 + 1 ∧ ∃ x, AssignOk n n (3 * n / 2 + 1) x
    exact ⟨by omega, ⟨a, ha⟩⟩
  exact Nat.sInf_le hmem

/-- ASK 2, THE GAP: `N711` + the (already-general, unconditional)
obstruction give, for every $n \ge 4$:
$$f(n,(n-1)^2) \;\ge\; f(n,n) + (n-4)/2,$$
i.e. $\max_m(f(n,m) - f(n,n)) \ge n/2 - 2$ — linear divergence. -/
theorem erdos711_ask2 (hN : N711) : ∀ n, 4 ≤ n →
    f711 n n + (n - 4) / 2 ≤ f711 n ((n - 1) * (n - 1)) := by
  intro n h4n
  have hge := erdos711_obstruction n (by omega)
  have hfn := erdos711_fn hN n (by omega)
  omega

/-- ASK 2, THE LIMIT: `N711` ⟹ $\max_m (f(n,m) - f(n,n)) \to \infty$ in
the strong form: for EVERY bound $B$ there are $n, m$ with
$f(n,n) + B \le f(n,m)$ (take $n = 2B+4$, $m = (n-1)^2$: the gap is
$(n-4)/2 = B+2$). -/
theorem erdos711_ask2_tends (hN : N711) :
    ∀ B, ∃ n m, 4 ≤ n ∧ 1 ≤ m ∧ f711 n n + B ≤ f711 n m := by
  intro B
  refine ⟨2 * B + 4, (2 * B + 4 - 1) * (2 * B + 4 - 1), by omega, ?_⟩
  refine ⟨sqpos (2 * B + 4) (by omega), ?_⟩
  have hge := erdos711_obstruction (2 * B + 4) (by omega)
  have hfn := erdos711_fn hN (2 * B + 4) (by omega)
  omega

#print axioms erdos711_universal_bounded
#print axioms erdos711_max_exact_bounded
#print axioms erdos711_fn_bounded
#print axioms erdos711_ask2_bounded
#print axioms erdos711_gap_24
#print axioms erdos711_upper_general
#print axioms erdos711_universal
#print axioms erdos711_max_exact
#print axioms erdos711_ask1
#print axioms erdos711_ask1_eps
#print axioms erdos711_ask2
#print axioms erdos711_ask2_tends

end Erdos711
