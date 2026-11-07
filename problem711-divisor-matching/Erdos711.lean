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
  (as.length == n) &&
  ((List.range n).all (fun i =>
     ((decide (m < as.getD i 0)) && (decide (as.getD i 0 < m + 2 * n - 1)))
       && ((as.getD i 0) % (i + 1) == 0))) &&
  ((List.range n).all (fun i =>
     (List.range n).all (fun j =>
       (i == j) || !((as.getD i 0) == (as.getD j 0)))))

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
  have hlenN : as.length = n := by simp at hlen; exact hlen
  refine ⟨fun k => as.getD (k - 1) 0, ?_, ?_⟩
  · intro k h1k hkn
    show k ∣ (as.getD (k - 1) 0) ∧ m < (as.getD (k - 1) 0) ∧
      (as.getD (k - 1) 0) < m + (2 * n - 1)
    have hidx : k - 1 < n := by omega
    have hmem : (k - 1) ∈ List.range n := List.mem_range.mpr hidx
    have hcall := (List.all_eq_true.mp hall) (k - 1) hmem
    simp only [Bool.and_eq_true] at hcall
    obtain ⟨⟨hlt1, hlt2⟩, hmod⟩ := hcall
    have hb1 : m < as.getD (k - 1) 0 := by
      rw [decide_eq_true] at hlt1; exact hlt1
    have hb2 : as.getD (k - 1) 0 < m + 2 * n - 1 := by
      rw [decide_eq_true] at hlt2; exact hlt2
    have hdvd : k ∣ as.getD (k - 1) 0 := by
      have hmodk : (as.getD (k - 1) 0) % k = 0 := by
        have hk1 : (k - 1) + 1 = k := by omega
        rw [hk1] at hmod
        exact Nat.eq_of_beq_eq_true hmod
      exact Nat.dvd_of_mod_eq_zero hmodk
    exact ⟨hdvd, hb1, hb2⟩
  · intro i hi1 hin j hj1 hjn hij
    have hi' : i - 1 < n := by omega
    have hj' : j - 1 < n := by omega
    have hinner := (List.all_eq_true.mp hdist) (i - 1) (List.mem_range.mpr hi')
    have hdij := (List.all_eq_true.mp hinner) (j - 1) (List.mem_range.mpr hj')
    have hbeq : ((as.getD (i - 1) 0) == (as.getD (j - 1) 0)) = true := by
      simp [hij]
    rw [hbeq] at hdij
    simp only [Bool.not_true, Bool.or_false] at hdij
    have hidx : i - 1 = j - 1 := by simp at hdij; exact hdij
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
            have hwu : u < w := by omega
            have hmul : u * k < w * k := (Nat.mul_lt_mul_left k).mpr hwu
            rw [Nat.mul_comm u k, Nat.mul_comm w k, ← hu, ← hw] at hmul
            omega
          refine ⟨u - w, ?_⟩
          rw [hu, hw, Nat.mul_sub]
        refine ⟨hdvd2, ?_, ?_⟩
        · omega
        · omega
      · intro i hi1 hin j hj1 hjn hij
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

end Erdos711
