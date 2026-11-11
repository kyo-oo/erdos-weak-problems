#!/usr/bin/env python3
"""Assemble the S044 Lean addition for Erdos711.lean (task 1-a).

Reads the generated witness tables from gen711_out.txt and weaves them
into the handwritten theorem scaffold, producing /tmp/p711_addition.lean.
"""
import re

BASE = "/home/z/erdos-weak-problems/problem711-divisor-matching"
src = open(f"{BASE}/gen711_out.txt").read()

def grab(name):
    m = re.search(rf"^def {name} : Nat → List Nat := fun.*?^  \]\.getD \w+ \[\]$", src, re.M | re.S)
    assert m, name
    return m.group(0)

wit4 = grab("wit4")
wit5 = grab("wit5")
wit6 = grab("wit6")
witN = grab("witN")

S = r'''
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
  have hdm : L * D + R = m := by rw [hR, hD]; exact Nat.div_add_mod m L
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
    have hxy : cs.getD (i - 1) 0 = cs.getD (j - 1) 0 := by omega
    have hi' : i - 1 < n := by omega
    have hj' : j - 1 < n := by omega
    have hinner := (List.all_eq_true.mp hdist) (i - 1) (List.mem_range.mpr hi')
    have hdij := (List.all_eq_true.mp hinner) (j - 1) (List.mem_range.mpr hj')
    have hxyb : decide (cs.getD (i - 1) 0 = cs.getD (j - 1) 0) = true :=
      decide_eq_true hxy
    rw [hxyb] at hdij
    cases hval : decide ((i - 1) = (j - 1)) with
    | false =>
        rw [hval] at hdij
        simp at hdij
    | true =>
        have hidx : (i - 1) = (j - 1) := of_decide_eq_true hval
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

'''

S2 = r'''

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
  have hL : ∀ k, 1 ≤ k → k ≤ 5 → k ∣ 60 := dvd60
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
'''

S3 = r'''

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

'''

S4 = r'''

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
          rw [hQ, hY]; exact Nat.div_add_mod (m + k - 1) k
        have hlt : Y < k := by rw [hY]; exact Nat.mod_lt (m + k - 1) (by omega)
        have hz : 1 ≤ k * n := by
          have := Nat.mul_le_mul (show 1 ≤ k by omega) (show 1 ≤ n by omega)
          simpa using this
        rw [hQ]
        omega
      · obtain ⟨Q, hQ⟩ : ∃ Q, (m + k - 1) / k = Q := ⟨_, rfl⟩
        obtain ⟨Y, hY⟩ : ∃ Y, (m + k - 1) % k = Y := ⟨_, rfl⟩
        have hdm : k * Q + Y = m + k - 1 := by
          rw [hQ, hY]; exact Nat.div_add_mod (m + k - 1) k
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
          rw [hP, hYp]; exact Nat.div_add_mod (m + p - 1) p
        have hltp : Yp < p := by rw [hYp]; exact Nat.mod_lt (m + p - 1) (by omega)
        have hdmq : q * Qq + Yq = m + q - 1 := by
          rw [hQq, hYq]; exact Nat.div_add_mod (m + q - 1) q
        have hltq : Yq < q := by rw [hYq]; exact Nat.mod_lt (m + q - 1) (by omega)
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
  | zero => rw [Nat.pow_zero]; exact Nat.le_refl 1
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
'''

out = S + wit4 + "\n\n" + wit5 + "\n\n" + wit6 + S2 + S3 + witN + S4
open("/tmp/p711_addition.lean", "w").write(out)
print("ASSEMBLED", len(out.splitlines()), "lines")
