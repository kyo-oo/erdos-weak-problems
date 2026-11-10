/-
# ERDŐS #404 — THE RESIDUAL-TAIL CLASS LAW (Kernel 37, S042 full-proof campaign, r2)

## THE PROBLEM (verbatim, erdosproblems.com/404)

> For which integers $a \geq 1$ and primes $p$ is there a finite upper bound on
> those $k$ such that there are $a = a_1 < \cdots < a_n$ with
> $p^k \mid (a_1! + \cdots + a_n!)$?
> If $f(a,p)$ is the greatest such $k$, how does this function behave?
> Is there a prime $p$ and an infinite sequence $a_1 < a_2 < \cdots$ such that
> if $p^{m_k}$ is the highest power of $p$ dividing $\sum_{i \leq k} a_i!$
> then $m_k \to \infty$?

## THE NEW CLASS THEOREM (this kernel)

**THE RESIDUAL-TAIL CLASS LAW.**  For every `m ≥ 3`, every prime `p` with
`(m−1)·(m−1)! + 1 < p`, every seed `a ≥ 1` with `a ≡ p − m (mod p)`, and
every finite set `B` of distinct indices beyond `a`:

    v_p (a! + Σ_{i ∈ B} i!)  =  v_p (a!).

That is: **`f(a,p) = v_p(a!)` on the whole residual-tail family** — the
valuation NEVER grows, exactly as on the Kill-#15 class `p ∣ a+1`, but for a
NEW two-parameter family of classes.  For each prime `p` the covered seeds
are `a ≡ p−3, p−4, …, p−m_max (mod p)` with `m_max` the largest `m` with
`(m−1)·(m−1)! < p−1` — e.g. at `p = 101`: `a ≡ 98, 97, 96 (mod 101)`.

**THE m = 3 SHARPENING (Theorem B2).**  For every prime `p ≥ 7` and every
`a ≡ p − 3 (mod p)`: `f(a,p) = v_p(a!)` — the tail bound at `m = 3` is
`2·2! + 1 = 5 < p`, so the whole `m = 3` class is covered.

## THE ENGINE (r2: the DIVISIBILITY architecture — zero Int-mod lemmas)

The staircase split (Theorem A, Kill #7): every sum factors as
`a! + Σ i! = a! · (1 + Σ P_i)` with `P_i = pt a (i − a)` the product
staircase `(a+1)(a+2)···(a+i−a)`.  It suffices to show `p ∤ (1 + Σ P_i)`.

On the class `a ≡ −m (mod p)` each unit-block coin satisfies the SIGNED
FALLING-FACTORIAL CONGRUENCE `pt a j ≡ (−1)^j · ff m j (mod p)` with
`ff m j = (m−1)(m−2)···(m−j)` — proved here as a **divisibility**
`p ∣ (pt a j − (−1)^j · ff m j)` in ℤ by induction (pure ring arithmetic,
the seed split `a + j + 1 = k·p − (m−1−j)` closing the step), and the tail
coins die by `p ∣ pt a j` for `j ≥ m`.  A set of DISTINCT indices hits at
most one coin per level `j ∈ [1, m−1]` (the pigeonhole: `≤ m−1` coins), so
the signed block sum `s = bsumI` satisfies `(m−1) ∣ s` and
`−(m−1)·(m−1)! ≤ s ≤ (m−1)·(m−1)!` (two-sided triangle).  If
`p ∣ (1 + Σ P)` then `1 + s = p·t`, and the bounds force `−p < 1 + s < p`,
so `t = 0` and `s = −1` — impossible since `(m−1) ∣ s` with `m ≥ 3`.
So `p ∤ (1 + Σ P)` ALWAYS: the first p-adic level is obstructed on the whole
family, and `f(a,p) = v_p(a!)` exactly.

Engine: the K15 valuation architecture (`vpadf`/`vpad`, saturation, step,
non-divisor laws), the K15 Theorem-A split, a Euclid-powered multiplicative
law (fuel induction + `Nat.Prime.dvd_mul`), the growth_G1 pigeonhole pattern
for the coin count (`List.Nodup.map_on` + `Nat.card_Ico` +
`List.toFinset_card_of_nodup`), and `linear_combination` for the coin-step
ring identity.  No `sorry`.  No custom axioms.  No `Int.add_mod`-family
lemmas (none exist at this pin — the r1 lesson, L72).
-/

import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

-- ===========================================================================
-- §1  THE K15 ARCHITECTURE (lifted from TheoremBGeneral.lean; the helper is
--     renamed one_le_mul_nat — Mathlib already declares one_le_mul)
-- ===========================================================================

theorem one_le_mul_nat (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  induction a with
  | zero => omega
  | succ a' =>
    have hsm : (a' + 1) * b = a' * b + b := Nat.succ_mul a' b
    omega

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- `pt u j = (u+1)(u+2)···(u+j)` — the j-fold product tail. -/
def pt : Nat → Nat → Nat
  | _, 0 => 1
  | u, j + 1 => pt u j * (u + j + 1)

theorem fact_pos : ∀ u, 1 ≤ fact u
  | 0 => by simp [fact]
  | u + 1 => one_le_mul_nat _ _ (by omega) (fact_pos u)

/-- `fact (u + j) = fact u * pt u j`. -/
theorem fact_pt : ∀ (j u : Nat), fact (u + j) = fact u * pt u j
  | 0, u => by simp [pt]
  | j + 1, u => by
      have h1 : fact (u + (j + 1)) = (u + j + 1) * fact (u + j) := rfl
      have h2 : pt u (j + 1) = pt u j * (u + j + 1) := rfl
      rw [h1, fact_pt j u, h2, Nat.mul_comm (u + j + 1) (fact u * pt u j),
      Nat.mul_assoc]

def sumF : List Nat → Nat
  | [] => 0
  | i :: B => fact i + sumF B

def sumP (a : Nat) : List Nat → Nat
  | [] => 0
  | i :: B => pt a (i - a) + sumP a B

theorem mul_add_split (a x y : Nat) :
    a * x + a * (1 + y) = a * (1 + (x + y)) := by
  have L : a * x + a * (1 + y) = a * x + (a + a * y) := by
    rw [Nat.mul_add a 1 y]
    omega
  have R : a * (1 + (x + y)) = a + (a * x + a * y) := by
    rw [Nat.mul_add a 1 (x + y), Nat.mul_add a x y]
    omega
  rw [L, R]
  omega

/-- **Theorem A (factorization).** -/
theorem sumF_split (a : Nat) : ∀ (B : List Nat), (∀ i ∈ B, a < i) →
    fact a + sumF B = fact a * (1 + sumP a B)
  | [], _ => by
      show fact a + 0 = fact a * (1 + 0)
      simp
  | i :: B, hall => by
      have hi : a < i := hall i (List.mem_cons_self ..)
      have hrest := sumF_split a B (by
        intro j hj
        exact hall j (List.mem_cons_of_mem _ hj))
      obtain ⟨j, hj⟩ : ∃ j, i = a + j := ⟨i - a, by omega⟩
      have hfi : fact i = fact a * pt a j := by rw [hj, fact_pt j a]
      have hij : i - a = j := by omega
      have hpsame : pt a (i - a) = pt a j := by rw [hij]
      have hunfold : sumF (i :: B) = fact i + sumF B := rfl
      have hpu : sumP a (i :: B) = pt a (i - a) + sumP a B := rfl
      calc fact a + sumF (i :: B)
          = fact i + (fact a + sumF B) := by rw [hunfold]; omega
        _ = fact a * pt a j + fact a * (1 + sumP a B) := by rw [hfi, hrest]
        _ = fact a * (1 + (pt a (i - a) + sumP a B)) := by
            rw [hpsame]
            exact mul_add_split (fact a) (pt a j) (sumP a B)

/-- Fuel-structural p-adic valuation engine. -/
def vpadf : Nat → Nat → Nat → Nat
  | _, 0, _ => 0
  | _, _, 0 => 0
  | p, f + 1, n + 1 =>
      if (n + 1) % p = 0 then 1 + vpadf p f ((n + 1) / p) else 0

def vpad (p : Nat) (n : Nat) : Nat := vpadf p n n

theorem vpad_unfold_succ (p N : Nat) :
    vpad p (N + 1) =
      if (N + 1) % p = 0 then 1 + vpadf p N ((N + 1) / p) else 0 := rfl

theorem vpadf_sat (p : Nat) (hp : 2 ≤ p) :
    ∀ (F f : Nat), f ≤ F → ∀ (n : Nat), n ≤ f →
    vpadf p f n = vpadf p n n := by
  intro F
  induction F with
  | zero =>
    intro f hf n hn
    have hf0 : f = 0 := by omega
    subst hf0
    have hn0 : n = 0 := by omega
    subst hn0
    rfl
  | succ F ih =>
    intro f hf n hn
    cases f with
    | zero =>
      have hn0 : n = 0 := by omega
      subst hn0
      rfl
    | succ F' =>
      cases n with
      | zero => rfl
      | succ N =>
        have e1 : vpadf p (F' + 1) (N + 1) =
            if (N + 1) % p = 0 then 1 + vpadf p F' ((N + 1) / p) else 0 := rfl
        have e2 : vpadf p (N + 1) (N + 1) =
            if (N + 1) % p = 0 then 1 + vpadf p N ((N + 1) / p) else 0 := rfl
        rw [e1, e2]
        by_cases hmod : (N + 1) % p = 0
        · rw [if_pos hmod, if_pos hmod]
          have hdlt : (N + 1) / p < N + 1 :=
            Nat.div_lt_self (by omega) (by omega)
          have i1 := ih F' (by omega) ((N + 1) / p) (by omega)
          have i2 := ih N (by omega) ((N + 1) / p) (by omega)
          rw [i1, i2]
        · rw [if_neg hmod, if_neg hmod]

theorem vpad_nondiv (p n : Nat) (hn : 1 ≤ n) (hne : n % p ≠ 0) :
    vpad p n = 0 := by
  obtain ⟨N, hN⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hne' : (N + 1) % p ≠ 0 := by rw [← hN]; exact hne
  rw [hN, vpad_unfold_succ, if_neg hne']

theorem vpad_step (p n : Nat) (hp : 2 ≤ p) (hn : 1 ≤ n) (hd : n % p = 0) :
    vpad p n = 1 + vpad p (n / p) := by
  obtain ⟨N, hN⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hmod : (N + 1) % p = 0 := by rw [← hN]; exact hd
  have h1 : vpad p (N + 1) = 1 + vpadf p N ((N + 1) / p) := by
    rw [vpad_unfold_succ, if_pos hmod]
  have hdlt : (N + 1) / p < N + 1 := Nat.div_lt_self (by omega) (by omega)
  have h2 : vpadf p N ((N + 1) / p) = vpad p ((N + 1) / p) :=
    vpadf_sat p hp N N (Nat.le_refl _) ((N + 1) / p) (by omega)
  rw [hN, h1, h2]

-- ===========================================================================
-- §2  THE MULTIPLICATIVE LAW (Euclid-powered: p ∤ u → v_p(x·u) = v_p(x))
-- ===========================================================================

theorem mod_zero_of_dvd (x p c : Nat) (h : x = p * c) : x % p = 0 := by
  rw [h, Nat.mul_mod, Nat.mod_self, Nat.zero_mul]

/-- **The multiplicative law.**  For `p` prime and `p ∤ u ≥ 1`:
`v_p (x·u) = v_p (x)` for every `x ≥ 1`.  Fuel induction on `x`; the
`p ∤ x` case uses Euclid (`Nat.Prime.dvd_mul`). -/
theorem vpad_mul_nondiv (p : Nat) (hp : Nat.Prime p) :
    ∀ (F x u : Nat), x ≤ F → 1 ≤ x → 1 ≤ u → u % p ≠ 0 →
    vpad p (x * u) = vpad p x := by
  intro F
  induction F with
  | zero => intro x u hF hx _ _; omega
  | succ F ih =>
    intro x u hF hx hu hu0
    by_cases hx0 : x % p = 0
    · -- p ∣ x: step both sides down by one p
      have hmod := Nat.div_add_mod x p
      rw [hx0, Nat.add_zero] at hmod
      have hxdiv : p * (x / p) = x := hmod
      have hxp1 : 1 ≤ x / p := by
        rcases Nat.eq_zero_or_pos (x / p) with h | h
        · rw [h, Nat.mul_zero] at hxdiv; omega
        · exact h
      have hxdiv' : (x / p) * p = x := by rw [Nat.mul_comm]; exact hxdiv
      have hxpF : x / p ≤ F := by
        have h2 : (x / p) * 2 ≤ (x / p) * p := Nat.mul_le_mul_left _ hp.two_le
        omega
      have hxu0 : (x * u) % p = 0 := by
        rw [Nat.mul_mod, hx0, Nat.zero_mul]
      have hxu1 : 1 ≤ x * u := one_le_mul_nat x u hx hu
      have hstep := vpad_step p (x * u) hp.two_le hxu1 hxu0
      have hdiv : (x * u) / p = (x / p) * u := by
        obtain ⟨m, hm⟩ : ∃ m, x / p = m := ⟨x / p, rfl⟩
        have hdx : p * m = x := by rw [← hm]; exact hxdiv
        rw [hm, ← hdx, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by omega : 0 < p)]
      rw [hstep, hdiv, ih (x / p) u hxpF hxp1 hu hu0]
      have hstepx := vpad_step p x hp.two_le hx hx0
      omega
    · -- p ∤ x: Euclid forces p ∤ x·u, both valuations are 0
      have hnxu : (x * u) % p ≠ 0 := by
        intro hc
        have hd : p ∣ x * u := Nat.dvd_of_mod_eq_zero hc
        rcases (Nat.Prime.dvd_mul hp).mp hd with h1 | h2
        · obtain ⟨c, hc2⟩ := h1
          have hz := mod_zero_of_dvd x p c hc2
          omega
        · obtain ⟨c, hc2⟩ := h2
          have hz := mod_zero_of_dvd u p c hc2
          omega
      rw [vpad_nondiv p x hx hx0,
          vpad_nondiv p (x * u) (one_le_mul_nat x u hx hu) hnxu]

-- ===========================================================================
-- §3  THE PRODUCT-TAIL SPLIT + THE TAIL DIVISIBILITY
-- ===========================================================================

theorem pt_split : ∀ (u j k : Nat), pt u (j + k) = pt u j * pt (u + j) k
  | u, j, 0 => by simp [pt]
  | u, j, k + 1 => by
      have h1 : pt u (j + (k + 1)) = pt u (j + k) * (u + (j + k) + 1) := rfl
      have h2 : pt (u + j) (k + 1) = pt (u + j) k * (u + j + k + 1) := rfl
      rw [h1, pt_split u j k, h2]
      have hring : pt u j * (pt (u + j) k * (u + j + k + 1))
          = (pt u j * pt (u + j) k) * (u + (j + k) + 1) := by
        have ha : u + j + k + 1 = u + (j + k) + 1 := by omega
        rw [ha]
        ring
      rw [hring]

/-- The last-factor law: `pt a m = pt a (m-1) · (a + m)` for `m ≥ 1`. -/
theorem pt_last (a m' : Nat) : pt a (m' + 1) = pt a m' * (a + m' + 1) := rfl

/-- **The tail dies.**  If `a + m = k·p` with `m ≥ 1` and `m ≤ j` then
`p ∣ pt a j` — the staircase factor `a + m` itself carries the prime. -/
theorem pt_dvd_tail (m a p k : Nat) (hm : 1 ≤ m) (h : a + m = k * p) :
    ∀ j, m ≤ j → p ∣ pt a j := by
  intro j hj
  obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  subst hm'
  have hlast : pt a (m' + 1) = pt a m' * (a + m' + 1) := rfl
  have hfac : p ∣ pt a (m' + 1) := by
    refine ⟨pt a m' * k, ?_⟩
    rw [hlast]
    have hkey : a + m' + 1 = k * p := by omega
    rw [hkey]
    ring
  have hsplit := pt_split a (m' + 1) (j - (m' + 1))
  rw [Nat.add_sub_cancel' hj] at hsplit
  rw [hsplit]
  exact hfac.mul_right _

/-- **The tail dies in ℤ** (the cast of the Nat divisibility). -/
theorem pt_dvd_tail_int (m a p k : Nat) (hm : 1 ≤ m) (h : a + m = k * p) :
    ∀ j, m ≤ j → ∃ (c : ℤ), ((pt a j : ℕ) : ℤ) = ((p : ℕ) : ℤ) * c := by
  intro j hj
  obtain ⟨c, hc⟩ := pt_dvd_tail m a p k hm h j hj
  exact ⟨c, by rw [hc, Nat.cast_mul]⟩

-- ===========================================================================
-- §4  THE FALLING FACTORIAL (the coin values of the residual tail)
-- ===========================================================================

/-- `ff m j = (m−1)(m−2)···(m−j)` — the coin values of the residual tail. -/
def ff (m : Nat) : Nat → Nat
  | 0 => 1
  | j + 1 => ff m j * (m - 1 - j)

theorem ff_pos (m : Nat) : ∀ j, j ≤ m - 1 → 1 ≤ ff m j
  | 0, _ => rfl
  | j + 1, hj => by
      have hge : 1 ≤ m - 1 - j := by omega
      exact one_le_mul_nat _ _ (ff_pos m j (by omega)) hge

theorem ff_dvd (m : Nat) : ∀ j, 1 ≤ j → (m - 1) ∣ ff m j
  | 0, h => absurd h (by omega)
  | 1, _ => by
      have h1 : ff m 1 = ff m 0 * (m - 1) := rfl
      refine ⟨1, ?_⟩
      rw [h1]
      ring
  | j + 2, _ => by
      have h1 : ff m (j + 2) = ff m (j + 1) * (m - 1 - (j + 1)) := rfl
      obtain ⟨c, hc⟩ := ff_dvd m (j + 1) (by omega)
      refine ⟨c * (m - 1 - (j + 1)), ?_⟩
      rw [h1, hc]
      ring

theorem ff_mul_fact : ∀ (m j : Nat), j ≤ m - 1 →
    ff m j * fact (m - 1 - j) = fact (m - 1) := by
  intro m j
  induction j with
  | zero =>
      intro _
      have h0 : ff m 0 = 1 := rfl
      show ff m 0 * fact (m - 1 - 0) = fact (m - 1)
      rw [h0, Nat.sub_zero, Nat.one_mul]
  | succ j' ih =>
      intro hj
      have hff : ff m (j' + 1) = ff m j' * (m - 1 - j') := rfl
      have hsub : m - 1 - (j' + 1) = m - 1 - j' - 1 := by omega
      obtain ⟨n, hn⟩ : ∃ n, m - 1 - j' = n + 1 := ⟨m - 1 - j' - 1, by omega⟩
      have hfac : fact (m - 1 - j') = (m - 1 - j') * fact (m - 1 - j' - 1) := by
        rw [hn]
        rfl
      have hIH := ih (by omega)
      show ff m (j' + 1) * fact (m - 1 - (j' + 1)) = fact (m - 1)
      rw [hsub, hff, Nat.mul_assoc, ← hfac]
      exact hIH

theorem ff_le_fact (m j : Nat) (hj : j ≤ m - 1) : ff m j ≤ fact (m - 1) := by
  have h := ff_mul_fact m j hj
  have h1 : 1 ≤ fact (m - 1 - j) := fact_pos _
  have h2 := Nat.mul_le_mul_left (ff m j) h1
  rw [Nat.mul_one] at h2
  omega

-- ===========================================================================
-- §5  THE COIN DIVISIBILITY (the signed falling-factorial congruence, in ℤ)
-- ===========================================================================

/-- **THE COIN CONGRUENCE, divisibility form.**  On the class `a ≡ −m (mod p)`:
`p ∣ (pt a j − (−1)^j · ff m j)` for every `j ≤ m − 1`.  Pure Int ring
arithmetic — the seed split `a + j + 1 = k·p − (m−1−j)` closes the step;
NO Int-mod lemmas (none exist at this pin; the r1 lesson). -/
theorem coin_dvd (m a p k : Nat) (hm : 1 ≤ m) (h : a + m = k * p) :
    ∀ j, j ≤ m - 1 → ∃ (c : ℤ),
      ((pt a j : ℕ) : ℤ) - ((-1 : ℤ) ^ j) * ((ff m j : ℕ) : ℤ)
        = ((p : ℕ) : ℤ) * c := by
  intro j
  induction j with
  | zero =>
      intro _
      refine ⟨0, ?_⟩
      have e1 : pt a 0 = 1 := rfl
      have e2 : ff m 0 = 1 := rfl
      have e3 : ((-1 : ℤ) ^ 0) = 1 := by norm_num
      rw [e1, e2, e3]
      norm_num
  | succ j' ih =>
      intro hj
      obtain ⟨c, hc⟩ := ih (by omega)
      have hpt : ((pt a (j' + 1) : ℕ) : ℤ)
          = ((pt a j' : ℕ) : ℤ) * (((a + j' + 1 : ℕ) : ℤ)) := by
        have e : pt a (j' + 1) = pt a j' * (a + j' + 1) := rfl
        rw [e, Nat.cast_mul]
      have hseedI : (((a + j' + 1 : ℕ) : ℤ))
          = (((a + m : ℕ) : ℤ)) - (((m - 1 - j' : ℕ) : ℤ)) := by
        push_cast
        omega
      have hkm : (((a + m : ℕ) : ℤ)) = (((k : ℕ) : ℤ)) * (((p : ℕ) : ℤ)) := by
        rw [h, Nat.cast_mul]
      have hff : ff m (j' + 1) = ff m j' * (m - 1 - j') := rfl
      have hsign : ((-1 : ℤ) ^ (j' + 1)) = ((-1 : ℤ) ^ j') * (-1 : ℤ) := by
        rw [Int.pow_succ]
      refine ⟨((pt a j' : ℕ) : ℤ) * ((k : ℕ) : ℤ)
        - (((m - 1 - j' : ℕ) : ℤ)) * c, ?_⟩
      rw [hpt, hseedI, hkm, hff, Nat.cast_mul, hsign]
      linear_combination -(((m - 1 - j' : ℕ) : ℤ)) * hc

-- ===========================================================================
-- §6  THE BLOCK SUM: divisibility, two-sided bound, the pigeonhole count
-- ===========================================================================

/-- The Int-valued block sum: the signed coins of the unit block only. -/
def bsumI (m a : Nat) : List Nat → Int
  | [] => 0
  | i :: B => (if i - a < m then ((-1 : ℤ) ^ (i - a)) * (ff m (i - a) : ℤ) else 0)
             + bsumI m a B

/-- **The block divisibility.**  Every block sum is a multiple of `m − 1`. -/
theorem bsum_dvd (m a : Nat) : ∀ (B : List Nat), (∀ i ∈ B, a < i) →
    ∃ (K : ℤ), bsumI m a B = ((m - 1 : ℕ) : ℤ) * K := by
  intro B
  induction B with
  | nil => intro _; exact ⟨0, by simp [bsumI]⟩
  | cons i B ih =>
      intro hall
      have hi : a < i := hall i (List.mem_cons_self ..)
      have hrest := ih (by
        intro j hj
        exact hall j (List.mem_cons_of_mem _ hj))
      obtain ⟨K, hK⟩ := hrest
      by_cases hblk : i - a < m
      · obtain ⟨c, hc⟩ := ff_dvd m (i - a) (by omega)
        refine ⟨((-1 : ℤ) ^ (i - a)) * ((c : ℕ) : ℤ) + K, ?_⟩
        have hbu : bsumI m a (i :: B)
            = (if i - a < m then ((-1 : ℤ) ^ (i - a)) * (ff m (i - a) : ℤ) else 0)
              + bsumI m a B := rfl
        rw [hbu, if_pos hblk, hK]
        have hffcast : ((ff m (i - a) : ℕ) : ℤ) = ((m - 1 : ℕ) : ℤ) * ((c : ℕ) : ℤ) := by
          rw [← Nat.cast_mul, hc]
        rw [hffcast]
        ring
      · refine ⟨K, ?_⟩
        have hbu : bsumI m a (i :: B)
            = (if i - a < m then ((-1 : ℤ) ^ (i - a)) * (ff m (i - a) : ℤ) else 0)
              + bsumI m a B := rfl
        rw [hbu, if_neg hblk, hK]
        ring

theorem neg_one_pow_eq (j : Nat) : ((-1 : ℤ) ^ j) = 1 ∨ ((-1 : ℤ) ^ j) = -1 := by
  induction j with
  | zero => left; norm_num
  | succ j' ih =>
      rcases ih with h | h
      · rw [Int.pow_succ, h]; right; norm_num
      · rw [Int.pow_succ, h]; left; norm_num

/-- **The per-coin two-sided bound.**  Each signed coin lies in
`[−ff m j, +ff m j]` — no `abs` lemmas (none needed at this pin). -/
theorem coin_bounds (j m : Nat) :
    (-(ff m j : ℤ)) ≤ ((-1 : ℤ) ^ j) * (ff m j : ℤ) ∧
    ((-1 : ℤ) ^ j) * (ff m j : ℤ) ≤ (ff m j : ℤ) := by
  rcases neg_one_pow_eq j with h | h
  · rw [h]; exact ⟨by omega, by omega⟩
  · rw [h]; exact ⟨by omega, by omega⟩

/-- **The two-sided triangle-count bound.**  `−(count·(m−1)!) ≤ bsumI ≤ …`
with `count` the number of block coins (the per-coin bound + induction). -/
theorem bsum_bounds (m a : Nat) : ∀ (B : List Nat), (∀ i ∈ B, a < i) →
    -((((B.filter (fun i => i - a < m)).length * fact (m - 1) : ℕ) : ℤ))
      ≤ bsumI m a B
    ∧ bsumI m a B
      ≤ ((((B.filter (fun i => i - a < m)).length * fact (m - 1) : ℕ) : ℤ)) := by
  intro B
  induction B with
  | nil => intro _; simp [bsumI]
  | cons i B ih =>
      intro hall
      have hi : a < i := hall i (List.mem_cons_self ..)
      have hrest := ih (by
        intro j hj
        exact hall j (List.mem_cons_of_mem _ hj))
      obtain ⟨hlo, hhi⟩ := hrest
      have hbu : bsumI m a (i :: B)
          = (if i - a < m then ((-1 : ℤ) ^ (i - a)) * (ff m (i - a) : ℤ) else 0)
            + bsumI m a B := rfl
      by_cases hblk : i - a < m
      · obtain ⟨hclo, hchi⟩ := coin_bounds (i - a) m
        have hffb : ((ff m (i - a) : ℕ) : ℤ) ≤ ((fact (m - 1) : ℕ) : ℤ) := by
          exact_mod_cast ff_le_fact m (i - a) (by omega)
        have hflen : ((i :: B).filter (fun i => i - a < m)).length
            = (B.filter (fun i => i - a < m)).length + 1 := by simp [hblk]
        have hexp : ((B.filter (fun i => i - a < m)).length + 1) * fact (m - 1)
            = (B.filter (fun i => i - a < m)).length * fact (m - 1)
              + fact (m - 1) := by ring
        rw [hbu, if_pos hblk, hflen, hexp, Nat.cast_add]
        constructor <;> omega
      · have hflen : ((i :: B).filter (fun i => i - a < m)).length
            = (B.filter (fun i => i - a < m)).length := by simp [hblk]
        rw [hbu, if_neg hblk, hflen]
        constructor <;> omega

-- §6b  THE BLOCK COUNT PIGEONHOLE (distinct j's in [1, m-1] ≤ m-1 of them)

theorem block_count (m a : Nat) (hm : 1 ≤ m) (B : List Nat) (hB : B.Nodup)
    (hgt : ∀ i ∈ B, a < i) :
    (B.filter (fun i => i - a < m)).length ≤ m - 1 := by
  have hnd1 : (B.filter (fun i => i - a < m)).Nodup := List.Nodup.filter _ hB
  have hinj : ∀ x ∈ B.filter (fun i => i - a < m), ∀ y ∈ B.filter (fun i => i - a < m),
      x - a = y - a → x = y := by
    intro x hx y hy hxy
    have hxb : x ∈ B := (List.mem_filter.mp hx).1
    have hyb : y ∈ B := (List.mem_filter.mp hy).1
    have hxa : a < x := hgt x hxb
    have hya : a < y := hgt y hyb
    omega
  have hnd2 : ((B.filter (fun i => i - a < m)).map (fun i => i - a)).Nodup :=
    List.Nodup.map_on hinj hnd1
  have hsub : ∀ j ∈ (B.filter (fun i => i - a < m)).map (fun i => i - a),
      1 ≤ j ∧ j ≤ m - 1 := by
    intro j hj
    rw [List.mem_map] at hj
    obtain ⟨i, hi, hji⟩ := hj
    have hib : i ∈ B := (List.mem_filter.mp hi).1
    have hia : a < i := hgt i hib
    have hilt : i - a < m := of_decide_eq_true (List.mem_filter.mp hi).2
    omega
  have hfin : (((B.filter (fun i => i - a < m)).map (fun i => i - a)).toFinset)
      ⊆ Finset.Ico 1 m := by
    intro j hj'
    rw [List.mem_toFinset] at hj'
    obtain ⟨h1, h2⟩ := hsub j hj'
    exact Finset.mem_Ico.mpr ⟨h1, by omega⟩
  have hcard := Finset.card_le_card hfin
  rw [Nat.card_Ico] at hcard
  have hcard2 : ((B.filter (fun i => i - a < m)).map (fun i => i - a)).toFinset.card
      = ((B.filter (fun i => i - a < m)).map (fun i => i - a)).length :=
    List.toFinset_card_of_nodup hnd2
  rw [hcard2] at hcard
  have hlen : ((B.filter (fun i => i - a < m)).map (fun i => i - a)).length
      = (B.filter (fun i => i - a < m)).length := List.length_map _ _
  omega

/-- **The final two-sided block bound.**  `−(m−1)·(m−1)! ≤ bsumI ≤ (m−1)·(m−1)!`. -/
theorem bsum_bounds_final (m a : Nat) (hm : 1 ≤ m) (B : List Nat) (hB : B.Nodup)
    (hgt : ∀ i ∈ B, a < i) :
    -((((m - 1) * fact (m - 1) : ℕ) : ℤ)) ≤ bsumI m a B
    ∧ bsumI m a B ≤ ((((m - 1) * fact (m - 1) : ℕ) : ℤ)) := by
  obtain ⟨hlo, hhi⟩ := bsum_bounds m a B hgt
  have hcount := block_count m a hm B hB hgt
  have hmul : (B.filter (fun i => i - a < m)).length * fact (m - 1)
      ≤ (m - 1) * fact (m - 1) := Nat.mul_le_mul_right _ hcount
  have hcast : (((B.filter (fun i => i - a < m)).length * fact (m - 1) : ℕ) : ℤ)
      ≤ (((m - 1) * fact (m - 1) : ℕ) : ℤ) := by
    exact_mod_cast hmul
  exact ⟨by omega, by omega⟩

/-- **The block-sum difference divisibility.**  On the class,
`Σ P − bsumI` is a p-multiple in ℤ (the coin congruence for the block, the
tail divisibility beyond it) — the divisibility form of the r1 congruence. -/
theorem bsum_diff_dvd (m a p k : Nat) (hm : 1 ≤ m) (h : a + m = k * p) :
    ∀ (B : List Nat), (∀ i ∈ B, a < i) →
    ∃ (C : ℤ), ((sumP a B : ℕ) : ℤ) = bsumI m a B + ((p : ℕ) : ℤ) * C := by
  intro B
  induction B with
  | nil => intro _; exact ⟨0, by simp [sumP, bsumI]⟩
  | cons i B ih =>
      intro hall
      have hi : a < i := hall i (List.mem_cons_self ..)
      have hrest := ih (by
        intro j hj
        exact hall j (List.mem_cons_of_mem _ hj))
      obtain ⟨C, hC⟩ := hrest
      have hunfold : sumP a (i :: B) = pt a (i - a) + sumP a B := rfl
      have hcast : ((sumP a (i :: B) : ℕ) : ℤ)
          = ((pt a (i - a) : ℕ) : ℤ) + ((sumP a B : ℕ) : ℤ) := by
        rw [hunfold, Nat.cast_add]
      have hbu : bsumI m a (i :: B)
          = (if i - a < m then ((-1 : ℤ) ^ (i - a)) * (ff m (i - a) : ℤ) else 0)
            + bsumI m a B := rfl
      by_cases hblk : i - a < m
      · obtain ⟨c, hc⟩ := coin_dvd m a p k hm h (i - a) (by omega)
        refine ⟨C + c, ?_⟩
        rw [hcast, hbu, if_pos hblk, hC, Int.mul_add]
        omega
      · obtain ⟨c, hc⟩ := pt_dvd_tail_int m a p k hm h (i - a) (by omega)
        refine ⟨C + c, ?_⟩
        rw [hcast, hbu, if_neg hblk, hC, Int.mul_add]
        omega

-- ===========================================================================
-- §7  THE CLASS THEOREMS
-- ===========================================================================

/-- **ERDŐS #404 — THE RESIDUAL-TAIL CLASS LAW.**  For every `m ≥ 3`,
every prime `p` with `(m−1)·(m−1)! + 1 < p`, every seed `a ≥ 1` with
`a ≡ −m (mod p)`, and every finite set of distinct indices `B` beyond `a`:
the p-adic valuation NEVER grows — `f(a,p) = v_p(a!)` on the whole family. -/
theorem erdos404_residual_tail (m p : Nat) (hm : 3 ≤ m) (hp : Nat.Prime p)
    (hbound : (m - 1) * fact (m - 1) + 1 < p) (a : Nat) (ha : 1 ≤ a)
    (hseed : (a + m) % p = 0) (B : List Nat) (hB : B.Nodup)
    (hgt : ∀ i ∈ B, a < i) :
    vpad p (fact a + sumF B) = vpad p (fact a) := by
  have hp2 : 2 ≤ p := hp.one_lt
  have hmod := Nat.div_add_mod (a + m) p
  rw [hseed, Nat.add_zero] at hmod
  have hdv : p * ((a + m) / p) = a + m := hmod
  obtain ⟨k, hk⟩ : ∃ k, a + m = k * p :=
    ⟨(a + m) / p, by rw [Nat.mul_comm]; exact hdv.symm⟩
  -- the key obstruction: p ∤ (1 + sumP a B)
  have hne : (1 + sumP a B) % p ≠ 0 := by
    intro hc
    have hdp : p ∣ 1 + sumP a B := Nat.dvd_of_mod_eq_zero hc
    obtain ⟨q, hq⟩ := hdp
    obtain ⟨C, hC⟩ := bsum_diff_dvd m a p k (by omega) hk B hgt
    have hqI : ((1 + sumP a B : ℕ) : ℤ) = ((p : ℕ) : ℤ) * ((q : ℕ) : ℤ) := by
      rw [hq, Nat.cast_mul]
    have hD : (1 : ℤ) + bsumI m a B
        = ((p : ℕ) : ℤ) * (((q : ℕ) : ℤ) - C) := by
      have hsplit : ((p : ℕ) : ℤ) * (((q : ℕ) : ℤ) - C)
          = ((p : ℕ) : ℤ) * ((q : ℕ) : ℤ) - ((p : ℕ) : ℤ) * C := by ring
      rw [hsplit]
      omega
    -- the two-sided bound, cast to ℤ
    obtain ⟨hlo, hhi⟩ := bsum_bounds_final m a (by omega) B hB hgt
    have hboundI : (((m - 1) * fact (m - 1) : ℕ) : ℤ) + 1 < ((p : ℕ) : ℤ) := by
      exact_mod_cast hbound
    have hDlt : (1 : ℤ) + bsumI m a B < ((p : ℕ) : ℤ) := by omega
    have hDgt : -((p : ℕ) : ℤ) < (1 : ℤ) + bsumI m a B := by omega
    -- the t-cases force 1 + bsumI = 0
    have hzero : (1 : ℤ) + bsumI m a B = 0 := by
      rcases Int.lt_or_ge (((q : ℕ) : ℤ) - C) 0 with hTn | hTp
      · obtain ⟨s, hs⟩ : ∃ s, ((q : ℕ) : ℤ) - C = -1 - s :=
          ⟨-(((q : ℕ) : ℤ) - C) - 1, by omega⟩
        have hps : (0 : ℤ) ≤ ((p : ℕ) : ℤ) * s :=
          Int.mul_nonneg (by omega) (by omega)
        have hpt : ((p : ℕ) : ℤ) * (((q : ℕ) : ℤ) - C)
            = -((p : ℕ) : ℤ) - ((p : ℕ) : ℤ) * s := by
          rw [hs]; ring
        omega
      · rcases Int.eq_zero_or_pos (((q : ℕ) : ℤ) - C) with hT0 | hT0
        · rw [hD, hT0, Int.mul_zero]
        · obtain ⟨s, hs⟩ : ∃ s, ((q : ℕ) : ℤ) - C = 1 + s :=
            ⟨((q : ℕ) : ℤ) - C - 1, by omega⟩
          have hps : (0 : ℤ) ≤ ((p : ℕ) : ℤ) * s :=
            Int.mul_nonneg (by omega) (by omega)
          have hpt : ((p : ℕ) : ℤ) * (((q : ℕ) : ℤ) - C)
              = ((p : ℕ) : ℤ) + ((p : ℕ) : ℤ) * s := by
            rw [hs]; ring
          omega
    -- so bsumI = −1, but (m−1) ∣ bsumI with m ≥ 3 — contradiction
    obtain ⟨K, hK⟩ := bsum_dvd m a B hgt
    have hb1 : ((m - 1 : ℕ) : ℤ) * K = -1 := by omega
    have hm2 : (2 : ℤ) ≤ ((m - 1 : ℕ) : ℤ) := by
      exact_mod_cast (by omega : (2 : Nat) ≤ m - 1)
    rcases Int.eq_zero_or_pos K with hK0 | hK0
    · have hkk : ((m - 1 : ℕ) : ℤ) * K = 0 := by rw [hK0, Int.mul_zero]
      omega
    · rcases Int.lt_or_ge K 0 with hKn | hKp
      · obtain ⟨s, hs⟩ : ∃ s, K = -1 - s := ⟨-K - 1, by omega⟩
        have hps : (0 : ℤ) ≤ ((m - 1 : ℕ) : ℤ) * s :=
          Int.mul_nonneg (by omega) (by omega)
        have hpr : ((m - 1 : ℕ) : ℤ) * K = -(((m - 1 : ℕ) : ℤ))
          - ((m - 1 : ℕ) : ℤ) * s := by rw [hs]; ring
        omega
      · obtain ⟨s, hs⟩ : ∃ s, K = 1 + s := ⟨K - 1, by omega⟩
        have hps : (0 : ℤ) ≤ ((m - 1 : ℕ) : ℤ) * s :=
          Int.mul_nonneg (by omega) (by omega)
        have hpr : ((m - 1 : ℕ) : ℤ) * K = ((m - 1 : ℕ) : ℤ)
          + ((m - 1 : ℕ) : ℤ) * s := by rw [hs]; ring
        omega
  -- the split + the multiplicative law finish
  have hsplit := sumF_split a B hgt
  rw [hsplit]
  exact vpad_mul_nondiv p hp (fact a) (fact a) (1 + sumP a B)
    (Nat.le_refl _) (fact_pos a) (by omega) hne

/-- **The m = 3 class (Theorem B2).**  For every prime `p ≥ 7` and every
`a ≡ p − 3 (mod p)`: `f(a,p) = v_p(a!)`.  (The tail bound at m = 3 is
`2·2! + 1 = 5 < p`.) -/
theorem erdos404_class_p_minus_3 (p : Nat) (hp : Nat.Prime p) (hp7 : 7 ≤ p)
    (a : Nat) (ha : 1 ≤ a) (hseed : (a + 3) % p = 0) (B : List Nat) (hB : B.Nodup)
    (hgt : ∀ i ∈ B, a < i) :
    vpad p (fact a + sumF B) = vpad p (fact a) :=
  erdos404_residual_tail 3 p (by omega) hp (by
    have h3 : (3 - 1) * fact (3 - 1) + 1 = 5 := by decide
    omega) a ha hseed B hB hgt

-- ===========================================================================
-- §8  RECEIPTS + ARSENAL BRIDGE
-- ===========================================================================

/- The class instance (m, p, a) = (3, 7, 4): 4! + 5! = 144 ≡ 4 (mod 7),
4! + 6! = 744 ≡ 2, 4! + 5! + 6! = 864 ≡ 3 — never 0. -/
#eval vpad 7 (fact 4 + fact 5)
#eval vpad 7 (fact 4 + fact 6)
#eval vpad 7 (fact 4 + fact 5 + fact 6)
#eval vpad 7 (fact 4 + fact 5 + fact 6 + fact 7 + fact 8 + fact 9)

/- The class instance (m, p, a) = (4, 23, 19): the bound 3·3! + 1 = 19 < 23;
19! + 20! = 19!·21 with 23 ∤ 21. -/
#eval vpad 23 (fact 19 + fact 20)
#eval vpad 23 (fact 19 + fact 20 + fact 21)
#eval vpad 23 (fact 19 + fact 22)

/- v_p(a!) receipts on the classes (the values the sums never exceed). -/
#eval vpad 7 (fact 4)
#eval vpad 23 (fact 19)

/- The m = 3 first prime (5, below the tail bound — battery-verified class
a ≡ 2 (mod 5)) and the m = 4 first prime (23): ternary digits of both. -/
def arsenalBridgeProp404t : Prop :=
  [5 % 3, (5 / 3) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
  [23 % 3, (23 / 3) % 3, (23 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
  carryAtPos 5 1 < 4 ∧
  v2r (3 ^ 1 * 9) = v2r 9

theorem erdos404t_arsenal_bridge : arsenalBridgeProp404t :=
  ⟨by decide, by decide, carryAtPos_bound 5 1, CardinalWorldsV2.v2r_ternary_scaling 1 9⟩

#print axioms erdos404_residual_tail
#print axioms erdos404_class_p_minus_3
#print axioms erdos404t_arsenal_bridge

#eval "ERDOS404_RESIDUAL_TAIL_KERNEL_GREEN"
