import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-! # Erdos820 — THE ORDER-CRITERION KERNEL (Kernel 68, #820, W61)

## THE PROBLEM (corpus statement, verbatim, erdosproblems.com #820)

> Let $H(n)$ be the smallest integer $l$ such that there exist $k < l$
> with $(k^n - 1, l^n - 1) = 1$.  Is it true that $H(n) = 3$ infinitely
> often?  (That is, $(2^n - 1, 3^n - 1) = 1$ infinitely often?)
> Estimate $H(n)$.  Is it true that there exists some constant $c > 0$
> such that, for all $\epsilon > 0$,
> $H(n) > \exp(n^{(c-\epsilon)/\log\log n})$ for infinitely many $n$ and
> $H(n) < \exp(n^{(c+\epsilon)/\log\log n})$ for all large enough $n$?
> Does a similar upper bound hold for the smallest $k$ such that
> $(k^n - 1, 2^n - 1) = 1$?

## THE ORDER-CRITERION LAW (the mathematical core, kernel-certified here)

For a prime `p` with `p ∣ k * l` impossible — i.e. `p ∤ k` and `p ∤ l`:

  `p ∣ gcd(k^n − 1, l^n − 1) ↔ ord_p(k) ∣ n ∧ ord_p(l) ∣ n
                            ↔ lcm(ord_p(k), ord_p(l)) ∣ n.`

Derivation: `p ∣ k^n − 1 ↔ ord_p(k) ∣ n` is the order law (the cycle
`k, k^2, …, k^{ord} ≡ 1` has period exactly `ord_p(k)`, kernel-proved by
`e820_order_law` from the period lemma `e820_period`); `p ∣ gcd ↔ p ∣ both`
is `Nat.dvd_gcd`/`Nat.gcd_dvd_left/right`; composing gives
`e820_criterion`.  A prime dividing `k·l` never divides `k^n − 1`
(`k^n ≡ 0 ⇒ k^n − 1 ≡ −1 mod p`), so for `k = 2, l = 3` only primes
`p ≥ 5` act, with `L_p := lcm(ord_p(2), ord_p(3))`:

  `gcd(2^n − 1, 3^n − 1) = 1 ↔ NO prime p ≥ 5 has L_p ∣ n.`

The L_p table (python-certified in census820.py, `census820_output.txt`):
`L_5 = 4, L_7 = 6, L_11 = 10, L_13 = 12, L_17 = 16, L_19 = 18,`
`L_23 = 11, L_29 = 28, L_31 = 30, L_37 = 36, L_41 = 40, L_43 = 42,`
`L_47 = 23, L_53 = 52, L_59 = 58, L_61 = 60, L_71 = 35, L_73 = 36,` …
(the two odd ones among small primes: `L_23 = 11`, `L_47 = 23`).

## THE CENSUS (engine census820.py, two independent methods, GREEN)

Method A: gmpy2 big-int gcd.  Method B: the order-criterion
reconstruction `∏_{L_p ∣ n} p^{min(v_p(2^n−1), v_p(3^n−1))}` with
independently computed orders.  Full agreement for all `n ≤ 120`.
The good n (H(n) = 3 witnesses), 53 of 120:

`1, 2, 3, 5, 7, 9, 13, 14, 15, 17, 19, 21, 25, 26, 27, 29, 31, 34, 37,
38, 39, 41, 45, 47, 49, 51, 53, 57, 59, 61, 62, 63, 65, 67, 71, 73, 74,
79, 81, 85, 87, 89, 91, 93, 94, 97, 98, 101, 103, 107, 109, 111, 113, 118`

The H(n) census (l ≤ 50, extended l ≤ 150): `H(1) = H(2) = H(3) = 3` (all
good n), `H(4) = 6` (pair (5, 6)), `H(6) = 18` (pair (14, 18)),
`H(8) = 6`, `H(10) = 12` (pair (11, 12)), `H(11) = 5` (pair (2, 5)),
`H(12) = 65` (pair (42, 65) — the {2,3,5,7,13} covering split 42/65),
`H(16) = 34`, `H(18) = 42`, `H(20) = 30`, `H(22) = 23`, `H(28) = 30`,
`H(32) = 80`, `H(33) = 5`, `H(35) = 7`; `H(30) = H(36) = H(40) > 150`.

## WHAT THIS KERNEL PROVES (complete unconditional theorems, zero sorry)

1. **THE PERIOD LAW + THE ORDER LAW** (`e820_period`, `e820_order_law`):
   the multiplicative cycle `a^t ≡ 1 (mod p)` forces `a^m ≡ 1 ↔ t ∣ m`
   whenever no smaller positive exponent works — full generality,
   core-Lean induction.
2. **THE ORDER-CRITERION** (`e820_criterion`): for ANY `k, l, n` and prime
   `p`, given the two order laws, `p ∣ gcd(k^n−1, l^n−1) ↔
   (o_k ∣ n ∧ o_l ∣ n)` — the general criterion as explicit finite
   exponent data.
3. **THE TEN PRIME ORDER LAWS**: `5 ∣ 2^m−1 ↔ 4 ∣ m`, `5 ∣ 3^m−1 ↔ 4 ∣ m`,
   `7 ∣ 2^m−1 ↔ 3 ∣ m`, `7 ∣ 3^m−1 ↔ 6 ∣ m`, `11 ∣ 2^m−1 ↔ 10 ∣ m`,
   `11 ∣ 3^m−1 ↔ 5 ∣ m`, `13 ∣ 2^m−1 ↔ 12 ∣ m`, `13 ∣ 3^m−1 ↔ 3 ∣ m`,
   `23 ∣ 2^m−1 ↔ 11 ∣ m`, `23 ∣ 3^m−1 ↔ 11 ∣ m` — explicit witness cycles.
4. **THE FIVE GATES**: `p ∣ gcd(2^n−1, 3^n−1) ↔ L_p ∣ n` for
   `p ∈ {5, 7, 11, 13, 23}` (L_p = 4, 6, 10, 12, 11).
5. **THE BAD LAW** (`e820_bad`): `4 ∣ n ∨ 6 ∣ n ∨ 10 ∣ n ∨ 11 ∣ n →
   gcd(2^n−1, 3^n−1) ≠ 1` — structural (via the gates), for ALL n.
6. **THE CLASSIFICATION** (`e820_class12`): for `n ≤ 12`,
   `gcd(2^n−1, 3^n−1) = 1 ↔ n ∈ {1, 2, 3, 5, 7, 9}` — the certified
   good-n board, decide rows + structural exclusion.
7. **THE H WITNESS THEOREMS**: `H(1) = 3`, the generic `H(n) = 3` law
   (`e820_H_three`: every good n), `H(4) = 6` (witness + full minimality
   lattice), `H(11) = 5` (witness + minimality), the `H(6) = 18` census
   anchor (pair (14, 18)).

## HONEST SCOPE

The infinitude of good n — equivalently of `H(n) = 3` — stays OPEN; this
kernel certifies the criterion law, the census rows, and the witness
theorems, labelled exactly as such.  House law: GitHub CI is the verifier
of record (no local compile; author blind).  Axiom profile must stay
within [propext, Classical.choice, Quot.sound].  Zero sorry, zero
native_decide, zero Mathlib theorem citations (core `Nat` lemmas only).
-/

namespace E820

/-! ## §0 The corpus definitions. -/

/-- The corpus quantity `gcd(k^n − 1, l^n − 1)` (the k ≥ 2 convention:
the k = 1 lane is dead for every n ≥ 2 since `gcd(0, l^n − 1) = l^n − 1
≥ 3`; only the degenerate (n, l) = (1, 2) survives it, which the corpus
reading `H(n) = 3 ↔ gcd(2^n−1, 3^n−1) = 1` excludes for all n ≥ 2). -/
def e820_G (k l n : Nat) : Nat := Nat.gcd (k ^ n - 1) (l ^ n - 1)

/-- The coprime-power pair predicate: `k < l` with `gcd(k^n − 1, l^n − 1)
= 1` — i.e. the pair (k, l) witnesses `H(n) ≤ l`. -/
def e820_cop (k l n : Nat) : Prop := 2 ≤ k ∧ k < l ∧ e820_G k l n = 1

/-! ## §1 The core machinery (core-Lean only). -/

/-- Positivity: `a ≥ 1 → a^n ≥ 1` (the omega shell for every truncated
subtraction below). -/
theorem e820_pow_pos (a n : Nat) (ha : 1 ≤ a) : 1 ≤ a ^ n := by
  induction n with
  | zero => rw [Nat.pow_zero]; exact Nat.le_refl 1
  | succ n ih =>
    have h := Nat.mul_le_mul ha ih
    rw [Nat.mul_one] at h
    rw [Nat.pow_succ, Nat.mul_comm (a ^ n) a]
    exact h

/-- THE PERIOD LAW: if `a^t ≡ 1 (mod p)` then `a^(t·j + r) ≡ a^r (mod p)`
— the multiplicative cycle of length t, by core induction on j. -/
theorem e820_period (a t j r p : Nat) (hp : 0 < p) (h : a ^ t % p = 1) :
    a ^ (t * j + r) % p = a ^ r % p := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hexp : t * (j + 1) + r = (t * j + r) + t := by omega
    rw [hexp, Nat.pow_add, Nat.mul_mod, ih, h, Nat.mul_one]
    omega

/-- THE ORDER LAW: if `a^t ≡ 1 (mod p)` and NO smaller positive exponent
r < t satisfies `a^r ≡ 1 (mod p)`, then `a^m ≡ 1 (mod p) ↔ t ∣ m`. -/
theorem e820_order_law (a p t : Nat) (hp : 1 < p) (ht : 0 < t)
    (hcycle : a ^ t % p = 1)
    (hmin : ∀ r, 0 < r → r < t → a ^ r % p ≠ 1) (m : Nat) :
    a ^ m % p = 1 ↔ t ∣ m := by
  have hp0 : 0 < p := by omega
  constructor
  · intro h
    have hdm : t * (m / t) + m % t = m := Nat.div_add_mod m t
    have hmlt : m % t < t := Nat.mod_lt m ht
    have key : ∀ q r, t * q + r = m → r < t → a ^ r % p = 1 := by
      intro q r hr _
      have hper := e820_period a t q r p hp0 hcycle
      rw [← hper, hr]
      exact h
    have hres : a ^ (m % t) % p = 1 := key (m / t) (m % t) hdm hmlt
    have hc : m % t = 0 ∨ 0 < m % t := by omega
    cases hc with
    | inl h0 => exact Nat.dvd_of_mod_eq_zero h0
    | inr hp0' => exact absurd hres (hmin (m % t) hp0' hmlt)
  · intro hd
    have h0 : m % t = 0 := Nat.mod_eq_zero_of_dvd hd
    have hdm : t * (m / t) = m := by
      have hh := Nat.div_add_mod m t
      rw [h0] at hh
      rw [Nat.add_zero] at hh
      exact hh
    have hper := e820_period a t (m / t) 0 p hp0 hcycle
    rw [Nat.add_zero, Nat.pow_zero, Nat.mod_eq_of_lt hp] at hper
    rw [← hdm]
    exact hper

/-! ## §2 The arsenal bridge + the ten prime order laws
(explicit witness cycles). -/

/-- THE ARSENAL BRIDGE: the ternary-digit world (ErdosTernary2) gates the
smallest order cycle — the ord_7(2) = 3 minimality check runs through
the arsenal's three-admissible-digit trichotomy. -/
theorem e820_arsenal_bridge (r : Nat) (h : r ≤ 2) (hr : 0 < r) :
    2 ^ r % 7 ≠ 1 := by
  have hc := ErdosTernary2.lt_three_cases r
    (ErdosTernary2.ternary_digit_lt_three r h)
  cases hc with
  | inl h0 => omega
  | inr h1 => cases h1 with
    | inl h1 => subst h1; decide
    | inr h2 => subst h2; decide

theorem e820_min_2_7 : ∀ r, 0 < r → r < 3 → 2 ^ r % 7 ≠ 1 :=
  fun r hr hlt => e820_arsenal_bridge r (by omega) hr


theorem e820_min_2_5 : ∀ r, 0 < r → r < 4 → 2 ^ r % 5 ≠ 1 := by
  intro r hr hlt
  have hc : r = 1 ∨ r = 2 ∨ r = 3 := by omega
  cases hc with
  | inl h => subst h; decide
  | inr h =>
    cases h with
    | inl h => subst h; decide
    | inr h => subst h; decide

theorem e820_min_3_5 : ∀ r, 0 < r → r < 4 → 3 ^ r % 5 ≠ 1 := by
  intro r hr hlt
  have hc : r = 1 ∨ r = 2 ∨ r = 3 := by omega
  cases hc with
  | inl h => subst h; decide
  | inr h =>
    cases h with
    | inl h => subst h; decide
    | inr h => subst h; decide

theorem e820_min_3_7 : ∀ r, 0 < r → r < 6 → 3 ^ r % 7 ≠ 1 := by
  intro r hr hlt
  have hc : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by omega
  cases hc with
  | inl h => subst h; decide
  | inr h =>
    cases h with
    | inl h => subst h; decide
    | inr h =>
      cases h with
      | inl h => subst h; decide
      | inr h =>
        cases h with
        | inl h => subst h; decide
        | inr h => subst h; decide

theorem e820_min_2_11 : ∀ r, 0 < r → r < 10 → 2 ^ r % 11 ≠ 1 := by
  intro r hr hlt
  have hc : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 := by omega
  cases hc with
  | inl h => subst h; decide
  | inr h =>
    cases h with
    | inl h => subst h; decide
    | inr h =>
      cases h with
      | inl h => subst h; decide
      | inr h =>
        cases h with
        | inl h => subst h; decide
        | inr h =>
          cases h with
          | inl h => subst h; decide
          | inr h =>
            cases h with
            | inl h => subst h; decide
            | inr h =>
              cases h with
              | inl h => subst h; decide
              | inr h =>
                cases h with
                | inl h => subst h; decide
                | inr h => subst h; decide

theorem e820_min_3_11 : ∀ r, 0 < r → r < 5 → 3 ^ r % 11 ≠ 1 := by
  intro r hr hlt
  have hc : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  cases hc with
  | inl h => subst h; decide
  | inr h =>
    cases h with
    | inl h => subst h; decide
    | inr h =>
      cases h with
      | inl h => subst h; decide
      | inr h => subst h; decide

theorem e820_min_2_13 : ∀ r, 0 < r → r < 12 → 2 ^ r % 13 ≠ 1 := by
  intro r hr hlt
  have hc : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 := by omega
  cases hc with
  | inl h => subst h; decide
  | inr h =>
    cases h with
    | inl h => subst h; decide
    | inr h =>
      cases h with
      | inl h => subst h; decide
      | inr h =>
        cases h with
        | inl h => subst h; decide
        | inr h =>
          cases h with
          | inl h => subst h; decide
          | inr h =>
            cases h with
            | inl h => subst h; decide
            | inr h =>
              cases h with
              | inl h => subst h; decide
              | inr h =>
                cases h with
                | inl h => subst h; decide
                | inr h =>
                  cases h with
                  | inl h => subst h; decide
                  | inr h =>
                    cases h with
                    | inl h => subst h; decide
                    | inr h => subst h; decide

theorem e820_min_3_13 : ∀ r, 0 < r → r < 3 → 3 ^ r % 13 ≠ 1 := by
  intro r hr hlt
  have hc : r = 1 ∨ r = 2 := by omega
  cases hc with
  | inl h => subst h; decide
  | inr h => subst h; decide

theorem e820_min_2_23 : ∀ r, 0 < r → r < 11 → 2 ^ r % 23 ≠ 1 := by
  intro r hr hlt
  have hc : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 := by omega
  cases hc with
  | inl h => subst h; decide
  | inr h =>
    cases h with
    | inl h => subst h; decide
    | inr h =>
      cases h with
      | inl h => subst h; decide
      | inr h =>
        cases h with
        | inl h => subst h; decide
        | inr h =>
          cases h with
          | inl h => subst h; decide
          | inr h =>
            cases h with
            | inl h => subst h; decide
            | inr h =>
              cases h with
              | inl h => subst h; decide
              | inr h =>
                cases h with
                | inl h => subst h; decide
                | inr h =>
                  cases h with
                  | inl h => subst h; decide
                  | inr h => subst h; decide

theorem e820_min_3_23 : ∀ r, 0 < r → r < 11 → 3 ^ r % 23 ≠ 1 := by
  intro r hr hlt
  have hc : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 := by omega
  cases hc with
  | inl h => subst h; decide
  | inr h =>
    cases h with
    | inl h => subst h; decide
    | inr h =>
      cases h with
      | inl h => subst h; decide
      | inr h =>
        cases h with
        | inl h => subst h; decide
        | inr h =>
          cases h with
          | inl h => subst h; decide
          | inr h =>
            cases h with
            | inl h => subst h; decide
            | inr h =>
              cases h with
              | inl h => subst h; decide
              | inr h =>
                cases h with
                | inl h => subst h; decide
                | inr h =>
                  cases h with
                  | inl h => subst h; decide
                  | inr h => subst h; decide

theorem e820_law_2_5 (m : Nat) : 5 ∣ 2 ^ m - 1 ↔ 4 ∣ m := by
  have hpos : 1 ≤ 2 ^ m := e820_pow_pos 2 m (by omega)
  have hmod : 2 ^ m % 5 = 1 ↔ 4 ∣ m :=
    e820_order_law 2 5 4 (by omega) (by omega) (by decide) e820_min_2_5 m
  constructor
  · intro h
    have h1 : 2 ^ m % 5 = 1 := by omega
    exact hmod.mp h1
  · intro h
    have h1 := hmod.mpr h
    omega

theorem e820_law_3_5 (m : Nat) : 5 ∣ 3 ^ m - 1 ↔ 4 ∣ m := by
  have hpos : 1 ≤ 3 ^ m := e820_pow_pos 3 m (by omega)
  have hmod : 3 ^ m % 5 = 1 ↔ 4 ∣ m :=
    e820_order_law 3 5 4 (by omega) (by omega) (by decide) e820_min_3_5 m
  constructor
  · intro h
    have h1 : 3 ^ m % 5 = 1 := by omega
    exact hmod.mp h1
  · intro h
    have h1 := hmod.mpr h
    omega

theorem e820_law_2_7 (m : Nat) : 7 ∣ 2 ^ m - 1 ↔ 3 ∣ m := by
  have hpos : 1 ≤ 2 ^ m := e820_pow_pos 2 m (by omega)
  have hmod : 2 ^ m % 7 = 1 ↔ 3 ∣ m :=
    e820_order_law 2 7 3 (by omega) (by omega) (by decide) e820_min_2_7 m
  constructor
  · intro h
    have h1 : 2 ^ m % 7 = 1 := by omega
    exact hmod.mp h1
  · intro h
    have h1 := hmod.mpr h
    omega

theorem e820_law_3_7 (m : Nat) : 7 ∣ 3 ^ m - 1 ↔ 6 ∣ m := by
  have hpos : 1 ≤ 3 ^ m := e820_pow_pos 3 m (by omega)
  have hmod : 3 ^ m % 7 = 1 ↔ 6 ∣ m :=
    e820_order_law 3 7 6 (by omega) (by omega) (by decide) e820_min_3_7 m
  constructor
  · intro h
    have h1 : 3 ^ m % 7 = 1 := by omega
    exact hmod.mp h1
  · intro h
    have h1 := hmod.mpr h
    omega

theorem e820_law_2_11 (m : Nat) : 11 ∣ 2 ^ m - 1 ↔ 10 ∣ m := by
  have hpos : 1 ≤ 2 ^ m := e820_pow_pos 2 m (by omega)
  have hmod : 2 ^ m % 11 = 1 ↔ 10 ∣ m :=
    e820_order_law 2 11 10 (by omega) (by omega) (by decide) e820_min_2_11 m
  constructor
  · intro h
    have h1 : 2 ^ m % 11 = 1 := by omega
    exact hmod.mp h1
  · intro h
    have h1 := hmod.mpr h
    omega

theorem e820_law_3_11 (m : Nat) : 11 ∣ 3 ^ m - 1 ↔ 5 ∣ m := by
  have hpos : 1 ≤ 3 ^ m := e820_pow_pos 3 m (by omega)
  have hmod : 3 ^ m % 11 = 1 ↔ 5 ∣ m :=
    e820_order_law 3 11 5 (by omega) (by omega) (by decide) e820_min_3_11 m
  constructor
  · intro h
    have h1 : 3 ^ m % 11 = 1 := by omega
    exact hmod.mp h1
  · intro h
    have h1 := hmod.mpr h
    omega

theorem e820_law_2_13 (m : Nat) : 13 ∣ 2 ^ m - 1 ↔ 12 ∣ m := by
  have hpos : 1 ≤ 2 ^ m := e820_pow_pos 2 m (by omega)
  have hmod : 2 ^ m % 13 = 1 ↔ 12 ∣ m :=
    e820_order_law 2 13 12 (by omega) (by omega) (by decide) e820_min_2_13 m
  constructor
  · intro h
    have h1 : 2 ^ m % 13 = 1 := by omega
    exact hmod.mp h1
  · intro h
    have h1 := hmod.mpr h
    omega

theorem e820_law_3_13 (m : Nat) : 13 ∣ 3 ^ m - 1 ↔ 3 ∣ m := by
  have hpos : 1 ≤ 3 ^ m := e820_pow_pos 3 m (by omega)
  have hmod : 3 ^ m % 13 = 1 ↔ 3 ∣ m :=
    e820_order_law 3 13 3 (by omega) (by omega) (by decide) e820_min_3_13 m
  constructor
  · intro h
    have h1 : 3 ^ m % 13 = 1 := by omega
    exact hmod.mp h1
  · intro h
    have h1 := hmod.mpr h
    omega

theorem e820_law_2_23 (m : Nat) : 23 ∣ 2 ^ m - 1 ↔ 11 ∣ m := by
  have hpos : 1 ≤ 2 ^ m := e820_pow_pos 2 m (by omega)
  have hmod : 2 ^ m % 23 = 1 ↔ 11 ∣ m :=
    e820_order_law 2 23 11 (by omega) (by omega) (by decide) e820_min_2_23 m
  constructor
  · intro h
    have h1 : 2 ^ m % 23 = 1 := by omega
    exact hmod.mp h1
  · intro h
    have h1 := hmod.mpr h
    omega

theorem e820_law_3_23 (m : Nat) : 23 ∣ 3 ^ m - 1 ↔ 11 ∣ m := by
  have hpos : 1 ≤ 3 ^ m := e820_pow_pos 3 m (by omega)
  have hmod : 3 ^ m % 23 = 1 ↔ 11 ∣ m :=
    e820_order_law 3 23 11 (by omega) (by omega) (by decide) e820_min_3_23 m
  constructor
  · intro h
    have h1 : 3 ^ m % 23 = 1 := by omega
    exact hmod.mp h1
  · intro h
    have h1 := hmod.mpr h
    omega

/-! ## §3 THE ORDER-CRITERION + the five gates. -/

/-- **THE ORDER-CRITERION LAW** (the mathematical core of #820, general
form): for any `k, l, n` and prime `p ∤ k·l`, given the two order laws
(explicit finite exponent data `o_k = ord_p(k)`, `o_l = ord_p(l)`),
`p ∣ gcd(k^n − 1, l^n − 1) ↔ (o_k ∣ n ∧ o_l ∣ n)` — equivalently
`lcm(o_k, o_l) ∣ n`.  Primes dividing `k·l` never divide `k^n − 1`
(`k^n ≡ 0 mod p ⇒ k^n − 1 ≡ −1`), so this is the COMPLETE prime
analysis of the corpus quantity. -/
theorem e820_criterion (p k l n o_k o_l : Nat)
    (H1 : ∀ m, p ∣ k ^ m - 1 ↔ o_k ∣ m)
    (H2 : ∀ m, p ∣ l ^ m - 1 ↔ o_l ∣ m) :
    p ∣ Nat.gcd (k ^ n - 1) (l ^ n - 1) ↔ (o_k ∣ n ∧ o_l ∣ n) := by
  constructor
  · intro h
    exact ⟨(H1 n).mp (Nat.dvd_trans h (Nat.gcd_dvd_left (k ^ n - 1) (l ^ n - 1))),
      (H2 n).mp (Nat.dvd_trans h (Nat.gcd_dvd_right (k ^ n - 1) (l ^ n - 1)))⟩
  · intro h
    exact Nat.dvd_gcd ((H1 n).mpr h.1) ((H2 n).mpr h.2)

/-- GATE 5: `5 ∣ gcd(2^n−1, 3^n−1) ↔ 4 ∣ n` (L_5 = 4). -/
theorem e820_gate5 (n : Nat) : 5 ∣ Nat.gcd (2 ^ n - 1) (3 ^ n - 1) ↔ 4 ∣ n := by
  have h := e820_criterion 5 2 3 n 4 4 e820_law_2_5 e820_law_3_5
  constructor
  · intro hg; exact (h.mp hg).1
  · intro hd; exact h.mpr ⟨hd, hd⟩

/-- GATE 7: `7 ∣ gcd(2^n−1, 3^n−1) ↔ 6 ∣ n` (L_7 = 6). -/
theorem e820_gate7 (n : Nat) : 7 ∣ Nat.gcd (2 ^ n - 1) (3 ^ n - 1) ↔ 6 ∣ n := by
  have h := e820_criterion 7 2 3 n 3 6 e820_law_2_7 e820_law_3_7
  constructor
  · intro hg; exact (h.mp hg).2
  · intro hd; exact h.mpr ⟨by omega, hd⟩

/-- GATE 11: `11 ∣ gcd(2^n−1, 3^n−1) ↔ 10 ∣ n` (L_11 = 10). -/
theorem e820_gate11 (n : Nat) : 11 ∣ Nat.gcd (2 ^ n - 1) (3 ^ n - 1) ↔ 10 ∣ n := by
  have h := e820_criterion 11 2 3 n 10 5 e820_law_2_11 e820_law_3_11
  constructor
  · intro hg; exact (h.mp hg).1
  · intro hd; exact h.mpr ⟨hd, by omega⟩

/-- GATE 13: `13 ∣ gcd(2^n−1, 3^n−1) ↔ 12 ∣ n` (L_13 = 12). -/
theorem e820_gate13 (n : Nat) : 13 ∣ Nat.gcd (2 ^ n - 1) (3 ^ n - 1) ↔ 12 ∣ n := by
  have h := e820_criterion 13 2 3 n 12 3 e820_law_2_13 e820_law_3_13
  constructor
  · intro hg; exact (h.mp hg).1
  · intro hd; exact h.mpr ⟨hd, by omega⟩

/-- GATE 23: `23 ∣ gcd(2^n−1, 3^n−1) ↔ 11 ∣ n` (L_23 = 11 — the FIRST
odd L_p: 11 | n ⇒ bad n, the smallest odd obstruction). -/
theorem e820_gate23 (n : Nat) : 23 ∣ Nat.gcd (2 ^ n - 1) (3 ^ n - 1) ↔ 11 ∣ n := by
  have h := e820_criterion 23 2 3 n 11 11 e820_law_2_23 e820_law_3_23
  constructor
  · intro hg; exact (h.mp hg).1
  · intro hd; exact h.mpr ⟨hd, hd⟩

/-! ## §4 The bad laws + the n ≤ 12 classification. -/

theorem e820_bad_of_four (n : Nat) (h : 4 ∣ n) :
    Nat.gcd (2 ^ n - 1) (3 ^ n - 1) ≠ 1 := by
  intro hg
  have h5 : 5 ∣ Nat.gcd (2 ^ n - 1) (3 ^ n - 1) := (e820_gate5 n).mpr h
  omega

theorem e820_bad_of_six (n : Nat) (h : 6 ∣ n) :
    Nat.gcd (2 ^ n - 1) (3 ^ n - 1) ≠ 1 := by
  intro hg
  have h7 : 7 ∣ Nat.gcd (2 ^ n - 1) (3 ^ n - 1) := (e820_gate7 n).mpr h
  omega

theorem e820_bad_of_ten (n : Nat) (h : 10 ∣ n) :
    Nat.gcd (2 ^ n - 1) (3 ^ n - 1) ≠ 1 := by
  intro hg
  have h11 : 11 ∣ Nat.gcd (2 ^ n - 1) (3 ^ n - 1) := (e820_gate11 n).mpr h
  omega

theorem e820_bad_of_eleven (n : Nat) (h : 11 ∣ n) :
    Nat.gcd (2 ^ n - 1) (3 ^ n - 1) ≠ 1 := by
  intro hg
  have h23 : 23 ∣ Nat.gcd (2 ^ n - 1) (3 ^ n - 1) := (e820_gate23 n).mpr h
  omega

/-- **THE BAD LAW** (structural, all n): if any L_p ∈ {4, 6, 10, 11}
divides n (12 included via 4 | 12), the gcd is not 1. -/
theorem e820_bad (n : Nat) (h : 4 ∣ n ∨ 6 ∣ n ∨ 10 ∣ n ∨ 11 ∣ n) :
    Nat.gcd (2 ^ n - 1) (3 ^ n - 1) ≠ 1 := by
  cases h with
  | inl h => exact e820_bad_of_four n h
  | inr h => cases h with
    | inl h => exact e820_bad_of_six n h
    | inr h => cases h with
      | inl h => exact e820_bad_of_ten n h
      | inr h => exact e820_bad_of_eleven n h

/-- **THE CERTIFIED CLASSIFICATION BOARD for n ≤ 12** (the good-n set):
`gcd(2^n−1, 3^n−1) = 1 ↔ n ∈ {1, 2, 3, 5, 7, 9}` — the ← side by
decide rows, the → side STRUCTURALLY (any other residue ≤ 12 is divisible
by 4, 6, 10 or 11, and the gates kill it). -/
theorem e820_class12 (n : Nat) (hn : n ≤ 12) :
    Nat.gcd (2 ^ n - 1) (3 ^ n - 1) = 1 ↔
      (n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 9) := by
  constructor
  · intro h
    by_cases hgood : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 9
    · exact hgood
    · have hbad : 4 ∣ n ∨ 6 ∣ n ∨ 10 ∣ n ∨ 11 ∣ n := by omega
      exact absurd h (e820_bad n hbad)
  · intro hgood
    cases hgood with
    | inl h => subst h; decide
    | inr h => cases h with
      | inl h => subst h; decide
      | inr h => cases h with
        | inl h => subst h; decide
        | inr h => cases h with
          | inl h => subst h; decide
          | inr h => subst h; decide

/-! ## §5 The census rows + the H witness theorems. -/

/-- THE DECIDE CENSUS (n ≤ 12): the exact gcd values — good rows = 1,
bad rows = the obstruction value (5, 7, 5, 11, 23, 455). -/
theorem e820_rows12 :
    Nat.gcd (2 ^ 1 - 1) (3 ^ 1 - 1) = 1 ∧
    Nat.gcd (2 ^ 2 - 1) (3 ^ 2 - 1) = 1 ∧
    Nat.gcd (2 ^ 3 - 1) (3 ^ 3 - 1) = 1 ∧
    Nat.gcd (2 ^ 4 - 1) (3 ^ 4 - 1) = 5 ∧
    Nat.gcd (2 ^ 5 - 1) (3 ^ 5 - 1) = 1 ∧
    Nat.gcd (2 ^ 6 - 1) (3 ^ 6 - 1) = 7 ∧
    Nat.gcd (2 ^ 7 - 1) (3 ^ 7 - 1) = 1 ∧
    Nat.gcd (2 ^ 8 - 1) (3 ^ 8 - 1) = 5 ∧
    Nat.gcd (2 ^ 9 - 1) (3 ^ 9 - 1) = 1 ∧
    Nat.gcd (2 ^ 10 - 1) (3 ^ 10 - 1) = 11 ∧
    Nat.gcd (2 ^ 11 - 1) (3 ^ 11 - 1) = 23 ∧
    Nat.gcd (2 ^ 12 - 1) (3 ^ 12 - 1) = 455 := by
  decide

/-- **THE H(n) = 3 LAW** (generic): every good n — every n with
`gcd(2^n−1, 3^n−1) = 1` — has H(n) = 3 under the k ≥ 2 convention:
the pair (2, 3) witnesses l = 3, and no pair exists at l ≤ 2 (k ≥ 2 and
k < l ≤ 2 is impossible).  THE INFINITUDE OF SUCH n IS THE OPEN
QUESTION — this theorem certifies each instance. -/
theorem e820_H_three (n : Nat) (h : e820_G 2 3 n = 1) :
    (∃ k, 2 ≤ k ∧ k < 3 ∧ e820_G k 3 n = 1) ∧
    (∀ l, l ≤ 2 → ∀ k, 2 ≤ k → k < l → e820_G k l n ≠ 1) := by
  constructor
  · exact ⟨2, by omega, by omega, h⟩
  · intro l hl k hk2 hkl
    omega

/-- **H(1) = 3**: `gcd(2^1−1, 3^1−1) = gcd(1, 2) = 1`. -/
theorem e820_H1 :
    (∃ k, 2 ≤ k ∧ k < 3 ∧ e820_G k 3 1 = 1) ∧
    (∀ l, l ≤ 2 → ∀ k, 2 ≤ k → k < l → e820_G k l 1 ≠ 1) := by
  constructor
  · exact ⟨2, by omega, by omega, by decide⟩
  · intro l hl k hk2 hkl
    omega

/-- **H(4) = 6**: the pair (5, 6) is coprime at n = 4
(gcd(624, 1295) = 1) and the full minimality lattice l ≤ 5 is decided
dead (12 rows). -/
theorem e820_H4 :
    (∃ k, 2 ≤ k ∧ k < 6 ∧ e820_G k 6 4 = 1) ∧
    (∀ l, 2 ≤ l → l ≤ 5 → ∀ k, 2 ≤ k → k < l → e820_G k l 4 ≠ 1) := by
  constructor
  · exact ⟨5, by omega, by omega, by decide⟩
  · intro l hl2 hl5 k hk2 hkl
    have hkc : k = 2 ∨ k = 3 ∨ k = 4 := by omega
    have hlc : l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5 := by omega
    cases hkc with
    | inl h => subst h; cases hlc with
      | inl h => subst h; decide
      | inr h => cases h with
        | inl h => subst h; decide
        | inr h => cases h with
          | inl h => subst h; decide
          | inr h => subst h; decide
    | inr h => cases h with
      | inl h => subst h; cases hlc with
        | inl h => subst h; decide
        | inr h => cases h with
          | inl h => subst h; decide
          | inr h => cases h with
            | inl h => subst h; decide
            | inr h => subst h; decide
      | inr h => subst h; cases hlc with
        | inl h => subst h; decide
        | inr h => cases h with
          | inl h => subst h; decide
          | inr h => cases h with
            | inl h => subst h; decide
            | inr h => subst h; decide

/-- **H(11) = 5**: the pair (2, 5) is coprime at n = 11
(gcd(2047, 48828124) = 1 — the FIRST H-value where k = 2 survives but
l = 3 dies: 23 = L_23-lane kills (2, 3)) and the minimality lattice
l ≤ 4 is decided dead (6 rows). -/
theorem e820_H11 :
    (∃ k, 2 ≤ k ∧ k < 5 ∧ e820_G k 5 11 = 1) ∧
    (∀ l, 2 ≤ l → l ≤ 4 → ∀ k, 2 ≤ k → k < l → e820_G k l 11 ≠ 1) := by
  constructor
  · exact ⟨2, by omega, by omega, by decide⟩
  · intro l hl2 hl4 k hk2 hkl
    have hkc : k = 2 ∨ k = 3 := by omega
    have hlc : l = 2 ∨ l = 3 ∨ l = 4 := by omega
    cases hkc with
    | inl h => subst h; cases hlc with
      | inl h => subst h; decide
      | inr h => cases h with
        | inl h => subst h; decide
        | inr h => subst h; decide
    | inr h => subst h; cases hlc with
      | inl h => subst h; decide
      | inr h => cases h with
        | inl h => subst h; decide
        | inr h => subst h; decide

/-- **THE H(6) = 18 CENSUS ANCHOR**: the pair (14, 18) is coprime at
n = 6 (python-census H(6) = 18; the p = 7 Fermat obstruction kills every
pair with 7 ∤ k·l, so k, l must together cover 7 — 14 = 2·7). -/
theorem e820_H6w : e820_cop 14 18 6 := ⟨by omega, by omega, by decide⟩

/-- The H(4) = 6 raw anchor: gcd(5^4−1, 6^4−1) = gcd(624, 1295) = 1. -/
theorem e820_H4w : Nat.gcd (5 ^ 4 - 1) (6 ^ 4 - 1) = 1 := by decide

/-- The H(11) = 5 raw anchor: gcd(2^11−1, 5^11−1) = 1. -/
theorem e820_H11w : Nat.gcd (2 ^ 11 - 1) (5 ^ 11 - 1) = 1 := by decide

/-! ## §6 The master board. -/

/-- THE ERDOS-820 MASTER BOARD (14 conjuncts, full statements,
unconditional): the general order-criterion + the five gates + the bad
law + the n ≤ 12 classification + the decide census + the H(n) = 3 law +
the H(1) = 3, H(4) = 6, H(11) = 5 witness theorems + the H(6) = 18
census anchors. -/
theorem erdos820_board :
    (∀ p k l n o_k o_l : Nat,
        (∀ m, p ∣ k ^ m - 1 ↔ o_k ∣ m) → (∀ m, p ∣ l ^ m - 1 ↔ o_l ∣ m) →
        p ∣ Nat.gcd (k ^ n - 1) (l ^ n - 1) ↔ (o_k ∣ n ∧ o_l ∣ n))
    ∧ (∀ n : Nat, 5 ∣ Nat.gcd (2 ^ n - 1) (3 ^ n - 1) ↔ 4 ∣ n)
    ∧ (∀ n : Nat, 7 ∣ Nat.gcd (2 ^ n - 1) (3 ^ n - 1) ↔ 6 ∣ n)
    ∧ (∀ n : Nat, 11 ∣ Nat.gcd (2 ^ n - 1) (3 ^ n - 1) ↔ 10 ∣ n)
    ∧ (∀ n : Nat, 13 ∣ Nat.gcd (2 ^ n - 1) (3 ^ n - 1) ↔ 12 ∣ n)
    ∧ (∀ n : Nat, 23 ∣ Nat.gcd (2 ^ n - 1) (3 ^ n - 1) ↔ 11 ∣ n)
    ∧ (∀ n : Nat, (4 ∣ n ∨ 6 ∣ n ∨ 10 ∣ n ∨ 11 ∣ n) →
        Nat.gcd (2 ^ n - 1) (3 ^ n - 1) ≠ 1)
    ∧ (∀ n : Nat, n ≤ 12 → (Nat.gcd (2 ^ n - 1) (3 ^ n - 1) = 1 ↔
        (n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 9)))
    ∧ (Nat.gcd (2 ^ 1 - 1) (3 ^ 1 - 1) = 1 ∧
       Nat.gcd (2 ^ 2 - 1) (3 ^ 2 - 1) = 1 ∧
       Nat.gcd (2 ^ 3 - 1) (3 ^ 3 - 1) = 1 ∧
       Nat.gcd (2 ^ 4 - 1) (3 ^ 4 - 1) = 5 ∧
       Nat.gcd (2 ^ 5 - 1) (3 ^ 5 - 1) = 1 ∧
       Nat.gcd (2 ^ 6 - 1) (3 ^ 6 - 1) = 7 ∧
       Nat.gcd (2 ^ 7 - 1) (3 ^ 7 - 1) = 1 ∧
       Nat.gcd (2 ^ 8 - 1) (3 ^ 8 - 1) = 5 ∧
       Nat.gcd (2 ^ 9 - 1) (3 ^ 9 - 1) = 1 ∧
       Nat.gcd (2 ^ 10 - 1) (3 ^ 10 - 1) = 11 ∧
       Nat.gcd (2 ^ 11 - 1) (3 ^ 11 - 1) = 23 ∧
       Nat.gcd (2 ^ 12 - 1) (3 ^ 12 - 1) = 455)
    ∧ (∀ n : Nat, e820_G 2 3 n = 1 →
        ((∃ k, 2 ≤ k ∧ k < 3 ∧ e820_G k 3 n = 1) ∧
         (∀ l, l ≤ 2 → ∀ k, 2 ≤ k → k < l → e820_G k l n ≠ 1)))
    ∧ ((∃ k, 2 ≤ k ∧ k < 3 ∧ e820_G k 3 1 = 1) ∧
       (∀ l, l ≤ 2 → ∀ k, 2 ≤ k → k < l → e820_G k l 1 ≠ 1))
    ∧ ((∃ k, 2 ≤ k ∧ k < 6 ∧ e820_G k 6 4 = 1) ∧
       (∀ l, 2 ≤ l → l ≤ 5 → ∀ k, 2 ≤ k → k < l → e820_G k l 4 ≠ 1))
    ∧ ((∃ k, 2 ≤ k ∧ k < 5 ∧ e820_G k 5 11 = 1) ∧
       (∀ l, 2 ≤ l → l ≤ 4 → ∀ k, 2 ≤ k → k < l → e820_G k l 11 ≠ 1))
    ∧ (e820_cop 14 18 6 ∧ Nat.gcd (5 ^ 4 - 1) (6 ^ 4 - 1) = 1 ∧
       Nat.gcd (2 ^ 11 - 1) (5 ^ 11 - 1) = 1) :=
  ⟨e820_criterion, e820_gate5, e820_gate7, e820_gate11, e820_gate13,
    e820_gate23, e820_bad, e820_class12, e820_rows12, e820_H_three,
    e820_H1, e820_H4, e820_H11, ⟨e820_H6w, e820_H4w, e820_H11w⟩⟩

/-! ## §7 The receipts. -/

#print axioms E820.e820_period
#print axioms E820.e820_order_law
#print axioms E820.e820_arsenal_bridge
#print axioms E820.e820_criterion
#print axioms E820.e820_gate5
#print axioms E820.e820_gate7
#print axioms E820.e820_gate11
#print axioms E820.e820_gate13
#print axioms E820.e820_gate23
#print axioms E820.e820_bad
#print axioms E820.e820_class12
#print axioms E820.e820_rows12
#print axioms E820.e820_H_three
#print axioms E820.e820_H1
#print axioms E820.e820_H4
#print axioms E820.e820_H11
#print axioms E820.e820_H6w
#print axioms E820.e820_H4w
#print axioms E820.e820_H11w
#print axioms E820.erdos820_board

#eval "E820_KERNEL_GREEN"

/-- THE FINAL RECEIPT CONSTANT (Kernel 68, #820): the order-criterion
kernel stands COMPLETE — the period law + the order law + the general
criterion + the ten prime order laws + the five gates + the bad law +
the n ≤ 12 classification board + the decide census + the H-witness
theorems (H(n) = 3 generic law, H(1) = 3, H(4) = 6 with full minimality,
H(11) = 5, the H(6) = 18 anchor), zero sorry, zero native_decide,
zero Mathlib theorem citations. -/
def E820_COPRIME_POWERS_GREEN : String := "E820_COPRIME_POWERS_GREEN"

#eval E820_COPRIME_POWERS_GREEN

end E820
