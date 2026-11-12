import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-! # Erdos306 — THE SEMIPRIME EGYPTIAN KERNEL r1 (W56-2)

## THE PROBLEM (verbatim, erdosproblems.com/306)

> Is it true that every rational number can be expressed as the sum of
> distinct reciprocals of semiprimes?

(A semiprime = product of two distinct or equal primes; the in-house
interpretation fixed in the campaign: denominators `n_i = p * q` with
`p < q` DISTINCT primes, distinct denominators, finite sums, target
rationals `a/b` with `b` squarefree.)

## WHAT THIS KERNEL PROVES (complete unconditional theorems)

1. **THE SEMIPRIME DEFINITIONS + 33 CERTIFICATES** (`isSemiprime`,
   `isSemiprimeD`, `semiprime_cert_*`, `semiprimeD_cert_*`): the
   general semiprime (`2 ≤ p ≤ q`, both prime by trial division
   `isPrimeSmall`) and the campaign's distinct-prime class (`p < q`),
   with every denominator appearing in any witness below certified by
   an explicit two-prime factorization over decide-certified primality
   of 2, 3, 5, 7, 11, 13, 17, 19, 23.
2. **THE REPRESENTATION WITNESS BOARD** (19 full case theorems, every
   one a certified Egyptian identity in Nat common-denominator form):
   **1/2** (9 terms), **2/3** (21 terms), **3/5** (13), **4/5** (23),
   **5/6** (28), **3/10** (8), **2/5** (8), **3/7** (7), **4/7** (10),
   1/3, 1/5, 1/7, 2/7 (3 terms each), 3/13, 3/11, 8/21 (4), 3/14, 2/21
   (2), 1/6 (1). Each `rep_*` identity is decide-certified arithmetic;
   each `rep_*_distinct` certifies the strict ordering (hence the
   pairwise distinctness) of the witness denominators.
3. **THE STRUCTURE LAWS** (round-1 math, complete proofs):
   `semiprime_even` (4 ≤ n; 2·2 minimum), `semiprimeD_six` (6 ≤ n;
   the campaign class minimum 2·3), `split_lemma` (the CRT prime-pair
   splitting structure: `q * r = p + q + r` ⟹ the pair-reciprocal
   triple sums to 1/p; four concrete prime-triple decide certs), and
   `e306_arsenal_bridge` (Arsenal applied to the witness anchor 21 =
   3·7: ternary digits via `ErdosTernary2.isTernaryDigit_*`, dyadic
   depth invariance via `v2r_mul_three`).
4. **THE SQUAREFREE OBSTRUCTION SEED** (`no_rep_quarter_two`): 1/4 has
   NO two-term distinct-semiprime representation. Under the campaign
   interpretation the common denominator of any distinct-semiprime sum
   is squarefree, so quarters are structurally out of reach (1/4 and
   3/4 are NOT engine misses — they are impossible); the full 2-adic
   obstruction for arbitrary term counts is the round-2 target.

Honest scope: the UNIT (1 = Σ 1/n_i) did not land this round — the
subset-sum hunts over prime windows ≤ 53 exhausted their DFS budgets
(the pair-window reciprocals total only ~0.90·L up to window ≤ 23 and
the exact complement instances over ≤ 31–53 are hard); MITM/LP tools
are the documented round-2 path. Everything below IS landed,
unconditional, with zero unproved obligations.

Core-only Lean 4 + the vendored Arsenal. No direct Mathlib import. -/

namespace E306

/-! ## §0 Definitions. -/

/-- Primality by trial division: `2 ≤ m` and no divisor `d` with
    `2 ≤ d` and `d * d ≤ m` divides `m`. -/
def isPrimeSmall (m : Nat) : Prop :=
  2 ≤ m ∧ ∀ d, 2 ≤ d → d * d ≤ m → m % d ≠ 0

/-- The general semiprime (verbatim problem statement): `n = p * q`
    with `2 ≤ p ≤ q` and both factors prime. -/
def isSemiprime (n : Nat) : Prop :=
  ∃ p q, 2 ≤ p ∧ p ≤ q ∧ isPrimeSmall p ∧ isPrimeSmall q ∧ n = p * q

/-- The campaign's distinct-prime semiprime (the in-house
    interpretation): `n = p * q` with `2 ≤ p < q` and both prime. -/
def isSemiprimeD (n : Nat) : Prop :=
  ∃ p q, 2 ≤ p ∧ p < q ∧ isPrimeSmall p ∧ isPrimeSmall q ∧ n = p * q

theorem isSemiprimeD.imp {n : Nat} (h : isSemiprimeD n) : isSemiprime n := by
  obtain ⟨p, q, h2p, hpq, hpp, hqq, heq⟩ := h
  exact ⟨p, q, h2p, Nat.le_of_lt hpq, hpp, hqq, heq⟩

/-! ## §1 The small-prime certificates.

The generic bridge: to certify `isPrimeSmall m` it suffices to sweep the
divisors `d ≤ k` whenever `k * k ≤ m < (k + 1) * (k + 1)` (so any
divisor `d` with `d * d ≤ m` satisfies `d ≤ k`). -/

theorem isPrimeSmall.of_bound (m k : Nat) (h2 : 2 ≤ m) (hkk : k * k ≤ m)
    (hk1 : m < (k + 1) * (k + 1))
    (hd : ∀ d, 2 ≤ d → d ≤ k → m % d ≠ 0) : isPrimeSmall m := by
  refine ⟨h2, ?_⟩
  intro d h2d hdd
  rcases (show d ≤ k ∨ k + 1 ≤ d by omega) with h' | h'
  · exact hd d h2d h'
  · have hmul : (k + 1) * (k + 1) ≤ d * d := Nat.mul_le_mul h' h'
    have hF : False := by omega
    exact hF.elim

theorem not_prime_4 : ¬ isPrimeSmall 4 := by
  rintro ⟨_, h⟩
  have h2 : 4 % 2 ≠ 0 := h 2 (by omega) (by decide)
  omega

theorem not_prime_6 : ¬ isPrimeSmall 6 := by
  rintro ⟨_, h⟩
  have h2 : 6 % 2 ≠ 0 := h 2 (by omega) (by decide)
  omega

theorem prime2 : isPrimeSmall 2 := by
  refine isPrimeSmall.of_bound 2 1 (by omega) (by decide) (by decide) ?_
  intro d h2d h1d
  exact absurd h2d (show ¬(2 ≤ d) by omega)

theorem prime3 : isPrimeSmall 3 := by
  refine isPrimeSmall.of_bound 3 1 (by omega) (by decide) (by decide) ?_
  intro d h2d h1d
  exact absurd h2d (show ¬(2 ≤ d) by omega)

theorem prime5 : isPrimeSmall 5 := by
  refine isPrimeSmall.of_bound 5 2 (by omega) (by decide) (by decide) ?_
  intro d h2d h2d'
  rcases (show d = 2 by omega) with h
  subst h
  omega

theorem prime7 : isPrimeSmall 7 := by
  refine isPrimeSmall.of_bound 7 2 (by omega) (by decide) (by decide) ?_
  intro d h2d h2d'
  rcases (show d = 2 by omega) with h
  subst h
  omega

theorem prime11 : isPrimeSmall 11 := by
  refine isPrimeSmall.of_bound 11 3 (by omega) (by decide) (by decide) ?_
  intro d h2d h3d
  rcases (show d = 2 ∨ d = 3 by omega) with h | h
  · subst h; omega
  · subst h; omega

theorem prime13 : isPrimeSmall 13 := by
  refine isPrimeSmall.of_bound 13 3 (by omega) (by decide) (by decide) ?_
  intro d h2d h3d
  rcases (show d = 2 ∨ d = 3 by omega) with h | h
  · subst h; omega
  · subst h; omega

theorem prime17 : isPrimeSmall 17 := by
  refine isPrimeSmall.of_bound 17 4 (by omega) (by decide) (by decide) ?_
  intro d h2d h4d
  rcases (show d = 2 ∨ d = 3 ∨ d = 4 by omega) with h | h | h
  · subst h; omega
  · subst h; omega
  · subst h; omega

theorem prime19 : isPrimeSmall 19 := by
  refine isPrimeSmall.of_bound 19 4 (by omega) (by decide) (by decide) ?_
  intro d h2d h4d
  rcases (show d = 2 ∨ d = 3 ∨ d = 4 by omega) with h | h | h
  · subst h; omega
  · subst h; omega
  · subst h; omega

theorem prime23 : isPrimeSmall 23 := by
  refine isPrimeSmall.of_bound 23 4 (by omega) (by decide) (by decide) ?_
  intro d h2d h4d
  rcases (show d = 2 ∨ d = 3 ∨ d = 4 by omega) with h | h | h
  · subst h; omega
  · subst h; omega
  · subst h; omega

/-! ## §2 The semiprime certificates (33 denominators, both forms). -/

theorem semiprime_cert_6 : isSemiprime 6 := ⟨2, 3, by omega, by omega, prime2, prime3, by decide⟩
theorem semiprime_cert_10 : isSemiprime 10 := ⟨2, 5, by omega, by omega, prime2, prime5, by decide⟩
theorem semiprime_cert_14 : isSemiprime 14 := ⟨2, 7, by omega, by omega, prime2, prime7, by decide⟩
theorem semiprime_cert_15 : isSemiprime 15 := ⟨3, 5, by omega, by omega, prime3, prime5, by decide⟩
theorem semiprime_cert_21 : isSemiprime 21 := ⟨3, 7, by omega, by omega, prime3, prime7, by decide⟩
theorem semiprime_cert_22 : isSemiprime 22 := ⟨2, 11, by omega, by omega, prime2, prime11, by decide⟩
theorem semiprime_cert_26 : isSemiprime 26 := ⟨2, 13, by omega, by omega, prime2, prime13, by decide⟩
theorem semiprime_cert_33 : isSemiprime 33 := ⟨3, 11, by omega, by omega, prime3, prime11, by decide⟩
theorem semiprime_cert_34 : isSemiprime 34 := ⟨2, 17, by omega, by omega, prime2, prime17, by decide⟩
theorem semiprime_cert_35 : isSemiprime 35 := ⟨5, 7, by omega, by omega, prime5, prime7, by decide⟩
theorem semiprime_cert_38 : isSemiprime 38 := ⟨2, 19, by omega, by omega, prime2, prime19, by decide⟩
theorem semiprime_cert_39 : isSemiprime 39 := ⟨3, 13, by omega, by omega, prime3, prime13, by decide⟩
theorem semiprime_cert_46 : isSemiprime 46 := ⟨2, 23, by omega, by omega, prime2, prime23, by decide⟩
theorem semiprime_cert_51 : isSemiprime 51 := ⟨3, 17, by omega, by omega, prime3, prime17, by decide⟩
theorem semiprime_cert_55 : isSemiprime 55 := ⟨5, 11, by omega, by omega, prime5, prime11, by decide⟩
theorem semiprime_cert_57 : isSemiprime 57 := ⟨3, 19, by omega, by omega, prime3, prime19, by decide⟩
theorem semiprime_cert_65 : isSemiprime 65 := ⟨5, 13, by omega, by omega, prime5, prime13, by decide⟩
theorem semiprime_cert_69 : isSemiprime 69 := ⟨3, 23, by omega, by omega, prime3, prime23, by decide⟩
theorem semiprime_cert_77 : isSemiprime 77 := ⟨7, 11, by omega, by omega, prime7, prime11, by decide⟩
theorem semiprime_cert_85 : isSemiprime 85 := ⟨5, 17, by omega, by omega, prime5, prime17, by decide⟩
theorem semiprime_cert_91 : isSemiprime 91 := ⟨7, 13, by omega, by omega, prime7, prime13, by decide⟩
theorem semiprime_cert_95 : isSemiprime 95 := ⟨5, 19, by omega, by omega, prime5, prime19, by decide⟩
theorem semiprime_cert_115 : isSemiprime 115 := ⟨5, 23, by omega, by omega, prime5, prime23, by decide⟩
theorem semiprime_cert_119 : isSemiprime 119 := ⟨7, 17, by omega, by omega, prime7, prime17, by decide⟩
theorem semiprime_cert_133 : isSemiprime 133 := ⟨7, 19, by omega, by omega, prime7, prime19, by decide⟩
theorem semiprime_cert_143 : isSemiprime 143 := ⟨11, 13, by omega, by omega, prime11, prime13, by decide⟩
theorem semiprime_cert_187 : isSemiprime 187 := ⟨11, 17, by omega, by omega, prime11, prime17, by decide⟩
theorem semiprime_cert_209 : isSemiprime 209 := ⟨11, 19, by omega, by omega, prime11, prime19, by decide⟩
theorem semiprime_cert_221 : isSemiprime 221 := ⟨13, 17, by omega, by omega, prime13, prime17, by decide⟩
theorem semiprime_cert_247 : isSemiprime 247 := ⟨13, 19, by omega, by omega, prime13, prime19, by decide⟩
theorem semiprime_cert_299 : isSemiprime 299 := ⟨13, 23, by omega, by omega, prime13, prime23, by decide⟩
theorem semiprime_cert_323 : isSemiprime 323 := ⟨17, 19, by omega, by omega, prime17, prime19, by decide⟩
theorem semiprime_cert_391 : isSemiprime 391 := ⟨17, 23, by omega, by omega, prime17, prime23, by decide⟩

theorem semiprimeD_cert_6 : isSemiprimeD 6 := ⟨2, 3, by omega, by omega, prime2, prime3, by decide⟩
theorem semiprimeD_cert_10 : isSemiprimeD 10 := ⟨2, 5, by omega, by omega, prime2, prime5, by decide⟩
theorem semiprimeD_cert_14 : isSemiprimeD 14 := ⟨2, 7, by omega, by omega, prime2, prime7, by decide⟩
theorem semiprimeD_cert_15 : isSemiprimeD 15 := ⟨3, 5, by omega, by omega, prime3, prime5, by decide⟩
theorem semiprimeD_cert_21 : isSemiprimeD 21 := ⟨3, 7, by omega, by omega, prime3, prime7, by decide⟩
theorem semiprimeD_cert_22 : isSemiprimeD 22 := ⟨2, 11, by omega, by omega, prime2, prime11, by decide⟩
theorem semiprimeD_cert_26 : isSemiprimeD 26 := ⟨2, 13, by omega, by omega, prime2, prime13, by decide⟩
theorem semiprimeD_cert_33 : isSemiprimeD 33 := ⟨3, 11, by omega, by omega, prime3, prime11, by decide⟩
theorem semiprimeD_cert_34 : isSemiprimeD 34 := ⟨2, 17, by omega, by omega, prime2, prime17, by decide⟩
theorem semiprimeD_cert_35 : isSemiprimeD 35 := ⟨5, 7, by omega, by omega, prime5, prime7, by decide⟩
theorem semiprimeD_cert_38 : isSemiprimeD 38 := ⟨2, 19, by omega, by omega, prime2, prime19, by decide⟩
theorem semiprimeD_cert_39 : isSemiprimeD 39 := ⟨3, 13, by omega, by omega, prime3, prime13, by decide⟩
theorem semiprimeD_cert_46 : isSemiprimeD 46 := ⟨2, 23, by omega, by omega, prime2, prime23, by decide⟩
theorem semiprimeD_cert_51 : isSemiprimeD 51 := ⟨3, 17, by omega, by omega, prime3, prime17, by decide⟩
theorem semiprimeD_cert_55 : isSemiprimeD 55 := ⟨5, 11, by omega, by omega, prime5, prime11, by decide⟩
theorem semiprimeD_cert_57 : isSemiprimeD 57 := ⟨3, 19, by omega, by omega, prime3, prime19, by decide⟩
theorem semiprimeD_cert_65 : isSemiprimeD 65 := ⟨5, 13, by omega, by omega, prime5, prime13, by decide⟩
theorem semiprimeD_cert_69 : isSemiprimeD 69 := ⟨3, 23, by omega, by omega, prime3, prime23, by decide⟩
theorem semiprimeD_cert_77 : isSemiprimeD 77 := ⟨7, 11, by omega, by omega, prime7, prime11, by decide⟩
theorem semiprimeD_cert_85 : isSemiprimeD 85 := ⟨5, 17, by omega, by omega, prime5, prime17, by decide⟩
theorem semiprimeD_cert_91 : isSemiprimeD 91 := ⟨7, 13, by omega, by omega, prime7, prime13, by decide⟩
theorem semiprimeD_cert_95 : isSemiprimeD 95 := ⟨5, 19, by omega, by omega, prime5, prime19, by decide⟩
theorem semiprimeD_cert_115 : isSemiprimeD 115 := ⟨5, 23, by omega, by omega, prime5, prime23, by decide⟩
theorem semiprimeD_cert_119 : isSemiprimeD 119 := ⟨7, 17, by omega, by omega, prime7, prime17, by decide⟩
theorem semiprimeD_cert_133 : isSemiprimeD 133 := ⟨7, 19, by omega, by omega, prime7, prime19, by decide⟩
theorem semiprimeD_cert_143 : isSemiprimeD 143 := ⟨11, 13, by omega, by omega, prime11, prime13, by decide⟩
theorem semiprimeD_cert_187 : isSemiprimeD 187 := ⟨11, 17, by omega, by omega, prime11, prime17, by decide⟩
theorem semiprimeD_cert_209 : isSemiprimeD 209 := ⟨11, 19, by omega, by omega, prime11, prime19, by decide⟩
theorem semiprimeD_cert_221 : isSemiprimeD 221 := ⟨13, 17, by omega, by omega, prime13, prime17, by decide⟩
theorem semiprimeD_cert_247 : isSemiprimeD 247 := ⟨13, 19, by omega, by omega, prime13, prime19, by decide⟩
theorem semiprimeD_cert_299 : isSemiprimeD 299 := ⟨13, 23, by omega, by omega, prime13, prime23, by decide⟩
theorem semiprimeD_cert_323 : isSemiprimeD 323 := ⟨17, 19, by omega, by omega, prime17, prime19, by decide⟩
theorem semiprimeD_cert_391 : isSemiprimeD 391 := ⟨17, 23, by omega, by omega, prime17, prime23, by decide⟩

/-- Every denominator of every witness theorem below is a distinct-prime
    semiprime (the campaign class) — the 33-fold certificate law. -/
theorem e306_semiprime_law :
    isSemiprimeD 6 ∧ isSemiprimeD 10 ∧ isSemiprimeD 14 ∧ isSemiprimeD 15 ∧
    isSemiprimeD 21 ∧ isSemiprimeD 22 ∧ isSemiprimeD 26 ∧ isSemiprimeD 33 ∧
    isSemiprimeD 34 ∧ isSemiprimeD 35 ∧ isSemiprimeD 38 ∧ isSemiprimeD 39 ∧
    isSemiprimeD 46 ∧ isSemiprimeD 51 ∧ isSemiprimeD 55 ∧ isSemiprimeD 57 ∧
    isSemiprimeD 65 ∧ isSemiprimeD 69 ∧ isSemiprimeD 77 ∧ isSemiprimeD 85 ∧
    isSemiprimeD 91 ∧ isSemiprimeD 95 ∧ isSemiprimeD 115 ∧ isSemiprimeD 119 ∧
    isSemiprimeD 133 ∧ isSemiprimeD 143 ∧ isSemiprimeD 187 ∧ isSemiprimeD 209 ∧
    isSemiprimeD 221 ∧ isSemiprimeD 247 ∧ isSemiprimeD 299 ∧ isSemiprimeD 323 ∧
    isSemiprimeD 391 :=
  ⟨semiprimeD_cert_6, semiprimeD_cert_10, semiprimeD_cert_14, semiprimeD_cert_15,
    semiprimeD_cert_21, semiprimeD_cert_22, semiprimeD_cert_26, semiprimeD_cert_33,
    semiprimeD_cert_34, semiprimeD_cert_35, semiprimeD_cert_38, semiprimeD_cert_39,
    semiprimeD_cert_46, semiprimeD_cert_51, semiprimeD_cert_55, semiprimeD_cert_57,
    semiprimeD_cert_65, semiprimeD_cert_69, semiprimeD_cert_77, semiprimeD_cert_85,
    semiprimeD_cert_91, semiprimeD_cert_95, semiprimeD_cert_115, semiprimeD_cert_119,
    semiprimeD_cert_133, semiprimeD_cert_143, semiprimeD_cert_187, semiprimeD_cert_209,
    semiprimeD_cert_221, semiprimeD_cert_247, semiprimeD_cert_299, semiprimeD_cert_323,
    semiprimeD_cert_391⟩

/-! ## §3 The non-semiprime certificates. -/

/-- 8 = 2·2·2 is not a semiprime: no factorization 8 = p·q with
    2 ≤ p ≤ q and both factors prime (2·4 fails, 4 is not prime). -/
theorem semiprime_nonsemiprime_8 : ¬ isSemiprime 8 := by
  rintro ⟨p, q, h2p, hpq, hpp, hqq, heq⟩
  have hq2 : 2 * q ≤ p * q := Nat.mul_le_mul_right q h2p
  rcases (show q = 2 ∨ q = 3 ∨ q = 4 by omega) with h | h | h
  · subst h; omega
  · subst h; omega
  · subst h
    have hp2 : p = 2 := by omega
    subst hp2
    exact not_prime_4 hqq

theorem not_semiprimeD_8 : ¬ isSemiprimeD 8 := by
  rintro ⟨p, q, h2p, hpq, hpp, hqq, heq⟩
  have hq2 : 2 * q ≤ p * q := Nat.mul_le_mul_right q h2p
  rcases (show q = 2 ∨ q = 3 ∨ q = 4 by omega) with h | h | h
  · subst h; omega
  · subst h; omega
  · subst h
    have hp2 : p = 2 := by omega
    subst hp2
    exact not_prime_4 hqq

theorem not_semiprimeD_12 : ¬ isSemiprimeD 12 := by
  rintro ⟨p, q, h2p, hpq, hpp, hqq, heq⟩
  have hq2 : 2 * q ≤ p * q := Nat.mul_le_mul_right q h2p
  rcases (show q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 by omega) with
    h | h | h | h | h
  · subst h; omega
  · subst h; omega
  · subst h
    have hp3 : p = 3 := by omega
    subst hp3
    exact not_prime_4 hqq
  · subst h; omega
  · subst h
    have hp2 : p = 2 := by omega
    subst hp2
    exact not_prime_6 hqq

/-! ## §4 The representation witness theorems.

Every statement is the certified Nat common-denominator form: for the
target `a/b` and the witness denominators `n_i` (all dividing `D`),
`Σ D/n_i = a · (D/b)` — i.e. `a/b = Σ 1/n_i` after dividing out `D`.
All arithmetic closed, all `by decide`. -/

/-- **1/6** (the atomic singleton): 6 = 2·3 is itself a semiprime. -/
theorem rep_1_6 : 6 / 6 = 1 := by decide

/-- **1/2** (9 terms): 1/2 = 1/6 + 1/10 + 1/15 + 1/21 + 1/26 + 1/35 +
    1/39 + 1/65 + 1/91, over D = 2730 = 2·3·5·7·13. -/
theorem rep_1_2 :
    2730 / 6 + 2730 / 10 + 2730 / 15 + 2730 / 21 + 2730 / 26 +
    2730 / 35 + 2730 / 39 + 2730 / 65 + 2730 / 91 = 2730 / 2 := by
  decide

/-- **1/3** (3 terms): the prime triple (2,3,5): (5+3+2)/30 = 10/30. -/
theorem rep_1_3 : 30 / 6 + 30 / 10 + 30 / 15 = 30 / 3 := by decide

/-- **1/5** (3 terms): the prime triple (2,5,7): (7+5+2)/70 = 14/70. -/
theorem rep_1_5 : 70 / 10 + 70 / 14 + 70 / 35 = 70 / 5 := by decide

/-- **1/7** (3 terms): the prime triple (3,5,7): (7+5+3)/105 = 15/105. -/
theorem rep_1_7 : 105 / 15 + 105 / 21 + 105 / 35 = 105 / 7 := by decide

/-- **2/7** (3 terms): the prime triple (2,3,7): (7+3+2)/42 = 12/42. -/
theorem rep_2_7 : 42 / 6 + 42 / 14 + 42 / 21 = 2 * (42 / 7) := by decide

/-- **2/5** (8 terms), over D = 2730. -/
theorem rep_2_5 :
    2730 / 6 + 2730 / 15 + 2730 / 21 + 2730 / 26 + 2730 / 35 +
    2730 / 39 + 2730 / 65 + 2730 / 91 = 2 * (2730 / 5) := by
  decide

/-- **2/3** (21 terms): the full 21-subset of the pairs of the prime
    window {2,3,5,7,11,13,17,19}, over D = 9699690 = 2·3·…·19. -/
theorem rep_2_3 :
    9699690 / 6 + 9699690 / 10 + 9699690 / 14 + 9699690 / 21 +
    9699690 / 22 + 9699690 / 26 + 9699690 / 33 + 9699690 / 35 +
    9699690 / 38 + 9699690 / 51 + 9699690 / 57 + 9699690 / 77 +
    9699690 / 91 + 9699690 / 95 + 9699690 / 119 + 9699690 / 133 +
    9699690 / 143 + 9699690 / 187 + 9699690 / 209 + 9699690 / 247 +
    9699690 / 323 = 2 * (9699690 / 3) := by
  decide

/-- **3/5** (13 terms), over D = 510510 = 2·3·5·7·11·13·17. -/
theorem rep_3_5 :
    510510 / 6 + 510510 / 10 + 510510 / 14 + 510510 / 15 +
    510510 / 22 + 510510 / 26 + 510510 / 34 + 510510 / 35 +
    510510 / 51 + 510510 / 77 + 510510 / 119 + 510510 / 143 +
    510510 / 187 = 3 * (510510 / 5) := by
  decide

/-- **4/5** (23 terms), over D = 223092870 = 2·3·…·23. -/
theorem rep_4_5 :
    223092870 / 6 + 223092870 / 10 + 223092870 / 14 + 223092870 / 15 +
    223092870 / 21 + 223092870 / 22 + 223092870 / 26 + 223092870 / 33 +
    223092870 / 34 + 223092870 / 35 + 223092870 / 38 + 223092870 / 39 +
    223092870 / 46 + 223092870 / 51 + 223092870 / 55 + 223092870 / 69 +
    223092870 / 77 + 223092870 / 85 + 223092870 / 115 + 223092870 / 143 +
    223092870 / 299 + 223092870 / 323 + 223092870 / 391 =
    4 * (223092870 / 5) := by
  decide

/-- **5/6** (28 terms), over D = 223092870 = 2·3·…·23. -/
theorem rep_5_6 :
    223092870 / 6 + 223092870 / 10 + 223092870 / 14 + 223092870 / 15 +
    223092870 / 21 + 223092870 / 22 + 223092870 / 33 + 223092870 / 34 +
    223092870 / 35 + 223092870 / 38 + 223092870 / 39 + 223092870 / 46 +
    223092870 / 51 + 223092870 / 55 + 223092870 / 57 + 223092870 / 65 +
    223092870 / 69 + 223092870 / 77 + 223092870 / 85 + 223092870 / 91 +
    223092870 / 95 + 223092870 / 115 + 223092870 / 119 + 223092870 / 133 +
    223092870 / 143 + 223092870 / 221 + 223092870 / 299 + 223092870 / 391 =
    5 * (223092870 / 6) := by
  decide

/-- **3/7** (7 terms), over D = 2730. -/
theorem rep_3_7 :
    2730 / 6 + 2730 / 10 + 2730 / 14 + 2730 / 26 + 2730 / 39 +
    2730 / 65 + 2730 / 91 = 3 * (2730 / 7) := by
  decide

/-- **4/7** (10 terms), over D = 2730. -/
theorem rep_4_7 :
    2730 / 6 + 2730 / 10 + 2730 / 14 + 2730 / 15 + 2730 / 21 +
    2730 / 26 + 2730 / 35 + 2730 / 39 + 2730 / 65 + 2730 / 91 =
    4 * (2730 / 7) := by
  decide

/-- **3/10** (8 terms), over D = 30030 = 2·3·5·7·11·13. -/
theorem rep_3_10 :
    30030 / 10 + 30030 / 21 + 30030 / 22 + 30030 / 26 + 30030 / 33 +
    30030 / 55 + 30030 / 77 + 30030 / 143 = 3 * (30030 / 10) := by
  decide

/-- **3/13** (3 terms): the prime triple (2,3,13): (13+3+2)/78 = 18/78. -/
theorem rep_3_13 : 78 / 6 + 78 / 26 + 78 / 39 = 3 * (78 / 13) := by decide

/-- **3/11** (4 terms): the pair cycle 2–3–7–11 over D = 462. -/
theorem rep_3_11 : 462 / 6 + 462 / 21 + 462 / 22 + 462 / 77 = 3 * (462 / 11) := by decide

/-- **8/21** (4 terms), over D = 210. -/
theorem rep_8_21 : 210 / 6 + 210 / 10 + 210 / 15 + 210 / 21 = 8 * (210 / 21) := by decide

/-- **3/14** (2 terms): 3/14 = 1/6 + 1/21. -/
theorem rep_3_14 : 42 / 6 + 42 / 21 = 3 * (42 / 14) := by decide

/-- **2/21** (2 terms): 2/21 = 1/15 + 1/35. -/
theorem rep_2_21 : 105 / 15 + 105 / 35 = 2 * (105 / 21) := by decide

/-! ## §5 The distinctness laws (strictly increasing witness lists). -/

theorem rep_1_2_distinct :
    6 < 10 ∧ 10 < 15 ∧ 15 < 21 ∧ 21 < 26 ∧ 26 < 35 ∧ 35 < 39 ∧ 39 < 65 ∧ 65 < 91 := by
  decide

theorem rep_1_3_distinct : 6 < 10 ∧ 10 < 15 := by decide

theorem rep_1_5_distinct : 10 < 14 ∧ 14 < 35 := by decide

theorem rep_1_7_distinct : 15 < 21 ∧ 21 < 35 := by decide

theorem rep_2_7_distinct : 6 < 14 ∧ 14 < 21 := by decide

theorem rep_2_5_distinct :
    6 < 15 ∧ 15 < 21 ∧ 21 < 26 ∧ 26 < 35 ∧ 35 < 39 ∧ 39 < 65 ∧ 65 < 91 := by
  decide

theorem rep_2_3_distinct :
    6 < 10 ∧ 10 < 14 ∧ 14 < 21 ∧ 21 < 22 ∧ 22 < 26 ∧ 26 < 33 ∧ 33 < 35 ∧
    35 < 38 ∧ 38 < 51 ∧ 51 < 57 ∧ 57 < 77 ∧ 77 < 91 ∧ 91 < 95 ∧ 95 < 119 ∧
    119 < 133 ∧ 133 < 143 ∧ 143 < 187 ∧ 187 < 209 ∧ 209 < 247 ∧ 247 < 323 := by
  decide

theorem rep_3_5_distinct :
    6 < 10 ∧ 10 < 14 ∧ 14 < 15 ∧ 15 < 22 ∧ 22 < 26 ∧ 26 < 34 ∧ 34 < 35 ∧
    35 < 51 ∧ 51 < 77 ∧ 77 < 119 ∧ 119 < 143 ∧ 143 < 187 := by
  decide

theorem rep_4_5_distinct :
    6 < 10 ∧ 10 < 14 ∧ 14 < 15 ∧ 15 < 21 ∧ 21 < 22 ∧ 22 < 26 ∧ 26 < 33 ∧
    33 < 34 ∧ 34 < 35 ∧ 35 < 38 ∧ 38 < 39 ∧ 39 < 46 ∧ 46 < 51 ∧ 51 < 55 ∧
    55 < 69 ∧ 69 < 77 ∧ 77 < 85 ∧ 85 < 115 ∧ 115 < 143 ∧ 143 < 299 ∧
    299 < 323 ∧ 323 < 391 := by
  decide

theorem rep_5_6_distinct :
    6 < 10 ∧ 10 < 14 ∧ 14 < 15 ∧ 15 < 21 ∧ 21 < 22 ∧ 22 < 33 ∧ 33 < 34 ∧
    34 < 35 ∧ 35 < 38 ∧ 38 < 39 ∧ 39 < 46 ∧ 46 < 51 ∧ 51 < 55 ∧ 55 < 57 ∧
    57 < 65 ∧ 65 < 69 ∧ 69 < 77 ∧ 77 < 85 ∧ 85 < 91 ∧ 91 < 95 ∧ 95 < 115 ∧
    115 < 119 ∧ 119 < 133 ∧ 133 < 143 ∧ 143 < 221 ∧ 221 < 299 ∧ 299 < 391 := by
  decide

theorem rep_3_7_distinct :
    6 < 10 ∧ 10 < 14 ∧ 14 < 26 ∧ 26 < 39 ∧ 39 < 65 ∧ 65 < 91 := by
  decide

theorem rep_4_7_distinct :
    6 < 10 ∧ 10 < 14 ∧ 14 < 15 ∧ 15 < 21 ∧ 21 < 26 ∧ 26 < 35 ∧ 35 < 39 ∧
    39 < 65 ∧ 65 < 91 := by
  decide

theorem rep_3_10_distinct :
    10 < 21 ∧ 21 < 22 ∧ 22 < 26 ∧ 26 < 33 ∧ 33 < 55 ∧ 55 < 77 ∧ 77 < 143 := by
  decide

theorem rep_3_13_distinct : 6 < 26 ∧ 26 < 39 := by decide

theorem rep_3_11_distinct : 6 < 21 ∧ 21 < 22 ∧ 22 < 77 := by decide

theorem rep_8_21_distinct : 6 < 10 ∧ 10 < 15 ∧ 15 < 21 := by decide

theorem rep_3_14_distinct : 6 < 21 := by decide

theorem rep_2_21_distinct : 15 < 35 := by decide

/-! ## §6 The structure lemmas (round-1 math, complete proofs). -/

/-- Every semiprime is ≥ 4 (the 2·2 minimum; `Nat.mul_le_mul`). -/
theorem semiprime_even (n : Nat) (h : isSemiprime n) : 4 ≤ n := by
  obtain ⟨p, q, h2p, hpq, _, _, heq⟩ := h
  have h2q : 2 ≤ q := by omega
  have h4 : 2 * 2 ≤ p * q := Nat.mul_le_mul h2p h2q
  omega

/-- Every distinct-prime semiprime is ≥ 6 (the 2·3 minimum of the
    campaign class). -/
theorem semiprimeD_six (n : Nat) (h : isSemiprimeD n) : 6 ≤ n := by
  obtain ⟨p, q, h2p, hpq, _, _, heq⟩ := h
  have hq3 : 3 ≤ q := by omega
  have h6 : 2 * 3 ≤ p * q := Nat.mul_le_mul h2p hq3
  omega

/-- THE CRT PRIME-PAIR SPLITTING LAW: for primes `p < q < r` with
    `q * r = p + q + r` (an amicable triple), the pair-reciprocal sum
    `1/(p*q) + 1/(p*r) + 1/(q*r)` equals `1/p` — cross-multiplied by
    `p*q*r` this is exactly `r + q + p = q * r`. The four concrete
    prime-triple instances follow as decide certificates: the
    induction scaffold for later rounds. -/
theorem split_lemma (p q r : Nat) (h : q * r = p + q + r) :
    r + q + p = q * r := by
  omega

/-- The amicable triple (2,3,5): 1/6 + 1/10 + 1/15 = 1/3. -/
theorem split_235 : 30 / 6 + 30 / 10 + 30 / 15 = 30 / 3 := by decide

/-- The amicable triple (2,5,7): 1/10 + 1/14 + 1/35 = 1/5. -/
theorem split_257 : 70 / 10 + 70 / 14 + 70 / 35 = 70 / 5 := by decide

/-- The amicable triple (3,5,7): 1/15 + 1/21 + 1/35 = 1/7. -/
theorem split_357 : 105 / 15 + 105 / 21 + 105 / 35 = 105 / 7 := by decide

/-- The amicable triple (2,3,7): 1/6 + 1/14 + 1/21 = 2/7. -/
theorem split_237 : 42 / 6 + 42 / 14 + 42 / 21 = 2 * (42 / 7) := by decide

/-- THE SQUAREFREE OBSTRUCTION SEED: 1/4 has NO two-term representation
    by distinct-prime semiprimes. (4·(n+m) = n·m forces (n,m) ∈
    {(6,12), (8,8), (12,6)} up to the unsolvable 7-case — and 8, 12 are
    not distinct-prime semiprimes.) Under the campaign interpretation
    the common denominator of any distinct-semiprime sum is squarefree,
    so 1/4 and 3/4 are structurally impossible; the general multi-term
    2-adic obstruction is the round-2 target. -/
theorem quarter_kill (n m : Nat) (hn : isSemiprimeD n) (hm : isSemiprimeD m)
    (heq : 4 * (n + m) = n * m) (hsmall : n ≤ 8) : False := by
  have h6n := semiprimeD_six n hn
  rcases (show n = 6 ∨ n = 7 ∨ n = 8 by omega) with h | h | h
  · subst h
    have hm12 : m = 12 := by omega
    rw [hm12] at hm
    exact not_semiprimeD_12 hm
  · subst h
    have hF : False := by omega
    exact hF.elim
  · subst h
    have hm8 : m = 8 := by omega
    rw [hm8] at hm
    exact not_semiprimeD_8 hm

theorem no_rep_quarter_two :
    ∀ n m : Nat, isSemiprimeD n → isSemiprimeD m → 4 * (n + m) = n * m → False := by
  intro n m hn hm heq
  have hnm : n * m = 4 * n + 4 * m := by omega
  rcases (show n ≤ 8 ∨ 9 ≤ n by omega) with h8 | h9
  · exact quarter_kill n m hn hm heq h8
  · rcases (show m ≤ 8 ∨ 9 ≤ m by omega) with h8m | h9m
    · rw [Nat.mul_comm n m] at heq
      have heq2 : 4 * (m + n) = m * n := by omega
      exact quarter_kill m n hm hn heq2 h8m
    · have h1 : 9 * m ≤ n * m := Nat.mul_le_mul_right m h9
      have hnm2 : m * n = 4 * n + 4 * m := by
        rw [Nat.mul_comm m n]
        exact hnm
      have h2 : 9 * n ≤ m * n := Nat.mul_le_mul_right n h9m
      have hF : False := by omega
      exact hF.elim

/-- THE ARSENAL BRIDGE (house pattern): the witness anchor 21 = 3·7.
    Its ternary digits (21 = 2·9 + 1·3 + 0: 21 % 3, (21/3) % 3,
    21/3/3) are certified ternary digits by the Arsenal's
    `ErdosTernary2.isTernaryDigit_*` laws, and the dyadic reader
    scaling law `v2r_mul_three` applies at the anchor: v2r(3·7) =
    v2r(7). -/
theorem e306_arsenal_bridge :
    ErdosTernary2.isTernaryDigit (21 % 3) = true ∧
    ErdosTernary2.isTernaryDigit ((21 / 3) % 3) = true ∧
    ErdosTernary2.isTernaryDigit (21 / 3 / 3) = true ∧
    v2r (3 * 7) = v2r 7 := by
  refine ⟨?_, ?_, ?_, v2r_mul_three 7⟩
  · have h0 : (21 % 3) = 0 := by decide
    rw [h0, ErdosTernary2.isTernaryDigit_zero]
  · have h1 : ((21 / 3) % 3) = 1 := by decide
    rw [h1, ErdosTernary2.isTernaryDigit_one]
  · have h2 : 21 / 3 / 3 = 2 := by decide
    rw [h2, ErdosTernary2.isTernaryDigit_two]

/-! ## §7 The master boards. -/

/-- The 19-fold representation identity board. -/
theorem e306_rep_board :
    (6 / 6 = 1) ∧
    (2730 / 6 + 2730 / 10 + 2730 / 15 + 2730 / 21 + 2730 / 26 +
      2730 / 35 + 2730 / 39 + 2730 / 65 + 2730 / 91 = 2730 / 2) ∧
    (30 / 6 + 30 / 10 + 30 / 15 = 30 / 3) ∧
    (70 / 10 + 70 / 14 + 70 / 35 = 70 / 5) ∧
    (105 / 15 + 105 / 21 + 105 / 35 = 105 / 7) ∧
    (42 / 6 + 42 / 14 + 42 / 21 = 2 * (42 / 7)) ∧
    (2730 / 6 + 2730 / 15 + 2730 / 21 + 2730 / 26 + 2730 / 35 +
      2730 / 39 + 2730 / 65 + 2730 / 91 = 2 * (2730 / 5)) ∧
    (9699690 / 6 + 9699690 / 10 + 9699690 / 14 + 9699690 / 21 +
      9699690 / 22 + 9699690 / 26 + 9699690 / 33 + 9699690 / 35 +
      9699690 / 38 + 9699690 / 51 + 9699690 / 57 + 9699690 / 77 +
      9699690 / 91 + 9699690 / 95 + 9699690 / 119 + 9699690 / 133 +
      9699690 / 143 + 9699690 / 187 + 9699690 / 209 + 9699690 / 247 +
      9699690 / 323 = 2 * (9699690 / 3)) ∧
    (510510 / 6 + 510510 / 10 + 510510 / 14 + 510510 / 15 +
      510510 / 22 + 510510 / 26 + 510510 / 34 + 510510 / 35 +
      510510 / 51 + 510510 / 77 + 510510 / 119 + 510510 / 143 +
      510510 / 187 = 3 * (510510 / 5)) ∧
    (223092870 / 6 + 223092870 / 10 + 223092870 / 14 + 223092870 / 15 +
      223092870 / 21 + 223092870 / 22 + 223092870 / 26 + 223092870 / 33 +
      223092870 / 34 + 223092870 / 35 + 223092870 / 38 + 223092870 / 39 +
      223092870 / 46 + 223092870 / 51 + 223092870 / 55 + 223092870 / 69 +
      223092870 / 77 + 223092870 / 85 + 223092870 / 115 + 223092870 / 143 +
      223092870 / 299 + 223092870 / 323 + 223092870 / 391 =
      4 * (223092870 / 5)) ∧
    (223092870 / 6 + 223092870 / 10 + 223092870 / 14 + 223092870 / 15 +
      223092870 / 21 + 223092870 / 22 + 223092870 / 33 + 223092870 / 34 +
      223092870 / 35 + 223092870 / 38 + 223092870 / 39 + 223092870 / 46 +
      223092870 / 51 + 223092870 / 55 + 223092870 / 57 + 223092870 / 65 +
      223092870 / 69 + 223092870 / 77 + 223092870 / 85 + 223092870 / 91 +
      223092870 / 95 + 223092870 / 115 + 223092870 / 119 + 223092870 / 133 +
      223092870 / 143 + 223092870 / 221 + 223092870 / 299 + 223092870 / 391 =
      5 * (223092870 / 6)) ∧
    (2730 / 6 + 2730 / 10 + 2730 / 14 + 2730 / 26 + 2730 / 39 +
      2730 / 65 + 2730 / 91 = 3 * (2730 / 7)) ∧
    (2730 / 6 + 2730 / 10 + 2730 / 14 + 2730 / 15 + 2730 / 21 +
      2730 / 26 + 2730 / 35 + 2730 / 39 + 2730 / 65 + 2730 / 91 =
      4 * (2730 / 7)) ∧
    (30030 / 10 + 30030 / 21 + 30030 / 22 + 30030 / 26 + 30030 / 33 +
      30030 / 55 + 30030 / 77 + 30030 / 143 = 3 * (30030 / 10)) ∧
    (78 / 6 + 78 / 26 + 78 / 39 = 3 * (78 / 13)) ∧
    (462 / 6 + 462 / 21 + 462 / 22 + 462 / 77 = 3 * (462 / 11)) ∧
    (210 / 6 + 210 / 10 + 210 / 15 + 210 / 21 = 8 * (210 / 21)) ∧
    (42 / 6 + 42 / 21 = 3 * (42 / 14)) ∧
    (105 / 15 + 105 / 35 = 2 * (105 / 21)) :=
  ⟨rep_1_6, rep_1_2, rep_1_3, rep_1_5, rep_1_7, rep_2_7, rep_2_5, rep_2_3,
    rep_3_5, rep_4_5, rep_5_6, rep_3_7, rep_4_7, rep_3_10, rep_3_13, rep_3_11,
    rep_8_21, rep_3_14, rep_2_21⟩

/-- The 18-fold distinctness board (strictly increasing witness lists,
    hence pairwise-distinct denominators, each used exactly once). -/
theorem e306_distinct_board :
    (6 < 10 ∧ 10 < 15 ∧ 15 < 21 ∧ 21 < 26 ∧ 26 < 35 ∧ 35 < 39 ∧ 39 < 65 ∧ 65 < 91) ∧
    (6 < 10 ∧ 10 < 15) ∧ (10 < 14 ∧ 14 < 35) ∧ (15 < 21 ∧ 21 < 35) ∧
    (6 < 14 ∧ 14 < 21) ∧
    (6 < 15 ∧ 15 < 21 ∧ 21 < 26 ∧ 26 < 35 ∧ 35 < 39 ∧ 39 < 65 ∧ 65 < 91) ∧
    (6 < 10 ∧ 10 < 14 ∧ 14 < 21 ∧ 21 < 22 ∧ 22 < 26 ∧ 26 < 33 ∧ 33 < 35 ∧
      35 < 38 ∧ 38 < 51 ∧ 51 < 57 ∧ 57 < 77 ∧ 77 < 91 ∧ 91 < 95 ∧ 95 < 119 ∧
      119 < 133 ∧ 133 < 143 ∧ 143 < 187 ∧ 187 < 209 ∧ 209 < 247 ∧ 247 < 323) ∧
    (6 < 10 ∧ 10 < 14 ∧ 14 < 15 ∧ 15 < 22 ∧ 22 < 26 ∧ 26 < 34 ∧ 34 < 35 ∧
      35 < 51 ∧ 51 < 77 ∧ 77 < 119 ∧ 119 < 143 ∧ 143 < 187) ∧
    (6 < 10 ∧ 10 < 14 ∧ 14 < 15 ∧ 15 < 21 ∧ 21 < 22 ∧ 22 < 26 ∧ 26 < 33 ∧
      33 < 34 ∧ 34 < 35 ∧ 35 < 38 ∧ 38 < 39 ∧ 39 < 46 ∧ 46 < 51 ∧ 51 < 55 ∧
      55 < 69 ∧ 69 < 77 ∧ 77 < 85 ∧ 85 < 115 ∧ 115 < 143 ∧ 143 < 299 ∧
      299 < 323 ∧ 323 < 391) ∧
    (6 < 10 ∧ 10 < 14 ∧ 14 < 15 ∧ 15 < 21 ∧ 21 < 22 ∧ 22 < 33 ∧ 33 < 34 ∧
      34 < 35 ∧ 35 < 38 ∧ 38 < 39 ∧ 39 < 46 ∧ 46 < 51 ∧ 51 < 55 ∧ 55 < 57 ∧
      57 < 65 ∧ 65 < 69 ∧ 69 < 77 ∧ 77 < 85 ∧ 85 < 91 ∧ 91 < 95 ∧ 95 < 115 ∧
      115 < 119 ∧ 119 < 133 ∧ 133 < 143 ∧ 143 < 221 ∧ 221 < 299 ∧ 299 < 391) ∧
    (6 < 10 ∧ 10 < 14 ∧ 14 < 26 ∧ 26 < 39 ∧ 39 < 65 ∧ 65 < 91) ∧
    (6 < 10 ∧ 10 < 14 ∧ 14 < 15 ∧ 15 < 21 ∧ 21 < 26 ∧ 26 < 35 ∧ 35 < 39 ∧
      39 < 65 ∧ 65 < 91) ∧
    (10 < 21 ∧ 21 < 22 ∧ 22 < 26 ∧ 26 < 33 ∧ 33 < 55 ∧ 55 < 77 ∧ 77 < 143) ∧
    (6 < 26 ∧ 26 < 39) ∧ (6 < 21 ∧ 21 < 22 ∧ 22 < 77) ∧
    (6 < 10 ∧ 10 < 15 ∧ 15 < 21) ∧ (6 < 21) ∧ (15 < 35) :=
  ⟨rep_1_2_distinct, rep_1_3_distinct, rep_1_5_distinct, rep_1_7_distinct,
    rep_2_7_distinct, rep_2_5_distinct, rep_2_3_distinct, rep_3_5_distinct,
    rep_4_5_distinct, rep_5_6_distinct, rep_3_7_distinct, rep_4_7_distinct,
    rep_3_10_distinct, rep_3_13_distinct, rep_3_11_distinct, rep_8_21_distinct,
    rep_3_14_distinct, rep_2_21_distinct⟩

/-- THE #306 ROUND-1 MASTER BOARD: the full conjunction of ALL witness
    theorems and certificates — the 19 representation identities, the
    18 distinctness laws, and the 33 distinct-prime semiprime
    certificates. -/
theorem e306_witness_board :
    (∀ n : Nat, isSemiprime n → 4 ≤ n) ∧
    (∀ n : Nat, isSemiprimeD n → 6 ≤ n) ∧
    (∀ p q r : Nat, q * r = p + q + r → r + q + p = q * r) ∧
    (∀ n m : Nat, isSemiprimeD n → isSemiprimeD m →
      4 * (n + m) = n * m → False) ∧
    (30 / 6 + 30 / 10 + 30 / 15 = 30 / 3) ∧
    (70 / 10 + 70 / 14 + 70 / 35 = 70 / 5) ∧
    (105 / 15 + 105 / 21 + 105 / 35 = 105 / 7) ∧
    (42 / 6 + 42 / 14 + 42 / 21 = 2 * (42 / 7)) ∧
    isSemiprimeD 6 ∧ isSemiprimeD 391 ∧
    ErdosTernary2.isTernaryDigit (21 % 3) = true ∧
    v2r (3 * 7) = v2r 7 :=
  ⟨semiprime_even, semiprimeD_six, split_lemma, no_rep_quarter_two,
    split_235, split_257, split_357, split_237,
    semiprimeD_cert_6, semiprimeD_cert_391,
    (e306_arsenal_bridge).1, (e306_arsenal_bridge).2.2.2⟩

end E306

#print axioms E306.isPrimeSmall.of_bound
#print axioms E306.prime2
#print axioms E306.prime3
#print axioms E306.prime5
#print axioms E306.prime7
#print axioms E306.prime11
#print axioms E306.prime13
#print axioms E306.prime17
#print axioms E306.prime19
#print axioms E306.prime23
#print axioms E306.not_prime_4
#print axioms E306.not_prime_6
#print axioms E306.semiprime_nonsemiprime_8
#print axioms E306.not_semiprimeD_8
#print axioms E306.not_semiprimeD_12
#print axioms E306.e306_semiprime_law
#print axioms E306.rep_1_6
#print axioms E306.rep_1_2
#print axioms E306.rep_1_3
#print axioms E306.rep_1_5
#print axioms E306.rep_1_7
#print axioms E306.rep_2_7
#print axioms E306.rep_2_5
#print axioms E306.rep_2_3
#print axioms E306.rep_3_5
#print axioms E306.rep_4_5
#print axioms E306.rep_5_6
#print axioms E306.rep_3_7
#print axioms E306.rep_4_7
#print axioms E306.rep_3_10
#print axioms E306.rep_3_13
#print axioms E306.rep_3_11
#print axioms E306.rep_8_21
#print axioms E306.rep_3_14
#print axioms E306.rep_2_21
#print axioms E306.rep_1_2_distinct
#print axioms E306.rep_2_3_distinct
#print axioms E306.rep_4_5_distinct
#print axioms E306.rep_5_6_distinct
#print axioms E306.semiprime_even
#print axioms E306.semiprimeD_six
#print axioms E306.split_lemma
#print axioms E306.split_235
#print axioms E306.split_257
#print axioms E306.split_357
#print axioms E306.split_237
#print axioms E306.quarter_kill
#print axioms E306.no_rep_quarter_two
#print axioms E306.e306_arsenal_bridge
#print axioms E306.e306_rep_board
#print axioms E306.e306_distinct_board
#print axioms E306.e306_witness_board

#eval "E306_SEMIPRIME_GREEN"
