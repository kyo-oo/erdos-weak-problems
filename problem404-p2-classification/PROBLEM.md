# ERDŐS #404 — THE p = 2 CLASSIFICATION: OBSTRUCTION FAMILIES (Kill #11 + T5 extension)

## The problem (verbatim, erdosproblems.com/404, [ErGr80, p.79])

> For which integers `a ≥ 1` and primes `p` is there a finite upper bound on
> those `k` such that there are `a = a₁ < ⋯ < aₙ` with `p^k ∣ (a₁! + ⋯ + aₙ!)`?
> If `f(a,p)` is the greatest such `k`, how does this function behave?
> Is there a prime `p` and an infinite sequence `a₁ < a₂ < ⋯` such that if
> `p^{m_k}` is the highest power of `p` dividing `Σ_{i≤k} aᵢ!` then `m_k → ∞`?

Prior art on the page: **Lin [Li76] has shown that f(2,2) ≤ 2⁵⁴.**

## What this package proves (Lean kernel-green, zero sorry)

The campaign's kernel-green reduction (problem404-full/PadicReduction.lean):

  `f(a,2) = v₂(a!) + g(a,2)`,  `g(a,2) = max { g : ∃B ⊆ {a+1, a+2, …}, 2^g ∣ (1 + Σ_{j∈B} P_j(a)) }`

where `P_j(a) = (a+1)(a+2)⋯(a+j) = (a+j)!/a!`. **This kernel settles four
INFINITE families of (a,2) exactly, for EVERY a in the family:**

| Family | g(a,2) | f(a,2) | Witness | Obstruction |
|---|---|---|---|---|
| a odd (Theorem B, prior kernel) | 0 | v₂(a!) | B = ∅ | p ∣ a+1 |
| **a ≡ 4 (mod 8)** (T2) | **3** | **v₂(a!) + 3** | B = {a+1, a+3} | mod 16 (3-coin window) |
| **a ≡ 10 (mod 16)** (T3) | **6** | **v₂(a!) + 6** | B = {a+1, a+3} | mod 128 (5-coin window) |
| **a ≡ 32 or 48 (mod 64)** (T4) | **6** | **v₂(a!) + 6** | {a+1,a+3,a+5} / {a+1,a+3,a+4} | mod 128 (7-coin window) |
| **a ≡ 8 (mod 64)** (T5, NEW) | **6** | **v₂(a!) + 6** | B = {a+1, a+3, a+4, a+6} | mod 128 (7-coin window, 2 leaf residues) |

The obstructions are **uniform modular obstructions**: for every a in the
family, ALL 2^k sub-sums of the window coins `{P_1(a), …, P_k(a)}` miss −1
modulo 2^{g+1} (2 sub-cases for T2, 8 for T3, 4 for T4 — all decided in the
kernel), and all coins beyond the window vanish mod 2^{g+1} (the vanish
lemmas, proved by 2-adic factor extraction + induction).

## The classification data (engine-certified, verify_p2class.py — 144 checks)

* Full small-g table for a ≤ 200 (the deep run of the (a,2) classifier).
* **Deep survivors at 2²⁸** (g ≥ 28, BITS-LIMIT certified):
  a ∈ {2, 6, 14, 16, 18, 24, 30, 34, 38, 62, 64, 78, 94, 98, 102, 126, 142,
  146, 158, 162, 190, 194}.
* Bounded deep values: g(46,2)=27, g(86,2)=26, g(104,2)=23, g(110,2)=21,
  g(144,2)=18, g(174,2)=23, g(400,2)=14.
* Family uniformity verified: T2 to a=204, T3 to a=202, T4 to a=304, T5 to a=456
  (T5: {8, 72, 136, 200, 264, 328, 392, 456} all g=6, engine-certified BOUNDED).
* Consistency with Lin: g(2,2) ≥ 28 ≪ 2⁵⁴.

## What remains open for #404

* sub-Q1 for p = 2: the deep survivors' exact g (astronomically deep obstruc-
  tions; f(2,2) ≤ 2⁵⁴ by Lin; the other survivors unbounded candidates).
* sub-Q1 for odd p: the scan shows deep survivors everywhere (e.g. g(1,3),
  g(4,3), g(7,3), g(9,3), g(10,3), g(12,3) all ≥ 19 at 3¹⁹) — no uniform
  obstruction families found at scan depth.
* sub-Q3 (the infinite chain): open; no (a,p) with g = ∞ is known or refuted.

## Files

* `ObstructionFamilies.lean` — the kernel (1745 lines, 0 errors, 0 sorry;
  axioms [propext, Quot.sound] (T2/T3), [propext, Classical.choice,
  Quot.sound] (T4/T5)).
* `verify_p2class.py` — the battery (T5 checks added; ALL PASSED).
* `DERIVATION.tex` — the LaTeX exposition (problem → proof).
