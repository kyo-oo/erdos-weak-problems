# ERDŐS #404 — THE p = 2 CLASSIFICATION: OBSTRUCTION FAMILIES (Kills #11 + T5 + T6/T6b/T6c/T7/T7b)

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

where `P_j(a) = (a+1)(a+2)⋯(a+j) = (a+j)!/a!`. **This kernel settles NINE
INFINITE families of (a,2) exactly, for EVERY a in the family:**

| Family | g(a,2) | f(a,2) | Witness | Obstruction |
|---|---|---|---|---|
| a odd (Theorem B, prior kernel) | 0 | v₂(a!) | B = ∅ | p ∣ a+1 |
| **a ≡ 4 (mod 8)** (T2) | **3** | **v₂(a!) + 3** | B = {a+1, a+3} | mod 16 (3-coin window) |
| **a ≡ 10 (mod 16)** (T3) | **6** | **v₂(a!) + 6** | B = {a+1, a+3} | mod 128 (5-coin window) |
| **a ≡ 32 or 48 (mod 64)** (T4) | **6** | **v₂(a!) + 6** | {a+1,a+3,a+5} / {a+1,a+3,a+4} | mod 128 (7-coin window) |
| **a ≡ 8 (mod 64)** (T5) | **6** | **v₂(a!) + 6** | B = {a+1, a+3, a+4, a+6} | mod 128 (7-coin window, 2 leaf residues) |
| **a ≡ 40 (mod 128)** (T6, NEW) | **7** | **v₂(a!) + 7** | B = {a+1, a+3, a+4, a+6} | mod 256 (7-coin window, 2 leaf residues) |
| **a ≡ 56 (mod 128)** (T6b, NEW) | **7** | **v₂(a!) + 7** | B = {a+1, a+3, a+5, a+6} | mod 256 (7-coin window, 2 leaf residues) |
| **a ≡ 88 (mod 128)** (T6c, NEW) | **7** | **v₂(a!) + 7** | B = {a+1, a+3, a+4, a+7} | mod 256 (7-coin window, 2 leaf residues) |
| **a ≡ 70 (mod 128)** (T7, NEW) | **10** | **v₂(a!) + 10** | B = {a+1, a+3, a+6, a+7, a+9} | mod 2048 (9-coin window, 16 leaf residues) |
| **a ≡ 118 (mod 128)** (T7b, NEW) | **10** | **v₂(a!) + 10** | B = {a+1, a+3, a+6, a+7, a+9} | mod 2048 (9-coin window, 16 leaf residues) |

The obstructions are **uniform modular obstructions**: for every a in the
family, ALL 2^k sub-sums of the window coins `{P_1(a), …, P_k(a)}` miss −1
modulo 2^{g+1} (2 sub-cases for T2, 8 for T3, 4 for T4 — all decided in the
kernel), and all coins beyond the window vanish mod 2^{g+1} (the vanish
lemmas, proved by 2-adic factor extraction + induction).

## The five new families (Kill #13): theorem statements & proof sketches

**Theorem T6.** For every a ≡ 40 (mod 128): g(a,2) = 7 exactly, i.e.
f(a,2) = v₂(a!) + 7.

**Theorem T6b.** For every a ≡ 56 (mod 128): g(a,2) = 7 exactly.

**Theorem T6c.** For every a ≡ 88 (mod 128): g(a,2) = 7 exactly.

**Theorem T7.** For every a ≡ 70 (mod 128): g(a,2) = 10 exactly, i.e.
f(a,2) = v₂(a!) + 10.

**Theorem T7b.** For every a ≡ 118 (mod 128): g(a,2) = 10 exactly.

*Proof sketch, T6/T6b/T6c (shared machinery).* The vanish profile of the
T6-family is v₂(a+2) = 1, v₂(a+4) = 2, v₂(a+6) = 1, v₂(a+8) = 4 — i.e.
(a+2)%2, (a+4)%4, (a+6)%2, (a+8)%16 vanish — so 2^(1+2+1+4) = 2^8 = 256
divides every P_j(a) with j ≥ 8 (`vanish_T6fam`). The window is the seven
coins P_1..P_7 mod 256; the leaf residues are a % 256 ∈ {40, 168} (T6),
{56, 184} (T6b), {88, 216} (T6c). In each of the six leaves, all 2^7 = 128
sub-sums miss −1 mod 256 (decided in the kernel as boolean case trees,
`leaf_T6_40` … `leaf_T6c_216`), giving the obstruction `obs_T6/T6b/T6c` and
the upper bound `f404_T6*_bound` (v₂ ≤ v₂(a!) + 7). The witnesses
{a+1, a+3, a+4, a+6} (T6), {a+1, a+3, a+5, a+6} (T6b), {a+1, a+3, a+4, a+7}
(T6c) attain 1 + Σ P_j ≡ 0 (mod 128) but not (mod 256) (`wit_T6/T6b/T6c`),
so g ≥ 7 and f = v₂(a!) + 7 exactly (`f404_T6*_exact`).

*Proof sketch, T7/T7b (shared machinery).* The vanish profile of the
T7-family is v₂(a+2) = 3, v₂(a+4) = 1, v₂(a+6) = 2, v₂(a+8) = 1, v₂(a+10) = 4
— i.e. (a+2)%8, (a+4)%2, (a+6)%4, (a+8)%2, (a+10)%16 vanish — so
2^(3+1+2+1+4) = 2^11 = 2048 divides every P_j(a) with j ≥ 10 (`vanish_T7fam`).
The window is the NINE coins P_1..P_9 mod 2048, with 16 leaf residues per
family: a % 2048 ∈ {70, 198, …, 1990} (T7) and {118, 246, …, 2038} (T7b).
Each leaf has 2^9 = 512 sub-sums, ALL missing −1 mod 2048. The witness
{a+1, a+3, a+6, a+7, a+9} attains 1 + Σ P_j ≡ 0 (mod 1024) but not
(mod 2048) (`wit_T7/T7b`), so g ≥ 10 and f = v₂(a!) + 10 exactly
(`f404_T7*_exact`).

*The memory-safe leaf architecture (mc9/boundedForall).* A naive T7 leaf
proof by tactic case-splitting (32 residues × 2^9 coin choices = 32768
goals) OOM'd the sandbox. The kernel instead packs each 9-coin sub-sum into
ONE closed term: `memMask a B` is the 9-bit membership mask of the window
(bits j−1 set iff a+j ∈ B, provably < 512), `mc9 r n` reconstructs the
sub-sum Σ_j P_{r,j} · bit_j(n) from the mask n, and
`boundedForall (fun n => (1 + mc9 r n) % 2048 ≠ 0) 512 = true` is ONE
kernel-evaluated `decide` per leaf residue (`check_T7_70` … `check_T7b_2038`,
32 checks, each evaluating all 512 sub-sums). The bridge `bf_true` +
`memMask_lt` then instantiates the checked leaf at the actual mask of any
B. Result: the whole T7/T7b obstruction is 32 kernel decides, zero tactic
explosion — the sandbox-stressing 32×1024-goal bomb is gone.

*Engine receipts (kernel #eval, cross-checked by the battery):*
f(40,2)=45, f(168,2)=172, f(296,2)=300, f(424,2)=427 (T6);
f(56,2)=60, f(184,2)=187 (T6b); f(88,2)=92, f(216,2)=219 (T6c);
f(70,2)=77, f(198,2)=204, f(326,2)=332, f(454,2)=459 (T7);
f(118,2)=123, f(246,2)=250 (T7b).

## The classification data (engine-certified, verify_p2class.py — 287 checks)

* Full small-g table for a ≤ 200 (the deep run of the (a,2) classifier).
* **Deep survivors at 2²⁸** (g ≥ 28, BITS-LIMIT certified):
  a ∈ {2, 6, 14, 16, 18, 24, 30, 34, 38, 62, 64, 78, 94, 98, 102, 126, 142,
  146, 158, 162, 190, 194}.
* Bounded deep values: g(46,2)=27, g(86,2)=26, g(104,2)=23, g(110,2)=21,
  g(144,2)=18, g(174,2)=23, g(400,2)=14.
* Family uniformity verified: T2 to a=204, T3 to a=202, T4 to a=304, T5 to a=456
  (T5: {8, 72, 136, 200, 264, 328, 392, 456} all g=6, engine-certified BOUNDED);
  T6/T6b/T6c/T7/T7b to a<900 (7 members each, all g=7/7/7/10/10, BOUNDED),
  with the 14 exact true-integer witness sums (plain-loop v₂) and the 6+32
  obstruction leaves (2^7 sub-sums mod 256 / 2^9 sub-sums mod 2048) re-verified.
* Consistency with Lin: g(2,2) ≥ 28 ≪ 2⁵⁴.

## What remains open for #404

* sub-Q1 for p = 2: the deep survivors' exact g (astronomically deep obstruc-
  tions; f(2,2) ≤ 2⁵⁴ by Lin; the other survivors unbounded candidates).
* sub-Q1 for odd p: the scan shows deep survivors everywhere (e.g. g(1,3),
  g(4,3), g(7,3), g(9,3), g(10,3), g(12,3) all ≥ 19 at 3¹⁹) — no uniform
  obstruction families found at scan depth.
* sub-Q3 (the infinite chain): open; no (a,p) with g = ∞ is known or refuted.

## Files

* `ObstructionFamilies.lean` — the kernel (3338 lines, 0 errors, 0 sorry;
  axioms [propext, Quot.sound] (T2/T3), [propext, Classical.choice,
  Quot.sound] (T4/T5/T6/T6b/T6c/T7/T7b)).
* `verify_p2class.py` — the battery (T6/T6b/T6c/T7/T7b checks added;
  ALL 287 PASSED).
* `DERIVATION.tex` — the LaTeX exposition (problem → proof).
