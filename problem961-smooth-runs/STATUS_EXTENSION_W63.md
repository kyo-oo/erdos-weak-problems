# STATUS_EXTENSION_W63 — THE 17-TIER AND THE 19-TIER: Erdős #961 frontier
# extended, f(17) = f(18) = 6 and f(19) = f(20) = f(21) = f(22) = 6

**S063 W63 volley, task W63-C1r (resumed from the salvage pack — the predecessor's
killing blow was an adapter timeout; its completed probe `probe_k17_fund.py`/
`probe_k17_fund.json` (the mod-M filtered CF over all 127 equations, log
`probe_k17_v3.log`: "ALL 127 fundamentals done… alive (Y1 17-smooth): 88 ; dead: 39")
is now the (A1) cross-implementation receipt of the 17-tier engine).** Engines:
`stormer961_k17.py` (output `stormer961_k17_output.txt`, ALL GREEN, 5.9s) with the
companion brute-minimality job `brute_k17_heavy.py` (log
`logs/brute_k17_heavy.log`, GREEN, 152,418,404 checks, 56s); and — the second
frontier row of the same wave — `stormer961_k19.py` (output
`stormer961_k19_output.txt`, ALL GREEN, 16.5s) with its companion
`brute_k19_heavy.py` (log `logs/brute_k19_heavy.log`, GREEN, 691,764,617 checks,
364s).

## THE NEW CERTIFIED THEOREMS (complete, unconditional)

$$f(17)=f(18)=6 \qquad\text{and}\qquad f(19)=f(20)=f(21)=f(22)=6 .$$

The certified frontier of #961 now reads
$$f(2)=2,\quad f(3)=f(4)=3,\quad f(k)=4\ (5\le k\le 12),\quad f(k)=6\ (13\le k\le 22).$$

*Proof architecture (the campaign's generic Størmer–Pell certification, T8 of
COMPLETE_PROOF.md, executed at the 7-prime and 8-prime tiers).* For every
k ∈ {17,18} the primes ≤ k are exactly S₇ = {2,3,5,7,11,13,17} (18 = 2·3²
adds no new prime); for every k ∈ {19,20,21,22} the primes ≤ k are exactly
S₈ = S₇ ∪ {19} (20 = 2²·5, 21 = 3·7, 22 = 2·11 add no new prime); so
k-smooth is 17-smooth resp. 19-smooth on each block, and by the window law
(L0): f(k) = 1 + max{L : L consecutive k-smooth integers all > k}.

**The complete Størmer–Pell census at S = {2,3,5,7,11,13,17} (the new T2-tier
theorem).** The consecutive 17-smooth pairs (x, x+1), x ≥ 1, are **exactly 108**;
the largest is **(336140, 336141)** (x = 2²·5·7⁵, x+1 = 3²·13³·17,
sf(x(x+1)) = 7735 = 5·7·13·17, b = 3822 = 2·3·7²·13; machine-checked). The 68
W62 13-tier pairs appear
**verbatim** (full-list equality by k-smooth filtering); the **40 new pairs**
(all involving the prime 17 on at least one side): x = 16, 17, 33, 34, 50, 51,
84, 119, 135, 153, 169, 220, 255, 272, 288, 374, 441, 560, 594, 714, 832, 935,
1088, 1155, 1224, 1274, 1700, 2057, 2430, 2499, 2600, 4913, 5831, 12375, 14399,
28560, 31212, 37179, 194480, 336140. Every component machine-certified:

- **(A) The 127 Pell equations.** For each squarefree S-unit a (2⁷−1 = 127
  subset products): fundamental (X1, Y1) of X²−aY² = 1 by exact integer CF of √a;
  X1²−aY1² = 1 checked direct; convergent denominators checked non-decreasing
  in-loop, every pre-hit convergent checked p²−aq² ≠ 1 — the first +1
  convergent is value-least (Legendre: |X/Y−√a| < 1/(2Y²)). Sanity anchors
  asserted: (2)→(3,2), (3)→(2,1), (5)→(9,4), (6)→(5,2), (7)→(8,3),
  (13)→(649,180), (17)→(33,8), (5005)→(44268809311,625742712). Largest
  fundamentals: X1 = 803170174072265, Y1 = 22199221738044 (a = 1309).
  - **(A1) CROSS-IMPLEMENTATION:** all 127 fundamentals EQUAL the W63 salvage
    probe (mod-M filtered CF, M = 2⁶¹−1 prime — a true solution always passes
    the congruence filter, so no hit is ever skipped; false mod-hits are
    exactly checked): `probe_k17_fund.json`, 127/127 EQUAL.
  - **(A2) THE P-TH-POWER DESCENT CERTIFICATE (new W63 law — a COMPLETE proof
    of fundamentality, independent of CF/Legendre, valid at every Y1 size).**
    Positive solutions of X²−aY²=1 are the norm-1 units u = X+Y√a > 1; by the
    campaign law L3 (descent on the well-ordered Y-index; u/ε_min^n lands in
    [1, ε_min) with norm 1, forcing coefficient v = 0) the solutions are
    EXACTLY ε_min^k (k ≥ 1); our (X1,Y1) is fundamental iff k = 1. If k ≥ 2,
    a prime p | k with p ≤ k ≤ log_{2+√3}(ε) (ε_min ≥ 2+√3: Y = 1 forces
    X² = a+1 squarefree a = X²−1 with least X = 2 at a = 3; Y ≥ 2 forces
    X ≥ 3, ε ≥ 3+2√2) would exhibit δ = ε_min^{k/p}, a norm-1 unit > 1 with
    δ^p = ε. The machine search: for every prime p ≤ P_max (+3 margin), the
    real root r = ε^{1/p} (mpmath, 130 digits) nominates the ONLY candidate
    δ = X+Y√a (δ+δ⁻¹ = 2X, δ−δ⁻¹ = 2Y√a); EXACT integer verification:
    X ≥ 2, Y ≥ 1, X²−aY² = **+1** (norm −1 roots such as 1+√2 at a = 2 do
    NOT decompose the norm-1 chain — rejected), and Brahmagupta binary
    powering δ^p = (X1,Y1) exactly. No prime admits such δ ⇒ k = 1 ⇒
    (X1,Y1) IS the fundamental. **127 equations certified, 558 prime-exponent
    searches** — this covers the five monster rows whose Y1 (up to 2.2·10¹³)
    lies beyond any conceivable brute scan: a = 1309 (Y1 = 22199221738044),
    3094 (98876026314), 36465 (17987356140), 85085 (17947617300),
    2431 (3836541735).
  - **(A3) BRUTE minimality** (independent of CF/Legendre AND of the p-power
    law): for every 1 ≤ Y' < Y1, aY'²+1 is not a square —
    **2,835,600 checks in-engine** (the 117 rows with Y1 ≤ 10⁶) **+
    152,418,404 checks in the W63 companion job** `logs/brute_k17_heavy.log`
    (the four feasible heavy rows: a = 17017 Y1 = 2373732, a = 34034
    Y1 = 13786506, a = 1105 Y1 = 48828432, a = 13090 Y1 = 87429738) **+ the
    W62 receipt** `logs/brute5005.log` (a = 5005, Y1 = 625742712:
    625,742,711 checks) — **122 of 127 equations brute-certified minimal;
    the 5 monster rows carry the complete (A2) proof.**
- **(B) The prune.** 39 equations die (Y1 not 17-smooth), each with the kill
  receipt (the prime > 17 dividing Y1): a=85 (41), 130 (19), 187 (41),
  286 (113), 374 (29), 385 (37), 429 (73), 561 (31), 595 (23), 715 (23),
  1001 (83), 1105 (857), 1309 (19), 1365 (19), 1870 (47), 2002 (53),
  2145 (19), 2210 (47), 2431 (1031), 3094 (3931), 3315 (31), 4862 (59),
  5005 (557), 6545 (23), 6630 (19), 7293 (71), 7854 (53), 13090 (613),
  14586 (211), 15470 (37), 17017 (31), 23205 (19), 34034 (31), 36465 (29),
  46410 (29), 51051 (47), 85085 (1823), 102102 (103), 255255 (19).
  **88 survive.**
- **(C) Lucas valuation laws.** U₀=0, U₁=1, U_{n+2}=2X1·U_{n+1}−U_n;
  Y_n = Y1·U_n asserted per n. Entry points z_p for odd p ≤ 17 satisfy
  z_p ≤ p+1 ≤ 18 (asserted); the valuation law
  v_p(U_n) = v_p(U_{z_p}) + v_p(n/z_p) on z_p | n, and p ∤ U_n otherwise,
  instance-verified over the whole used range n = 2..N_a for every survivor
  and every p ∈ {3,5,7,11,13,17}; parity laws (X_{2m} odd; v₂(X_odd) = v₂(X1);
  v₂(U_n) = v₂(n) + [n even]·v₂(X1)) instance-verified over the same range.
- **(D) The size bound (termination).** C_a = log₂Y1 + v₂(X1) + Σ_{p odd ≤ 17}
  B_{a,p}·log₂p with B_{a,p} = max_{1≤m≤18} v_p(U_m); if Y_n is 17-smooth then
  log₂Y_n ≤ C_a + 2log₂n (instance-checked whenever Y_n is 17-smooth), while
  log₂Y_n ≥ n·log₂α − log₂(3√a), α = X1+Y1√a ≥ 2+√3 (asserted); g(n) =
  n·log₂α − 2log₂n asserted strictly increasing over the used range.
  Per-a caps N_a ∈ [8, 23] (largest N_a = 23 at a = 3). The census loop
  n = 1..N_a only — FINITE.
- **(E) The census.** For surviving a, n = 1..N_a (gmpy2 mpz powers): keep
  X_n odd, Y_n even, x = (X_n−1)/2 with x, x+1 both 17-smooth. Completeness:
  every consecutive 17-smooth pair has a = sf(x(x+1)) among the 127, and
  (2x+1)² − a(2b)² = 1, hence = (X_n,Y_n) for a unique n ≤ N_a (Størmer's
  law, L1/L3 of COMPLETE_PROOF.md). **Exactly 108 pairs** (identity asserts
  Xn²−aYn² = 1, Xn = 2x+1, x(x+1) = a·b², smoothness of x, x+1, b, and the
  dictionary assert a = sf(x(x+1)) per pair; checkpoint receipt
  `census_k17.json`).

## THE f(k) ROWS (dual: witness + exclusion)

- **Witness law (lower bound).** The run (24, 25, 26, 27, 28) =
  (2³·3, 5², 2·13, 3³, 2²·7) — all 17-smooth, all > 18 — is a 5-run of
  k-smooth integers entirely above k for both k = 17, 18. Hence f(k) ≥ 6.
- **Exclusion law (upper bound).** For k ∈ {17, 18}: NO census pair x > k has
  x, x+1, …, x+5 all 17-smooth (machine scan of all 108 pairs). A 6-run above
  k would contain the census pair (m, m+1) with m > k — none exists. Hence
  f(k) ≤ 6.
- **f(k) = 1 + L(k)**, L(k) = max over maximal runs of the suffix above k
  (elements > k form a suffix; machine: L(17) = L(18) = 5 — three distinct
  5-runs exist above 18: (24..28), (32..36), (48..52)).

**Maximal-run decomposition of the 17-smooth integers (the new T3-tier
theorem):** (1, …, 18) [len 18 — 17 and 18 join the W62 initial run], then
(20,21,22), (24,25,26,27,28) [5], **(32,33,34,35,36) [5 — NEW:
(2⁵, 3·11, 2·17, 5·7, 2²·3²)]**, **(48,49,50,51,52) [5 — NEW: the W62
(48,49,50) extended by 51 = 3·17 and 52 = 2²·13]**, (54,55,56),
(63,64,65,66) [4], (98,99,100), **(119,120,121) [NEW: (7·17, 2³·3·5, 11²)]**,
**(168,169,170) [NEW]**, (350,351,352), **(440,441,442) [NEW]**; all other
runs have length ≤ 2. **No 6-run of 17-smooth integers exists above 18**
(indeed above 17). The initial run (1..18) has length 18 = the global maximum
(any 19 consecutive integers contain a multiple of the prime 19 — the
nonemptiness window law).

## CALIBRATION LAW (the engine re-derives the certified tip)

- All **40 certified 11-smooth pairs** (K25) and all **68 certified 13-smooth
  pairs** (W62) appear VERBATIM — full-list equality by k-smooth filtering
  (asserted against the embedded K25/W62 constants).
- f(2) = 2, f(3) = f(4) = 3, f(5..12) = 4, f(13..16) = 6: re-derived from
  THIS census by k-smooth filtering of the pairs — asserted equal to the
  certified table [2, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 6, 6]. GREEN.

## DUAL CROSS-CHECK (independent of Pell)

Brute enumeration of **all 2,750,000 17-smooth numbers ≤ 10¹⁸** (7-deep nested
smooth generation, sorted): consecutive pairs = **exactly the 108 census
pairs** (EQUAL: True, asserted — the largest census pair 336140 ≪ 10¹⁸, so
the brute covers the FULL census range); the brute no-6-run check for
k = 17, 18 below 10¹⁸: CLEAN; the brute maximal-run decomposition equals the
census decomposition; the brute L recount (5 for both k) equals the Pell L.
The completeness beyond 10¹⁸ is the Pell architecture (D) — the census is
global, the brute is the independent dual.

## Receipts (machine counts)

| component | count |
|---|---|
| Pell equations solved + Pell-identity checks | 127 |
| (A1) cross-implementation agreement (salvage probe) | 127/127 |
| (A2) p-th-power descent certificates (prime-exponent searches) | 127 eq / 558 |
| (A3) brute minimality checks (in-engine, Y1 ≤ 10⁶) | 2,835,600 |
| (A3) brute minimality checks (companion, 4 heavy rows) | 152,418,404 |
| (A3) brute minimality checks (a=5005, W62 receipt) | 625,742,711 |
| dead-equation kill receipts (prime > 17 in Y1) | 39 |
| survivors: Lucas/valuation/parity instances | 88 × (n = 2..N_a) × 6 primes |
| census pairs certified (Pell identity + smoothness + x(x+1)=ab² + dictionary) | 108 |
| exclusion scans (no 6-run above k, k = 17, 18) | 2 × 108 pairs |
| calibration: old-pair containment + f(2..16) re-derivation | 40 + 68 + 15 rows |
| brute dual: 17-smooth enumerated ≤ 10¹⁸ | 2,750,000 |
| brute pairs equality + no-6-run + run decomposition + L recount | 108 / 2 / 12 runs / 2 |

## Honest scope

Each new value is a certified exact value of f at the stated k — "the certified
frontier extended to k = 22" (six consecutive new rows in one wave). The
general-k law (Erdős's asymptotic f(k) < 3k/log k, conjectured (log k)^{O(1)})
remains OPEN and is not claimed. The next tier (k = 23..28, prime set
{2,3,5,7,11,13,17,19,23} — 2⁹−1 = 511 Pell equations) is the next fixed prime
set the same architecture closes; the W63 (A2) p-th-power descent certificate
is the law that keeps every monster-Y1 row (the 19-tier already carries
Y1 = 8.7·10³¹ at a = 46189) certifiable without any brute scan.

---

# PART II — THE 19-TIER: f(19) = f(20) = f(21) = f(22) = 6

Engine `stormer961_k19.py` (ALL GREEN, 16.5s) — the 8-prime tier
S = {2,3,5,7,11,13,17,19}, 255 squarefree S-units, SODD = {3,5,7,11,13,17,19},
ZMAX = 20 (z_p ≤ p+1 ≤ 20). Identical architecture to Part I; the deltas:

## The complete Størmer–Pell census at S = {2,3,5,7,11,13,17,19}

The consecutive 19-smooth pairs (x, x+1), x ≥ 1, are **exactly 167**; the
largest is **(11859210, 11859211)** (x = 2·3⁴·5·11⁴, x+1 = 7·13·19⁴,
sf(x(x+1)) = 910 = 2·5·7·13, b = 393129 = 3²·11²·19², n = 3; machine-checked).
The 108 W63 17-tier pairs appear **verbatim** (full-list equality by k-smooth
filtering, asserted against the receipt `census_k17.json`); the **59 new pairs**
(all involving the prime 19 on at least one side): x = 18, 19, 38, 56, 75, 76,
95, 132, 152, 170, 189, 208, 209, 285, 323, 342, 360, 399, 455, 475, 494,
512, 968, 1215, 1330, 1444, 1520, 1539, 1728, 2375, 2431, 2925, 3135, 3249,
4199, 5775, 5928, 5984, 6174, 6859, 10240, 10829, 12635, 13376, 14079, 14364,
23408, 27455, 28899, 43680, 89375, 104975, 165375, 228095, 601425, 633555,
709631, 5909760, 11859210.

- **(A) The 255 Pell equations.** Exact CF with the in-loop certificates
  (non-decreasing denominators, every pre-hit convergent exactly checked);
  anchors (2)→(3,2), (3)→(2,1), (5)→(9,4), (6)→(5,2), (7)→(8,3),
  (13)→(649,180), (17)→(33,8), **(19)→(170,39)**, (5005)→(44268809311,
  625742712). Largest fundamentals: **X1 with 35 digits, Y1 =
  86758237470381438680540739974304 (32 digits) at a = 46189**.
  - **(A1) CROSS-IMPLEMENTATION:** a second, structurally different CF run —
    the mod-M filtered CF (M = 2⁶¹−1, the salvage-probe law) — **255/255
    EQUAL**.
  - **(A2) THE P-TH-POWER DESCENT CERTIFICATE (the W63 law): 255 equations
    certified fundamental, 1398 prime-exponent searches** — including the
    monster rows beyond any brute scan: a = 46189 (Y1 = 8.7·10³¹), 461890
    (4.8·10²⁶), 3233230 (2.2·10²⁷), 58786 (3.0·10²⁰), 9699690
    (2.2·10¹⁶), 3553 (2.2·10¹⁶), 969969 (1.2·10¹⁶), … This is the tier where
    the new law became LOAD-BEARING: the W62-style brute-only certification
    would have been impossible.
  - **(A3) BRUTE minimality:** 5,244,374 checks in-engine (the 189 rows with
    Y1 ≤ 10⁶) **+ 691,764,617 checks in the W63 companion job**
    `logs/brute_k19_heavy.log` (the 26 rows with 10⁶ < Y1 ≤ 10⁸) — **215 of 255
    equations brute-certified minimal; the 40 monster rows (Y1 up to 8.7·10³¹)
    carry the complete (A2) proof.**
- **(B) The prune.** 112 equations die (Y1 not 19-smooth), each with the kill
  receipt (the prime > 19 dividing Y1; full list in `stormer961_k19_output.txt`).
  **143 survive.**
- **(C) Lucas/valuation/parity laws** — instance-verified over n = 2..N_a for
  all 143 survivors × 7 odd primes; **(D) size bound** with
  C_a = log₂Y1 + v₂(X1) + Σ_{p odd ≤ 19} B_{a,p} log₂p, N_a ∈ [8, 26];
  **(E) the census** with per-pair identity + dictionary asserts
  (checkpoint receipt `census_k19.json`).

## THE f(k) ROWS k = 19..22 (dual: witness + exclusion)

- **Witness.** (24,25,26,27,28) — all 19-smooth, all > 22 — gives f(k) ≥ 6 for
  all four k. **Exclusion.** No census pair x > k has x, …, x+5 all 19-smooth
  (machine scan of all 167 pairs, k = 19..22) — a 6-run above k would contain
  a census pair (m, m+1) with m > k. Hence **f(19) = f(20) = f(21) = f(22) = 6**
  (machine: L = 5 for all four — the three 5-runs (24..28), (32..36), (48..52)
  all sit above 22).

**Maximal-run decomposition of the 19-smooth integers:** (1, …, 22) [len 22 —
19..22 join; any 23 consecutive integers contain a multiple of the prime 23,
so 22 is the global maximum], then (20,21,22) merges away; the 5-runs (24..28),
(32,33,34,35,36), (48,49,50,51,52); **NEW 4-runs** (54,55,56,57) [57 = 3·19
extends the W62 run], (75,76,77,78) [75 = 3·5², 76 = 2²·19, 77 = 7·11,
78 = 2·3·13], (63,64,65,66), (168,169,170,171) [171 = 3²·19 extends the W63
run]; **NEW 3-runs** (38,39,40), (98,99,100), (119,120,121), (152,153,154),
(208,209,210), (323,324,325), (350,351,352), (440,441,442), (2430,2431,2432)
[2431 = 11·13·17, 2432 = 2⁷·19]; all other runs have length ≤ 2. **No 6-run
of 19-smooth integers exists above 22** (indeed above 19).

## CALIBRATION + DUAL CROSS-CHECK (19-tier)

- The 40 K25 / 68 W62 / 108 W63 pairs appear VERBATIM (full-list equality by
  k-smooth filtering; the 108 x-values loaded from the receipt
  `census_k17.json`). f(2..18) re-derived: [2, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4,
  6, 6, 6, 6, 6, 6] — GREEN.
- Brute enumeration of **all 7,039,193 19-smooth numbers ≤ 10¹⁸** (8-deep
  nested smooth generation): consecutive pairs = **exactly the 167 census
  pairs** (EQUAL: True — the largest census pair 11859210 ≪ 10¹⁸, so the brute
  covers the FULL census range); brute no-6-run checks for k = 19..22 below
  10¹⁸: CLEAN; brute maximal-run decomposition EQUALS the census decomposition;
  brute L recount (5 for all four k) equals the Pell L — GREEN ×4.

## Receipts (machine counts, 19-tier)

| component | count |
|---|---|
| Pell equations solved + Pell-identity checks | 255 |
| (A1) cross-implementation agreement (mod-M filtered CF) | 255/255 |
| (A2) p-th-power descent certificates (prime-exponent searches) | 255 eq / 1,398 |
| (A3) brute minimality checks (in-engine, Y1 ≤ 10⁶) | 5,244,374 |
| (A3) brute minimality checks (companion, 26 heavy rows) | 691,764,617 |
| (A3) monster rows certified by the (A2) complete proof (Y1 > 10⁸) | 40 |
| dead-equation kill receipts (prime > 19 in Y1) | 112 |
| survivors: Lucas/valuation/parity instances | 143 × (n = 2..N_a) × 7 primes |
| census pairs certified (identity + smoothness + x(x+1)=ab² + dictionary) | 167 |
| exclusion scans (no 6-run above k, k = 19..22) | 4 × 167 pairs |
| calibration: old-pair containment (11/13/17-tiers) + f(2..18) | 40 + 68 + 108 + 17 rows |
| brute dual: 19-smooth enumerated ≤ 10¹⁸ | 7,039,193 |
| brute pairs equality + no-6-run + decomposition + L recount | 167 / 4 / 17 runs / 4 |
