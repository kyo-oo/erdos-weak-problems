# STATUS — THE 13-TIER: Erdős #961 frontier extended, f(13)=f(14)=f(15)=f(16)=6

**S063 W62 volley, task 1-c (the guaranteed-kill executor).** Engines:
`stormer961_k13.py` (output `stormer961_k13_output.txt`, ALL GREEN, 1.0s) and
the companion brute-minimality job `brute5005.py` (log `logs/brute5005.log`,
GREEN, 625,742,711 checks, 271s). Calibration law honored: the engine re-derives
the certified 5-tier inside itself (see (F) CALIBRATION below).

## THE NEW CERTIFIED THEOREM (complete, unconditional)

$$f(13)=f(14)=f(15)=f(16)=6 .$$

The certified frontier of #961 now reads
$$f(2)=2,\quad f(3)=f(4)=3,\quad f(k)=4\ (5\le k\le 12),\quad f(k)=6\ (13\le k\le 16).$$

*Proof architecture (the campaign's generic Størmer–Pell certification, T8 of
COMPLETE_PROOF.md, executed at the 6-prime tier).* For every k ∈ {13,14,15,16}
the primes ≤ k are exactly S = {2,3,5,7,11,13} (14 = 2·7, 15 = 3·5, 16 = 2⁴
add no new prime), so k-smooth = 13-smooth for all four k, and by the window
law (L0): f(k) = 1 + max{L : L consecutive 13-smooth integers all > k}.

**The complete Størmer–Pell census at S = {2,3,5,7,11,13} (the new T2-tier
theorem).** The consecutive 13-smooth pairs (x, x+1), x ≥ 1, are **exactly 68**;
the largest is (123200, 123201). Every component machine-certified:

- **(A) The 63 Pell equations.** For each squarefree S-unit a (2⁶−1 = 63 subset
  products): fundamental (X1, Y1) of X²−aY² = 1 by exact integer CF of √a;
  X1²−aY1² = 1 checked direct; convergent denominators checked non-decreasing
  in-loop, every pre-hit convergent checked p²−aq² ≠ 1 — the first +1
  convergent is value-least (Legendre: |X/Y−√a| < 1/(2Y²)). Sanity anchors
  asserted: (2)→(3,2), (3)→(2,1), (5)→(9,4), (6)→(5,2), (7)→(8,3),
  (13)→(649,180), (61)→(1766319049,226153980), (5005)→(44268809311,625742712).
  **Brute minimality** (independent of CF/Legendre): for every 1 ≤ Y' < Y1,
  aY'²+1 is not a square — 405,933 checks in-engine for the 62 equations with
  Y1 ≤ 10⁶, plus 625,742,711 checks for a = 5005 (Y1 = 625742712) in
  `logs/brute5005.log`. **All 63 equations brute-certified minimal.**
- **(B) The prune.** 10 equations die (Y1 not 13-smooth), each with the kill
  receipt (the prime > 13 dividing Y1): a=130 (19), 286 (113), 385 (37),
  429 (73), 715 (23), 1001 (83), 1365 (19), 2002 (53), 2145 (19), 5005 (557).
  **53 survive.**
- **(C) Lucas valuation laws.** U₀=0, U₁=1, U_{n+2}=2X1·U_{n+1}−U_n;
  Y_n = Y1·U_n asserted per n. Entry points z_p for odd p ≤ 13 satisfy
  z_p ≤ p+1 ≤ 14 (asserted); the valuation law
  v_p(U_n) = v_p(U_{z_p}) + v_p(n/z_p) on z_p | n, and p ∤ U_n otherwise,
  is instance-verified over the whole used range n = 2..N_a for every survivor
  and every p ∈ {3,5,7,11,13}; parity laws (X_{2m} odd; v₂(X_odd) = v₂(X1);
  v₂(U_n) = v₂(n) + [n even]·v₂(X1)) instance-verified over the same range.
- **(D) The size bound (termination).** C_a = log₂Y1 + v₂(X1) + Σ_{p odd ≤ 13}
  B_{a,p}·log₂p with B_{a,p} = max_{1≤m≤14} v_p(U_m); if Y_n is 13-smooth then
  log₂Y_n ≤ C_a + 2log₂n (instance-checked whenever Y_n is 13-smooth), while
  log₂Y_n ≥ n·log₂α − log₂(3√a), α = X1+Y1√a ≥ 2+√3 (asserted); g(n) =
  n·log₂α − 2log₂n asserted strictly increasing over the used range
  (log₂α ≥ 1.90 > 2·log₂(3/2) = 1.17). Per-a caps N_a ∈ [8, 19]
  (largest N_a = 19 at a = 3). The census loop n = 1..N_a only — FINITE.
- **(E) The census.** For surviving a, n = 1..N_a (gmpy2 mpz powers): keep
  X_n odd, Y_n even, x = (X_n−1)/2 with x, x+1 both 13-smooth. Completeness:
  every consecutive 13-smooth pair has a = sf(x(x+1)) among the 63, and
  (2x+1)² − a(2b)² = 1, hence = (X_n, Y_n) for a unique n ≤ N_a (Størmer's
  law, L1/L3 of COMPLETE_PROOF.md). **Exactly 68 pairs** (identity asserts
  Xn²−aYn² = 1, Xn = 2x+1, x(x+1) = a·b², smoothness of x, x+1, b per pair).

## THE f(k) ROWS (dual: witness + exclusion)

- **Witness law (lower bound).** The run (24, 25, 26, 27, 28) =
  (2³·3, 5², 2·13, 3³, 2²·7) — all 13-smooth, all > 16 — is a 5-run of
  k-smooth integers entirely above k for every k ≤ 16. Hence f(k) ≥ 6 for
  k = 13, 14, 15, 16.
- **Exclusion law (upper bound).** For every k ∈ {13..16}: NO census pair
  x > k has x, x+1, x+2, x+3, x+4, x+5 all 13-smooth (machine scan of all
  68 pairs). A 6-run above k would contain the census pair (m, m+1) with
  m > k — none exists. Hence f(k) ≤ 6.
- **f(k) = 1 + L(k)**, L(k) = max over maximal runs of the suffix above k
  (elements > k of a run form a suffix; machine: L(13)=L(14)=L(15)=L(16)=5).

**Maximal-run decomposition of the 13-smooth integers (the new T3-tier
theorem):** (1, …, 16) [len 16], then (20,21,22), (24,25,26,27,28) [len 5 —
the frontier witness], (48,49,50), (54,55,56), (63,64,65,66) [len 4],
(98,99,100), (350,351,352) [len 3]; all other runs have length ≤ 2.
**No 6-run of 13-smooth integers exists above 16** (indeed above 13).

## CALIBRATION LAW (the engine re-derives the certified tip)

- All **40 certified 11-smooth pairs** of the 5-tier census (stormer961.py)
  appear verbatim among the 68 (11-smooth ⊂ 13-smooth; asserted).
- f(2) = 2 (no 2-run of 2-smooth above 2 — pairs filter empty — and the
  singleton 2k is always k-smooth and > k), f(3) = f(4) = 3, f(5..12) = 4:
  re-derived from THIS census by k-smooth filtering of the pairs — asserted
  equal to the certified table [2, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4]. GREEN.

## DUAL CROSS-CHECK (independent of Pell)

Brute enumeration of **all 958,460 13-smooth numbers ≤ 10¹⁸** (6-deep nested
smooth generation, sorted): consecutive pairs = **exactly the 68 census
pairs** (EQUAL: True, asserted); the brute no-6-run check for k = 13..16
below 10¹⁸: CLEAN; the brute maximal-run decomposition equals the census
decomposition. The completeness beyond 10¹⁸ is the Pell architecture (D) —
the census is global, the brute is the independent dual below 10¹⁸.

## Receipts (machine counts)

| component | count |
|---|---|
| Pell equations solved + Pell-identity checks | 63 |
| brute minimality checks (in-engine, Y1 ≤ 10⁶) | 405,933 |
| brute minimality checks (a=5005, companion job) | 625,742,711 |
| dead-equation kill receipts (prime > 13 in Y1) | 10 |
| survivors: Lucas/valuation/parity instances | 53 × (n = 2..N_a) × 5 primes |
| census pairs certified (Pell identity + smoothness + x(x+1)=ab²) | 68 |
| exclusion scans (no 6-run above k, k = 13..16) | 4 × 68 pairs |
| calibration: old-pair containment + f(2..12) re-derivation | 40 + 11 rows |
| brute dual: 13-smooth enumerated ≤ 10¹⁸ | 958,460 |
| brute pairs equality + no-6-run + run decomposition | 68 / 4 / 8 runs |

## Honest scope

Each new value is a certified exact value of f at the stated k — "the
certified frontier extended to k = 16". The general-k law (Erdős's asymptotic
f(k) < 3k/log k, conjectured (log k)^{O(1)}) remains OPEN and is not claimed.
The next tier (k = 17..19, prime set {2,3,5,7,11,13,17} then +19) is the next
fixed prime set the same architecture closes (2⁷−1 = 127 Pell equations; the
expected wall is the growing census cardinality and the brute-minimality cost
of any equation with a large 17-smooth Y1, both finite by T8).
