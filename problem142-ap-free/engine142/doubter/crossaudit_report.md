# W68-142D Cross-Audit Report -- Erdos #142 (AP-free r_k(N))

**Doubter lane** (branch `w67-p142d` @ `5f031ed`) adversarially cross-audits the
**killer lane kernel** (branch `w67-p142k` @ `011cb3e`, `problem142-ap-free/Erdos142.lean`,
namespace `E142`) against the doubter's CI-certified exact tables
(kernel-142d CI run 43726649205: **success**, all 4 jobs green,
`BATTERY_VERDICT: GREEN`).

## Verdicts

| # | kernel claim | verdict |
|---|--------------|---------|
| K1_t3free | `Cantor ternary set 3-AP-free (x+z=2y => x=z)` | **CONFIRMED** |
| K2_cantor_lower | `r_3(3^k-1) >= 2^k-1, k=1..8` | **CONFIRMED** |
| K3_r3_exact_small | `r_3(N) N=1..8 = [1,2,2,3,4,4,4,4]` | **CONFIRMED** |
| K4_block_upper | `|S| <= (k-1)*floor(N/k)+N mod k; r3_upper k=3` | **CONFIRMED** |
| K5_k2_edge | `r_2(N)=1 for N>=2 (pinned d>=1)` | **CONFIRMED** |
| K6_r5_tight_third_method | `r_5(N)=block bound tight on N<=20 (greedy third method)` | **CONFIRMED** |

All checks below are NEW code paths (nothing imported from `mirror_battery.py`):
digit-tuple product generator, range-scan digit predicate, literal replicas of
Arsenal `noTernaryTwo` and the killer's `genT`/`genTp`, full `2^N` bitmask
exhaustive enumeration, fresh z3 encoding, left-to-right greedy construction,
explicit mod-5 drop construction.

## K3 -- r_3(N) fresh re-derivation (N <= 12)

Fresh exhaustive `2^N` enumeration + fresh z3 SAT/UNSAT dual both reproduce
`r_3(1..8) = 1,2,2,3,4,4,4,4` (kernel `E142.r3_exact_small`) and the certified
table through N=12: `1,2,2,3,4,4,4,4,5,5,6,6`.

## K4 -- r_3 tightness map (kernel `E142.r3_upper` = `2*floor(N/3) + N mod 3`)

| N | bound | true r_3(N) | slack | tight? |
|---|-------|-------------|-------|--------|
| 1 | 1 | 1 | 0 | TIGHT |
| 2 | 2 | 2 | 0 | TIGHT |
| 3 | 2 | 2 | 0 | TIGHT |
| 4 | 3 | 3 | 0 | TIGHT |
| 5 | 4 | 4 | 0 | TIGHT |
| 6 | 4 | 4 | 0 | TIGHT |
| 7 | 5 | 4 | 1 |  |
| 8 | 6 | 4 | 2 |  |
| 9 | 6 | 5 | 1 |  |
| 10 | 7 | 5 | 2 |  |
| 11 | 8 | 6 | 2 |  |
| 12 | 8 | 6 | 2 |  |
| 13 | 9 | 7 | 2 |  |
| 14 | 10 | 8 | 2 |  |
| 15 | 10 | 8 | 2 |  |
| 16 | 11 | 8 | 3 |  |
| 17 | 12 | 8 | 4 |  |
| 18 | 12 | 8 | 4 |  |
| 19 | 13 | 8 | 5 |  |
| 20 | 14 | 9 | 5 |  |
| 21 | 14 | 9 | 5 |  |
| 22 | 15 | 9 | 6 |  |
| 23 | 16 | 9 | 7 |  |
| 24 | 16 | 10 | 6 |  |
| 25 | 17 | 10 | 7 |  |
| 26 | 18 | 11 | 7 |  |
| 27 | 18 | 11 | 7 |  |
| 28 | 19 | 11 | 8 |  |
| 29 | 20 | 11 | 9 |  |
| 30 | 20 | 12 | 8 |  |

The block bound is TIGHT for r_3 only at N=1..6 (and it is a valid upper bound
everywhere on N<=30, slack growing to 8 at N=30). For r_4: tight at N=1..6, 8..10.
For r_5: tight at **every** N<=20 (slack 0 across the whole frontier) -- see K6.
For r_2 (k=2 pinned d>=1): tight at N=1,2 (bound = N mod 2 + floor(N/2)).

## K6 -- r_5(N) = block bound, tight on all N <= 20 (third method)

| N | bound 4*floor(N/5)+N mod 5 | greedy | mod-5 drop | certified r_5 |
|---|---------------------------|--------|-----------|---------------|
| 1 | 1 | 1 | 1 | 1 |
| 2 | 2 | 2 | 2 | 2 |
| 3 | 3 | 3 | 3 | 3 |
| 4 | 4 | 4 | 4 | 4 |
| 5 | 4 | 4 | 4 | 4 |
| 6 | 5 | 5 | 5 | 5 |
| 7 | 6 | 6 | 6 | 6 |
| 8 | 7 | 7 | 7 | 7 |
| 9 | 8 | 8 | 8 | 8 |
| 10 | 8 | 8 | 8 | 8 |
| 11 | 9 | 9 | 9 | 9 |
| 12 | 10 | 10 | 10 | 10 |
| 13 | 11 | 11 | 11 | 11 |
| 14 | 12 | 12 | 12 | 12 |
| 15 | 12 | 12 | 12 | 12 |
| 16 | 13 | 13 | 13 | 13 |
| 17 | 14 | 14 | 14 | 14 |
| 18 | 15 | 15 | 15 | 15 |
| 19 | 16 | 16 | 16 | 16 |
| 20 | 16 | 16 | 16 | 16 |

Greedy certificate sets (left-to-right, AP-check only, no mod-5 knowledge), the
explicit construction {n in [1,N] : n mod 5 != 0} (every 5-AP with d not
divisible by 5 hits exactly one multiple of 5, and d divisible by 5 needs
a+4d >= 21 > 20), and fresh z3 UNSAT@bound+1 certificates all agree: TIGHT.

## Killer-lane CI intel (observed 2026-11-15, frozen fact)

The killer kernel's OWN CI verdict at `011cb3e`: run **43736909745 = FAILURE**
(job `kernel-142k` red; `kernel-a/b/c` green). 73 compile errors in
`Erdos142.lean` (tactic `rfl` failures, type mismatches, unknown identifiers
such as `CardinalWorlds.two_pow_pos` and a stray `hp'`); Lean's error
recovery inserts `sorryAx`, so **7 of the 9 board theorems as-compiled
rest on `sorryAx`** -- only `E142.arsenal_bridge` lands clean. The source
contains no literal `sorry` (only the 'zero sorry' comment), but the
artifact is nonetheless NOT CI-certified. Consequence for this audit:
the kernel's mathematical claims are all CONFIRMED numerically below,
while the kernel's Lean proofs await the killer lane's own repair loop
(that lane owns its <=5 CI repair rounds; this lane does not touch it).

## Scope (honest)

* Numerical audits cover the finite windows: Cantor k<=8 (3^8=6561, full
  pairwise midpoint scans), r_3 N<=30, r_4/r_5 N<=20, r_2 N<=30, exhaustive
  2^N N<=12. The kernel's Lean proofs (unbounded t3free via mod-3 descent,
  the general block_upper window pigeonhole, etc.) are NOT currently
  CI-certified (see killer CI intel above) and are not re-proved here;
  this cross-audit certifies their mathematical CONTENT on the stated
  windows.
* The kernel `r3Is` convention (subsets of [1,N], d>=1) matches the doubter
  convention exactly; every disagreement would have been reported BROKEN.
* INTEL carried forward: the printed reference string corrupt at
  N=9,11,13,14,15,16,20 -- own computation is truth; the kernel values
  N=1..8 are clean of that corruption.
