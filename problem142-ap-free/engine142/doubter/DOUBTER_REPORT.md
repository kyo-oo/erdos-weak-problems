# W67-142D DOUBTER REPORT — Erdős #142 (r_k(N) AP-free), audit of killer claims C1–C5

Task ID: W67-142D. Lane: doubter/engine. Worktree: `/home/z/waves/w67-p142d`
(branch `w67-p142d`, base campaign `bcf7e9d`). The killer lane is `w67-p142k`
(not pushed at audit time — the MATH was audited, not their repo).

Frozen statement: "Let r_k(N) be the largest possible size of a subset of
{1,...,N} that does not contain any non-trivial k-term arithmetic progression.
Prove an asymptotic formula for r_k(N)."

Convention pinned (the kernel header must pin the same): non-trivial k-AP =
a, a+d, ..., a+(k−1)d with **d ≥ 1**. Under it r_2(N)=1 for N ≥ 2 (any two
distinct elements are a 2-AP); under the alternative "non-trivial means k ≥ 3"
convention the r_2 claim is void.

## Verdicts (all CERTIFIED, dual/triple methods, exact integer arithmetic)

| Claim | Statement | Verdict | Method |
|---|---|---|---|
| C1 | ternary-digit-{0,1} set T is 3-AP-free | **CERTIFIED** | triple digitization (divmod / digit-vector product / gmpy2.digits) + dual pair-scan, k ≤ 8 (3^8−1=6560, 32640 pairs, 0 violations) |
| C2 | r_3(3^k−1) ≥ 2^k−1 | **CERTIFIED** | exact B&B table; gaps 2, 4/3, 11/7 at k=1,2,3 |
| C3 | r_k(N) ≤ (k−1)⌊N/k⌋ + (N mod k) | **CERTIFIED** | dominates every exact value k=3 N≤30, k=4/5 N≤20, k=2 N≤30 |
| C4 | r_2(N) = 1 for N ≥ 2 | **CERTIFIED** | exact k=2 table (B&B+z3), d ≥ 1 convention |
| C5 | exact small r_3(N) | **CERTIFIED** | independent table below; engines A/B/C agree |

NO BREAK FOUND. The killer's five mathematical claims survive the audit.

## The certified exact r_3 table (N ≤ 30)

```
N : 1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30
r3: 1  2  2  3  4  4  4  4  5  5  6  6  7  8  8  8  8  8  8  9  9  9  9 10 10 11 11 11 11 12
```
Witness sets for every N in `r3_exact_table.json`. Engine A = branch-and-bound
DFS with AP-completion propagation + exact-suffix bounds (translation
invariance); Engine B = z3 SAT@r + UNSAT@(r+1) certificates; Engine C =
exhaustive 2^N brute force N ≤ 12 (100% agreement); AP census itself dual-
checked ((a,d)-driven vs endpoint-driven). Witnesses independently re-validated.

**INTEL — printed-reference corruption detected:** the OEIS-printed reference
string supplied in MISSION.md ("1,2,2,3,4,4,4,4,4,5,5,6,6,6,6,7,8,8,8,8,9...")
DEVIATES from the certified truth at **N = 9, 11, 13, 14, 15, 16, 20**:
printed 4,5,6,6,6,7,8 vs certified **5,6,7,8,8,8,9** (witnesses, e.g.
N=9: {1,2,4,8,9}; N=14: {1,2,4,5,10,11,13,14}; N=20: {1,2,6,7,9,14,15,18,20}).
Per mission law our own dual-engine computation is the truth. Any kernel or
document that hard-codes the printed string at those positions is WRONG.

## Frontier tables

- r_4(N ≤ 20): 1,2,3,3,4,5,5,6,7,8,8,8,9,9,10,10,11,11,12,12. Block bound
  (k=4) margin at N=20: 15 − 12 = 3.
- r_5(N ≤ 20): 1,2,3,4,4,5,6,7,8,8,9,10,11,12,12,13,14,15,16,16. The block
  bound (k=5) is TIGHT at every N ≤ 20 (r_5(N) = 4⌊N/5⌋ + N mod 5); witness
  at 20: {1,2,3,4,6,7,8,9,11,12,13,14,16,17,18,19}.
- Honest ratio r_3(N)·3/(2N) (exact fractions in the JSON): from 6/5 (> 1) at
  N=5 down to 3/5 at N=30 — small-N densities exceed the block-bound slope;
  the asymptotic density is o(1).

## Cantor-vs-true gap (certified scale, k ≤ 3)

| k | N = 3^k−1 | Cantor 2^k−1 | true r_3(N) | ratio |
|---|---|---|---|---|
| 1 | 2 | 1 | 2 | 2/1 |
| 2 | 8 | 3 | 4 | 4/3 |
| 3 | 26 | 7 | 11 | 11/7 ≈ 1.571 |

The certified Cantor lower bound sits a factor ~1.3–1.6 below truth at the
certified scale (r_3(26)=11 vs 7).

## Complement (niche-maximality) intel for T_8

Base B = T_8 \ {0} (255 elements) in [1,6560]: 6297 of 6305 non-members are
blocked by a 3-AP through B (dual-method agreement, identical blocked sets and
identical minimal d; largest minimal-d = 3279 at u=6559, blocked by
(1, 3280, 6559)). The 8 unblockable non-members
{4374, 5832, 6318, 6480, 6534, 6552, 6558, 6560} all need the element 0 for
their blocking APs — T_8 \ {0} is NOT maximal in [1,6560], while T_8 itself
is maximal in its niche. Intel only; the C1 kill-claim (T is 3-AP-free) is
unaffected.

## Artifacts (this directory)

- `mirror_battery.py` — the end-to-end battery (re-runs C1–C5, exit nonzero on
  any failure; prints `E142_DOUBTER_BATTERY_GREEN` iff all green).
- `mirror_battery_log.txt` — full battery output log.
- `r3_exact_table.json` — r_3/r_4/r_5/r_2 tables with witnesses, block-bound
  margins, exact ratios, Cantor gap, OEIS-printed diffs, engine agreement.
- `cantor_cert.txt` — dual-method T_k certification k ≤ 8 + complement scan +
  gap analysis.

CI: job `kernel-142d` in `.github/workflows/kills.yml` (branch `w67-p142d`)
runs the battery end-to-end on every push touching `problem142-ap-free/**`.
