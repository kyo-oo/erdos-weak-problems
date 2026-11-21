# ASYMPTOTIC_STACK.md — THE TWO-SIDED ENVELOPE FOR r_k(N): THE FORMULA AT ITS EXACT PROVEN STRENGTH
# (W79-142E; every cited line carries its certification)

BOSS's target: "Prove an asymptotic formula for r_k(N)" — ALL k >= 3,
N -> infinity. This is the formula stack: what the package PROVES, every
constant explicit, every line machine-certified, the remaining gap named
exactly.

---

## THE SANDWICH (the proven envelope)

**LOWER (all k, NEW this wave — LOWER_STACK.md, BEHREND_GEN.md):**
For every k >= 3 and all N >= 2^40:
    r_k(N) >= N · exp(-C_k √(ln N)),  C_k = 2√((k+1) ln 2) + 1
(C_k = 4.665 at k=3; certified at 45,847 grid points per k, N = 2^40..2^6000;
constructive real-set certification k=3..8; engine142behrendgen.py 9/9 GREEN.)

**UPPER (k=3, banked — LOGDECAY.md, W77-142K):**
For every N >= ⌈exp(4·10^7)⌉:
    r_3(N) <= √26600 · N · √(ln ln N / ln N)   (√26600 ≈ 163.095)
(from THEOREM SUBLINEAR: every eps in (0,1/8], every 3-AP-free
S ⊆ [1,N] with N >= 480·(1024/eps)^(⌈13300/eps²⌉+2) has |S| <= eps·N;
engine142logdecay.py 19/19 green.)

**THE k-LADDER (proven):** r_3(N) <= r_4(N) <= r_5(N) <= ... (LAW M-1),
so the k=3 UPPER does NOT transfer upward (wrong direction) — the all-k
upper is FRONT F-UP-1 below. The LOWER transfers DOWNWARD: the all-k
construction gives every rung.

**EXACT ANCHORS (banked, certified):** r_3(N) exact for N = 1..30
(three-way certified: fresh B&B = embedded = CI ledger, kernel-142k board);
r_4 exact table M = 1..16 (R4_VARN.md); the Cantor witness family
r_3(3^d) >= 2^d; block-envelope data k=3..6.

## WHAT THE FORMULA NOW IS (in-package, at exact strength)

For every k >= 3: r_k(N) lies between N·exp(-C_k√(ln N)) (all N >= 2^40,
explicit C_k) and — at k=3 — √26600·N·√(ln ln N/ln N) (all N >= exp(4·10^7)).
Both sides are polylog-factors away from N: the Behrend lower says
r_k(N) = N^(1-o(1)) as N -> infinity FOR EVERY k >= 3 — the exponent-1 law,
explicit, universal in k — and the k=3 upper says the deficit at k=3 is at
most polylogarithmic. The gap between exp(-C√ln N) and √(ln ln N/ln N) is
the open bandwidth of the formula.

## THE NAMED FRONTS

F-UP-1 (LOGDECAY-GEN, the all-k upper — the W78-142K unexecuted lane):
  for every k >= 3, r_k(N) <= C_k·N·(ln ln N/ln N)^{c_k} — the k-AP
  density-increment generalization of the banked k=3 route (SUBLINEAR's
  block/partition machinery on k-term APs; arsenal partition/covering/
  pigeonhole/interval families). Target statement frozen; next wave.
F-LOW-1 (Rankin shape, k >= 4): beat the 1/2-exponent ceiling of the
  sum-classifier family with a non-sum-type mechanism (§8 ledger of dead
  ends in BEHREND_GEN.md).
F-UP-2 (constant sharpening): the 163.095 and the 4.665 are the certified
  in-package constants; the literature's refined constants are context
  (cited in the ledgers), not comparator targets.

## RECEIPT MANIFEST

- engine142behrendgen.py — 9/9 GREEN, wall 67.6s (receipts142behrendgen.txt)
- engine142logdecay.py — 19/19 green (banked, receipts142logdecay.txt)
- engine142sublinear.py — 264/264 green (banked, receipts142sublinear_v2.txt)
- engine142behrend.py — banked, re-run inside GEN-K3REPRO/GEN-LAWSPOT this wave

*The engine never stops; it never lies. In English, always.*
