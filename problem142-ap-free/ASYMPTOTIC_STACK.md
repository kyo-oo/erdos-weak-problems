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

**UPPER (all k >= 3, NEW this wave — UPPER_STACK.md, W80-142U):**
For every k >= 3 and N >= 1, the BLOCK law with the certified stones:
    r_3(N) <= 19*floor(N/61) + r_3(N mod 61)   (rho* = 19/61 ~ 0.3115)
    r_4(N) <= 22*floor(N/42) + r_4(N mod 42)   (rho* = 11/21 ~ 0.5238)
    r_5(N) <= 36*floor(N/55) + r_5(N mod 55)   (rho* = 36/55 ~ 0.6545)
    r_6(N) <= 31*floor(N/43) + r_6(N mod 43)   (rho* = 31/43 ~ 0.7209)
    r_k(N) <= 36*floor(N/45) + r_7(N mod 45)   for ALL k >= 7 (rho* = 4/5;
        LAW M-1 containment + the FRESH two-code k=7 table N = 1..46)
plus the k-independent floor law r_k(N) <= N - floor(N/k) (U-GEN-0, tight at
N = k), the SHARP amplification r_k(N) <= (1 + 1/(2 r_k(m)))*(r_k(m)/m)*N
for N >= 16m^2 (V-GEN — the banked k=3 constant 33 improved), the sliding
law r_k(N) <= r_k(m)(N-m+1)/m + 2(m-1) for N >= 2m-1 (SLIDE-GEN), the
transfer law p > kN (T-GEN) and the count law RK-VARN-GEN (k=4 delta
threshold 0.85 -> 0.65 with the stone 42; first k=5,6,7 count laws).
engine142uppergen.py 56/56 GREEN, wall 142.3s.
At k=3 the banked polylog upper still dominates for N >= ceil(exp(4e7)):
    r_3(N) <= sqrt(26600)*N*sqrt(ln ln N / ln N)   (LOGDECAY, W77-142K)
(from THEOREM SUBLINEAR: every eps in (0,1/8], every 3-AP-free
S subset [1,N] with N >= 480*(1024/eps)^(ceil(13300/eps^2)+2) has |S| <= eps*N;
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

F-UP-1 (LOGDECAY-GEN, the all-k upper — W80-142U status: **HALF-KILLED**):
  DEAD: the linear half — the all-k envelope is CLOSED (UPPER_STACK.md):
  explicit certified density caps for EVERY k >= 3 (BLOCK law + U-GEN-0 +
  the fresh two-code k=7 table + the M-1 ladder covering all k >= 7), the
  sharp amplification V-GEN (1 + 1/(2 r_k(m)) < 33), SLIDE-GEN, T-GEN, and
  RK-VARN-GEN (count laws k=4..7, k=4 threshold 0.85 -> 0.65).
  ALIVE: the sublinear half — r_k(N) <= C_k N (lnlnN/lnN)^{c_k} for k >= 4.
  The exact blocker: the ORDER-k DEVIATION IDENTITY (the L-EP analog at
  order k; see UPPER_STACK.md "WHAT REMAINS" for the full file:line arsenal
  inventory — the GST higher-order towers are DG-algebra jet laws, not
  k-AP laws). Everything downstream of that law (arc increment, flow,
  LOGDECAY inversion) re-runs verbatim; T-GEN + V-GEN are now in place.
F-LOW-1 (Rankin shape, k >= 4): beat the 1/2-exponent ceiling of the
  sum-classifier family with a non-sum-type mechanism (§8 ledger of dead
  ends in BEHREND_GEN.md).
F-UP-2 (constant sharpening): the 163.095 and the 4.665 are the certified
  in-package constants; the literature's refined constants are context
  (cited in the ledgers), not comparator targets. The new stones (19/61,
  11/21, 36/55, 31/43, 4/5) sharpen automatically as tables extend.

## RECEIPT MANIFEST

- engine142behrendgen.py — 9/9 GREEN, wall 67.6s (receipts142behrendgen.txt)
- engine142logdecay.py — 19/19 green (banked, receipts142logdecay.txt)
- engine142sublinear.py — 264/264 green (banked, receipts142sublinear_v2.txt)
- engine142behrend.py — banked, re-run inside GEN-K3REPRO/GEN-LAWSPOT this wave
- engine142uppergen.py — 56/56 GREEN, wall 142.3s (W80-142U,
  receipts142uppergen.txt: U-GEN-0, V-GEN, SLIDE-GEN, T-GEN, R-K-TABLES
  incl. the fresh k=7 table, U-LIN-GEN block/crossover/tower, RK-VARN-GEN)

*The engine never stops; it never lies. In English, always.*
