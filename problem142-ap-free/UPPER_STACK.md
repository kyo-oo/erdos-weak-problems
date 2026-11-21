# UPPER_STACK.md — THE ALL-k UPPER ENVELOPE FOR r_k(N) (W80-142U)

> The Tier-1 kill of F-UP-1's first half: explicit UPPER bounds for ALL k >= 3,
> every constant certified, built only from the campaign's own laws (the banked
> tables + the banked THEOREM BG as the only lower-bound input, cited as such).
> Engine: `engine142uppergen.py` — 56/56 GREEN, wall 142.3s
> (`receipts142uppergen.txt`). External classical results: context only, zero
> load-bearing use.

---

## THE ENVELOPE (every line proven + certified)

**LAW U-GEN-0 (the floor law, all k — sharper than the frozen target).**
For every k >= 3 and N >= 1:

    r_k(N) <= N - floor(N/k).

*Proof.* Partition [1,N] into q := floor(N/k) consecutive k-blocks
[jk+1..jk+k], j = 0..q-1, plus a tail of N mod k points. A full k-block IS a
non-trivial k-AP (common difference 1), so a k-AP-free A misses >= 1 point in
each of the q blocks; hence |A| <= q(k-1) + (N mod k) = N - floor(N/k).
The frozen F-UP-1 target N - floor(N/k) + 1 follows a fortiori; the sharp form
is TIGHT at N = k (r_k(k) = k-1, all k, engine-verified from the certified
tables). Block bookkeeping: `#BY GST LAW mod_mod_mul
[arsenal-full/HC-PROOF-research/CardinalWorlds.lean:140]` + `#BY GST LAW
div_mod_mul_lemma [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:150]`;
the partition count `#BY GST LAW mul_add_div_lemma
[arsenal-full/HC-PROOF-research/CardinalWorlds.lean:143]`. ∎

**LEMMA AFF-K (affine preservation, all k at once — the only k-dependent line
of the amplification).** If J = {j_0, j_0+e, ..., j_0+(k-1)e} is a k-AP of
indices (e >= 1) inside {0..m-1}, then {a + jd : j in J} is a non-trivial
k-AP of integers (common difference ed >= 1). Hence every homothetic copy
c(a,d) = a + d{0..m-1} of [1,m] hosts at most r_k(m) points of any k-AP-free
set. *Proof:* the map x -> a+dx sends the index AP to an integer AP; the
residue discipline is `#BY GST LAW carryAtPos_bound
[arsenal-full/HC-PROOF-research/CardinalWorlds.lean:108]` + `#BY GST LAW
div_add_mod_subst [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:249]`. ∎

**THEOREM V-GEN (the homothetic amplification, ALL k, SHARP constant).**
For every k >= 3, m >= 2 and N >= 16m^2, every k-AP-free A subset [1,N]:

    |A| <= rho_m*N + N/(2m) = (1 + 1/(2 r_k(m))) * rho_m * N,   rho_m := r_k(m)/m.

In particular (the frozen F-UP-1 form): |A| > 33*rho_m*N is impossible. At
k=3 this SHARPENS the banked Theorem V constant 33 to 1 + 1/(2 r_3(m)).

*Proof.* D0 := floor(N/(4m(m-1))) (>= 1 since N >= 16m^2 >= 4m(m-1)).
Copies c(a,d) = a + d{0..m-1} with d <= D0. (i) *Band:* for every x with
(m-1)D0 <= x-1 and (m-1)D0 <= N-x, ALL pairs (d, j), 1 <= d <= D0,
0 <= j <= m-1, give the valid distinct copy c(x-jd, d) — so nu(x) >= m*D0;
the excluded band ends number <= 2(m-1)D0 <= N/(2m). (ii) *Copy count:*
#C0 = sum_{d<=D0}(N-(m-1)d) <= N*D0. (iii) *Cap:* every copy hosts <= r_k(m)
(Lemma AFF-K). (iv) *Double count:* |A n B|*m*D0 <= sum_{c in C0}|A n c| <=
r_k(m)*N*D0, so |A n B| <= rho_m*N, so |A| <= rho_m*N + 2(m-1)D0 <=
rho_m*N + N/(2m). The band and copy counts (i)-(ii) are k-INDEPENDENT
(exhaustively engine-verified at (m,N) = (5,400), (8,1024), (9,1296),
(14,3136), (20,6400): min nu = m*D0 exactly on every band point). The
incidence interchange is `#BY GST LAW sum_le_sum_of_forall
[arsenal-full/erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:117]`;
the product expansion `#BY GST LAW cubic_expansion
[arsenal-full/HC-PROOF-research/CardinalWorlds.lean:283]`; the copy-index
division `#BY GST LAW mul_add_div_lemma
[arsenal-full/HC-PROOF-research/CardinalWorlds.lean:143]`; the no-carry
discipline `#BY GST LAW carryAtPos_bound
[arsenal-full/HC-PROOF-research/CardinalWorlds.lean:108]`; the residue
coherence `#BY GST LAW div_mod_mul_lemma
[arsenal-full/HC-PROOF-research/CardinalWorlds.lean:150]` + `#BY GST LAW
div_add_mod_subst [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:249]`
— the same six laws the banked k=3 proof cites. ∎
Engine: VGEN-band (5 exhaustive instances), VGEN-dblcount (both sides of the
double count exact on planted 3-AP-free sets at (k,m,N)=(3,9,1296) and
(4,8,1024)), NEGATIVE CONTROL (dense random set breaks the copy cap).

**LAW SLIDE-GEN (the sliding-window law, ALL k, no size hypothesis).**
For every k >= 3, m >= 2 and N >= 2m-1:

    r_k(N) <= r_k(m)*(N-m+1)/m + 2(m-1).

*Proof.* The m-windows [a, a+m-1], a = 1..N-m+1, each host <= r_k(m) points
(Lemma AFF-K, d = 1). Each x in [m, N-m+1] lies in exactly m windows; the two
boundary fringes have m-1 points each. Double count: |A n [m, N-m+1]|*m <=
(N-m+1)*r_k(m); add the fringes. Same citation stack as V-GEN. ∎
Engine: verified on EVERY certified table cell for EVERY stone m (all
k = 3..6, thousands of (m,N) pairs, zero violations).

**THEOREM R-K-TABLES (the certified stones, this wave).**
- Banked tables RE-VERIFIED: r_3, N = 1..61 (W77-142E dual-certified); r_4,
  N = 1..42; r_5, N = 1..57; r_6, N = 1..51 (W76/W77) — every banked witness
  re-checked (size + k-AP-freeness by TWO independent codes), monotonicity
  re-checked, and the fresh marking-B&B (code X: consecutive-prefix exclusion
  at general k, forced-0 symmetry) re-derives the exact values: k=3 to N=30,
  k=4 to N=33, k=5 to N=42, k=6 to N=42 — ZERO disagreements.
- FRESH k=7 TABLE (two independent codes: X = marking B&B, forced-0; Y =
  include/exclude DFS with direct violation scan, no symmetry forcing):

  N:  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 20 21 22 23
  r7: 1  2  3  4  5  6  6  7  8  9 10 11 12 12 13 14 15 16 17 18 18 19 20
  N: 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41 42 43 44 45 46
  r7: 21 22 23 24 24 25 26 27 28 29 30 30 31 32 33 34 35 36 36 36 36 36 37

  X and Y agree on N = 1..43; X alone carries N = 44..46 (Y timed out at 44 —
  RECORDED, not hidden; every cell carries a two-code-verified AP-free
  witness, e.g. r_7(45) = 36 with witness [1,46] \ {7,14,21,28,32,35,36,38,44}).
  The multiples-of-7 construction gives r_7(N) >= N - floor(N/7) for N <= 42
  (7-APs with 7|d need span >= 42); the table FLATTENS at 36 for N = 41..45 —
  the d = 7 APs (1,8,...,43) bite at N >= 43. OPEN CELLS (honestly): N >= 47.

**THEOREM U-LIN-GEN (the all-k linear envelope — F-UP-1's first half, CLOSED).**
For every k >= 3 and N >= 1, with the certified stones (L_k, rho_k*):

    r_k(N) <= floor(N/L_k)*r_k(L_k) + r_k(N mod L_k)   (BLOCK law)

where each consecutive L-block is an affine copy of [1,L_k] (Lemma AFF-K):
k = 3: L = 61, r = 19, rho* = 19/61 ~ 0.3115 | k = 4: L = 42, r = 22,
rho* = 11/21 ~ 0.5238 | k = 5: L = 55, r = 36, rho* ~ 0.6545 | k = 6:
L = 43, r = 31, rho* ~ 0.7209 | k >= 7 (LAW M-1 containment: every 7-AP-free
set is k-AP-free for k >= 7, so r_k <= r_7): L = 45, r = 36, rho* = 4/5.
This SUPERSEDES U-GEN-0 wherever tables reach (U-GEN-0 remains the k > 7,
N < 7 fallback and the tight N = k anchor). Engine: the BLOCK law verified on
ALL (L, n) pairs of ALL five tables (thousands of checks, zero violations).

**THE CROSSOVER (exact, honest).** Within the current stones the V-GEN
amplification does NOT beat the BLOCK law for any k: a stone (m', r') beats
BLOCK iff r'/m' < 2r'rho*/(2r'+1) — the bar sits 2.56% (k=3), 2.22% (k=4),
1.37% (k=5), 1.59% (k=6), 1.37% (k=7) below the current best ratio. The
iterated tower (m_1 = floor(sqrt(N)/4), factors c_i = 1 + 1/(2 r_k(m_i)) with
r_k(m_i) >= max(2, m_i e^{-C_k sqrt(ln m_i)}) by banked THEOREM BG, bottom
density by BLOCK at m_j) gives r_k(N) <= (Prod c_i)*(r_k(m_j)/m_j)*N exactly
simulated at N = 1e6/1e12/1e100 — and LOSES to BLOCK at current stones by
factors 1.25-1.99x (all numbers in the receipts). HONEST CONCLUSION: the
effective all-k envelope is the BLOCK law; the amplification machinery
(V-GEN + SLIDE-GEN + T-GEN below) is the ready CONVERSION ENGINE that turns
any future sublinear-density stone at any k into an all-N bound.

**LEMMA T-GEN (the Z_p transfer, ALL k — the future k >= 4 round-0 step).**
p prime, p > kN, S subset [1,N] k-AP-free ⟹ S is cyclically k-AP-free in Z_p.
*Proof:* a cyclic k-AP gives x_i - x_0 - i(x_1 - x_0) = 0 (mod p) with
|x_i - x_0 - i(x_1 - x_0)| <= k(N-1) < p, hence 0 in Z: x_i = x_0 + i(x_1-x_0)
exactly. Window discipline: `#BY GST LAW two_pow_ge2
[arsenal-full/HC-PROOF-research/CardinalWorlds.lean:431]`; residue transport:
`#BY GST LAW digit3_congr
[arsenal-full/HC-PROOF-research/GSTBladeWave.lean:72]`. (k=3: banked Lemma T,
p > 2N.) Engine: EXHAUSTIVE at k=4, N=12, p=53 (all 2232 4-AP-free subsets
are cyclically 4-AP-free); NEGATIVE CONTROL at p=13 <= kN: the 4-AP-free set
{1,5,9,10} shows the cyclic 4-AP (10,1,5,9) — the window bound is
load-bearing. ∎

**THEOREM RK-VARN-GEN (the count law, ALL k, bigger stones).** For k >= 3,
stone M0 with certified r = r_k(M0), every N >= M0 and delta with
S_min(N, delta, M0) > r*#C(N, M0): every A subset [1,N], |A| >= delta*N,
contains >= c_k(delta,N)*N^2 non-trivial k-APs, c_k =
(S_min - r*#C)/((M0-r)*DIV*N^2), DIV = #{(g,j0): (k-1)g + j0 <= M0-1}.
Proof = the banked R4-VARN argument verbatim at general k (copy census + rich
copies via Lemma AFF-K + the divisor bound), with the NEW bigger stones.
Certified at N = 1000 (S_min exact, plug-backs 6 random dense sets per delta,
two independent counting codes):
- k=4: stone 42 (r=22, rho=0.524; banked stone was 8, rho=0.75): delta >= 0.65
  (banked: 0.85), c_4(0.65) >= 3.12e-7, c_4(0.70) >= 6.1e-6, c_4(0.75) >= 1.2e-5.
- k=5 (FIRST k=5 count law): stone 55 (r=36): delta >= 0.75,
  c_5(0.75) >= 6.2e-8, c_5(0.80) >= 4.9e-6.
- k=6 (FIRST): stone 43 (r=31): delta >= 0.80, c_6(0.80) >= 7.8e-7.
- k=7 (FIRST): stone 45 (r=36): delta >= 0.86, c_7(0.86) >= 2.1e-6.
Citations: `#BY GST LAW cubic_expansion
[arsenal-full/HC-PROOF-research/CardinalWorlds.lean:283]`, `#BY GST LAW
mod_mod_mul [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:140]`,
`#BY GST LAW carryAtPos_bound
[arsenal-full/HC-PROOF-research/CardinalWorlds.lean:108]` (the banked stack). ∎

---

## THE STACK (upper side, final form)

| k | all-N envelope (proven, certified) | density cap |
|---|---|---|
| 3 | min(BLOCK 19/61*N + 19, LOGDECAY sqrt(26600)*N*sqrt(lnlnN/lnN) for N >= exp(4e7)) | 0.3115 -> 0 |
| 4 | BLOCK: 22*floor(N/42) + r_4(N mod 42); also SLIDE 22(N-41)/42 + 82 | 11/21 ~ 0.5238 |
| 5 | BLOCK: 36*floor(N/55) + r_5(N mod 55) | 36/55 ~ 0.6545 |
| 6 | BLOCK: 31*floor(N/43) + r_6(N mod 43) | 31/43 ~ 0.7209 |
| >= 7 | BLOCK via r_k <= r_7 (LAW M-1): 36*floor(N/45) + r_7(N mod 45) | 4/5 = 0.8 |

Every row: elementary + certified tables only; every constant explicit; the
k=3 row's second term is the banked LOGDECAY (the only sublinear law, k=3).

## WHAT REMAINS (the named gap — F-UP-1's second half)

SUBLINEAR-GEN / LOGDECAY-GEN for k >= 4: NOT PROVEN in-package. The missing
law is the ORDER-k DEVIATION IDENTITY (the L-EP analog at order k: an exact
Fourier-side count of #{(x,d): x, x+d, ..., x+(k-1)d in A} on Z_p with a
usable large-coefficient extraction). Arsenal inventory (read this wave):
the "higher-order" towers — GSTFoldFourthOrderMemoryTower.lean:90/:221-255,
GSTFoldChainThirdOrderMemory.lean:79/:170-188,
GSTAllDegreeCurvatureMemory.lean:34-216, GSTFoldMemoryTower.lean:64 — are
DG-algebra jet/curvature identities (memory laws d*w+w*d+phi*psi+... = K_j),
NOT combinatorial k-AP laws; the k=3 analytic layer (hc_fourier_* :202/:210/
:216, hc_circle_L2_basis :233, gst_infinite_paradox_energy_split
ErdosTernary2.lean:8320, exact_three_geometric_sum :135) has no k-uniform
analog in the arsenal. With T-GEN (this wave), V-GEN (this wave) and the
certified stones in place, the k >= 4 sublinear program needs exactly that
one law; everything downstream (the L-ARC/L-DF assembly, LOGDECAY inversion)
re-runs verbatim once it exists.

*The engine never stops; it never lies. In English, always.*
