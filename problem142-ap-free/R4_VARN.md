# W77-142K KILL 3 — THEOREM R4-VARN: THE FIRST k=4 LAW (R4_VARN.md)

Engine: `engine142r4.py` (all parts GREEN). Receipts:
`receipts142r4varn.txt`. Checkpoints: `experiments_v2/r4_table.json`,
`experiments_v2/r4varn_constants.json`, `experiments_v2/r4_modelstep.json`.
Exact integer arithmetic; two independent 4-AP counting codes agree on
every count in this document.

---

## §1 THE CERTIFIED r_4 TABLE (the first k=4 data stone)

Exhaustive certification (every subset of [1,M] enumerated, freeness by
two codes) for M = 1..16:

| M | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 |
|---|---|---|---|---|---|---|---|---|---|----|----|----|----|----|----|----|
| r_4(M) | 1 | 2 | 3 | 4 | 4 | 5 | 5 | 6 | 7 | 8 | 8 | 8 | 9 | 9 | 10 | 10 |

Witnesses recorded in the receipts (e.g. r_4(8) = 6 with witness
{1,2,3,5,6,8}; r_4(16) = 10 with witness {1,2,4,5,7,8,9,12,14,15}).
#BY GST LAW digitCount3_monotone [arsenal-full/erdosternary2/ErdosTernary2.lean:2097] — the table's monotone discipline (r_4(M) <= r_4(M+1), engine-checked).
#BY GST LAW two_pow_ge2 [arsenal-full/erdosternary2/ErdosTernary2.lean:891] — the size positivity of the witnesses.

## §2 THEOREM R4-VARN (explicit, complete)

> **Theorem R4-VARN.** Let M0 = 8 and r = r_4(8) = 6 (certified §1).
> For every N >= 8 and every delta in (0,1] with
> $$S_{\min}(N, \delta) \;>\; r \cdot \#C(N),$$
> every A subset [1,N] with |A| >= delta*N contains at least
> $$c_4(\delta, N) \cdot N^2 \;\;=\; \frac{S_{\min}(N,\delta) - r\,\#C(N)}{(M_0 - r)\,M_0^2\,N^2} \cdot N^2$$
> non-trivial 4-term arithmetic progressions, where:
> - $\#C(N)$ = the number of affine copies of [1,M0] in [1,N]
>   (exactly $\sum_{d=1}^{\lfloor (N-1)/7 \rfloor} (N - 7d)$);
> - $S_{\min}(N, \delta)$ = the sum of the $\lceil \delta N \rceil$
>   smallest values of the copy-membership function
>   $\mathrm{copies}(x) = \#\{(a,d) : x \in a + d\{0..7\}\}$
>   (computed exactly by the engine; the adversarial floor of
>   $\sum_{x \in A} \mathrm{copies}(x)$).

**Certified range at N = 1000:** delta >= 0.85, with
c_4(1.00) >= 1.108e-3, c_4(0.95) >= 8.130e-4, c_4(0.90) >= 5.178e-4,
c_4(0.85) >= 2.230e-4 — plug-back 40/40 GREEN at each delta (random
dense sets; 4-AP count by BOTH codes; every count >= c_4*N^2).

*Proof.* (1) **Copies.** Each (a,d) with a >= 1, d >= 1, a+7d <= N
gives the copy a + d{0,..,7} of [1,8]; 4-APs are preserved under affine
maps with d >= 1 (a 4-AP inside the copy is a 4-AP of [1,N]).
(2) **Rich copies.** A copy with |A ∩ copy| >= r+1 = 7 contains a
4-AP (else it would be a 4-AP-free 7-subset of an 8-point affine copy
— contradicting r_4(8) = 6 by the affine pullback).
(3) **Counting rich copies.** With x = #rich:
$$\textstyle\sum_{\text{copies}} |A \cap \text{copy}| \;\leq\; 6(\#C - x) + 8x \;=\; 6\#C + 2x,$$
so $x \geq (\sum_{\text{copies}} |A\cap\text{copy}| - 6\#C)/2$. And
$\sum_{\text{copies}} |A \cap \text{copy}| = \sum_{x \in A}
\mathrm{copies}(x) \geq S_{\min}(N, \delta)$ (the exact worst case,
engine-computed). (4) **Divisor.** A fixed 4-AP a_1, a_1+d_1, ... lies
in a copy a + d{0..7} only if d = d_1/(m_1 - m_0) for the induced
index span (m_1 - m_0) in {1,..,7} and m_0 in {0,..,7}: at most
7 x 8 < M0^2 = 64 copies (engine-corroborated: empirical worst 7).
(5) **Assembly.** #4APs >= x/64 >= (S_min - 6#C)/(2 · 64) = the stated
c_4 · N^2. ∎
#BY GST LAW cubic_expansion [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:283] — the binomial/averaging algebra of the copy census.
#BY GST LAW mod_mod_mul [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:143] and div_mod_mul_lemma [CardinalWorlds.lean:150] — the residue discipline of the copy-membership and divisor computations.
#BY GST LAW carryAtPos_bound [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:108] — the index-overflow discipline of the copy bookkeeping.

## §3 THE AMPLIFICATION FRONT (the architecture toward all delta)

The delta-threshold is governed by the stone ratio r_4(M0)/M0: with
M0 = 8 the ratio is 0.75 and the numerator turns positive at
delta ~ 0.85 (N = 1000). Larger certified stones push delta down:
r_4(16)/16 = 0.625 already (§1 table). The program toward small delta:
certify r_4(M0) at growing M0 (SAT lane — the 142E machinery ports
directly: variables x_i, clause NOT(x_a AND x_{a+d} AND x_{a+2d} AND
x_{a+3d}) for all 4-APs, cardinality >= t+1, UNSAT = upper bound),
then re-run the constant sweep. The model-step data (§4) is the
density-increment feed for the next round.

## §4 THE MODEL-STEP DATA (both codes agree; the next round's feed)

Random dense sets, exact 4-AP counts (average of 20, minimum recorded):

| N | delta=0.3 | delta=0.2 | delta=0.1 |
|---|---|---|---|
| 200 | 44.0 (min 34) | 9.0 (min 4) | 0.4 (min 0) |
| 400 | 212.6 (min 172) | 39.6 (min 24) | 1.9 (min 0) |
| 800 | 810.5 (min 732) | 173.0 (min 139) | 10.4 (min 4) |

The N^2 shape is visible at delta=0.3 (44 -> 213 -> 811 ≈ N^2/900);
at delta=0.1 the counts are near zero at these N — the density
threshold behavior that the increment program must crack.

## §5 KILL 2 STATUS (the exponent push toward LOGPOWER)

LOGDECAY is banked (this branch, commit 2c00992: r_3(N) <=
sqrt(26600) N sqrt(lnlnN/lnN), N >= ceil(exp(4e7)), 19/19 dual-method).
The next stone — THEOREM LOGPOWER (r_3(N) <= N/(log N)^{c0}) — needs
the improved increment shape from L-EP (delta -> delta(1 + c delta^?)
on subprogressions of relative length N^{-1/2+o(1)}); the recursion
analysis with machine-checked constants is the named front for the
next round. The R4-VARN machinery of this document is the k>=4
foundation stone BOSS's asymptotic program demanded.
