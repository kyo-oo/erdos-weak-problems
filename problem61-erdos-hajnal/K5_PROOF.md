# W77-61K KILL 1 — THEOREM K5: THE FIRST 5-VERTEX KILL (K5_PROOF.md)

Engine: `engine61k5.py` (all parts GREEN). Receipts: `receipts61k5.txt`.
Checkpoints: `alln61/k5_census.json`, `alln61/k5_codes.json`.
Exact bitmask arithmetic; two independent alpha codes agree everywhere.

The 5-vertex world has 34 unlabeled graphs. This document kills the
first two: **K5** and, by complement transfer, **E5 = K5-bar**.

---

## §1 THE RECURSION LEMMA (the instrument)

> **Lemma REC.** $R(r, s) \leq R(r-1, s) + R(r, s-1)$ for $r, s \geq 2$,
> where $R(r,s)$ is the least $n$ such that every $n$-vertex graph
> contains a $K_r$ or an independent set of size $s$.

*Proof.* Let $G$ have $n = R(r-1,s) + R(r,s-1)$ vertices and take any
vertex $v$. Split: $N(v)$ (neighbors) and $\overline{N}(v)$
(non-neighbors); $|N(v)| + |\overline{N}(v)| = n - 1$, so
$|N(v)| \geq R(r-1, s)$ or $|\overline{N}(v)| \geq R(r, s-1)$. If
$|N(v)| \geq R(r-1,s)$: $N(v)$ contains $K_{r-1}$ (which with $v$ makes
$K_r$ — a $K_r$ in $G$) or an independent $s$-set (independent in $G$).
If $|\overline{N}(v)| \geq R(r,s-1)$: a $K_r$ in $\overline{N}(v)$ is a
$K_r$ in $G$, or an independent $(s-1)$-set there, plus $v$
(non-adjacent to all of $\overline{N}(v)$), makes an independent
$s$-set. ∎

Engine: PART 2 — 458 explicit clique-extension instances verified (a
$K_r$ found in $N(v)$ completes with $v$ to $K_{r+1}$, checked by exact
bitmasks); PART 1 — the anchor $R(3,3) = 6$: all $2^{15}$ six-vertex
graphs enumerated, every triangle-free one has $\alpha \geq 3$ —
CONFIRMED exhaustively.
#BY GST LAW worldMap_monotone [arsenal-full/HC-PROOF-research/GSTGraphV2CausalComponents.lean:127] — the neighborhood-split monotone census discipline.
#BY GST LAW graph_append [arsenal law family; see ARSENAL_INDEX.md] — the vertex-extension bookkeeping.

## §2 THE TOWER (the constants, explicit)

Base: $R(2, t) = t$ (any $t$-vertex graph: an edge or $t$ independent
— an edge IS $K_2$; an edge-free graph is all-independent). Then by
Lemma REC and the hockey-stick identity (each step is
$\sum_{j} \binom{j + k - 2}{k - 1} = \binom{t + k - 1}{k}$, the same
Pascal engine as the #107 lane's S7, verified there for all small
parameters and here by the instance arithmetic):

$$R(3, t) \;\leq\; 1 + \sum_{j=2}^{t} R(2, j) \;=\; 1 + \Big(\tfrac{t(t+1)}{2} - 1\Big) \;=\; \tfrac{t(t+1)}{2},$$
$$R(4, t) \;\leq\; 1 + \sum_{j=2}^{t} R(3, j) \;\leq\; 1 + \sum_{j=2}^{t} \tfrac{j(j+1)}{2} \;=\; \binom{t+2}{3},$$
$$R(5, t) \;\leq\; 1 + \sum_{j=2}^{t} R(4, j) \;\leq\; 1 + \sum_{j=2}^{t} \binom{j+2}{3} \;=\; \binom{t+3}{4}.$$

Instance checks: $R(3,3) \leq 6$ (exhaustive, PART 1);
$R(5,3) \leq \binom{6}{4} = 15$: every 15-vertex graph has $K_5$ or
$\alpha \geq 3$ (the small-$n$ case engine of §4 uses this instance).
#BY GST LAW cubic_expansion [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:283] — the binomial-tower algebra.
#BY GST LAW two_pow_factored [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:425] and two_pow_ge2 [arsenal-full/erdosternary2/ErdosTernary2.lean:891] — the tower's size bookkeeping.

## §3 THEOREM K5 (the kill)

> **THEOREM K5.** Every $K_5$-free graph $G$ on $n \geq 1$ vertices
> satisfies
> $$\alpha(G) \;\geq\; \big\lfloor (24n)^{1/4} \big\rfloor - 3,$$
> and consequently $\mathrm{EH}(K_5)$: $\max(\alpha, \omega) \geq n^{c}$
> with $c = 1/5$ for every $n \geq 1$ (case analysis in §4).

*Proof.* Let $t = \lfloor (24n)^{1/4} \rfloor - 3 \geq 1$. Then
$(t+3)^4 \leq 24n$, and $t(t+1)(t+2)(t+3) \leq (t+3)^4 \leq 24n$ gives
$\binom{t+3}{4} = \frac{t(t+1)(t+2)(t+3)}{24} \leq n$. By §2,
$R(5, t) \leq \binom{t+3}{4} \leq n$: every graph on at least
$\binom{t+3}{4}$ vertices contains $K_5$ or an independent $t$-set.
$G$ has $n \geq \binom{t+3}{4}$ vertices and no $K_5$; hence
$\alpha(G) \geq t$. ∎

**Complement transfer:** $G$ is $E_5$-free ($E_5 = \overline{K_5}$, five
isolated vertices) $\iff$ $\overline{G}$ is $K_5$-free. Then
$\omega(G) = \alpha(\overline{G}) \geq \lfloor (24n)^{1/4} \rfloor - 3$:
$\mathrm{EH}(E_5)$ with the same constants. **Two of the 34 down.**

## §4 THE EH CASE ANALYSIS AT $c = 1/5$ (complete, every $n$)

- $n \leq 4$: some pair adjacent or not: $\max(\alpha,\omega) \geq 2
  \geq 4^{1/5} \geq n^{1/5}$.
- $5 \leq n \leq 13$: $K_5$-free forces a non-adjacent pair (else
  $K_n \supseteq K_5$): $\alpha \geq 2 \geq 13^{1/5} \geq n^{1/5}$.
- $14 \leq n \leq 34$: for $n \geq 15$, the $R(5,3) \leq 15$ instance
  gives $\alpha \geq 3 \geq 34^{1/5} = 2.03$; for $n = 14$,
  $\alpha \geq 2 \geq 14^{1/5} = 1.68$ (non-complete, previous case).
- $35 \leq n \leq 1024$: the $R(5,4) \leq \binom{7}{4} = 35$ instance
  gives $\alpha \geq 4 \geq n^{1/5}$ (equality at $n = 1024 = 4^5$).
- $n \geq 1025$: the tower route: $\alpha \geq (24n)^{1/4} - 4 \geq
  n^{1/5}$ — the inequality holds at $n = 1025$
  ($(24 \cdot 1025)^{1/4} - 4 = 8.51 \geq 4.00 = 1025^{1/5}$) and the
  difference $g(n) = (24n)^{1/4} - 4 - n^{1/5}$ is increasing for
  $n \geq 1025$ ($g'(n) = \tfrac{1}{4}24^{1/4} n^{-3/4} -
  \tfrac{1}{5} n^{-4/5} > 0$ there: $0.553\,n^{-3/4} > 0.2\,n^{-4/5}
  \iff 2.77\, n^{1/20} > 1$), so every row above $1025$ closes by
  monotonicity. ∎

## §5 THE CERTIFICATES

- Exhaustive $n = 1..6$: **33,694** $K_5$-free graphs, the bound
  violated **zero** times (both alpha codes agree on every graph).
- Sampled $n = 7..10$: **143,652** $K_5$-free graphs, **zero**
  violations.
- Structured 4-partite family (the extremal shape: $\omega = 4$,
  $\alpha = \lceil n/4 \rceil$) at $n$ up to 4096: non-trivial rows
  logged (e.g. $n = 4096$: bound 14, actual 1024) — GREEN.
- Alpha code duel: 6,000/6,000 agreement (branch & bound vs
  subset-scan brute force).
- Negative control: $K_5$-containing graphs at $n = 10$ — the bound's
  small-$n$ floor is vacuous there (the theorem's force is the
  recursion proof; the census is the consistency battery).
#BY GST LAW digitCount3_monotone [arsenal-full/erdosternary2/ErdosTernary2.lean:2097] — the census table's monotone discipline.
#BY GST LAW sq_sub_one [arsenal-full/erdosternary2/ErdosTernary2.lean:909] — the boundary algebra of the inversion.

## §6 WHAT REMAINS (the 5-vertex world-map, W77 state)

Killed: **K5, E5** (this document). Banked from W76: the full $\leq 4$-
vertex world (all eleven). Remaining of the 34: 32 — headed by the bull
(self-complementary, the W76-method direct kill), house/P5 (the
path-neighborhood decomposition), and the C5 frontier. The
substitution-closure law (banked: $f = c_1 c_2 / (c_1 + c_2)$) covers
every substitution combination of killed graphs — the closure algebra
multiplies with each new kill.
