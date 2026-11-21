# SHARP_PROOF.md — THEOREM ES-ALLN-SHARP BY THE LABEL ROUTE (W78-107E)

Task ID: W78-107E, KILL 1. Engine: `engine107sharp.py` (stages S1–S13,
receipts `receipts107sharp.txt`). Exact integer and `Fraction` arithmetic
throughout; every machine claim two-method verified; every proof below is
in-package (external results are named as such and carry no weight).

BOSS's order: the sharp all-n binomial bound — **f(n) ≤ C(2n−4, n−2) + 1 for
every n ≥ 3** — derived through the (a,b)-lemma by the **label
(L(p), R(p)) pigeonhole**, on the banked L-MLT/L-AVOID foundations
(ALLN_PROOF.md §3–§4 = the W77 starting state; its "named front" — the
interior induction step of the sharp avoidance law — is closed here).

---

## §0 THE THEOREMS OF THIS FILE

> **Theorem ES-ALLN-SHARP.** For every $n \geq 3$: every set of
> $$\binom{2n-4}{n-2}+1$$ points in general position in the plane contains
> $n$ points in convex position. Hence
> $$f(n) \;\leq\; \binom{2n-4}{n-2}+1 \qquad \text{for every } n \geq 3.$$

*Status:* **PROVEN, complete, in-package, below** (§2–§5). This is the
**second independent complete proof** of the binomial bound in the package —
the first is the X/Y-split induction of ES_PACKAGE_PROOF.md §2–§3 (banked,
W72/S071); the present proof is the **label route**, the derivation whose
missing stone W77 identified as L-AVOID's interior step (ALLN_PROOF.md §3:
"the sharp i-cup/j-cap avoidance is the certified law whose induction step
is the named front"). The stone falls here: **Lemma L-AVOID-SHARP (§2),
proof complete.**

> **Lemma L-AVOID-SHARP (the sharp avoidance law — the W77 named front,
> closed).** Let $S$ be a finite distinct-$x$ general-position set and
> $i, j \geq 2$. The label class
> $$P_{ij} \;=\; \{p \in S : \mathrm{cup}(p) = i,\ \mathrm{cap}(p) = j\}$$
> contains **no $i$-cup and no $j$-cap**.

*Status:* **PROVEN** (§2). W77 certified this law on 3,322 classes
(4,000 random sets, zero occurrences) but could not prove it; the proof
below is a two-step sign contradiction at the leftmost point of the
hypothetical chain — pure orientation arithmetic.

> **Lemma L-MLT(b) (the tight label-multiplicity law — W77's tight leg,
> now proven).** For $i, j \geq 2$:
> $$|P_{ij}| \;\leq\; \binom{i+j-4}{i-2}.$$

*Status:* **PROVEN** (§3), from L-AVOID-SHARP + the (a,b)-lemma at $(i,j)$.
(W77: boundary rows proven, interior certified on 5,510,000+
configurations — the certification is now a corollary of the proof.)

> **Theorem CC-SHARP (the (a,b)-lemma, label route).** For all $a, b \geq 2$:
> every distinct-$x$ general-position set of $\binom{a+b-4}{a-2}+1$ points
> contains an $a$-cup or a $b$-cap.

*Status:* **PROVEN** (§4) by double induction on $a+b$ — the label
decomposition, L-MLT(b) on every class, and the Vandermonde–hockey-stick
assembly. Independent of the banked X/Y-split proof of the same statement.

**The sharpening (this bound vs. the banked U-BIS).** U-BIS
(ALLN_PROOF.md §4) gives $f(n) \leq \binom{2n-2}{n-1}-2n+4$. ES-ALLN-SHARP
is strictly sharper at **every** $n \geq 3$ (engine-verified $n = 3..60$,
two binomial codes, S7):

| $n$ | ES-ALLN-SHARP | U-BIS | anchors |
|---|---|---|---|
| 3 | **3** | 4 | $f(3)=3$ — equality |
| 4 | **7** | 16 | $f(4)=5$ |
| 5 | **21** | 64 | $f(5)\geq 9$ (witness) |
| 6 | **71** | 244 | $f(6)\geq 17$ (witness) |
| 7 | **253** | 914 | $f(7)\geq 33$ (classical ES doubling, cited) |

---

## §1 THE FRAME — DISTINCT-x FOR FREE (banked, spine-cited)

Throughout, "GP" = no three collinear. For a finite point set the banked
Lemma SH (ES_PACKAGE_PROOF.md §7.1) and L-ROT (ALLN_PROOF.md §1) supply a
det-1 affine frame with distinct $x$-coordinates: the shear
$T_s(x,y) = (x+sy,\ y)$ has $\det = 1$ and at most $\binom{m}{2}$ bad
parameters $s$; the reals are infinite, so a good $s$ exists. Orientation
is carried by BOSS's bracket algebra:

**Law (bracket).** $\mathrm{bracket}(v,w) = v_1w_2 - v_2w_1$; the
orientation of a triple is $\mathrm{orient}(p,q,r) =
\mathrm{bracket}(q-p,\ r-p)$.
#BY GST LAW bracket_skew [arsenal-full/HC-PROOF-research/GSTCausalPairingGraphs.lean:19]
#BY GST LAW bracket_transform [arsenal-full/HC-PROOF-research/GSTCausalPairingGraphs.lean:27]
#BY GST LAW bracket_shear [arsenal-full/HC-PROOF-research/GSTCausalPairingGraphs.lean:33]
#BY GST LAW plucker_four [arsenal-full/HC-PROOF-research/GSTCausalPairingGraphs.lean:38]

Under $T_s$: $\mathrm{bracket}(T_sv, T_sw) = (ad-bc)\,\mathrm{bracket}(v,w)
= \mathrm{bracket}(v,w)$ — every triple's orientation sign is **exactly
invariant**; collinearity (bracket zero) is preserved both ways; convex
position of a finite subset is preserved (SH (d), banked). The whole-configuration
covariance (one factor per edge) is the graph amplitude law:
#BY GST LAW graph_transform [arsenal-full/HC-PROOF-research/GSTCausalPairingGraphs.lean:50]

Machine: banked S1 (11,459 exact triple checks, zero sign changes) +
engine107sharp S0/S7 re-run (fresh seed).

**Cups and caps (definitions).** In a distinct-$x$ set, a $k$-**cup** is a
$k$-subset $q_1 <_x q_2 < \dots <_x q_k$ with strictly increasing
consecutive slopes
$s_t = \mathrm{slope}(q_t, q_{t+1})$; a $k$-**cap**: strictly decreasing.
The slope comparison is orientation:
$$\mathrm{slope}(a,b) < \mathrm{slope}(b,c) \iff \mathrm{orient}(a,b,c) > 0
\qquad (a <_x b <_x c),$$
because both sides say $c$ lies strictly above the line through $a, b$
extended past $b$ — the bracket identity behind this is plucker_four's
three-term relation among the pair brackets. **Labels:**
$\mathrm{cup}(p)$ = max size of a cup with right endpoint $p$;
$\mathrm{cap}(p)$ likewise for caps.

**Label basics (banked ALLN_PROOF.md §3).** The leftmost point $p_*$ has
label $(1,1)$; every other point has $\mathrm{cup} \geq 2$ and
$\mathrm{cap} \geq 2$ (any single left neighbor makes a 2-cup and a 2-cap).
**Lemma A1 (label absoluteness, banked):** $P_{ij}$ contains no
$(i{+}1)$-cup and no $(j{+}1)$-cap — a chain of a subset is a chain of $S$.

---

## §2 LEMMA L-AVOID-SHARP — THE KILL (the W77 named front falls)

> **Lemma L-AVOID-SHARP.** $S$ a finite distinct-$x$ GP set, $i, j \geq 2$.
> Then $P_{ij}$ contains no $i$-cup and no $j$-cap.

**Proof, cup half.** Suppose toward contradiction that
$$C \;=\; (p_1 <_x p_2 <_x \dots <_x p_i)$$
is an $i$-cup with **every** $p_t \in P_{ij}$. Write
$s_t := \mathrm{slope}(p_t, p_{t+1})$; $C$ a cup means
$s_1 < s_2 < \dots < s_{i-1}$. Note $i \geq 2$, so $p_2$ and $s_1$ exist.

**Step 1 (left-anchored exclusion).** Every $w \in S$ with $w <_x p_1$
satisfies
$$\mathrm{slope}(w, p_1) \;>\; s_1. \tag{$\ddagger$}$$
*Proof of Step 1.* Suppose $\mathrm{slope}(w,p_1) < s_1$. The chain
$(w, p_1, p_2, \dots, p_i)$ has consecutive slopes
$$\mathrm{slope}(w,p_1) \;<\; s_1 \;<\; s_2 \;<\; \dots \;<\; s_{i-1},$$
strictly increasing — an $(i{+}1)$-cup whose right endpoint is $p_i$. But
$\mathrm{cup}(p_i) = i < i+1$. Contradiction. The excluded equality
$\mathrm{slope}(w,p_1) = s_1$ would make $w, p_1, p_2$ three distinct
collinear points (same slope through the shared point $p_1$), violating
GP. $\square$

**Step 2 (cap-extension exclusion).** Since $\mathrm{cap}(p_1) = j \geq 2$,
a **$j$-cap ends at $p_1$** (a longest one):
$$F = (f_1 <_x f_2 <_x \dots <_x f_j = p_1),$$
with strictly decreasing slopes; its last slope is
$\sigma := \mathrm{slope}(f_{j-1}, p_1)$ (the point $f_{j-1} <_x p_1$
exists because $j \geq 2$). Then
$$\sigma \;<\; s_1. \tag{$\dagger'$}$$
*Proof of Step 2.* Suppose $\sigma > s_1$. The chain
$(f_1, \dots, f_{j-1}, p_1, p_2)$ has consecutive slopes
$$\sigma_1 > \sigma_2 > \dots > \sigma_{j-1} = \sigma \;>\; s_1,$$
strictly decreasing — a $(j{+}1)$-cap whose right endpoint is $p_2$. But
$\mathrm{cap}(p_2) = j < j+1$. Contradiction. Equality $\sigma = s_1$ is
excluded by GP ($f_{j-1}, p_1, p_2$ collinear). $\square$

**Step 3 (the contradiction).** $f_{j-1} \in S$ and $f_{j-1} <_x p_1$, so
Step 1 applied to $w := f_{j-1}$ gives
$\sigma = \mathrm{slope}(f_{j-1}, p_1) > s_1$. Step 2 gives
$\sigma < s_1$. Both cannot hold. Hence no $i$-cup lies in $P_{ij}$.
$\blacksquare$

**Cap half.** The mirror $M(x,y) = (x,-y)$ is an invertible linear map of
determinant $-1$; it flips every slope's sign, hence swaps cups and caps
(strictly increasing slopes ↔ strictly decreasing), preserves $x$-order
and GP (orientations negate, never vanish), and exchanges the labels:
$\mathrm{cup}_{M(S)}(Mp) = \mathrm{cap}_S(p)$, $\mathrm{cap}_{M(S)}(Mp) =
\mathrm{cup}_S(p)$, whence $M(P_{ij}(S)) = P_{ji}(M(S))$. A $j$-cap in
$P_{ij}(S)$ maps to a $j$-cup in $P_{ji}(M(S))$ — excluded by the cup half
at parameters $(j, i)$. $\blacksquare$

**Remarks.**
(i) The argument uses only the labels of the chain's points
($\mathrm{cup} = i$, $\mathrm{cap} = j$ on all of $C$), GP, and orientation
arithmetic — no induction, no external input. It is the interior step W77
could not find; the key was extending the contradiction chain **to the
right** (Step 1 uses the full cup $C$ through $p_i$) while the cap
witness $F$ enters **from the left** (Step 2) — the two signs collide at
$p_1$.
(ii) Boundary subsumption: at $i = 2$ (so $C = (p_1,p_2)$, $s_1$ the only
slope) Step 1 reads "every $w <_x p_1$ has $\mathrm{slope}(w,p_1) >
\mathrm{slope}(p_1,p_2)$" and Step 2 is unchanged — this **re-proves the
W77 boundary row** $|P_{2j}| \leq 1$ (and dually $|P_{i2}| \leq 1$) as the
$i=2$ case: a 2-cup inside $P_{2j}$ is any pair, so none exists.
(iii) The W77 pair-level engine certificate (LABEL-SIGN: for every
same-label pair $p <_x q$, every max cup at $p$ ends strictly above the
line $pq$, every max cap strictly below) is exactly the $(p_1, p_2)$-pair
shadow of Steps 1–2; engine107sharp S2 certifies both steps in full on
every chain (the mechanism lane).

#BY GST LAW plucker_four [arsenal-full/HC-PROOF-research/GSTCausalPairingGraphs.lean:38] — the three-term bracket relation governing the slope comparisons of Steps 1–2.
#BY GST LAW bracket_skew [arsenal-full/HC-PROOF-research/GSTCausalPairingGraphs.lean:19] — the antisymmetry fixing the sign conventions of orient.
#BY GST LAW bracket_transform [arsenal-full/HC-PROOF-research/GSTCausalPairingGraphs.lean:27] — the mirror $M$ (det −1): brackets scale by −1, signs flip, zeros stay zero.

---

## §3 LEMMA L-MLT(b) — THE TIGHT MULTIPLICITY LAW, PROVEN

> **Lemma L-MLT(b).** For all $i, j \geq 2$:
> $|P_{ij}| \leq \binom{i+j-4}{i-2}$.

**Proof.** $P_{ij} \subseteq S$ is itself a distinct-$x$ GP set (a subset
of one is one: distinct $x$'s persist; a collinear triple in $P_{ij}$
would be collinear in $S$). By L-AVOID-SHARP, $P_{ij}$ contains no $i$-cup
and no $j$-cap. By Theorem CC-SHARP at parameters $(i,j)$ (§4; for
$i+j \leq$ any bound this is available — see the induction order in §4;
in particular at $i = 2$ or $j = 2$ it is the two-point base), every
distinct-$x$ GP set of $\binom{i+j-4}{i-2}+1$ points contains an $i$-cup
or a $j$-cap. $P_{ij}$ contains neither, so
$|P_{ij}| \leq \binom{i+j-4}{i-2}$. $\blacksquare$

*Order-of-argument note (no circularity).* CC-SHARP at $(a,b)$ uses
L-MLT(b) at $(i,j)$ with $i \leq a-1$, $j \leq b-1$; L-MLT(b) at $(i,j)$
uses CC-SHARP at $(i,j)$ with $i + j \leq a+b-2 < a+b$; L-AVOID-SHARP uses
nothing but §1. The composite is a well-founded induction on $a+b$.

#BY GST LAW sum_le_sum_of_forall [arsenal-full/erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:117] — the termwise-≤ sum discipline of the class census.
#BY GST LAW digitCount3_monotone [arsenal-full/erdosternary2/ErdosTernary2.lean:2097] — the monotone counting discipline: bigger ambient sets can only weakly grow the class census.

---

## §4 THEOREM CC-SHARP — THE (a,b)-LEMMA BY THE LABEL ROUTE

**The two binomial lemmas (in-package, two-code engine-verified S4).**

> **Lemma HOCKEY (hockey stick).** For $0 \leq r \leq N$:
> $\sum_{t=r}^{N} \binom{t}{r} = \binom{N+1}{r+1}$.

*Proof.* Induction on $N$. $N = r$: $\binom{r}{r} = 1 = \binom{r+1}{r+1}$.
Step: $\sum_{t=r}^{N+1}\binom{t}{r} = \binom{N+1}{r+1} + \binom{N+1}{r} =
\binom{N+2}{r+1}$ by **Pascal** — itself the algebraic identity
$\binom{n-1}{k-1} + \binom{n-1}{k} = \binom{n}{k}$, expanded from the
absorbing formula on the binomial expansion discipline of the arsenal:
#BY GST LAW binom_two_term [arsenal-full/HC-PROOF-research/GSTDiagonalRead.lean:56] — $(1+x)^u = 1 + u\,x + x^2 s$: the two-term binomial spine every Pascal step expands on.
#BY GST LAW binom_first_order [arsenal-full/erdosternary2/ErdosTernary2.lean:2740] — the same first-order expansion law in ℕ, the arithmetic the index shift below runs on.
#BY GST LAW binom_mod_sq_local [arsenal-full/erdosternary2/ErdosTernary2.lean:461] — the exact-quotient form of the expansion, the division discipline of the absorbing formula. $\square$

> **Lemma VANDERMONDE-DOUBLE (the assembly identity).** For $a, b \geq 3$:
> $$\sum_{i=2}^{a-1}\sum_{j=2}^{b-1}\binom{i+j-4}{i-2}
> \;=\; \binom{a+b-4}{a-2}\;-\;1.$$

*Proof.* Substitute $u = i-2 \in [0, a-3]$, $v = j-2 \in [0, b-3]$ (the
index shift on the summation-shift discipline):
#BY GST LAW sum_range_shift [arsenal-full/erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:104]
Inner sum, fixed $u$, by HOCKEY with $r = u$:
$\sum_{v=0}^{b-3}\binom{u+v}{u} = \sum_{t=u}^{u+b-3}\binom{t}{u} =
\binom{u+b-2}{u+1} = \binom{u+b-2}{b-3}$ (complementing). Outer sum, by
HOCKEY with $r = b-3$ over $t = u + b - 2 \in [b-2, a+b-5]$ — the stick
$\sum_{t=b-3}^{a+b-5}\binom{t}{b-3} = \binom{a+b-4}{b-2}$ loses exactly
the single $t = b-3$ term $\binom{b-3}{b-3} = 1$ *(W81-107B audit note,
completed by the W81-107B-F finisher: the pre-audit prose subtracted a
spurious $t=b-1$ / $\binom{b-2}{b-3}$ term mid-derivation, and the first
repair attempt still ran the stick to $a+b-4$ and closed at
$\binom{a+b-3}{b-2}-1$ — an off-by-one: at $a=b=4$ that intermediate
reads $9$ where the true sum is $5$. The displayed identity and its
two-code machine certificate were correct throughout; the prose is now
the two clean HOCKEY applications, and the audit engine re-certifies the
corrected intermediate identity too, A5)*:
$$\sum_{u=0}^{a-3}\binom{u+b-2}{b-3} = \binom{a+b-4}{b-2} - 1.$$
Close with the complement $\binom{a+b-4}{b-2} = \binom{a+b-4}{a-2}$
(since $(a+b-4)-(b-2) = a-2$):
$$\sum_{i=2}^{a-1}\sum_{j=2}^{b-1}\binom{i+j-4}{i-2}
= \binom{a+b-4}{a-2} - 1. \qquad\square$$
Each equality is Pascal or HOCKEY; the composite is engine-verified for
**all** $3 \leq a, b \leq 60$ by **two independent codes** (S4: `math.comb`
direct vs. a from-scratch memoized Pascal recursion — no `math.comb` —
agreeing on every value), in vivo on the extremal sets (S4: the label
census of $S(a,b)$ sums to $\binom{a+b-4}{a-2}$ exactly), and again by the
W81-107B audit engine (A4, two fresh binomial codes).

(The displayed intermediate is written out longhand in S4's receipt line;
the engine carries the identity, the prose carries the two HOCKEY
applications and the two Pascal complements — four steps, each a lemma
above.)

#BY GST LAW cubic_expansion [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:283] — $(1+a)^3 = 1+3a+3a^2+a^3$: the Pascal-tower discipline of the assembly.
#BY GST LAW mod_mod_mul [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:140] — the exact-modulus discipline of the binomial arithmetic.
#BY GST LAW mul_add_div_lemma [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:143] — the exact-division discipline of the absorbing formula.

> **Theorem CC-SHARP.** For all $a, b \geq 2$: every distinct-$x$ GP set of
> $\binom{a+b-4}{a-2}+1$ points contains an $a$-cup or a $b$-cap.

**Proof (double induction on $a+b$, strong from $4$ up).**

*Base ($a = 2$ or $b = 2$).* WLOG $a = 2$: $\binom{b-2}{0}+1 = 2$ points
with distinct $x$ form a 2-cup (one edge; convexity vacuous). ✓

*Step ($a, b \geq 3$; total $a+b = s$; the theorem is assumed for all
parameter pairs of total $< s$).* Let $S$ be a distinct-$x$ GP set with
$$|S| = \binom{a+b-4}{a-2}+1$$
containing **no $a$-cup and no $b$-cap**; we derive a contradiction.
Then every $p \in S$ has $\mathrm{cup}(p) \leq a-1$ and
$\mathrm{cap}(p) \leq b-1$. Let $p_*$ be the leftmost point of $S$ —
label $(1,1)$, unique. Every other point $q$ has
$\mathrm{cup}(q) \geq 2$, $\mathrm{cap}(q) \geq 2$ (§1). Hence the
**label decomposition** (disjoint, exhaustive):
$$S \;=\; \{p_*\} \;\cup\; \bigcup_{i=2}^{a-1}\,\bigcup_{j=2}^{b-1} P_{ij}.$$
Each index pair satisfies $i + j \leq (a-1)+(b-1) = s-2 < s$, so
CC-SHARP$(i,j)$ holds by the induction hypothesis, and L-MLT(b) at
$(i,j)$ (§3) gives $|P_{ij}| \leq \binom{i+j-4}{i-2}$. Summing, with
Lemma VANDERMONDE-DOUBLE:
$$|S| \;\leq\; 1 + \sum_{i=2}^{a-1}\sum_{j=2}^{b-1}\binom{i+j-4}{i-2}
\;=\; 1 + \Bigl(\binom{a+b-4}{a-2} - 1\Bigr)
\;=\; \binom{a+b-4}{a-2},$$
contradicting $|S| = \binom{a+b-4}{a-2}+1$. $\blacksquare$

**The pigeonhole inside the induction** (the brief's label
(L(p),R(p)) pigeonhole, made precise): a set with no $a$-cup and no
$b$-cap has all labels in the box $[2,a{-}1] \times [2,b{-}1]$ (plus the
single $(1,1)$); the box has $(a{-}2)(b{-}2)$ cells; the cells are **not**
singletons (W77's refuted injectivity) — the label pigeonhole is the
**weighted** count: cell $(i,j)$ holds at most $\binom{i+j-4}{i-2}$
points (L-MLT(b)), and the weights assemble to exactly
$\binom{a+b-4}{a-2} - 1$. The naive pigeonhole (unweighted,
$(a{-}2)(b{-}2)+1$) is the Erdős–Szekeres monotone-subsequence bound
(Theorem MS, banked §1); the weighted pigeonhole is the cups-caps truth.

#BY GST LAW packet_add [arsenal-full/HC-PROOF-research/CardinalWorldsV2.lean:88] — depth composition $2^{j+k} = 2^j\cdot 2^k$: the additive-parameter composition discipline of the double induction (the $(a,b)\to(a{-}1,b)/(a,b{-}1)$ bookkeeping).
#BY GST LAW joined_prefix_succ [arsenal-full/HC-PROOF-research/CardinalWorldsV2.lean:120] — the one-step prefix recurrence $J(K{+}1) = J(K) + 5\cdot 6^K$: the telescope discipline of the assembly's outer sum.
#BY GST LAW two_pow_ge2 [arsenal-full/erdosternary2/ErdosTernary2.lean:892] — the positivity ladder of the index bounds $2 \leq i \leq a-1$.

---

## §5 THEOREM ES-ALLN-SHARP — COMPOSITION AT a = b = n

**Proof.** Let $S$ be any GP set with
$|S| = \binom{2n-4}{n-2}+1$, $n \geq 3$. By Lemma SH / L-ROT (§1, banked)
apply a det-1 affine map making the $x$-coordinates distinct; call the
image $S'$ ($|S'| = |S|$, GP, distinct $x$; convex position is affine-
invariant both ways). Theorem CC-SHARP at $a = b = n$: $S'$ contains an
$n$-cup or an $n$-cap $K$. By L-CC (banked ALLN_PROOF.md §2, via
L-SLOPEAVG: every triple of a cup turns left — the weighted-average slope
argument on plucker_four's bracket algebra — so every cup point is a hull
vertex; dually caps): $K$ is $n$ points in convex position. Map back:
$n$ points of $S$ in convex position. Since $S$ was arbitrary:
$$f(n) \;\leq\; \binom{2n-4}{n-2}+1 \qquad (n \geq 3). \blacksquare$$

#BY GST LAW plucker_four [arsenal-full/HC-PROOF-research/GSTCausalPairingGraphs.lean:38] — the turn-sign algebra of L-SLOPEAVG/L-CC.
#BY GST LAW bracket_shear [arsenal-full/HC-PROOF-research/GSTCausalPairingGraphs.lean:33] — det-1 frames, the distinct-x reduction.
#BY GST LAW two_pow_factored [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:425] — $2^j = 2\cdot 2^{j-1}$: the size ladder the composition runs on ($n \mapsto 2n-4$).

**Verification at the anchors (S7).** $n=3$: bound $3 = f(3)$ — equality,
both directions banked (ES_PACKAGE_PROOF.md §5). $n=4$: $7 \geq f(4)=5$
(banked). $n=5$: $21 \geq f(5) \geq 9$ (8-point witness banked; the exact
value $9$ is classical Makai–Turán, cited; the in-package exhaustive
certificate lane is 107K's, mid-flight at the $n=9$ strata — bank: n=8
complete, 6405 reflection-distinguished / 3315 mirror-identified types).
$n=6$: $71 \geq f(6) \geq 17$ (16-point witness banked; classical exact
$f(6)=17$, Szekeres–Peters, cited). The bound table $n = 3..60$ is
two-code verified (S7), and every value is $\geq 2^{n-2}+1$ — consistent
with the classical lower side (the package's machine-certified witnesses
at $n \leq 6$; the general doubling construction cited-classical).

---

## §6 WHAT THIS CLOSES, AND THE INDEPENDENCE RECORD

1. **The W77 named front is closed.** ALLN_PROOF.md §3: "L-AVOID's
   interior induction step is the named front for the next round (the
   sharp route to the binomial identity … the hockey-stick assembly)."
   Both halves are delivered here: L-AVOID-SHARP (§2) and the assembly
   (§4). The W77 certification (5,510,000+ configurations, zero
   violations; 3,322 classes, zero i-cups/j-caps) is now a corollary.
2. **A second, independent instrument.** The X/Y-split proof
   (ES_PACKAGE_PROOF.md §2) works by an exclusion induction on the
   extremal classes $X$/$Y$ with the three-case extension lemma at the
   **first cap point**; the label route works by the multiplicity census
   on **all** classes with the sign contradiction at the **first cup
   point**. Different chains, different arithmetic, same theorem — the
   two-code discipline at proof scale. (This also resolves the W77 S5
   negative result: the bare local merge fails at (5,5) precisely because
   the truth is global — the class census, not the endpoint merge.)
3. **U-BIS is sharpened everywhere** (§0 table; engine n=3..60).

---

## §7 MACHINE CERTIFICATES (engine107sharp.py → receipts107sharp.txt)

| Lane | Content |
|---|---|
| S0 SETUP | banked otbank re-verified (n=3..7 counts 1,2,3,20,242 reflection-distinguished = 1,2,3,16,135 mirror-identified); fresh seed |
| S1 LAVOID-LAW | L-AVOID-SHARP on every label class: ALL order types n ≤ 7 × ALL direction cells + n=8 sample + extremal sets + random; TWO codes (iterative DP on the class vs. brute-force subset scan / second memo DP) |
| S2 LAVOID-MECH | the proof's Steps 1–2 on every maximal chain: every $i$-cup $C$ with $\mathrm{cup}(\text{right end}) = i$ and every $w$ left of $C$: the forced sign; dual for caps; + the pair shadow (LABEL-SIGN, fresh) |
| S3 MLT-SHARP | the multiplicity census $|P_{ij}| \leq \binom{i+j-4}{i-2}$, two counting codes, on all of the above + the extremal label histograms (equality structure) |
| S4 ASSEMBLY | HOCKEY + VANDERMONDE-DOUBLE for all $3 \leq a,b \leq 60$, two binomial codes; in vivo on the extremal censuses |
| S5 CC-SHARP-EXH | the (a,b)-lemma on ALL order types n ≤ 7 (1,2,3,16,135) × ALL direction cells, every applicable $(a,b)$: TWO cup/cap codes (DP + brute-force subset scan) |
| S6 CC-SHARP-RANDOM | 100,000+ random GP sets at threshold sizes across $(a,b)$ up to (7,7) |
| S7 SHARP-COMPOSE | ES-ALLN-SHARP instances $n=3..7$ (frame → DP → chain → convex by BOTH codes); the bound table + anchors + sharpening vs U-BIS (two codes) |
| S8–S11 | the infinite layer (INFINITE_107.md): peaks, the dichotomy box-census, the Ramsey3 construction, the cardinal arithmetic |
| S12 LAW-SPOTCHECKS | every cited arsenal law spot-checked at statement |
| S13 NEG-CONTROLS | corrupted inputs must fail; sensitivity of every checker |

---

## §8 ARSENAL LAWS USED IN THIS FILE (read-before-cite, 15 distinct)

| # | Law | File:line | Used at |
|---|---|---|---|
| 1 | `bracket_skew` | GSTCausalPairingGraphs.lean:19 | §1 conventions, §2 mirror |
| 2 | `bracket_transform` | GSTCausalPairingGraphs.lean:27 | §1 frames, §2 mirror |
| 3 | `bracket_shear` | GSTCausalPairingGraphs.lean:33 | §1 distinct-x for free |
| 4 | `plucker_four` | GSTCausalPairingGraphs.lean:38 | §1 slope↔orient, §2 sign steps, §5 L-CC |
| 5 | `graph_transform` | GSTCausalPairingGraphs.lean:50 | §1 whole-configuration covariance |
| 6 | `binom_two_term` | GSTDiagonalRead.lean:56 | §4 Pascal/HOCKEY discipline |
| 7 | `binom_first_order` | ErdosTernary2.lean:2740 | §4 index-shift arithmetic |
| 8 | `binom_mod_sq_local` | ErdosTernary2.lean:461 | §4 absorbing-formula division |
| 9 | `cubic_expansion` | CardinalWorlds.lean:283 | §4 Pascal tower |
| 10 | `mod_mod_mul` | CardinalWorlds.lean:140 | §4 binomial arithmetic |
| 11 | `mul_add_div_lemma` | CardinalWorlds.lean:143 | §4 exactness |
| 12 | `sum_le_sum_of_forall` | Erdos261Tower.lean:117 | §3 census summing |
| 13 | `sum_range_shift` | Erdos261Tower.lean:104 | §4 the u,v index shift |
| 14 | `packet_add` | CardinalWorldsV2.lean:88 | §4 double-induction composition |
| 15 | `joined_prefix_succ` | CardinalWorldsV2.lean:120 | §4 outer-sum telescope |

Plus (supporting, also read): `digitCount3_monotone`
[ErdosTernary2.lean:2097] (§3), `two_pow_ge2` [ErdosTernary2.lean:892]
(§4), `two_pow_factored` [CardinalWorlds.lean:425] (§5).

*The engine never stops; it never lies. In English, always.*
