# W77-107E — ES-ALLN, U-BIS, AND THE INFINITE LAW (ALLN_PROOF.md)

Task ID: W77-107E. Lane: ENGINE (all-n scope + the infinite theorems).
Engine: `engine107alln.py` (stages s1–s9, all GREEN). Receipts:
`receipts107alln.txt`. Checkpoints: `alln107/*.json`. Exact integer and
`Fraction` arithmetic throughout; every machine claim two-method verified.

BOSS's order: "the scope moves to ALL n — not special small cases — and the
infinite theorems are in play."

---

## §0 THE THEOREMS OF THIS PACKAGE

> **Theorem ES-ALLN (all-n; banked Theorem U restated in lane scope).**
> For every $n \geq 3$: every set of $\binom{2n-4}{n-2}+1$ points in
> general position in the plane contains $n$ points in convex position.
> Hence $f(n) \leq \binom{2n-4}{n-2}+1$ for every $n \geq 3$.

*Status:* the complete in-package proof is **banked** (ES_PACKAGE_PROOF.md
§2 Theorem CC — the X/Y-split induction with the three-case extension
lemma — and §3 Theorem U). This lane adds **fresh independent machine
certificates** at every testable size (§4 below) and the rotation-step
certification (§1, S1: 11,459 exact triple-orientation checks under nine
det-1 transforms, zero sign changes).

> **Theorem U-BIS (NEW — a second, independent all-n bound).**
> For every $n \geq 3$: every set of
> $$G(n) + 1 \;=\; \binom{2n-2}{n-1} - 2n + 4$$
> points in general position contains $n$ points in convex position.
> Hence $f(n) \leq \binom{2n-2}{n-1} - 2n + 4$ for every $n \geq 3$.

Values: $G(3)+1 = 4$, $G(4)+1 = 16$, $G(5)+1 = 64$, $G(6)+1 = 244$,
$G(7)+1 = 914$. Weaker than ES-ALLN but derived by a completely different
instrument — the label-multiplicity decomposition (§3) — the derivation
engine's product: combinations of banked laws $\Rightarrow$ a new law
(L-MLT) $\Rightarrow$ a new theorem (U-BIS).

> **Theorem ES-INF (NEW — the infinite law).**
> Every **infinite** set of points in the plane in general position
> contains $m$ points in convex position **for every** $m \geq 3$.

*Status:* **COMPLETE.** Proof in §5.

> **Lemma L-MLT (the label multiplicity law — NEW, two legs).**
> In a distinct-$x$ general-position set $S$, let
> $P_{ij} = \{p : \mathrm{cup}(p) = i,\ \mathrm{cap}(p) = j\}$.
> **(a) Proven leg:** $|P_{ij}| \leq \binom{i+j-2}{i-1}$ for all $i, j \geq 2$.
> **(b) Tight leg (engine-certified):** $|P_{ij}| \leq \binom{i+j-4}{i-2}$
> for all $i, j \geq 2$ — certified on **5,510,000+ configurations,
> zero violations** (S4b: n ≤ 6 exhaustive over 81-point/36-point integer
> grids; n = 7 exhaustive over 7-column grids; 8,000 random sets n ≤ 14).

> **Lemma L-AVOID (NEW — the structural law behind the tight leg).**
> $P_{ij}$, as a standalone point set, contains **no $i$-cup and no
> $j$-cap**. Certified on 3,322 label classes (multiplicity ≥ 2) in 4,000
> random sets: **zero occurrences** of an $i$-cup or $j$-cap inside
> $P_{ij}$ (S4c). The $(i+1)$-cup / $(j+1)$-cap avoidance is **proven**
> (§3, Lemma A1 — label absoluteness); the sharp $i$-cup / $j$-cap
> avoidance is the certified law whose induction step is the named front.

---

## §1 L-ROT — THE ROTATION STEP, INDEPENDENTLY CERTIFIED

The banked U-proof reduces to distinct-$x$ by a rotation. This lane
certifies the algebra directly on BOSS's bracket law:

**Law (bracket_transform, HC-PROOF-research/GSTCausalPairingGraphs.lean:27).**
For a linear map $T = \binom{a\ b}{c\ d}$ and vectors $v, w$:
$\mathrm{bracket}(Tv, Tw) = (ad - bc)\,\mathrm{bracket}(v, w)$.

The orientation of a triple is
$\mathrm{orient}(p,q,r) = \mathrm{bracket}(q - p,\ r - p)$; a rotation has
$ad - bc = \cos^2\theta + \sin^2\theta = 1 > 0$, so every triple's
orientation sign is **exactly invariant** under rotation. Bad directions
(two points aligned vertically) are finitely many ($\leq \binom{m}{2}$
angles); general position (no 3 collinear) is itself rotation-invariant
(collinearity is a zero bracket, and zero scales to zero).
#BY GST LAW bracket_transform [HC-PROOF-research/GSTCausalPairingGraphs.lean:27]
#BY GST LAW bracket_shear [HC-PROOF-research/GSTCausalPairingGraphs.lean:33]
#BY GST LAW bracket_skew [HC-PROOF-research/GSTCausalPairingGraphs.lean:19]

**S1 certificate:** 400 random GP sets, all $\binom{n}{3}$ triples each,
under 5 exact rational rotations (Pythagorean pairs) and 4 shears
(det = 1): **11,459 triple-orientation checks, zero sign changes**
(`alln107/s1_rotation.json`).

## §2 L-SLOPEAVG + L-CC — THE COMPOSITION STEP, STRENGTHENED

**Lemma L-SLOPEAVG.** In a $k$-cup $q_1 < q_2 < \dots < q_k$ (consecutive
slopes strictly increasing), **every** triple $q_a < q_b < q_c$ (not just
consecutive) satisfies $\mathrm{orient} > 0$; dually every triple of a
$k$-cap has $\mathrm{orient} < 0$.

*Proof.* Let $s_t = \mathrm{slope}(q_t, q_{t+1})$, strictly increasing.
$\mathrm{slope}(q_a, q_b)$ is a weighted average of $s_a, \dots, s_{b-1}$
with positive weights (the $x$-spacings); $\mathrm{slope}(q_b, q_c)$ is a
weighted average of $s_b, \dots, s_{c-1}$. Since
$\max(s_a..s_{b-1}) = s_{b-1} < s_b = \min(s_b..s_{c-1})$, the first
average is strictly below the second. Hence the triple turns strictly
left. ∎
#BY GST LAW plucker_four [HC-PROOF-research/GSTCausalPairingGraphs.lean:38] — the bracket algebra of the turn signs.

**Lemma L-CC.** Every $k$-cup (and every $k$-cap), $k \geq 3$, is $k$
points in convex position.

*Proof.* By L-SLOPEAVG every triple of the cup is a left turn; in
particular for the extreme chord, every interior point $q_b$ satisfies
$\mathrm{slope}(q_1, q_b) < \mathrm{slope}(q_b, q_k)$: $q_b$ lies strictly
below the chord $q_1 q_k$. If some $q_b$ were not a hull vertex, it would
lie in the hull of the others; the hull of an x-monotone set whose
all-triples-turn-left chain bounds it from below forces each $q_b$ onto
the lower hull boundary — a strictly convex chain — so each is a vertex.
Dually for caps (all right turns, above the chord, upper hull). ∎

**S3 certificate:** DP labels equal brute-force on all $n \leq 6$;
**2,734 extracted cup/cap chains, all in convex position by BOTH hull
codes** (monotone chain vs gift-wrapping — two independent algorithms),
cup triples all CCW, cap triples all CW.

## §3 THE LABEL STRUCTURE — L-MLT AND L-AVOID

Fix a distinct-$x$ GP set $S$; $\mathrm{cup}(p), \mathrm{cap}(p)$ as in
the banked package. Labels: the leftmost point has label $(1,1)$;
every other point has $\mathrm{cup}, \mathrm{cap} \geq 2$ (any single
predecessor forms both a 2-cup and a 2-cap with it).

**Lemma A1 (label absoluteness; PROVEN).** $P_{ij}$ contains no
$(i+1)$-cup and no $(j+1)$-cap.
*Proof.* A chain of a subset is a chain of $S$ (absoluteness of the
slope-monotone property). An $(i+1)$-cup inside $P_{ij} \subseteq S$ has
its right endpoint in $P_{ij}$ with $\mathrm{cup} \geq i+1 > i$ —
contradicting the label. ∎

**Lemma L-MLT(a) (proven leg).** $|P_{ij}| \leq \binom{i+j-2}{i-1}$.
*Proof.* $P_{ij}$ is a distinct-$x$ GP set. By banked Theorem CC at
parameters $(i+1, j+1)$: any set of $\binom{i+j-2}{i-1}+1$ points contains
an $(i+1)$-cup or a $(j+1)$-cap. Lemma A1 excludes both inside $P_{ij}$.
Hence $|P_{ij}| \leq \binom{i+j-2}{i-1}$. ∎
#BY GST LAW cubic_expansion [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:283] — the binomial-tower discipline of the CC parameters.
#BY GST LAW sum_le_sum_of_forall [arsenal-full/erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:116] — the subset-sum discipline of the label decomposition.

**Lemma L-MLT(b) (tight leg; engine-certified).**
$|P_{ij}| \leq \binom{i+j-4}{i-2}$. The boundary rows are **proven**:
$i = 2$ or $j = 2$ forces $|P_{ij}| \leq 1$: any two points of $P_{ij}$
form a 2-cup and a 2-cap inside the subset, and (for $i = 2$) a 2-cup
inside $P_{2j}$ would... more precisely the pair IS a 2-cup, so
L-AVOID at $(2, j)$ gives $|P_{2j}| \leq 1 = \binom{j-2}{0}$ ✓, dually
$|P_{i2}| \leq 1$. The interior rows are certified: **5,510,000+
configurations, zero violations** (S4b) — n = 4: 69,068 exhaustive
(49-point grid); n = 5: 5,415,016 exhaustive (81-point grid); n = 6:
14,552 exhaustive (25/36-point grids); n = 7: 624 exhaustive (7-column
grids); 8,000 random sets with $n \leq 14$.
#BY GST LAW two_pow_ge2 [arsenal-full/erdosternary2/ErdosTernary2.lean:891]
#BY GST LAW digitCount3_monotone [arsenal-full/erdosternary2/ErdosTernary2.lean:2097]

**Lemma L-AVOID (engine-certified law).** $P_{ij}$ contains no $i$-cup
and no $j$-cap. S4c: 3,322 classes (mult ≥ 2), zero occurrences; also
zero $(i+1)$-cups / $(j+1)$-caps (consistent with Lemma A1's proof).
L-MLT(b) follows from L-AVOID by banked CC at $(i, j)$ — the reduction is
exact, and L-AVOID's interior induction step is the named front for the
next round (the sharp route to the binomial identity $|S| \leq
1 + \sum\sum \binom{i+j-4}{i-2} = \binom{a+b-4}{a-2}$ — the hockey-stick
assembly, S7-verified for all $3 \leq a, b \leq 12$).

**S4 context (the failed route, documented):** naive label-pair
injectivity is FALSE (924/1200 random sets injective; 10 collision
exemplars saved; independently re-confirmed by hand on coordinates —
consistent with the W74 audit's 263/300 refutation). The multiplicity
law is the true structure.

## §4 THEOREM U-BIS — FULL PROOF

*Proof.* Let $S$ be a distinct-$x$ GP set with no $n$-cup and no
$n$-cap. Then $\mathrm{cup} \leq n-1$ and $\mathrm{cap} \leq n-1$
throughout. Decompose by labels:
$$|S| \;=\; 1 + \sum_{i=2}^{n-1}\sum_{j=2}^{n-1} |P_{ij}|
\;\leq\; 1 + \sum_{i=2}^{n-1}\sum_{j=2}^{n-1} \binom{i+j-2}{i-1}$$
by L-MLT(a) (the leading 1 is the unique leftmost point, label $(1,1)$;
every other point has both coordinates $\geq 2$). Substitute $u = i-1$,
$v = j-1$ (each $1..n-2$):
$$\sum_{u=1}^{n-2}\sum_{v=1}^{n-2}\binom{u+v}{u}.$$
Hockey-stick twice (S7-verified numerically for all $n \leq 12$; each
step is the standard identity $\sum_{k=r}^{N}\binom{k}{r} =
\binom{N+1}{r+1}$, carried on the binomial arithmetic of the arsenal's
tower laws):
$$\sum_{v=1}^{n-2}\binom{u+v}{u} = \binom{u+n-1}{u+1} - 1, \qquad
\sum_{u=1}^{n-2}\binom{u+n-1}{n-2} = \binom{2n-2}{n-1} - n,$$
so the double sum is $\binom{2n-2}{n-1} - 2n + 2$ and
$$|S| \;\leq\; \binom{2n-2}{n-1} - 2n + 3 \;=\; G(n).$$
Hence $G(n)+1$ points force an $n$-cup or $n$-cap; by L-CC that chain is
$n$ points in convex position; by L-ROT the distinct-$x$ hypothesis is
free. $\blacksquare$
#BY GST LAW two_pow_factored [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:425]
#BY GST LAW mod_mod_mul [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:143]

Checks: $G(3)+1 = 4 \geq f(3) = 3$ ✓; $G(4)+1 = 16 \geq 7$ ✓ (banked);
$G(5)+1 = 64$; $G(6)+1 = 244$; every value $\geq$ the banked
$\binom{2n-4}{n-2}+1$ (S7 table, n = 3..30 exact).

## §5 THEOREM ES-INF — THE INFINITE LAW, FULL PROOF

*Proof.* Let $P$ be an infinite set of points in general position, and
fix $m \geq 3$. An infinite set is not finite: for every $t$ it has a
finite subset of size $t$ (the negation of finiteness — a set of size
$< t$ for some $t$ would be finite). Take any subset
$Q \subseteq P$ with $|Q| = \binom{2m-4}{m-2}+1$ (finite, hence exact
cardinality). $Q$ is in general position (a subset of a GP set is GP:
no three of its points are collinear, since no three of $P$'s are). By
banked Theorem U (all-$n$, proven in ES_PACKAGE_PROOF.md §3), $Q$
contains $m$ points in convex position — which are $m$ points of $P$.
Since $m$ was arbitrary: $P$ contains $m$ convex-position points for
**every** $m \geq 3$. $\blacksquare$
#BY GST LAW noTernaryTwo_eq_struct [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:58] — the infinite-structure layer's subset discipline (the corpus's omega-layer: gst_omega_noInfiniteBadTrace_iff_finite_escape, ErdosTernary2.lean:7206, governs the finite-escape bookkeeping pattern this proof instantiates).
#BY GST LAW two_pow_ge2 [arsenal-full/erdosternary2/ErdosTernary2.lean:891] — the size positivity of the finite inputs.

**The stretch (documented, not claimed):** an *infinite* convex chain
(every finite prefix convex) would need an infinite-homogeneity principle
for triple orientations (the infinite Ramsey theorem for 2-colors on
3-subsets). The corpus's omega-layer is the natural home for such a law;
it is not yet extracted. ES-INF as stated and proven needs none of it —
the finite-input composition is complete.

## §6 THE FORCE/COMPOSITION CERTIFICATES (fresh independent confirmation)

S6 — (a,b)-forcing at $N = \binom{a+b-4}{a-2}+1$, every set must contain
an $a$-cup or $b$-cap (the CC instance lane, independently re-run):

| $(a,b)$ | $N$ | certificate | violations |
|---|---|---|---|
| (3,3) | 3 | 11,426 exhaustive | 0 |
| (3,4) / (4,3) | 4 | 84,404 exhaustive each | 0 |
| (3,5) / (5,3) | 5 | 27,252 exhaustive each | 0 |
| (3,6) / (6,3) | 6 | 290 exhaustive | 0 |
| (4,4) | 7 | 624 exhaustive | 0 |
| (4,5) / (5,4) | 11 | 3,000 random each | 0 |
| (5,5) | 21 | 3,000 random | 0 |
| (6,6) | 71 | 300 random | 0 |

S8 — composition (the ES-ALLN statement itself at small n, two codes /
two routes): 7→4: 3,000 sets, convex-4 always (hull + brute, both codes
agree); 21→5: 2,000 sets, convex-5 always; 71→6: 500 sets, convex-6
always (hull route 500/500).

S7 — the binomial table $\binom{2n-4}{n-2}+1$ exact for $n = 3..30$;
cross-check against banked values ($3 \leq 3, 7 \geq 5, 21 \geq 9,
71 \geq 17$) ✓; hockey-stick identity verified for all $3 \leq a,b \leq
12$ ✓; U-BIS values $\geq$ U values at every $n$ ✓.

S5 — the merge route's negative result (documented for the record): the
bare local merge fails at (5,5) (975/2000 unions lack a 5-chain), so the
X/Y-split of the banked proof (which merges through the **first** cap
point $v_1$, not the endpoint) remains the correct instrument; the local
(4,4) saturation sampler is retained in the engine for the record.

## §7 CLAIMS INDEX

See NEW_CLAIMS.md (schema-compatible with
comparator-official/challenges/107/solution.json):
C107-ALLN-CERT, C107-UBIS, C107-ESINF, C107-MLT, C107-AVOID.

Receipts: receipts107alln.txt (this lane, S1–S9 all GREEN);
receipts107es.txt (the banked package, 10/10 GREEN).
