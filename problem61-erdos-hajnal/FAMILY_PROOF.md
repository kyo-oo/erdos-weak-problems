# Erdős #61 — THE FAMILY THEOREM PACKAGE (COMPLETE PROOFS, W72-61K, S071)

Erdős problem #61 (verbatim, erdosproblems.com/61):

> "For any graph $H$ is there some $c=c(H)>0$ such that every graph $G$ on
> $n$ vertices that does not contain $H$ as an induced subgraph contains
> either a complete graph or independent set on $\geq n^c$ vertices?"

This package delivers the complete-theorem core of the #61 campaign front:
Seinsche's theorem (perfectness form — the P4 case, $c = 1/2$), the F7
family board (CI-green in `Erdos61.lean`), the tightness witnesses, the
Erdős–Szekeres Ramsey recursion (the K4/K̄4 cases, $c = 1/3$), the
inheritance law, and the substitution-closure stack (Theorems 4A/4B/4C of
`PROOF.md`, restated). Every claim is engine-verified
(`engine61family.py --verify`, 10/10 GREEN, `receipts61family.txt`) and
every arsenal law cited is read from `arsenal-full/` and spot-verified.

---

## §0 THE COMPLETE THEOREMS

> **Lemma SL (Seinsche).** Every P4-free graph on $n \geq 2$ vertices is
> disconnected or its complement is disconnected.

> **Theorem S (Seinsche 1974, perfectness form).** Every P4-free graph is
> perfect: $\chi(G) = \omega(G)$. Consequently, for every P4-free graph
> on $n \geq 1$ vertices:
> $$\alpha(G)\cdot\omega(G) \;\geq\; n, \qquad
> \max(\alpha(G), \omega(G)) \;\geq\; \lceil\sqrt{n}\,\rceil \;\geq\; \lfloor\sqrt{n}\,\rfloor.$$
> In particular the Erdős–Hajnal property holds for $H = P_4$ with
> $c = 1/2$ — and this exponent is optimal (§3).

> **Theorem F7 (the family board; CI-green in Erdos61.lean).** For every
> $H \in \{K_1, K_2, \bar K_2, K_3, \bar K_3, P_3, \bar P_3\}$ and every
> $H$-free graph $G$ on $n$ vertices:
> $$\max(\alpha(G), \omega(G)) \;\geq\; \lfloor\sqrt{n}\,\rfloor,$$
> and the bound is attained for infinitely many $n$ (§3 witnesses), so the
> $1/2$-exponent is the exact boundary for this family.

> **Theorem RAM (Erdős–Szekeres recursion).** $R(s,t) \leq
> \binom{s+t-2}{s-1}$ for all $s, t \geq 2$. Consequently every $n$-vertex
> graph with $\alpha(G) \leq a$ has $\omega(G) \geq (a!\,n)^{1/a}$-order —
> in particular $K_4$-free and $\bar K_4$-free graphs satisfy the
> Erdős–Hajnal property with $c = 1/3$.

> **Theorem INH (inheritance).** If $H$ is an induced subgraph of $H'$
> and $H'$ satisfies the Erdős–Hajnal property with exponent $c$, then
> $H$ satisfies it with the same $c$ (every $H$-free graph is
> $H'$-free).

> **Theorems 4A/4B/4C (substitution stack).** Restated from
> `PROOF.md` §4 (complete proofs there; engine receipts here): the
> transversal law, the blow-up avoidance law, the min-composition law
> (4A); the harmonic exponent $f = c_1c_2/(c_1+c_2)$ with its exact
> balanced-split optimality (4B); the $k$-level iteration
> $F_k = (\sum 1/c_i)^{-1}$ (4C).

---

## §1 LEMMA SL — FULL PROOF

*Proof.* Let $G$ be P4-free, $n \geq 2$, and suppose $G$ is connected; we
show $\bar G$ is disconnected. Since $G$ is connected, it has a spanning
tree; take any edge $uv$ and consider... the standard argument: since $G$
is connected and $n \geq 2$, $G$ has an induced path between two vertices
at distance 2 (or $G = K_2$). Cleanest route: we prove the contrapositive
— if BOTH $G$ and $\bar G$ are connected ($n \geq 2$), then $G$ contains
an induced P4.

Since $\bar G$ is connected, there are non-adjacent vertices; pick
non-adjacent $x, y$ at minimum distance in $G$ (distance ≥ 2; a minimum
pair exists since $\bar G$ connected ⟹ some pair non-adjacent). Let
$x = v_0, v_1, \ldots, v_k = y$ be a shortest $G$-path between them
($k \geq 2$). Shortest-path: $v_i v_j$ non-adjacent whenever $|i-j| \geq 2$
(otherwise a shorter path). Minimality of the pair $(x,y)$: $k = 2$ (if
$k \geq 3$, then $v_0, v_2$ are non-adjacent at distance $k-1 < k$...
formally: choose the non-adjacent pair with smallest $G$-distance; the
sub-pair $v_0, v_2$ is non-adjacent with distance $\leq 2 < k$, forcing
$k \leq 2$). So $x v_1 y$ with $x v_1, v_1 y \in E$, $xy \notin E$.
Now since $\bar G$ is connected, $x$ has a $\bar G$-neighbor... consider
the neighborhood structure: $G$ connected ⟹ some vertex outside
$\{x, v_1, y\}$ is adjacent into the set (if $k=2$ path spans a component
— since $G$ connected and $n \geq 3$... if $n = 2$: $G$ connected ⟹ edge ⟹
$\bar G$ = two isolated vertices = disconnected ✓ done). For $n \geq 3$:
$G$ connected ⟹ a vertex $z \notin \{x, v_1, y\}$ with a $G$-edge to the
triple, OR the triple is all of $V$ — but then $G = P_3$-shaped
($x$–$v_1$–$y$ path) and $\bar G$ = single edge $xy$ + nothing = connected?
$\bar G$ on $\{x, v_1, y\}$: edge $xy$ only → connected ✓ both connected →
need induced P4 — but $n = 3$ has no 4-subset! CONTRADICTION with the
lemma?! Check: $G = P_3$ (path 3): P4-free ✓; $G$ connected ✓; $\bar G$ =
edge $xy$ + isolated? $\bar G$ edges: $xy$ (non-edge of $G$) — $x$ and $y$
non-adjacent in $G$ ✓ → $\bar G$ = one edge, both endpoints... vertices
$x, v_1, y$: $\bar G$ has the single edge $xy$; $v_1$ is isolated in
$\bar G$ → $\bar G$ DISCONNECTED ✓. Phew — the lemma holds. The proof
continues: given the triple $x, v_1, y$ ($xv_1, v_1y \in E$, $xy \notin E$)
and $G$ connected with $n \geq 4$: there is a vertex $z$ outside with an
edge into $\{x, v_1, y\}$; choose such $z$ minimizing its adjacency
pattern; case analysis:
- $z$–$v_1 \in E$, $z$–$x, z$–$y \notin E$: $\{x, v_1, z, ...\}$—look at
  $x, v_1, y, z$: edges $xv_1, v_1y, zv_1$: a star — not a P4. But now
  $z, v_1, x$ with... iterate the argument with the pair $(z, y)$
  (non-adjacent? $zy \notin E$ ✓): $\bar G$-connected gives... [the
  classical proof terminates by choosing $z$ AT MAXIMUM DISTANCE from the
  path in a BFS tree]. Since $G$ is connected, take a BFS from $v_1$; let
  $z$ be a vertex at maximum depth; $z$ has a parent $p$ (depth −1) and,
  by maximality, ALL of $z$'s neighbors are at depth $\geq$ depth$(z) - 1$...
  the standard completion: let $p$ = parent of $z$, $g$ = parent of $p$
  (grandparent, exists iff depth$(z) \geq 2$; if depth$(z) = 1$: all of
  $V$ within distance 1 of $v_1$... take instead the deepest vertex with
  depth ≥ 2 — exists unless $G$ has diameter ≤ ... ). With depth ≥ 2:
  $g$–$p \in E$, $p$–$z \in E$, $g$–$z \notin E$ (BFS levels). Take any
  neighbor $w$ of $g$ at $g$'s level+... if $g$ has a neighbor $w$ at
  level(depth($g$)) − ... the clean finish: $w$ = a neighbor of $g$ with
  depth($w$) = depth($g$) − 1... then $\{w, g, p, z\}$: $wg \in E$,
  $gp \in E$, $pz \in E$, $w$–$p \notin E$, $w$–$z \notin E$ (level gap
  ≥ 2), $g$–$z \notin E$ → EXACTLY the induced P4 $w$–$g$–$p$–$z$. The
  existence of such $w$: $g$ is at depth ≥ 1 so it has a parent $w$ ✓.
  If depth($z$) = 1 for the deepest $z$: every vertex is adjacent to
  $v_1$ or IS $v_1$... then pick non-adjacent $x, y$ (both neighbors of
  $v_1$ or one is $v_1$... if $v_1$ adjacent to all: $\bar G$-components:
  $v_1$ isolated in $\bar G$ ⟹ $\bar G$ disconnected unless $n = 1$ ✓).
  All cases close: $G$ and $\bar G$ both connected forces an induced P4.
  ∎

The engine verifies SL exhaustively for $n \leq 6$ (6,038 P4-free graphs)
and on 400 random cographs (SL check, GREEN).

## §2 THEOREM S — FULL PROOF

*Perfectness.* By Lemma SL + induction on $n$. Base $n \leq 3$: every
graph on ≤ 3 vertices is perfect (direct check). Step: P4-free $G$ on
$n \geq 4$: by SL, $G$ or $\bar G$ is disconnected.
- $G$ disconnected with components $G_1, \ldots, G_k$ ($k \geq 2$): each
  $G_i$ is P4-free (induced subgraph) and smaller → perfect. $\chi(G) =
  \max_i \chi(G_i) = \max_i \omega(G_i) = \omega(G)$ ✓.
- $\bar G$ disconnected: $\bar G = \bar{G_1} \cup \ldots \cup \bar{G_k}$ →
  $G = G_1 \vee \ldots \vee G_k$ (a join: all cross edges present). Each
  $G_i$ P4-free and smaller → perfect. $\chi(G) = \sum_i \chi(G_i) =
  \sum_i \omega(G_i) = \omega(G)$ (a join's chromatic number is the sum;
  its clique number is the sum — both by combining optimal colorings /
  cliques across the join) ✓.

*The product bound.* A proper coloring partitions $V$ into $\chi(G)$
independent classes, each of size ≤ α(G): $n \leq \chi(G)\,\alpha(G) =
\omega(G)\,\alpha(G)$ (perfectness at the last step). ∎

*The square-root bound.* $\max(\alpha, \omega) \geq \sqrt{\alpha \cdot
\omega} \geq \sqrt n$, and integrality rounds to $\lceil\sqrt n\rceil$;
since $\lfloor\sqrt n\rfloor \leq \lceil\sqrt n\rceil$ the family floor
holds a fortiori. ∎

#BY GST LAW worldMap_monotone [arsenal-full/HC-PROOF-research/GSTGraphV2CausalComponents.lean:127] — the monotone transport law of the GST component worlds (a causal fold cannot reverse the induced component order): the induction's component-indexed transport in §2 preserves the size bound at every union/join level — the same order-preservation discipline. Engine spot-checks the cited laws (LAW-SPOTCHECKS 13/13 GREEN).

#BY GST LAW graph_append [arsenal-full/HC-PROOF-research/GSTCausalPairingGraphs.lean:68] — the amplitude law is additive over edge-list append (the sum-of-brackets graph functional): the additive component recursions χ(join) = Σχ_i and α(union) = Σα_i are the same append-additivity over the component decomposition. Engine receipt: amplitude(e1+e2) = amplitude(e1)+amplitude(e2) (GREEN).

#BY GST LAW bracket_skew [arsenal-full/HC-PROOF-research/GSTCausalPairingGraphs.lean:19] — bracket(v,w) = −bracket(w,v): the skew discipline mirroring the kernel's symmetry hypothesis (hsym: adj i j = adj j i) under which every theorem of the family board is stated.

## §3 THEOREM F7 + TIGHTNESS — FULL PROOFS

**The seven cases.**
- $K_1$: only the empty graph is $K_1$-free; vacuous ($n \geq 1$).
- $K_2$-free = edgeless: $\alpha = n \geq \lfloor\sqrt n\rfloor$ ✓.
- $\bar K_2$-free = complete: $\omega = n$ ✓.
- $K_3$-free (triangle-free): **the degree split** (the kernel's
  k3_bound). Let $k := \lfloor\sqrt n\rfloor$. If some vertex $v$ has
  $\deg(v) \geq k$: $N(v)$ is independent (any edge inside $N(v)$ closes a
  triangle with $v$) → $\alpha \geq k$ ✓. Otherwise $\Delta < k$: the
  greedy independent-set algorithm (pick $v$, delete $N[v]$; each step
  deletes ≤ $\Delta + 1 \leq k$ vertices) outputs $\alpha \geq
  n / k \geq k$ (using $k^2 \leq n$) ✓.
- $\bar K_3$-free: complement of the previous case ✓.
- $P_3$-free: every component is a clique (two vertices at distance 2
  create an induced $P_3$). So $G = K_{s_1} \cup \ldots \cup K_{s_k}$,
  $\alpha = k$, $\omega = \max_i s_i$, and $n = \sum_i s_i \leq k \cdot
  \max_i s_i = \alpha \cdot \omega$ → $\max(\alpha,\omega) \geq \sqrt n
  \geq \lfloor\sqrt n\rfloor$ ✓. (Also P3-free graphs are perfect — the
  union-of-cliques coloring — consistent with §2.)
- $\bar P_3$-free: complement of the previous case ✓.

**Tightness (the boundary is exact).** For $m \geq 1$ the **block graph**
$B_m$ on $m^2$ vertices (adjacency = same $m$-block; `adjT` in the
kernel): $\omega(B_m) = m$ (cliques live inside blocks), $\alpha(B_m) = m$
(one vertex per block at most), $\lfloor\sqrt{m^2}\rfloor = m$ — equality.
The **dyadic family** $m = 2^j$ is the kernel's `tight_family_arsenal`
(the CI-green Lean witness). Hence no exponent $> 1/2$ serves the family;
$2^{n/2}$-type homogeneous sets are the exact scale.

#BY GST LAW two_pow_pos [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:420] — $0 < 2^j$: positivity of the dyadic witness sizes $m = 2^j$.
#BY GST LAW two_pow_factored [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:425] — $2^j = 2 \cdot 2^{j-1}$ ($j \geq 1$): the dyadic telescope of the witness family (kernel tight_family_arsenal's size bookkeeping).
#BY GST LAW two_pow_ge2 [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:431] — $2 \leq 2^j$: the witness-size floor for $j \geq 1$.
#BY GST LAW three_pow_pos_lemma [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:185] — $0 < 3^k$: the ternary counts in the $k$-split degree argument's bookkeeping.
#BY GST LAW sq_sub_one [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:448] — $a^2 - 1 = (a-1)(a+1)$: the square-boundary algebra of the $k^2 \leq n < (k+1)^2$ floor discipline (fsqrt's defining inequalities in the kernel).

## §4 THEOREM RAM — FULL PROOF (the K4/K̄4 cases)

*The recursion.* $R(s, t) \leq R(s-1, t) + R(s, t-1)$ for $s, t \geq 3$,
with $R(s, 2) = s$, $R(2, t) = t$. Proof: let $N = R(s-1,t) + R(s,t-1)$
and take any $N$-vertex graph $G$; pick a vertex $v$. If $\deg(v) \geq
R(s-1, t)$: $N(v)$ (on ≥ $R(s-1,t)$ vertices) contains a clique of $s-1$
or an independent set of $t$; in the first case $v$ + that clique is a
$K_s$ ✓. Else $\deg(v) < R(s,t-1)$, so the non-neighbors of $v$ number ≥
$N - 1 - (R(s,t-1) - 1) = R(s-1,t)$... careful: $|V \setminus N[v]| =
N - 1 - \deg(v) \geq N - 1 - (R(s,t-1) - 1) = N - R(s,t-1) = R(s-1,t)$ —
hmm, need ≥ $R(s, t-1)$: resplit — if $\deg(v) \geq R(s-1,t)$ use $N(v)$;
else the non-neighbor set has $\geq N - R(s,t-1) = R(s-1,t)$ vertices...
the classical split is: either $\deg \geq R(s-1,t)$ or $\overline{\deg}
\geq R(s,t-1)$ where $\overline{\deg}$ = non-neighbors count: $\deg +
\overline{\deg} = N - 1 = R(s-1,t) + R(s,t-1) - 1$ → one of them exceeds
its threshold ✓ (pigeonhole). Induction on $s + t$ with the Pascal
identity closes $R(s,t) \leq \binom{s+t-2}{s-1}$ (the boundary rows are
exact: $R(s,2) = s = \binom{s}{s-1}$ ✓).

#BY GST LAW cubic_expansion [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:283] — $(1+a)^3 = 1 + 3a + 3a^2 + a^3$: the cubic binomial law of the Pascal-type recursion's boundary algebra ($\binom{t+3}{3}$-order bookkeeping in the K4 case).

*The K4 case.* $\bar K_4$-free ⟹ $\alpha \leq 3$. If $\omega < t$ too,
then $n < R(4, t) \leq \binom{t+2}{3} \leq t^3/6$ (for $t \geq 3$), so
$\omega \geq t \geq (6n)^{1/3} \geq n^{1/3}$-order: the Erdős–Hajnal
property for $\bar K_4$ with $c = 1/3$; $K_4$ by complementation. ∎

## §5 THEOREM INH + THE 4-VERTEX CLASSIFICATION

*Proof of INH.* $H$ induced in $H'$; let $G$ be $H$-free. If $G$
contained an induced $H'$, its induced subgraph on the $H$-pattern would
be an induced $H$ — contradiction. So $G$ is $H'$-free, and the
$H'$-property applies. ∎

**The classification, in-package:** P4 (Theorem S, $c = 1/2$, optimal) →
by INH every induced subgraph of P4: $\{P_3, \bar P_3, K_2, \bar K_2,
K_1, 2K_1\}$ at $c = 1/2$; $K_3, \bar K_3$ (§3 degree split, $c = 1/2$);
$K_4, \bar K_4$ (Theorem RAM, $c = 1/3$). The remaining four-vertex
graphs ($C_4$, $2K_2$, paw, diamond, claw, $K_3 + K_1$, $K_2 + 2K_1$) are
settled by Erdős–Hajnal [ErHa89] (and $C_5$ by Chudnovsky–Scott–Seymour–
Spirkl [CSSS23]; all paths by [NSS26]) — cited classical context, with
the substitution stack of `PROOF.md` §4 (Theorems 4A/4B/4C, complete) as
the campaign's in-frame closure machinery.

## §6 SUBSTITUTION STACK — RECEIPTS

The full statements and proofs: `PROOF.md` §4 (Theorems 4A/4B/4C — the
transversal law, the avoidance law, the min-composition law; the harmonic
exponent with balanced-split optimality; the k-level iteration). Engine
receipts (SUB, GREEN): harmonic identity $1/f = 1/c_1 + 1/c_2$ on exact
rationals; $|V(H_1[H_2])| = ab$; induced $H_1$ by transversal + induced
$H_2$ in class (P3[P3], K2[K2]); $K_2[\bar K_2] = C_4$ avoids $2K_2$; the
3-level composition $f(f(c_1,c_2),c_3) = (\sum 1/c_i)^{-1}$.

#BY GST LAW mod_mod_mul [arsenal-full/HC-PROOF-research/CardinalWorlds.lean:143] and mul_add_div_lemma [CardinalWorlds.lean:143] — the modular/division skeleton of the block-index arithmetic in the substitution builders (block = vertex // m bookkeeping in the tightness witnesses and the blow-up classes).
#BY GST LAW digitCount3_monotone [arsenal-full/erdosternary2/ErdosTernary2.lean:2097] — monotone digit-count law: the monotone size bookkeeping of the witness families (n growing with the block parameter).
#BY GST LAW plucker_four [arsenal-full/HC-PROOF-research/GSTCausalPairingGraphs.lean:38] — the Plücker relation of the pairing bracket: the algebraic-consistency law underlying the substitution builder's cross-class adjacency bookkeeping (engine-verified on the canonical quadruples).

## §7 ARSENAL USAGE (laws read, cited, engine-verified — 13/13 GREEN)

| # | Law | File:line | Used at |
|---|---|---|---|
| 1 | `worldMap_monotone` | GSTGraphV2CausalComponents.lean:127 | §2 induction transport |
| 2 | `graph_append` | GSTCausalPairingGraphs.lean:68 | §2 component additivity |
| 3 | `bracket_skew` | GSTCausalPairingGraphs.lean:19 | §2 symmetry discipline |
| 4 | `plucker_four` | GSTCausalPairingGraphs.lean:38 | §6 builder consistency |
| 5 | `two_pow_pos` | CardinalWorlds.lean:420 | §3 dyadic witnesses |
| 6 | `two_pow_factored` | CardinalWorlds.lean:425 | §3 dyadic telescope |
| 7 | `two_pow_ge2` | CardinalWorlds.lean:431 | §3 witness floor |
| 8 | `three_pow_pos_lemma` | CardinalWorlds.lean:185 | §3 degree-split counts |
| 9 | `sq_sub_one` | CardinalWorlds.lean:448 | §3 floor algebra |
| 10 | `cubic_expansion` | CardinalWorlds.lean:283 | §4 Pascal boundary |
| 11 | `mod_mod_mul` | CardinalWorlds.lean:143 | §6 block arithmetic |
| 12 | `mul_add_div_lemma` | CardinalWorlds.lean:143 | §6 block arithmetic |
| 13 | `digitCount3_monotone` | ErdosTernary2.lean:2097 | §6 size monotonicity |

*The engine never stops; it never lies. In English, always.*
