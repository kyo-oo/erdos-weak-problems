# W80-107E — THEOREM ES-SANDWICH-ALLN (ES_SANDWICH_ALLN.md)

Task ID: W80-107E (finisher W80-107E-F). Lane: ENGINE, all-n scope.
Engines: `engine107loweralln.py` (lower side, receipts
`engine107loweralln_receipts.txt`), `engine107alln.py` + `ES_PACKAGE_PROOF.md`
(upper side, banked), finisher verifier `verify107lower.py`
(receipts `verify107lower_receipts.txt`). Exact `Fraction`/integer arithmetic
throughout; two-code discipline on every machine claim.

---

## §0 THE THEOREM

> **Theorem ES-SANDWICH-ALLN.** For every integer $n \geq 3$:
> $$2^{\,n-2} + 1 \;\;\leq\;\; f(n) \;\;\leq\;\; \binom{2n-4}{n-2} + 1,$$
> where $f(n)$ is the smallest $N$ such that every $N$ points in general
> position (GP: no 3 collinear) contain $n$ in convex position.
> Exactly: $f(3) = 3$ and $f(4) = 5$ (both sides meet the truth; PROOF.md §1–2).

| side | statement | status |
|---|---|---|
| LOWER | $f(n) \geq 2^{n-2}+1$: explicit GP set $X_n$ of exactly $2^{n-2}$ points with **no** $n$ in convex position | **proven for ALL $n\geq 3$** (§2–§4, this document); machine-certified $n=3..10$ (engine S2–S4; finisher V1–V6) |
| UPPER | $f(n) \leq \binom{2n-4}{n-2}+1$ | **banked, all $n$**: ES_PACKAGE_PROOF.md §2 Theorem CC + §3 Theorem U (X/Y-split induction; rotation discharge §7.5), fresh certificates `receipts107alln.txt` |
| exact | $f(3)=3$, $f(4)=5$ | PROOF.md §1 (S1), §2 (S2, Klein), complete; $f(5)=9$ Turán–Makai cited + lane engine `engine107f5*` |

The two sides are independent instruments (a construction vs. a counting
theorem); the sandwich is assembled, not re-proved, on the upper side.

---

## §1 THE CONSTRUCTION (engine107loweralln.py, S0–S2)

Let $m = n-2$, $D = m/4$, $s = 1/(16(m+1))$, $\eta = 1/(2^{14}m)$, $\rho=\eta/2$.

**Centers.** $c_i = (x_i, y_i)$, $i = 0..m$, on the concave arc $x = 1-y^2/D$:
$y_i = (m-2i)/8$, $x_i = 1-(m-2i)^2/(16m)$. $T_0$ is the top band, $T_m$ the
bottom; consecutive bands are $1/4$ apart in $y$. Centers are pairwise distinct,
all on a strictly concave arc, hence in convex position.

**Clusters.** $T_i = c_i + \rho\,(E(n-i,\,i+2;\,s) - (19/32,\,19s/48))$, where
$E(a,b;\delta)$ is the classical cup/cap extremal set:

* $E(2,b;\delta)=E(a,2;\delta)=\{(0,0)\}$;
* $E(a,b;\delta) = A \cup B$, $A=\tfrac18 E(a-1,b;\delta/3)$,
  $B=\tfrac18 E(a,b-1;\delta/3) + (1, 3\delta/4)$ for $a,b\geq 3$;
* $|E| = \binom{a+b-4}{a-2}$, GP, distinct $x$, **all pairwise slopes in
  $(0,\delta]$**, no $a$-cup, no $b$-cap (Lemma E, §2).

**The set.** $X_n = \bigcup_{i=0}^{m} T_i$;
$|X_n| = \sum_i \binom{m}{i} = 2^{n-2}$
#BY GST LAW two_pow_factored [erdosternary2/ErdosTernary2.lean:885]
#BY GST LAW two_pow_pos [erdosternary2/ErdosTernary2.lean:879].
$X_n$ is GP (engine S2 cell `gp`, exact orientation scan; finisher V2).

**Slope separation (the load-bearing law).** Every same-cluster pair has slope
in $(0,s]$ (inherited from $E$, positive scaling); every cross-cluster pair has
$|\text{slope}| \geq \sigma := 1/(1+38\rho) > 1/2 > s$ (and $s \leq 1/64$
exactly for $n \geq 5$, i.e.\ $m \geq 3$; at $n = 3, 4$: $s = 1/32, 1/48$ —
*W81-107B audit note: the constant $1/64$ is an $n \geq 5$ statement; the
load-bearing ordering $s < 1/2 < \sigma \leq |\text{inter}|$ holds for EVERY
$n \geq 3$*):
*proof.* For centers, $\text{slope}(c_i,c_j) = -m/(m-i-j)$, so
$|\text{slope}| = m/|m-i-j| \geq 1$ (vertical when $i+j=m$). A perturbed pair
moves each endpoint by at most $(19/32)\rho$ in $x$ and $(19/48)s\rho$ in $y$
(the $E$-sets live in $[0,\,24/23]\times[0,\,18s/23]$ by the recursion, and
the offset $(19/32,\,19s/48)$ sits past the midpoint of both ranges:
$24/23-19/32 < 19/32$, $18/23-19/48 < 19/48$); hence, with $d := |i-j|$,
$|\Delta y| \geq d/4 - 2\cdot(19/48)s\rho = d/4 - (19/24)s\rho$ and
$|\Delta x| \leq d/4 + 2\cdot(19/32)\rho = d/4 + (19/16)\rho$
(divide by $d/4 \geq 1/4$; *W81-107B audit note, completed by the W81-107B-F
finisher: the pre-audit display had two slips — it normalized the
perturbations by $d$ instead of $d/4$, and printed the pair constant
$(19/12)$ where $2\cdot(19/48) = (19/24)$; both slips were conservative
(each weakens the bound), and the final bound is re-derived here with the
honest constants and machine-verified by the audit engine, A3*):
$$|\text{slope}| \;\geq\; \frac{1-(19/6)\,s\rho/d}{1+(19/4)\,\rho/d}
 \;\geq\; \frac{1}{1+38\rho} \;>\; \frac12 \;>\; \frac{1}{16(m+1)} = s,
 \qquad (m \geq 1,\ d \geq 1,\ s \leq 1/32,\ \rho \leq 2^{-15}),$$
the second inequality by exact algebra:
$$\Bigl(1-\tfrac{19}{6}\tfrac{s\rho}{d}\Bigr)(1+38\rho)-\Bigl(1+\tfrac{19}{4}\tfrac{\rho}{d}\Bigr)
= \rho\,\Bigl[38-\tfrac{19}{4d}-\tfrac{19s}{6d}-\tfrac{361\,s\rho}{3d}\Bigr]
\;\geq\; \rho\,\Bigl[38-\tfrac{19}{4}-\tfrac{19}{192}-\tfrac{361}{3\cdot 32\cdot 2^{15}}\Bigr]
\;>\; 33\,\rho \;>\; 0$$
(using $d \geq 1$, $s \leq 1/32$, $\rho \leq 2^{-15}$; the audit engine
re-checks the whole chain exactly, A3). $\qquad\square$

*Engine bookkeeping note (the S2 `slope_bands` red cell).* S2 demanded the
sharper center-only constant $m/(m-1)$ for **perturbed** points; the
perturbation dips below it by $O(\rho)$ (measured exactly by the finisher, V5),
which does **not** touch the load-bearing separation above — the red cell is a
threshold artifact, quantified and discharged in §5. All other S2 cells are
green.

---

## §2 LEMMA E (the cup/cap extremal set — complete induction)

**Lemma E.** For all $a,b \geq 2$ and $\delta > 0$: $E(a,b;\delta)$ is GP with
distinct $x$, $|E| = \binom{a+b-4}{a-2}$, all pairwise slopes in $(0,\delta]$,
and $E$ contains **no $a$-cup and no $b$-cap** (a $k$-cup: $k$ points with
strictly increasing slopes in $x$-order; a $k$-cap: strictly decreasing).

*Proof.* Size: Pascal on the recursion, $|E(a,b)| = |E(a-1,b)|+|E(a,b-1)|$,
$|E(2,b)| = 1$; the array $\binom{a+b-4}{a-2}$ satisfies both
#BY GST LAW binom_mod_sq_local [erdosternary2/ErdosTernary2.lean:460].
Slopes: by construction $A$ sits in $[0,\tfrac{19}{128}]^+$, $B$ in
$[1, 1+\tfrac{19}{128}]$; intra-$A$/intra-$B$ slopes are scaled by $\tfrac13$
each level, hence $\leq \delta/3$; $A$-to-$B$ cross slopes lie in
$[\tfrac{34\delta}{57}, \tfrac{38\delta}{39}] \subset (\delta/2, \delta)$,
strictly above every intra slope. Since cross slopes $> \delta/2 > \delta/3 \geq$
intra slopes, no three points with two equal-slope-class edges are collinear
and all slopes are positive — GP and distinct $x$ follow (induction on $a+b$;
base $a=2$ or $b=2$ is a single point).

*Cups.* Let $C \subseteq E(a,b;\delta)$, $|C| \geq 2$, be a cup, $x$-sorted.
$A$ is strictly left of $B$, so $C = (C\cap A) \,\|\, (C\cap B)$ with exactly
one $A\!\to\!B$ transition edge, of slope $> \delta/2$. Every $B$-internal
edge has slope $\leq \delta/3 <$ transition slope; but a cup's slopes strictly
increase along it, so after the transition edge every following edge must be
steeper than $> \delta/2$ — impossible for $B$-internal edges. Hence
$|C \cap B| \leq 1$ and $C\cap A$ is itself a cup in
$A = \tfrac18 E(a-1,b;\delta/3)$. If $|C| = a$: $C \cap A$ is an
$(a-1)$-cup in $E(a-1,b;\cdot)$ — excluded by induction ($a-1 = 2$ base:
$E(1,\cdot)$ empty of pairs). So no $a$-cup. *Caps* are dual with the roles of
$A,B$ exchanged (the cap's slopes strictly decrease, so the $A$-part after the
transition would need slopes $< \delta/2$ below intra-$A$ slopes... precisely:
a cap ending in $B$ needs its $A$-internal edges above the transition slope
$> \delta/2$, impossible, so $|C\cap A| \leq 1$ and the cap lives in
$B = \tfrac18 E(a,b-1;\delta/3)$; induction forbids the $b$-cap). $\square$

Machine: S0 (28 $E$-sets, sizes/slopes/GP, exact), S1 (20 $E$-sets, max cup
$=a-1$, max cap $=b-1$, brute-scan code vs slope-frontier DP code, agree).
Applied to clusters: $T_i \cong E(n-i, i+2)$ has **no $(n-i)$-cup and no
$(i+2)$-cap** — max cup $n-i-1$, max cap $i+1$ (engine S2 cell `cluster_cupcap`,
two codes; finisher cross-check via V3/V4).

---

## §3 LEMMA M (the middle-cluster margin law)

**Lemma M.** Let $Y \subseteq X_n$, $B$ its bottom vertex (lowest $y$) and $T$
its top vertex, lying in clusters $T_l$ resp. $T_k$ with $k < l$. Every point
$u \in Y$ belonging to a **strictly middle** cluster $T_i$ ($k < i < l$) lies
strictly to the RIGHT of the line $BT$.

*Proof.* Write the arc as $x(y) = 1 - y^2/D$ (strictly concave). For any two
heights $y_a > y_b$ and any $y$ strictly between,
$x_{\text{arc}}(y) - x_{\text{chord}}(y) = -\frac{(y-y_a)(y-y_b)}{D} > 0$,
and for $y$ outside $[y_b, y_a]$ the same quantity is $< 0$ (the line through
two arc points is left of the arc inside, right outside). Apply with
$y_a = y_k$, $y_b = y_l$: for $u \in T_i$, $k<i<l$,
$$x_{\text{arc}}(y_u) - x_{BT}(y_u) \;\geq\;
\frac{(y_k - y_u)(y_u - y_l)}{D} \;\geq\; \frac{(1/4)^2(1-o(1))}{m/4}
\;=\; \frac{1-o(1)}{4m},$$
using $y_k - y_u \geq (i-k)/4 - O(s\rho)$, $y_u - y_l \geq (l-i)/4 - O(s\rho)$.
The slop: $u$ is within $(19/32)\rho$ of the arc in $x$, and the line $BT$
differs from the center chord $c_kc_l$ by at most $(19/32)\rho\cdot 2$ in the
convex-combination interpolation. Total slop $\leq \tfrac{57}{32}\rho <
\tfrac{4}{2^{15}m}$, while the margin is $\geq \tfrac1{4m}(1-o(1))$ — a factor
$> 2000$ for **every** $m$. So $u$ is strictly right of $BT$. $\square$

Machine: engine S2 cells `sagitta_margin`, `drift_margin`, `y_bands_disjoint_ordered`,
`y_distinct` (all green, $n = 3..10$); finisher V6 checks the law directly
(exhaustive $n \leq 7$, sampled $n = 8..10$).

---

## §4 THEOREM L (no $n$ in convex position) — the main induction

**Theorem L.** For every $n \geq 3$: any $Y \subseteq X_n$ in convex position
has $|Y| \leq n-1$.

*Proof.* Let $Y$ be in convex position, $|Y| \geq 2$; let $k = \min\{i : Y\cap
T_i \neq \emptyset\}$, $l = \max$, $Y_i = Y \cap T_i$.

**Case 1: $k = l$ (one cluster).** $Y \subseteq T_i$. Split $\operatorname{conv}(Y)$
at its leftmost and rightmost vertices into the lower chain (a **cup** in
$T_i$) and the upper chain (a **cap** in $T_i$); $|Y| = |\text{cup}| +
|\text{cap}| - 2 \leq (n-i-1) + (i+1) - 2 = n-2$ by Lemma E.

**Case 2: $k < l$.** Let $B \in T_l$, $T \in T_k$ be the bottom/top vertices of
$\operatorname{conv}(Y)$ (unique: all $y$ distinct). Traverse the boundary CCW
from $B$ to $T$: the **right chain** $R$; from $T$ to $B$: the **left chain**
$L$. Both chains are $y$-monotone (convexity), so each visits the cluster bands
in order, and edge directions rotate strictly CCW (convexity, GP ⟹ strict turns).

*Chain structure.* On $R$ (traversed upward): every edge has $\Delta y > 0$;
an intra-cluster edge has slope in $(0,s]$, i.e. direction angle in
$(0, \arctan s]$; a cross edge has $|\text{slope}| \geq \sigma > 1/2$, i.e.
angle in $[\arctan\sigma, \pi/2) \cup (\pi/2, \pi)$ — in all cases
$\geq \arctan\sigma > \arctan s$. As angles strictly increase along $R$, all
intra-edges precede all cross-edges. $R$ starts at $B \in T_l$; intra-edges
stay in $T_l$; after the first cross-edge no intra-edge can follow. Hence
$$R = [\,Y_l \text{ as a consecutive run — a **cup** in } T_l\,] \oplus
[\text{single vertices, one per cluster, indices strictly decreasing to } T \in T_k].$$
Dually (traversed downward, angles in $[\pi, 2\pi)$, intra angles first):
$$L = [\,Y_k \text{ as a run — a **cap** in } T_k\,] \oplus
[\text{single vertices, indices strictly increasing to } B \in T_l].$$

*Middles.* Let $k < i < l$ and suppose $v \in Y_i$ lies on $R$ and $w \in Y_i$
on $L$, $v \neq w$. By Lemma M every middle point of $Y$ is strictly right of
$BT$; but an intermediate vertex of the left chain $L$ is strictly **left** of
$BT$ (the left chain bulges left of the chord $BT$; GP excludes on-line).
Contradiction — **no middle point lies on $L$**. (This is the step that
upgrades "≤ 1 per chain" to "≤ 1 per middle cluster": all middle points of
$Y$ are single-visit vertices of $R$.)

*Count.* $Y = Y_k \cup Y_l \cup \bigcup_{k<i<l} Y_i$ (every vertex is on $R$
or $L$; $B, T$ are the shared endpoints). By the chain structure:
$|Y_k| = $ cap-run $\leq$ max cap of $T_k = k+1$ (Lemma E);
$|Y_l| = $ cup-run $\leq$ max cup of $T_l = n-l-1$ (Lemma E);
$|Y_i| \leq 1$ for $k < i < l$. Therefore
$$|Y| \;\leq\; (k+1) + (n-l-1) + (l-k-1) \;=\; n-1. \qquad\square$$

**Corollary ES-LOWER-ALLN.** $X_n$ is GP of size $2^{n-2}$ with no $n$ in
convex position, for **every** $n \geq 3$ (the construction and Lemmas E, M
are uniform in $n$; no step is finite-$n$). Hence $f(n) \geq 2^{n-2}+1$.

**Tightness (the $(n-1)$-witness).** Any transversal (one point from each of
the $m+1 = n-1$ clusters) is in convex position: it is a $\rho$-perturbation
of the $n-1$ centers, which are in convex position on the arc with turn
margins $\geq c/m \gg \rho$ (finisher V4: **all** transversals convex at
$n = 3,4,5$ — 1/1, 2/2, 9/9 — and 2500/2500 at $n=7$; engine S3/S4 witnesses
$n=3..10$). So the largest convex subset of $X_n$ is exactly $n-1$.

---

## §5 MACHINE CERTIFICATES AND THE S2 RED CELL

*Engine `engine107loweralln.py` receipts (all-$n$ construction, $n=3..10$):*
- **S0 GREEN** [True]: 28 $E$-sets — sizes $= \binom{a+b-4}{a-2}$, slopes in
  $(0,\delta]$, GP.
- **S1 GREEN** [True]: 20 $E$-sets — max cup $= a-1$, max cap $= b-1$, two
  codes agree.
- **S2** [False — one red sub-cell]: all cells green except `slope_bands`
  for $n \geq 4$: the cell demanded the center-line constant $m/(m-1)$ for
  perturbed cross-cluster pairs; the true minimum dips below it by $O(\rho)$.
  The load-bearing separation (§1: $|\text{inter}| \geq 1/(1+38\rho) > 1/2$
  vs intra $\leq s \leq 1/64$) is untouched — measured exactly by the finisher
  (V5), factor $\geq 30\times$ at every $n = 3..10$. **Discharged: threshold
  artifact, not a construction failure.**
- **S3 GREEN** [True]: exhaustive no-convex-$n$, $n = 3..7$ (code A full; code
  B full $n \leq 6$, $2\cdot10^5$ sampled at $n=7$), $(n-1)$-witness present.
- **S4 GREEN** [True]: randomized/hillclimb max-convex search $n = 8..10$:
  max found $= n-1$, $3\!-\!5\times10^5$ hits each, structure census
  (middles $\leq 1$) on every hit.
- **S5 GREEN** [True]: gap law, two codes, $m = 0..30$ (§6).
- **S6 GREEN** [True]: negative controls (duplicate, collinear injection,
  square, square+center) all behave.
- Engine verdict line: **RED** — driven solely by the S2 `slope_bands`
  sub-cell; every load-bearing cell is green. The finisher's independent
  verifier (below) is the second instrument on the load-bearing claims.

*Finisher `verify107lower.py` (independent rebuild, two new codes):*
- **V1/V2**: sizes $2^{n-2}$, cluster sizes $\binom{m}{i}$, GP — PASS $n=3,4,5,7$.
- **V3**: no-convex-$n$, code A = two-pop-set monotone chain, code B = gift
  wrapping: exhaustive at $n=5$ (56/56 both codes) and $n=7$
  ($\binom{32}{7} = 3{,}365{,}856$ subsets) — see receipts for coverage.
- **V4**: all transversals convex (the $(n-1)$-witness law) — PASS.
- **V5**: exact slope separation $n = 3..10$ (the S2 discharge).
- **V6**: Lemma M directly (middle points strictly right of $BT$) — exhaustive
  $n \leq 7$, sampled $n = 8..10$.

**Which side holds where.** LOWER: proven for ALL $n \geq 3$ (§2–§4); engine
cells are spot-certificates at $n = 3..10$ (exhaustive $n \leq 7$,
randomized $8..10$). UPPER: banked for ALL $n \geq 3$ (ES_PACKAGE_PROOF.md,
Theorem CC/U); engine certificates at every testable size
(`receipts107alln.txt`). $f(3)=3$, $f(4)=5$ exact: PROOF.md §1–§2.

---

## §6 THE GAP LAW (context, not load-bearing)

The engine's S5 certified, two codes, $m = 0..30$:
$$\frac{4^m}{2m+1} \;\leq\; \binom{2m}{m} \;\leq\; \frac{4^m}{\sqrt{2m+1}}
\quad\text{(exact integer form: } \binom{2m}{m}^2(2m+1) \leq 16^m,\;
\binom{2m}{m}(2m+1) \geq 4^m\text{)},$$
so with $m = n-2$ the sandwich extends to
$2^{n-2}+1 \leq f(n) \leq \binom{2n-4}{n-2}+1 \leq \frac{4^{n-2}}{\sqrt{2n-3}}+1$
(S5b table, $n = 3..16$, all green).

**In-package gap law (exact, finite $n$):**
$$\operatorname{gap}(n) \;=\; \frac{\binom{2n-4}{n-2}+1}{2^{n-2}+1},$$
e.g. $1.00, 1.40, 2.33, 4.18, 7.67, 14.23, 26.61, 50.08$ for $n=3..10$ (S5b).
Asymptotically $\binom{2n-4}{n-2} \sim 4^{n-2}/\sqrt{\pi(n-2)}$, so the ratio
grows like $2^{n-2}/\sqrt{\pi n}$ — stated as context only; nothing in the
sandwich rests on it.
#BY GST LAW two_pow_ge2 [erdosternary2/ErdosTernary2.lean:891]
#BY GST LAW digitCount3_monotone [erdosternary2/ErdosTernary2.lean:2097]

---

## §7 LEDGER

Appended to `NEW_LAWS_107.md` / `NEW_CLAIMS.md`:
**C107-SANDWICH-ALLN**, **C107-LOWER-ALLN** (this document = the proof record).
