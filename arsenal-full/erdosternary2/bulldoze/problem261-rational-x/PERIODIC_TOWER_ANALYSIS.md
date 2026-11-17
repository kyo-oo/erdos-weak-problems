# ERDŐS #261 — RATIONAL-x CONTINUUM: THE PERIODIC-TOWER ANALYSIS
## Session 011 wall-sharpening (research note — NOT a kill; scope labels in §6)

The rational-x reading asks: does some **rational** $x$ admit
$2^{\aleph_0}$ representations $x = \sum_{a \in S} a\,2^{-a}$ over distinct
indices? Kill #6 killed the real-x variant (the Tower at irrational
$x^*$). This session maps the rational-x attack surface completely for
the gadget-tower paradigm and proves it DEAD for all periodic towers,
isolating the one surviving loophole (carries).

---

## 1. THE RATIONALITY ENGINE (the new weapon)

**Theorem 1 (AP identity — verified exact).** For $c, d \geq 1$:

$$\sum_{k \geq 0} (c + kd)\,2^{-(c+kd)} \;=\; 2^{-c}\left[\frac{c}{1-q} + \frac{d\,q}{(1-q)^2}\right], \qquad q = 2^{-d},$$

a **rational** number. (Partial sums match the closed form to $< 2^{-90}$
at $c=9, d=24$; the value is $1649267605504/93824981052075$.)
So: gadget towers anchored on an arithmetic progression have rational
total value. This is the ONLY clean rationality source — by the
Fatou-type dichotomy, $\sum_{k \in A} x^k$ ($0/1$ coefficients,
$x$ algebraic, $|x|<1$) is rational **iff** $A$ is eventually periodic.

## 2. THE GADGET SOLUTION SPACE (complete classification)

A **window gadget** at anchor $s$ with spacing $d$: window offsets
$\{1..d-1\}$ partitioned into $(\Pi, J, U)$ — D-side = $\{s\} \cup
(s + \Pi)$, E-side = $(s + J)$, unused = $(s+U)$. Write
$\sigma_X = \sum_{j \in X} 2^{-j}$, $\tau_X = \sum_{j \in X} j\,2^{-j}$.

**Theorem 2 (gadget equation — verified on 200 random triples).**
The gadget is value-balanced **iff**

$$s\,(1 + \sigma_\Pi - \sigma_J) \;=\; \tau_J - \tau_\Pi.$$

**Corollary 2.1 (the Tower is canonical).** At $\Pi = \varnothing$,
$J = \{1..d-1\}$ (full window): $s = 2^d - d - 1$. This is **exactly
Kill #6's exact-halving family** $m_{d-2} = 2^{d} - d - 1$:
$d = 3..11$ gives $4, 11, 26, 57, 120, 247, 502, 1013, 2036$ — the
CI receipts of `Erdos261Tower.lean`, re-derived as one point of the
solution space.

**Corollary 2.2 (the full singleton family, window $\leq 20$ — new
engine).** $\Pi = \varnothing$ with partial $J$:
$s \in \{1, 2, 3, 4, 5, 6, 7, 9, 11, 12, 13, 15, 17, 18, 19, 21, 26,
27, 32, 35, 57, 73, 78, 116, 120, 125, 166, 197, 198, 199, 200, \ldots\}$
(s ≤ 200), with **minimal windows** as low as 5 at $s = 57$, 6 at
$s = 120$, and the consecutive run $197, 198, 199, 200$. The census
family of Kill #6 ($9, 13, 21, 35$) is the subfamily with min-support
$\leq 40$.

**Theorem 3 (finite image).** For fixed spacing $d$, the map
$(\Pi, J) \mapsto s$ has at most $3^{d-1}$ values. An arithmetic
progression of anchors with **fixed** $d$ can host gadgets at only
finitely many of its elements. (Verified: $d = 5$ gives exactly
$\{1, 2, 4, 6, 11, 26\}$.)

## 3. THE FUNDING IMPOSSIBILITY (beyond the boundary)

**Theorem 4 (run-surplus identity — verified exact).** The run
$(s, s+d)$ has mass $R(s,d)$ with

$$R(s,d) - s\,2^{-s} \;=\; 2^{-s}\left[\,2 - (s+d+1)\,2^{1-d}\,\right].$$

The sign flips at exactly $s = 2^{d-1} - d - 1$ ($d = 24$: $s =
16777191$). Beyond it the run **undershoots** the singleton value
$s\,2^{-s}$, and:

**Theorem 5 (funding death — verified exact).** For $s >
2^{d-1}-d-1$, the borrow $s\,2^{-s} - R(s,d)$ **exceeds the combined
surplus of ALL later runs** $\sum_{j \geq 1} 2^{1-(s+jd)}$. (Worst
case, just past the boundary at $d=24$: ratio $125 \times$.) No
cross-run financing exists.

## 4. THE PERIODIC-TOWER IMPOSSIBILITY

Combining: a rational-total gadget tower needs eventually-periodic
anchor positions (Theorem 1 + Fatou) — i.e., finitely many APs with
fixed spacings; each AP admits only finitely many within-window
gadgets (Theorem 3) and cannot borrow across windows (Theorem 5 at
large anchors; small anchors are exhausted by the finite image).
**Conclusion: no periodic gadget tower of any pattern structure can
produce $2^{\aleph_0}$ representations of a rational.** This subsumes
and sharpens Wall 4 of the Kill #6 derivation.

## 5. THE SURVIVING LOOPHOLE (the next crack)

Periodicity of *positions* fails; what remains is **carry
non-uniqueness**: rational totals admit non-periodic representations
(the census collisions themselves are carry phenomena). The rational-x
question now reduces to: can a **non-periodic** perfect family of
representations of one rational exist? Equivalent formulation via the
perfect-set theorem: the representation set of a rational $x$ is a
closed subset of $2^{\mathbb{N}}$; it is countable **iff scattered**.
The conjectured kill: *for every rational $x$ the representation set
is scattered* (no perfect subtree in the full representation tree —
sharpening the greedy fork-comb Wall 1 to ALL trees). Attack route:
extract gadget pairs from a perfect subtree (tree surgery), then run
the Theorem 2/3/5 machinery against the extracted structure.

## 6. SCOPE LABELS (exact honesty)

- KILLED this session: the periodic-tower paradigm (Theorems 1–5).
- OPEN: the carry loophole / scattered-representation conjecture (§5).
- NOT a kill of the rational-x question itself. Walls mapped, sharper.

## 7. VERIFICATION

`verify_periodic_tower.py` — all checks exact (Fraction arithmetic):
AP identity, τ-identity, tower reproduction $d = 3..11$, census
reproduction, gadget equation on random triples, finite image at
$d=5$, run-surplus identity + boundary, funding death, singleton
family to $W = 20$. ALL PASSED this session.
