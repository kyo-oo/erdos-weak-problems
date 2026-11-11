# ERDŐS #404 — THE COMPLETE ASSEMBLY
## The partial structure theorem of $f(a,p)$: every closed class, every exact value, every general law, and the named open remainder

**Campaign:** erdos-weak-problems, W13 full-proof assembly (S046-W13).
**Base:** the ten CI-green kills of the #404 spine (README kill registry: #4, #7, #9,
#11, #12, #13, #14, #15, #16, #18 — spanning Kernels 2, 5, 7, 9, 10, 11, 12, 14 and the
S042 Kernel 37) + the exact-integer engine batteries (all re-run this session — §10).
**Scope label (honest):** this is the complete partial structure theorem — the strongest
rigorous state of the art on #404 assembled from the campaign's kernel-green material. The
named open remainder is stated precisely in §8. Nothing here is dressed as more than it is.

---

## 0. THE PROBLEM, VERBATIM

> For which integers $a \geq 1$ and primes $p$ is there a finite upper bound on
> those $k$ such that there are $a = a_1 < \cdots < a_n$ with
> $p^k \mid (a_1! + \cdots + a_n!)$?
> If $f(a,p)$ is the greatest such $k$, how does this function behave?
> Is there a prime $p$ and an infinite sequence $a_1 < a_2 < \cdots$ such that
> if $p^{m_k}$ is the highest power of $p$ dividing $\sum_{i \leq k} a_i!$
> then $m_k \to \infty$?

— erdosproblems.com/404 (Erdős–Graham 1980, p. 79; problem tags: number theory,
factorials). This transcription is recorded character-identically in the headers of
`problem404-full/PROBLEM.md`, `problem404-full/DERIVATION.tex`,
`problem404-p2-classification/PROBLEM.md`, `problem404-gadget-supply/PROBLEM.md`,
`PadicReduction.lean`, `TheoremBGeneral.lean`, `ResidualTail.lean`, `ExactF22.lean`,
`ExactF62.lean` (corpus page accessed 2026-11-02).

**The three corpus sub-questions:**
* **Q1** (the classification): for which $(a,p)$ does a finite upper bound exist — i.e. for which $(a,p)$ is $f(a,p) < \infty$?
* **Q2** (the behavior): what is $f(a,p)$, exactly or structurally?
* **Q3** (the infinite chain): does any $(p, a_1<a_2<\cdots)$ have $m_k \to \infty$?

**Prior art recorded on the page:** Lin [Li76] showed $f(2,2) \le 2^{54}$
(transcription note in §11 — the campaign's own unconditional value $f(2,2)=254$,
Theorem F22 of §5, supersedes both readings and depends on neither).
Status on page: **OPEN**.

Throughout, indices in a legal sum are **distinct** and the smallest is the seed $a$:
$a = a_1 < a_2 < \cdots < a_n$, i.e. the sum is $a! + \sum_{i \in B} i!$ with $B$ a finite
set of distinct integers $> a$. The corpus writes $f(a,p)$ (the prime second argument);
the mission's $f(a,b)$ is the same function with $b=p$ prime.

---

## 1. NOTATION AND THE MASTER REDUCTION (Theorem A)

Fix $a \ge 1$, a prime $p$, and let $B$ range over finite subsets of $\{a{+}1, a{+}2, \ldots\}$.
Write $v_p(n)$ for the exponent of $p$ in $n \ge 1$. Define the **quotient staircase**

$$P_i := \frac{i!}{a!} = (a+1)(a+2)\cdots i \qquad (i \ge a+1).$$

### Theorem A (the p-adic reduction — Kernel 5, Lean `erdos404_split` + the general-$p$ split of Kernels 11/37)

For every finite $B \subseteq \{a{+}1, a{+}2,\ldots\}$:

$$a! + \sum_{i\in B} i! \;=\; a! \cdot \Bigl(1 + \sum_{i \in B} P_i\Bigr), \qquad\text{hence}\qquad
v_p\Bigl(a! + \sum_{i\in B} i!\Bigr) = v_p(a!) + v_p\Bigl(1 + \sum_{i \in B} P_i\Bigr).$$

**Proof.** Each $i! = a! \, P_i$ by the telescoping product; factor $a!$ out of every term.
The valuation identity is the multiplicativity $v_p(xy) = v_p(x) + v_p(y)$ (valid for all
positive integers) applied to $a! \ge 1$ and $1 + \sum P_i \ge 1$. ∎

**Definition.**
$$f(a,p) := \sup\Bigl\{v_p\bigl(a! + \textstyle\sum_{i\in B} i!\bigr) : B \text{ finite}\Bigr\}, \qquad
g(a,p) := \sup\Bigl\{v_p\bigl(1 + \textstyle\sum_{i\in B} P_i\bigr)\Bigr\} \;\ge\; 0.$$

**Corollary A1 (the master split).** $f(a,p) = v_p(a!) + g(a,p)$ for **every** $(a,p)$ —
unconditionally. The classification of $f$ is the classification of $g$; the finiteness of
$f$ is the finiteness of $g$ (Q1 reduces to: is $g(a,p) < \infty$?). ∎

For $k \ge 1$ let $R_k \subseteq \mathbb{Z}/p^k$ be the set of subset sums of the *finite*
multiset $\{P_i \bmod p^k : v_p(P_i) < k\}$ (finite because $v_p(P_i) \to \infty$).

### Lemma A2 (prefix property)

$-1 \in R_{k+1} \Rightarrow -1 \in R_k$. Hence $\{k : -1 \in R_k\}$ is a prefix
$\{1,\ldots,g\}$ and $g(a,p) = \max\{k : -1 \in R_k\}$ (or $\infty$).

**Proof.** Reduce a subset sum $\equiv -1 \pmod{p^{k+1}}$ modulo $p^k$. ∎

### Lemma A3 (the lift lemma)

Let $-1 \in R_k$ with witness $B$: $\sum_{j\in B}P_j = -1 + p^k c$. Suppose there is a
**fresh gadget of exact valuation $k$ with unit part $-c$**: a finite $G$ of indices beyond
$a$, disjoint from $B$, with $\sum_{i\in G}P_i = p^k u$, $u \equiv -c \pmod p$. Then
$B \cup G$ witnesses $-1 \in R_{k+1}$. If the level-$k$ gadget supply covers all unit parts
of $\mathbb{Z}/p$, then $-1 \in R_{k+1}$.

**Proof.** $\sum_{j\in B\cup G}P_j = -1 + p^k(c+u) \equiv -1 \pmod{p^{k+1}}$ since $p \mid c+u$. ∎

### Theorem A4 (compactness — the sub-Q3 bridge)

The following are equivalent:

1. $g(a,p) = \infty$ (no level obstructs);
2. there is a set $Z \subseteq \{a, a{+}1, a{+}2,\ldots\}$ with $a \in Z$ and
   $\sum_{i\in Z} i! = 0$ in $\mathbb{Z}_p$ (the sum converges since $v_p(i!) \to \infty$);
3. there is an infinite chain $a = a_1 < a_2 < \cdots$ (the sorted elements of $Z$) with
   $m_k := v_p\bigl(\sum_{i \le k} a_i!\bigr) \to \infty$ — **Q3 answered YES for this $(a,p)$**.

**Proof.** (1)$\Rightarrow$(2): consider the tree whose depth-$k$ nodes are the level-$k$
witnesses ($B \subseteq [a{+}1, i_{\max}(k)]$ with $\sum_{j\in B}P_j \equiv -1 \pmod{p^k}$),
with an edge from a depth-$(k{+}1)$ node $B_{k+1}$ to the depth-$k$ node
$B_k = B_{k+1} \cap [a{+}1, i_{\max}(k)]$ — itself a level-$k$ witness since terms with
$v_p(P_i) \ge k$ vanish mod $p^k$. Every level is nonempty by (1) and every level is finite,
so by König's lemma there is an infinite branch $B_1 \subseteq B_2 \subseteq \cdots$; put
$Z' := \bigcup_k B_k$ and $Z := Z' \cup \{a\}$. For every $k$:
$\sum_{i\in Z'} P_i \equiv \sum_{i\in B_k} P_i \equiv -1 \pmod{p^k}$ (terms beyond
$i_{\max}(k)$ are $\equiv 0$), so $\sum_{i\in Z'} P_i = -1$ in $\mathbb{Z}_p$ and
$\sum_{i\in Z} i! = a!\,(1 + \sum_{i\in Z'}P_i) = 0$ in $\mathbb{Z}_p$.
(2)$\Rightarrow$(3): the partial sums satisfy
$\sum_{i\in Z,\, i\le N} i! = -\sum_{i\in Z,\, i > N} i!$, and the right side is divisible
by $\min_{i>N} v_p(i!) \to \infty$. (3)$\Rightarrow$(1): each $m_k$ certifies
$-1 \in R_{m_k}$, so $g \ge m_k$ for all $k$. ∎

**Consequence (the contrapositive is the campaign's Q3 engine):** $g(a,p) < \infty$
$\Rightarrow$ **no** infinite chain at $(a,p)$. Every exact finite value of $g$ kills Q3
at that pair.

---

## 2. THE ZERO-GROWTH CLASS LAWS: $f(a,p) = v_p(a!)$ EXACTLY

These are the classes on which the valuation **never grows**: $g = 0$ on the whole class.

### Theorem B (Kernel 11 — every prime; Lean `erdos404_theoremB`, CI run 41950834628)

**For every prime $p$ and every $a \ge 1$ with $p \mid a{+}1$, and every admissible $B$:**
$$v_p\Bigl(a! + \sum_{i\in B} i!\Bigr) = v_p(a!). \qquad\text{Hence}\qquad f(a,p) = v_p(a!) \text{ on the whole class.}$$

**Proof.** On this class $P_{a+1} = a+1 \equiv 0 \pmod p$, and every $P_i = P_{a+1}\cdot
(a+2)\cdots i$ with $i \ge a+1$ is $\equiv 0 \pmod p$. Hence
$1 + \sum_B P_i \equiv 1 \pmod p$ for *every* $B$: the multiplier in Theorem A's factorization
is a $p$-adic **unit congruent to $1$ mod $p$**. The unit-congruence law
$u \equiv 1 \pmod p \Rightarrow v_p(xu) = v_p(x)$ (fuel induction on $x$ using only
$(x\cdot u)\%p = x\%p$ — no Euclid lemma) then gives
$v_p(a!\,(1+\sum P)) = v_p(a!)$. ∎

**Instances (all unconditional):** every $(p-1, p)$ for every prime $p$; at $p=2$, **every
odd $a$** (the Kill-#7 class `erdos404_odd_a`); at $p=3$, every $a \equiv 2 \pmod 3$;
at $p=5$, every $a \equiv 4 \pmod 5$; … — a two-parameter family closed for all primes.
Primality is never used: the theorem holds for every integer $p \ge 2$ dividing $a+1$.

### Theorem B2 / the residual-tail class law (Kernel 37 — Lean `erdos404_residual_tail`, `erdos404_class_p_minus_3`)

**For every $m \ge 3$, every prime $p$ with $(m-1)\cdot(m-1)! + 1 < p$, every seed $a \ge 1$
with $a \equiv -m \pmod p$ (i.e. $a \equiv p-m$), and every admissible $B$:**
$$v_p\Bigl(a! + \sum_{i\in B} i!\Bigr) = v_p(a!). \qquad\text{Hence}\qquad f(a,p) = v_p(a!) \text{ on the whole family.}$$

**Proof.** By Theorem A it suffices to show $p \nmid \bigl(1 + \sum_B P_i\bigr)$.

*Step 1 (the signed falling-factorial congruence).* Write $j = i - a \ge 1$ for the coin
level of index $i$, and $a + j + 1 = kp - (m-1-j)$ with $j \le m-1$ (the seed split, valid
since $a \equiv -m$). The product staircase satisfies
$$p \;\Big|\; \bigl(pt\; a\; j - (-1)^j \, ff(m,j)\bigr), \qquad ff(m,j) := (m-1)(m-2)\cdots(m-j), \;\; 1 \le j \le m-1,$$
by induction on $j$ (pure ring arithmetic: the step closes by the seed split — each new
factor $a + j + 1 \equiv -(m-1-j) \pmod p$). So mod $p$ the unit-block coins are exactly
the signed falling factorials $(-1)^j ff(m,j)$, and — since $ff(m,j)$ contains the factor
$(m-1)$ — every coin is a multiple of $m-1$.

*Step 2 (the tail dies).* For $j \ge m$: $p \mid pt\;a\;j$ (the product contains the factor
$a + m \equiv 0 \pmod p$). So only coins at levels $j \in [1, m-1]$ contribute mod $p$.

*Step 3 (the pigeonhole).* A set of **distinct** indices $i > a$ hits at most one coin per
level $j = i - a$. Hence at most $m-1$ coins contribute, and the signed block sum
$s := \sum_{\text{coins}} (-1)^j ff(m,j)$ satisfies $(m-1) \mid s$ and the two-sided
triangle bound $-(m-1)\cdot(m-1)! \;\le\; s \;\le\; (m-1)\cdot(m-1)!$ (each
$ff(m,j) \le (m-1)!$).

*Step 4 (the small-multiple obstruction).* Suppose $p \mid 1 + \sum_B P_i$. Then
$1 + s = p\,t$; the bounds give $|1 + s| \le 1 + (m-1)(m-1)! < p$, so $t = 0$ and
$s = -1$. But $(m-1) \mid s$ with $m \ge 3$ forces $m - 1 \ge 2 \nmid -1$ —
contradiction. Hence $p \nmid (1 + \sum_B P_i)$ always: the **first p-adic level is
obstructed on the whole family**, $g = 0$, and $f(a,p) = v_p(a!)$. ∎

**Corollary B2a (the $m=3$ class).** For every prime $p \ge 7$ (the tail bound
$2\cdot 2! + 1 = 5 < p$) and every $a \equiv p - 3 \pmod p$: $f(a,p) = v_p(a!)$.
**Coverage per prime:** for each $p$, the covered seeds are $a \equiv p-3, p-4, \ldots,
p - m_{\max} \pmod p$ with $m_{\max}$ the largest $m$ with $(m-1)(m-1)! < p-1$ — e.g.
$p = 101$: $a \equiv 98, 97, 96 \pmod{101}$; $p = 23$: $a \equiv 20, 19 \pmod{23}$
(m = 3, 4); $p = 7$: $a \equiv 4 \pmod 7$.

**The class hierarchy and its boundary (structure):** Theorem B is the $m=1$ case
($a \equiv -1$); the residual-tail law covers $m \ge 3$ within the tail bound; the window
$m = 2$ ($a \equiv -2 \pmod p$) is **exactly the uncovered window** — and it is precisely
there that the campaign's odd-$p$ scans find deep survivors (at $p=3$: the class
$a \equiv 1 \pmod 3$, all surviving to depth $3^{19}$). The obstruction fails at $m=2$
because $m - 1 = 1$ divides $-1$: the small-multiple obstruction is vacuous. The theorem
and the engine data cohere perfectly. (Kernel receipts: $(m,p,a) = (3,7,4)$,
$(4,23,19)$, etc.; the $p=5$, $a \equiv 2 \pmod 5$ class — below the $m=3$ bound — is
separately battery-verified zero-growth; see §10.)

---

## 3. THE $p=2$ STRUCTURE LAWS (the staircase's exact algebra)

All identities below are verified by exact integer arithmetic in §10 (and formalized in
the kernels).

### Theorem K (the left-factorial kernel law — Kernel 2; Lean `kernel_law`, axioms [propext, Quot.sound])

**For every $u \ge 0$ and every $k \ge 3$:**
$$v_2\Bigl(\sum_{j=0}^{k} (u+j)!\Bigr) \;=\; v_2(u!) + v_2(u+2).$$

**Proof.** Factor $u!$ out: $\sum_{j=0}^{k}(u+j)! = u! \cdot K(u,k)$ with the partial kernel
$K(u,k) = \sum_{j=0}^{k} pt\;u\;j$. The three-term closed form
$$K(u,3) = 1 + (u+1) + (u+1)(u+2) + (u+1)(u+2)(u+3) = (u+2)\bigl(1 + (u+1)(u+4)\bigr)$$
has an **odd cofactor** ($u+1$ and $u+4$ have opposite parity, so $(u+1)(u+4)$ is even).
Every further summand $j \ge 4$ has $pt\;u\;j = (u+2)\cdot(\text{even})$ — the product
$(u+1)\cdots(u+j)$ contains the opposite-parity pair $u+1, u+4$ outside the extracted
factor $u+2$. Hence $K(u,k) = (u+2)\cdot(\text{odd})$ for every $k \ge 3$, and
$v_2 = v_2(u!) + v_2(u+2)$. ∎

**Consequence (universal lower bound):** the full consecutive tail is an admissible sum,
so $f(u,2) \ge v_2(u!) + v_2(u+2)$, i.e. $g(u,2) \ge v_2(u+2)$ for **every** $u$.

### Theorem CU (the cube identity — a second universal lower bound, tight on two whole residue classes)

**For every $a \ge 1$:**
$$1 + P_{a+1} + P_{a+3} \;=\; 1 + (a+1) + (a+1)(a+2)(a+3) \;=\; (a+2)^3,$$
so the two-coin subset $B = \{a+1, a+3\}$ always achieves
$$g(a,2) \;\ge\; 3\,v_2(a+2).$$

**Proof.** $1 + (a+1) + (a+1)(a+2)(a+3) = a + 2 + (a+2)(a^2+4a+3) = (a+2)^3$ (expand:
$a+2 + a^3+6a^2+11a+6 = a^3+6a^2+12a+8$). Take $v_2$. ∎

This bound is **tight** on the two flat classes $a \equiv 4 \pmod 8$ ($v_2(a+2)=1$,
$g=3$) and $a \equiv 10 \pmod{16}$ ($v_2(a+2)=2$, $g=6$) — Theorems T2/T3 below; nowhere
else among the swept values (§6).

### Theorem BI (the block-identity structure theory — Kernel 5, §6 of `PadicReduction.lean`)

For every $u \ge 0$, the consecutive factorial blocks factor exactly:
$$[u,u{+}1] := u! + (u{+}1)! = u!\,(u+2),$$
$$[u,u{+}2] = u!\,\bigl(1 + (u{+}1) + (u{+}1)(u{+}2)\bigr) = u!\,(u+2)^2,$$
$$[u,u{+}3] = u!\,\bigl(1 + (u{+}1) + (u{+}1)(u{+}2) + (u{+}1)(u{+}2)(u{+}3)\bigr)
= u!\,(u{+}2)(u^2+5u+5).$$

**Proof.** $u! + (u+1)! = u!(1 + (u+1)) = u!(u+2)$; $1 + (u+1) + (u+1)(u+2) = u^2+4u+4 = (u+2)^2$;
$1 + (u+1) + (u+1)(u+2) + (u+1)(u+2)(u+3) = (u+2)(u^2+5u+5)$ (expand both sides; verified
for $u = 0,1,2,5,9$ by exact arithmetic in §10). ∎

**Valuation corollaries (the gadget-supply laws — Kernel 7; Lean `lift_law`, `pair_law`, `triple_law`, axioms [propext, Quot.sound]):**

* **Lift law.** $v_2(x) = v_2(y) = V \Rightarrow v_2(x+y) \ge V+1$. *Proof:* $x = 2^V x'$,
  $y = 2^V y'$ with $x', y'$ odd (else $v_2 > V$); $x + y = 2^V(x'+y')$ with $x'+y'$ even. ∎
* **Companion facts.** a gadget of valuation $j < V$ **poisons** the sum down to $j$; one of
  valuation $j > V$ leaves the valuation at $V$ ($2^j o_1 + 2^V o_2 = 2^{\min(j,V)}(\cdots)$).
  *Construction rule:* at chain valuation $V$, add a gadget of exact valuation $V$.
* **Pair law.** For every $u \ge 3$: $P_u + P_{u+1} = P_u\,(u+2)$, so
  $v_2(P_u + P_{u+1}) = v_2(P_u) + v_2(u+2)$. *Proof:* $P_{u+1} = P_u (u+1)$;
  $P_u(1 + u + 1) = P_u(u+2)$; multiplicativity. ∎
* **Triple law.** For every $u \ge 3$: $P_u + P_{u+1} + P_{u+2} = P_u\,(u+2)^2$ (a perfect
  square), so $v_2 = v_2(P_u) + 2\,v_2(u+2)$. *Proof:* $1 + (u+1) + (u+1)(u+2) = (u+2)^2$. ∎

**Supply structure.** Single coins have $v_2(P_i) = i - s_2(i) - 1$ ($s_2$ = binary digit
sum at anchor 2): the levels $1, 4, 5, 8, 11, 12, 13, 16, \ldots$ carry **no single coin**
(the digit-sum gaps); pairs supply every level $v_2(P_u) + j$ ($j = v_2(u+2) \ge 0$);
square-triples supply $v_2(P_u) + 2j$; the deeper gaps need non-block gadgets (e.g.
$\{10,11,13\}$ has exact valuation 9). **Dead-end law:** the greedy chain $\{3\} \to \{3,4\}$
traps at $V = 4$ — having consumed $P_3$ and $P_4 \equiv 12$, the fresh staircase residues
mod 32 beyond index 4 are $P_5 \equiv 28,\ P_6 \equiv 8,\ P_7 \equiv 24$ (and $P_i \equiv 0$
for $i \ge 8$), whose subset sums span only $\{0, 4, 8, 20, 24, 28\}$ — $16$ is
unreachable, so no valuation-4 gadget exists disjoint from $\{3,4\}$: choice matters, and
the construction must instead take $P_5$ at $V = 2$ (odd sum: the chain value jumps to
$1 + 3 + 60 = 64 = 2^6$).

These laws structure the entire level-by-level staircase: every exact $g$-value in §4–§6 is
realized by subsets built from singles/pairs/triples/quads with these valuations.

---

## 4. THE $p=2$ CLASSIFICATION I: THE NINE INFINITE OBSTRUCTION FAMILIES (Kernel 9)

All nine theorems are Lean-proved **for every $a$ in the family** (universally
quantified): `ObstructionFamilies.lean` (3338 lines, 0 errors, 0 sorry; the obstruction
leaves are kernel-decided boolean case trees; T7/T7b use the memory-safe
`mc9`/`boundedForall` architecture — one kernel `decide` per leaf residue, 32 leaves ×
512 sub-sums). Every witness and every obstruction is re-verified by the engine battery
(`verify_p2class.py`, 287/287, §10).

| # | Family (for **all** $a$ in the class) | $g(a,2)$ | $f(a,2)$ | Witness $J$ (levels $j$) | Obstruction |
|---|---|---|---|---|---|
| T2 | $a \equiv 4 \pmod 8$ | $3$ | $v_2(a!) + 3$ | $\{1,3\}$ | mod 16, 3-coin window |
| T3 | $a \equiv 10 \pmod{16}$ | $6$ | $v_2(a!) + 6$ | $\{1,3\}$ | mod 128, 5-coin window |
| T4 | $a \equiv 32, 48 \pmod{64}$ | $6$ | $v_2(a!) + 6$ | $\{1,3,5\}$ / $\{1,3,4\}$ | mod 128, 7-coin window |
| T5 | $a \equiv 8 \pmod{64}$ | $6$ | $v_2(a!) + 6$ | $\{1,3,4,6\}$ | mod 128, 7-coin window |
| T6 | $a \equiv 40 \pmod{128}$ | $7$ | $v_2(a!) + 7$ | $\{1,3,4,6\}$ | mod 256, 7-coin window |
| T6b | $a \equiv 56 \pmod{128}$ | $7$ | $v_2(a!) + 7$ | $\{1,3,5,6\}$ | mod 256, 7-coin window |
| T6c | $a \equiv 88 \pmod{128}$ | $7$ | $v_2(a!) + 7$ | $\{1,3,4,7\}$ | mod 256, 7-coin window |
| T7 | $a \equiv 70 \pmod{128}$ | $10$ | $v_2(a!) + 10$ | $\{1,3,6,7,9\}$ | mod 2048, 9-coin window |
| T7b | $a \equiv 118 \pmod{128}$ | $10$ | $v_2(a!) + 10$ | $\{1,3,6,7,9\}$ | mod 2048, 9-coin window |

### Theorem T2 (full proof, representative)

**For every $a \equiv 4 \pmod 8$: $g(a,2) = 3$ exactly, i.e. $f(a,2) = v_2(a!)+3$.**

*Witness.* $1 + P_1 + P_3 = (a+2)^3$ (Theorem CU) with $v_2(a+2) = 1$ on the family, so
$g \ge 3$ — attained by $J = \{1, 3\}$, i.e. the sum $a! + (a+1)! + (a+3)!$.

*Obstruction.* Since $a \equiv 4 \pmod 8$: $v_2(a+2) = 1$ and $v_2(a+4) \ge 3$, so every
$P_j$ with $j \ge 4$ contains $(a+2)(a+4)$ and $16 \mid P_j$. Mod 16 the sum
$1 + \sum_J P_j$ is therefore congruent to a sub-sum of the three window coins
$P_1 = a{+}1$, $P_2 = (a{+}1)(a{+}2)$, $P_3 = (a{+}1)(a{+}2)(a{+}3)$. Two leaves:

* $a \equiv 4 \pmod{16}$: coins $\equiv \{5, 14, 2\}$; the eight values
  $1 + \sum_{S \subseteq \{5,14,2\}}$ are $\{1, 6, 15, 3, 4, 8, 1, 6\}$ — none $\equiv 0$.
* $a \equiv 12 \pmod{16}$: coins $\equiv \{13, 6, 10\}$; sub-sums
  $\{0, 13, 6, 10, 3, 7, 0, 13\}$ — none $\equiv 15 \pmod{16}$.

In both leaves $16 \nmid (1 + \sum_J P_j)$ for **every** $J$: $g \le 3$. ∎

### Theorems T3–T7b (full proof architecture, each Lean-complete)

Every family proof is the same three moves, with family-specific data:

1. **Vanish profile** (the window cut): on the family, the early offsets have fixed
   2-adic divisibility, so $2^{v} \mid P_j(a)$ for all $j \ge w$:
   * T3 ($a \equiv 10 \bmod 16$): $v_2(a{+}2) = 2,\ v_2(a{+}4) = 1,\ v_2(a{+}6) = 4$
     $\Rightarrow 2^{2+1+4} = 128 \mid P_j$, $j \ge 6$: **5-coin window mod 128**, 8 leaf
     residues $a \bmod 128 \in \{10, 26, 42, 58, 74, 90, 106, 122\}$, all $32$ sub-sums
     miss $-1$ (decided in the kernel).
   * T4 ($a \equiv 32, 48 \bmod 64$): $v_2(a{+}2) = v_2(a{+}6) = 1,\ v_2(a{+}4) = 2,
     v_2(a{+}8) = 3 \Rightarrow 2 \cdot 4 \cdot 2 \cdot 8 = 128 \mid P_j$, $j \ge 8$:
     **7-coin window mod 128**, leaves $\{32,96\}, \{48,112\}$.
   * T5 ($a \equiv 8 \bmod 64$): $2 \mid a{+}2,\ 4 \mid a{+}4,\ 2 \mid a{+}6,\ 8 \mid a{+}8
     \Rightarrow 128 \mid P_j$, $j \ge 8$: **7-coin window mod 128**, leaves
     $\{8, 72\}$ with coin residues $\{9, 90, 94, 104, 72, 112, 16\}$ /
     $\{73, 26, 30, 104, 72, 112, 16\}$, all $128$ sub-sums miss $-1$.
   * T6/T6b/T6c ($a \equiv 40, 56, 88 \bmod{128}$): shared profile $v_2(a{+}2) = 1,
     v_2(a{+}4) = 2, v_2(a{+}6) = 1, v_2(a{+}8) = 4 \Rightarrow 2^{1+2+1+4} = 256 \mid P_j$,
     $j \ge 8$: **7-coin window mod 256**, six leaf residues $\{40,168\}, \{56,184\},
     \{88,216\}$, all $2^7 = 128$ sub-sums miss $-1$ (`leaf_T6_40` … `leaf_T6c_216`).
   * T7/T7b ($a \equiv 70, 118 \bmod{128}$): shared profile $v_2(a{+}2) = 3, v_2(a{+}4) = 1,
     v_2(a{+}6) = 2, v_2(a{+}8) = 1, v_2(a{+}10) = 4 \Rightarrow 2^{3+1+2+1+4} = 2048 \mid
     P_j$, $j \ge 10$: **9-coin window mod 2048**, 16 leaf residues per family
     ($a \bmod 2048 \in \{70, 198, \ldots, 1990\}$, resp. $\{118, 246, \ldots, 2038\}$),
     all $2^9 = 512$ sub-sums miss $-1$.
2. **Witness.** The listed $J$ attains $1 + \sum_{j \in J} P_j \equiv 0$ modulo
   $2^{g}$ but not $2^{g+1}$, identically on the family (kernel-decided): e.g. T3's
   $J = \{1,3\}$ is the cube $(a+2)^3$ with $v_2(a+2) = 2$; T6's $J = \{1,3,4,6\}$ hits
   $128$ but not $256$; T7's $J = \{1,3,6,7,9\}$ hits $1024$ but not $2048$.
3. **Conclusion.** $g(a,2) = $ the family constant, for **every** member:
   $f(a,2) = v_2(a!) + g$. ∎ (Each family's uniformity is engine-verified to
   $a = 204/202/304/456$ for T2/T3/T4/T5 and $a < 900$ (7 members) for the T6/T7
   families; the Lean theorems are for all members.)

**Memory-safe leaf architecture (T7/T7b):** a naive tactic case-split
($32 \times 2^9 = 32768$ goals) exhausted the sandbox; the kernel instead packs each
9-coin sub-sum into ONE closed term (`memMask` = the 9-bit membership mask, provably
$< 512$; `mc9 r n` reconstructs $\sum_j P_j(r)\,\mathrm{bit}_j(n)$), and
`boundedForall (fun n => (1 + mc9 r n) % 2048 ≠ 0) 512 = true` is a single kernel-evaluated
`decide` per leaf — 32 decides total, zero tactic explosion.

**Engine receipts (kernel `#eval`, cross-checked by the battery):**
$f(4,2)=6$, $f(12,2)=13$, $f(20,2)=21$, $f(36,2)=37$ (T2);
$f(10,2)=14$, $f(26,2)=29$, $f(42,2)=45$ (T3); $f(32,2)=37$, $f(48,2)=52$ (T4);
$f(8,2)=13$, $f(72,2)=76$, $f(136,2)=140$, $f(200,2)=203$ (T5);
$f(40,2)=45$, $f(168,2)=172$, $f(296,2)=300$, $f(424,2)=427$ (T6);
$f(56,2)=60$, $f(184,2)=187$ (T6b); $f(88,2)=92$, $f(216,2)=219$ (T6c);
$f(70,2)=77$, $f(198,2)=204$, $f(326,2)=332$, $f(454,2)=459$ (T7);
$f(118,2)=123$, $f(246,2)=250$ (T7b).
Theorem C of Kernel 5 — $f(4,2) = 6$ — is the $a = 4$ instance of T2
(witness $4!+5!+7! = 5184 = 2^6\cdot 81$; mod-16 obstruction on the coins
$P_5 = 5, P_6 = 30, P_7 = 210$, all $P_i \equiv 0 \bmod 16$ for $i \ge 8$).

---

## 5. THE EXACT VALUES: $f(2,2) = 254$ AND $f(6,2) = 133$, UNCONDITIONAL

### Theorem F22 (Kernel 10; Lean `erdos404_f22_final`, ZERO hypotheses, axioms [propext, Classical.choice, Quot.sound]; CI run 41909053106 GREEN, commit 026c98c)

$$\boxed{f(2,2) = 254 \text{ EXACTLY — UNCONDITIONAL.}}$$

**Statement (Lean, verbatim):**
`v2 (2 + (witnessB.map fact).sum) = 254 ∧ ∀ B : List Nat, NoDupL B → (∀ i ∈ B, 3 ≤ i) → v2 (2 + (B.map fact).sum) ≤ 254`

* **Lower bound.** The explicit **118-element witness** $B \subseteq [3, 254]$
  (`witnessB` in `ExactF22.lean`, reproduced in §10's verification):
  $v_2\bigl(2! + \sum_{i\in B} i!\bigr) = 254$ — kernel-evaluated, and independently
  re-verified by exact integer arithmetic this session (§10: 118 distinct indices,
  all $\ge 3$, $v_2 = 254$ exactly).
* **Upper bound.** The certified **sound scheduled-precision class-DP** (the obstruction
  engine): the coin classes $v_2(P_i) = i - s_2(i) - 1$ fill $[0, 246]$ for $i \le 255$;
  the DP walks coins in class order with states $(t, u)$ meaning
  $G = 1 + (\text{chosen sum})$ has $v_2 G = t$ and $G/2^t \equiv u \pmod{2^{CP - t}}$
  ($CP = 262$), with FROZEN dropping ($t < V$: odd + even = odd — can never reach 254),
  CAP sentinel at $s = 0$ (valuation jumps $\ge CP$: the would-be witness that makes the
  final check fail), and **exact** state merging (the schedule $CP - t$ keeps the congruence
  exact — telescoping). The run certifies: **the first unreachable level is exactly 254**,
  i.e. $g(2,2) = 253$ and $f(2,2) = v_2(2!) + 253 = 1 + 253 = 254$.
* **Unconditionality.** The sole hypothesis of the earlier Kill-#14 form
  (`obstructionCheck = true`) was itself discharged in Lean
  (`obstructionCheck_true`, axioms [propext, Quot.sound]) via the 31-module §7 olean chain
  (`gen_f22_final.py`: all-slices + decide + kernel + show-free architecture), so
  `erdos404_f22_final` carries **zero hypotheses**.
* **Cross-validation.** C engine (GMP bignums, `class_dp 2 2 254` and stability run at
  $L = 320$: $g = 253$, first-unreachable 254, witness verified in-engine AND in pure
  Python — §10 battery 18/18), the Python bitset DP (`verify_f22.py`, 40/40 —
  definition-level subset-sum DP to $k = 25$ plus the sound class-DP at the Lin window),
  and Lin's [Li76] published bound (§11 note).

### Theorem F62 (Kernels 12 + 14; Lean `erdos404_f62_final`, ZERO hypotheses, axioms [propext, Classical.choice, Quot.sound]; CI run 42119256613 GREEN, commit 2498b4f)

$$\boxed{f(6,2) = 133 \text{ EXACTLY — UNCONDITIONAL.}}$$

**Statement (Lean, verbatim):**
`v2 (720 + (witnessB.map fact).sum) = 133 ∧ ∀ B : List Nat, NoDupL B → (∀ i ∈ B, 7 ≤ i) → v2 (720 + (B.map fact).sum) ≤ 133`

* **Lower bound.** The explicit **61-element witness** $B_6 \subseteq [7, 135]$
  (`witnessB` in `ExactF62.lean`): $v_2(6! + \sum_{i\in B_6} i!) = 133$ — kernel-evaluated;
  independently re-verified by exact integer arithmetic this session (§10: 61 distinct
  indices, all $\ge 7$, $v_2(720 + \sum) = 133$ exactly).
* **Upper bound.** The same scheduled-precision class-DP ported to anchor 6
  ($CP = 138$, 129 coins $[7,135]$, the 720-staircase, `coin_range_dvd` at the 136-cutoff,
  the inductive TailSorted, the NoDupF bridge): the **first unreachable level is exactly
  130** — $g(6,2) = 129$, $f(6,2) = v_2(6!) + 129 = 4 + 129 = 133$.
* **Unconditionality.** Kill #16's sole hypothesis (`obstructionCheck = true`) was
  discharged by the 24-module §7 olean ladder (`gen_f62_final.py`, the twin-port of the
  F22 architecture at half scale): `obstructionCheck_true` is a theorem
  [propext, Quot.sound] and `erdos404_f62_final` has **zero hypotheses**.
* **Cross-validation.** C engine (L = 130 death run + L = 200 stability, capped = 0, GMP
  witness), pure-Python DP twin (`verify_f62.py`, 218/218, peak 352 states, death
  $\le 129$, 200 random-subset soundness trials), L = 600 a-sweep stability runs.

---

## 6. THE $p=2$ COMPLETE a-SWEEP: EVERY $a \le 60$ EXACT (and the monsters beyond)

The C class-DP engine (`class_dp.c`, GMP bignums, sound scheduled-precision — validated
against the Lean-crossed ground truth `class_dp2.py` with **300/300 identical per-class
lines** at $a = 14$, $L = 300$, and the known-value battery 18/18, §10) certifies
two-sided exact values: "first unreachable $= g + 1$ at $L > g$" is a proof that **no**
subset of any coins reaches $g{+}1$ (level-$\ell$ reachability depends only on coins of
class $< \ell$; the DP tracks them at exact scheduled precision), while the extracted
witness (verified by GMP in-engine **and** pure Python out-of-engine, 34/34 PASS)
proves $g$ is achieved.

**Every odd $a$: $g = 0$, $f(a,2) = v_2(a!)$ (Theorem B). Every even $a \le 60$: exact
finite $g$:**

| $a$ | $g$ | $f = v_2(a!)+g$ | | $a$ | $g$ | $f = v_2(a!)+g$ |
|---|---|---|---|---|---|---|
| 2 | **253** | 254 | | 32 | 6 | 37 |
| 4 | 3 | 6 | | 34 | **18412** | 18444 |
| 6 | 129 | 133 | | 36 | 3 | 37 |
| 8 | 6 | 13 | | 38 | 793 | 828 |
| 10 | 6 | 14 | | 40 | 7 | 45 |
| 12 | 3 | 13 | | 42 | 6 | 45 |
| 14 | **1522** | 1533 | | 44 | 3 | 44 |
| 16 | 533 | 548 | | 46 | 27 | 69 |
| 18 | 45 | 61 | | 48 | 6 | 52 |
| 20 | 3 | 21 | | 50 | 14 | 61 |
| 22 | 11 | 30 | | 52 | 3 | 52 |
| 24 | 39 | 61 | | 54 | 12 | 62 |
| 26 | 6 | 29 | | 56 | 7 | 60 |
| 28 | 3 | 28 | | 58 | 6 | 60 |
| 30 | 100 | 126 | | 60 | 3 | 59 |

($v_2(a!) = a - s_2(a)$ by Legendre's formula; e.g. $v_2(34!) = 34 - 2 = 32$, witness
$v_2(34! + \sum) = 18444 = 32 + 18412$; $v_2(38!) = 35$, C-engine witness
$v_2(38! + \sum) = 828 = 35 + 793$. The $f$-column is recomputed this session and
cross-checked against every kernel receipt: $f(4,2)=6$, $f(8,2)=13$, $f(10,2)=14$,
$f(12,2)=13$, $f(20,2)=21$, $f(26,2)=29$, $f(36,2)=37$, $f(40,2)=45$, $f(42,2)=45$,
$f(56,2)=60$ — all MATCH.) **ALIVE candidates: NONE** — every even $a \le 60$
has a two-sided exact certificate. Every $g$-value $\ge 100$ occurs at $a \equiv 2 \pmod 4$
except $g(16) = 533$.

**The two monsters (multi-wall crossers, formerly the strongest "unbounded candidates"):**

* $g(14,2) = 1522$ — died below the 2048 wall (L = 2200 DP: first unreachable 1523;
  witness $|B| = 730 \subseteq (14, 1534]$, $v_2(14! + \sum) = 1533$; stability at
  L = 3000, 6072).
* $g(34,2) = 18412$ — crossed the 2048/4096/8192/**16384** walls (alive at every level up
  to $L = 16384$ — the self-similar dyadic frontier ladder $256{:}128{:}\cdots{:}1$ riding
  the precision ceiling), then died at L = 32768 (first unreachable 18413; witness
  $|B| = 9215 \subseteq (34, 18446]$, $v_2(34! + \sum) = 18444$; stability at L = 19000,
  20000; peak RSS 1230 MB).

**Beyond 60 (engine-certified, not yet Lean-frozen):** bounded deep values
$g(46,2) = 27$, $g(86,2) = 26$, $g(104,2) = 23$, $g(110,2) = 21$, $g(144,2) = 18$,
$g(174,2) = 23$, $g(400,2) = 14$. **Deep survivors at $2^{28}$** (obstruction-free to 28
consecutive 2-adic levels, unresolved): $a \in \{62, 64, 78, 94, 98, 102, 126, 142, 146,
158, 162, 190, 194, \ldots\}$ — every survivor probed to date has since been killed
($2, 6, 14, 16, 18, 24, 30, 34, 38$ all exact above), so these are the live frontier.

**Odd primes (scan data, engine-side):** $p = 3$: bounded $g(3,3) = 2$, $g(6,3) = 1$,
$g(15,3) = 1$, $g(21,3) = 3$, $g(22,3) = 3$, $g(24,3) = 1$, $g(30,3) = 2$, $g(33,3) = 1$,
$g(39,3) = 7$; deep survivors at $3^{19}$: most $a \equiv 1 \pmod 3$ — the $m = 2$ window
(and at $p=3$ the $m=3$ bound $5 < p$ fails, so $a \equiv 0 \pmod 3$ is uncovered there
too: $g(9,3), g(12,3) \ge 19$). $p = 5$: $g(2,5) = g(7,5) = g(12,5) = g(17,5) = g(22,5) =
g(27,5) = g(32,5) = 0$ (the $m=3$ class below the theorem's bound — battery-verified
zero-growth); $p = 7$: $g(2,7) = g(7,7) = g(12,7) = g(13,7) = 0$. No uniform obstruction
families found at odd-$p$ scan depth; the odd-$p$ staircase classes are the open side.

---

## 7. SUB-QUESTION 3 VERDICTS (via the compactness bridge, Theorem A4)

By Theorem A4, an infinite chain with $m_k \to \infty$ at $(a, p)$ exists **iff**
$g(a,p) = \infty$. Therefore — all unconditional:

* **$(2,2)$: NO infinite chain.** $g(2,2) = 253 < \infty$ (Theorem F22). The historically
  strongest candidate (Lin's own subject pair) is dead. *(Conjecture D of the early
  campaign — $g(2,2) = \infty$, sub-Q3 = YES at $(2,2)$ — is thereby REFUTED.)*
* **$(6,2)$: NO infinite chain.** $g(6,2) = 129 < \infty$ (Theorem F62).
* **Every odd $a$ at $p = 2$: NO** (Theorem B: $g = 0$).
* **Every member of the nine T-families: NO** (Theorem T2–T7b: finite $g \in \{3,6,7,10\}$).
* **Every even $a \le 60$: NO** (the exact a-sweep of §6: finite two-sided-certified $g$).
* **Every $(a,p)$ on the Theorem-B class ($p \mid a{+}1$): NO** (any prime).
* **Every $(a,p)$ on the residual-tail class ($a \equiv -m \bmod p$, $m \ge 3$,
  $(m-1)(m-1)!+1 < p$): NO** (Kernel 37: $g = 0$).

**The remaining Q3 question:** whether $g = \infty$ occurs *anywhere* — the candidates
are exactly the open staircase pairs of §8. All probed evidence says every ladder dies
(the universal geometric bleed-out regime: the live DP state set halves every class
through the death tail and hits zero exactly at $g+1$ — observed identically from
$g = 3$ values up to the $g = 18412$ monster; the dyadic frontier ladders that cross
power-of-two walls are real but finite). No general finiteness proof yet — the frontier.

---

## 8. THE MASTER CLASSIFICATION TABLE — THE PARTIAL STRUCTURE THEOREM OF $f(a,p)$

**The master split (Theorem A, all pairs, unconditional):**
$$f(a,p) = v_p(a!) + g(a,p).$$

Everything below is assembled from the kernel-green material; each row is either an
unconditional closed class (Lean kernel + battery) or an engine-certified exact value
(two-sided C/Python DP certificates).

### 8.1 The closed classes (unconditional, infinitely many pairs each)

| Class | Law | Kernel | Coverage |
|---|---|---|---|
| **$p \mid a{+}1$** (all $a \equiv -1 \bmod p$) | $f(a,p) = v_p(a!)$ ($g = 0$) | K11 (`erdos404_theoremB`) | **every prime $p$, every $a \equiv p-1$** |
| **Residual tail** $a \equiv -m \bmod p$, $m \ge 3$, $(m{-}1)(m{-}1)!+1 < p$ | $f(a,p) = v_p(a!)$ ($g = 0$) | K37 (`erdos404_residual_tail`) | for each $p$: seeds $a \equiv p-3, \ldots, p-m_{\max}$ |
| **$m = 3$ window** | $f(a,p) = v_p(a!)$ | K37 (`erdos404_class_p_minus_3`) | **every prime $p \ge 7$, every $a \equiv p-3$** |
| **$p=2$, odd $a$** | $f(a,2) = v_2(a!)$ | K5/K11 (the $p=2$ instance) | every odd $a$ |
| **$p=2$, $a \equiv 4 \pmod 8$** (T2) | $f = v_2(a!) + 3$ | K9 | every member |
| **$p=2$, $a \equiv 10 \pmod{16}$** (T3) | $f = v_2(a!) + 6$ | K9 | every member |
| **$p=2$, $a \equiv 32, 48 \pmod{64}$** (T4) | $f = v_2(a!) + 6$ | K9 | every member |
| **$p=2$, $a \equiv 8 \pmod{64}$** (T5) | $f = v_2(a!) + 6$ | K9 | every member |
| **$p=2$, $a \equiv 40, 56, 88 \pmod{128}$** (T6/b/c) | $f = v_2(a!) + 7$ | K9 | every member |
| **$p=2$, $a \equiv 70, 118 \pmod{128}$** (T7/b) | $f = v_2(a!) + 10$ | K9 | every member |

### 8.2 The exact isolated values (unconditional)

| Pair | Value | Kernel |
|---|---|---|
| $(2,2)$ | $f = 254$ ($g = 253$) | K10 (`erdos404_f22_final`, zero hypotheses) |
| $(6,2)$ | $f = 133$ ($g = 129$) | K12+K14 (`erdos404_f62_final`, zero hypotheses) |

### 8.3 The exact swept values (engine-certified two-sided; $p = 2$)

Every even $a \le 60$ (30 values, §6 table: $g$ from 3 to 18412; every odd $a$ in §8.1);
the monsters $g(14,2) = 1522$, $g(34,2) = 18412$; the bounded deep values
$g(46) = 27, g(86) = 26, g(104) = 23, g(110) = 21, g(144) = 18, g(174) = 23, g(400) = 14$.

### 8.4 The universal laws (unconditional, all pairs at $p = 2$)

* $f(a,2) = v_2(a!) + g(a,2)$ (Theorem A);
* $g(a,2) \ge v_2(a+2)$ (the kernel law, full-tail subset) and $g(a,2) \ge 3\,v_2(a+2)$
  (the cube identity) — tight exactly on T2/T3;
* the block/pair/triple/lift algebra of §3 (the supply structure behind every value);
* compactness: finite $g$ $\Leftrightarrow$ no $\mathbb{Z}_p$ zero-sum $\Leftrightarrow$
  no infinite chain (§7).

### 8.5 THE NAMED OPEN REMAINDER — the single open core of #404

**The complete two-variable classification of $f(a,p)$ (equivalently: the dichotomy
"does $g$ ever equal $\infty$, and what is $g$ on the whole bounded set").** Precisely
three components, all outside every closed class above:

* **(O1) $p = 2$, even seeds beyond the classified families and the swept range** — the
  deep survivors $a \in \{62, 64, 78, 94, 98, 102, 126, 142, 146, 158, 162, 190, 194,
  \ldots\}$ (obstruction-free at $2^{28}$): finite exact values expected (every survivor
  ever probed has died), but no uniform obstruction family found at scan depth and no
  Lean freeze yet.
* **(O2) odd $p$, the staircase classes** — every class not covered by Theorem B or the
  residual-tail law: prominently the **$m = 2$ window** $a \equiv -2 \pmod p$ (at $p = 3$:
  the $a \equiv 1 \pmod 3$ deep-survivor class to depth $3^{19}$) and every class beyond
  the residual tail's $m_{\max}$. No uniform odd-$p$ obstruction families known.
* **(O3) sub-Q3 in general** — whether $g = \infty$ anywhere (equivalently whether any
  $\mathbb{Z}_p$ factorial zero-sum exists, equivalently whether any infinite chain
  exists). All evidence points to **NO** (§7), but the general finiteness proof — *why
  every ladder dies* — is the frontier: the universal geometric bleed-out regime and the
  dyadic frontier ladders are the two observed regimes, and the "ladder operator"
  analysis on the class-2 coin pairs is the campaign's named next attack.

---

## 9. ARSENAL CITATIONS (BOSS's own mathematics, vendored at `arsenal/`)

Per the arsenal doctrine (README, Session 028): every S042-era kernel imports and applies
BOSS's vendored 16,021-theorem corpus (exact Mathlib pin 51e6992e):

* **`Arsenal/ErdosTernary2/Basic.lean`** (erdosternary2, 7,426 theorems):
  `isTernaryDigit` (witness-digit validity — Kernel 37's bridge checks the ternary digits
  of the $m=3$ first prime 5 and the $m=4$ first prime 23), `lt_three_cases`
  (trichotomy routing).
* **`Arsenal/CardinalWorlds.lean`** (HC-PROOF, 8,595 theorems): `carryAtPos_bound`
  (Kernel 37's bridge: `carryAtPos 5 1 < 4`).
* **`Arsenal/CardinalWorldsV2.lean`**: `v2r_ternary_scaling` (the dyadic scaling law —
  Kernel 37's bridge: `v2r (3^1 · 9) = v2r 9`; also the v2r bookkeeping pattern behind the
  S028/S029 kernels the 404 kernels share architecture with).
* **Earlier kernels (arsenal-era discipline, core-only):** Kernel 2/5/7/9/10/12/14 are
  core-Lean-only (no Mathlib), zero sorry, zero custom axioms beyond
  [propext, (Classical.choice,) Quot.sound] — the K15 valuation architecture
  (`vpadf`/`vpad`, saturation, step, non-divisor laws) and the Theorem-A split are shared
  between `TheoremBGeneral.lean` and `ResidualTail.lean`; the Euclid-powered
  multiplicative law, the `growth_G1` pigeonhole pattern (`List.Nodup.map_on` +
  `Nat.card_Ico`), and `linear_combination` for the coin-step ring identity are Kernel 37's
  engine (the r2 divisibility architecture — zero Int-mod lemmas).

The `#eval`/`#print axioms` receipts of every kernel are in-file and CI-grepped
(§10).

---

## 10. VERIFICATION RECEIPTS

### 10.1 Batteries re-run THIS SESSION (foreground, all GREEN)

| Battery | What it verifies | Result |
|---|---|---|
| `problem404-full/verify_404.py` | Theorem A/B/C machinery, the g-table, witnesses, block identities | **ALL 296 CHECKS PASSED** |
| `problem404-gadget-supply/verify_gadgets.py` | lift law (500 exact pairs), the certified chain valuations $[3,7,8,10,11,15,16,18,19,23]$, terminal witness $v_2 = 23$, dead-end law, reachable-set DP ($-1 \in R_k$, all $k \le 24$), level-1 unattainability | **ALL CHECKS PASSED** |
| `problem404-p2-classification/verify_p2class.py` | T2–T7b family uniformity (engine side), Lean receipt cross-checks ($v_2(a!) + g$ for every receipt value), the small-$g$ table $a \le 200$, deep survivors at $2^{28}$, bounded deep values, Lin consistency | **ALL 287 CHECKS PASSED** |
| `problem404-q3-chain/verify_f22.py` | the 118-element witness (size/distinct/min/max/valuation = 254), sound class-DP at the Lin window ($g = 253$), independent raw bitset DP $k \in [2,25]$, a-sweep cross-refs | **ALL 40 CHECKS PASSED** |
| `problem404-q3-chain/verify_f62.py` | the 61-element witness ($v_2 = 133$), DP twin, 200 random-subset soundness trials, stability | **ALL 218 CHECKS PASSED** |
| `problem404-full/battery404tail.py` | Kernel 37 dual-method: class instances $(3,7,4)$, $(3,11,8)$, $(3,13,10)$, $(4,23,19)$, $(4,29,25)$, $(5,101,96)$, $(3,17,14)$, $(3,19,16)$ — block census + window census + analysis; the $p=5$, $a \equiv 2 \pmod 5$ class | **ALL GREEN** |
| `problem404-q3-chain/run_battery.sh` (C engine rebuilt this session, `gcc -O2 -Wall -Wextra -std=gnu11 -lgmp`, zero warnings) | known-value battery: T2/T3/T5 Lean kills, $(2,2)$ at $L=254$ and $L=320$, $(6,2)$ at $L=130$/$200$, the deep values $16/18/24/30/38$ with stability runs — every run `capped = 0`, witness verified in-engine (GMP) **and** pure Python | **PASS = 18, FAIL = 0** |

### 10.2 Independent exact-integer re-derivations (this session, second method)

* **F22 witness:** extracted `witnessB` (118 elements) from `ExactF22.lean`; computed
  $v_2(2! + \sum_{i\in B} i!) = 254$ by direct big-integer factorization — **MATCH**.
* **F62 witness:** extracted `witnessB` (61 elements) from `ExactF62.lean`; computed
  $v_2(720 + \sum_{i\in B} i!) = 133$ — **MATCH** (with $v_2(6!) = 4$, $g = 129$).
* **Kernel law:** $u \in \{0, 1, 5, 10\}$, $k \in \{3, 4, 5, 7\}$ —
  $v_2(\sum_{j=0}^{k}(u+j)!) = v_2(u!) + v_2(u+2)$ — all **MATCH**.
* **Block identities:** $u \in \{0,1,2,5,9\}$ — $[u,u{+}1] = u!(u{+}2)$,
  $[u,u{+}2] = u!(u{+}2)^2$, $[u,u{+}3] = u!(u{+}2)(u^2{+}5u{+}5)$ — all **OK**.
* **Cube identity:** $a = 4, 204$: $v_2((a{+}2)^3) = 3\,v_2(a{+}2)$ — **OK**.

### 10.3 CI receipts (GitHub Actions, `kills.yml` — the only verdict that counts)

| Kernel | Lean file | Axioms | CI |
|---|---|---|---|
| Kernel 2 | `bulldoze/problem404-padic-kernel/KernelLaw.lean` | [propext, Quot.sound] | green (Kill #4) |
| Kernel 5 | `problem404-full/PadicReduction.lean` (`erdos404_split`, `erdos404_odd_a`, `erdos404_f42`) | CI-grepped | green (Kill #7) |
| Kernel 7 | `problem404-gadget-supply/GadgetSupply.lean` (`lift_law`, `pair_law`, `triple_law`) | [propext, Quot.sound] | green (Kill #9) |
| Kernel 9 | `problem404-p2-classification/ObstructionFamilies.lean` (T2/T3: [propext, Quot.sound]; T4–T7b: [propext, Classical.choice, Quot.sound]; all bounds + exacts grepped) | as listed | green (Kills #11/#12/#13) |
| Kernel 10 | `problem404-q3-chain/ExactF22.lean` + 37-module chain → `F22All.lean` | `erdos404_f22_final`: [propext, Classical.choice, Quot.sound], zero hypotheses | **CI run 41909053106 GREEN** (commit 026c98c; the closed form earlier: 41821641176, bf0e851) |
| Kernel 11 | `problem404-full/TheoremBGeneral.lean` (`erdos404_theoremB`) | [propext, Quot.sound] | **CI run 41950834628 GREEN** (commit 5f55fdc) |
| Kernel 12 | `problem404-q3-chain/ExactF62.lean` (`erdos404_f62_lower` / `erdos404_f62_exact`) | [propext, Quot.sound] / [propext, Classical.choice, Quot.sound] | **CI run 41955350415 GREEN** (commit 02e982e) |
| Kernel 14 | `problem404-q3-chain/F62All.lean` chain (24-module §7 ladder, `gen_f62_final.py`) | `erdos404_f62_final`: [propext, Classical.choice, Quot.sound], zero hypotheses | **CI run 42119256613 GREEN** (commit 2498b4f, first-round compile war) |
| Kernel 37 | `problem404-full/ResidualTail.lean` (`erdos404_residual_tail`, `erdos404_class_p_minus_3`, `erdos404t_arsenal_bridge`; receipt `ERDOS404_RESIDUAL_TAIL_KERNEL_GREEN` grepped) | [propext, Quot.sound]-family | green (S042; battery404tail in the same CI step) |

### 10.4 The engine's soundness architecture (why the DP certificates are proofs)

Level-$\ell$ reachability depends only on coins of class $< \ell$ (any coin of class
$\ge \ell$ contributes $2^\ell \cdot$ integer; if the class-$<\ell$ part has valuation
$< \ell$ the total does too). The scheduled-precision DP tracks all class-$<\ell$ coins at
exact congruence precision with **exact** state merging (the $CP - t$ schedule telescopes:
total consumed precision $\le$ class index). Hence "first unreachable $= g + 1$ at
$L > g$" is a machine certificate that no subset of **any** coins reaches $g{+}1$; the
extracted witness (backward DFS through the exact per-snapshot membership store, completed
at the initial state $(0,1)$, any completing chain being a real witness) certifies $g$ is
achieved; witnesses are re-verified by GMP big-integer factorials inside the engine and by
pure-Python factorials outside it. Cross-engine agreement: C / `py_ref.py` /
`class_dp2.py` produce **identical per-class lines** (300/300 at $a=14$, $L=300$; same at
$a=34$) and identical finals; the $(2,2)$ witness matches the Lean-proven parameters
(118 elements, $B \subseteq [3,254]$, $v_2 = 254$).

---

## 11. TRANSCRIPTION NOTE (Li76) — honest record

The corpus page's prior art is recorded in the campaign's transcriptions in two variants:
the early packages and the `verify_p2class.py` battery record **"$f(2,2) \le 2^{54}$
(Lin [Li76])"**, while `ExactF22.lean`'s header and the `verify_f22.py` battery record
**"Lin proved $f(2,2) \le 254$ (TIGHT)"**. The discrepancy is a campaign-internal
transcription matter only: **no kernel, theorem, or battery above depends on Lin's bound
in either reading** — the campaign's $f(2,2) = 254$ is proved unconditionally in Lean
from first principles (witness + sound obstruction DP, zero hypotheses), cross-validated
by three independent engines. Under the $2^{54}$ reading, the campaign's exact value
supersedes the prior art by ~46 binary orders of magnitude; under the 254 reading it
attains it exactly. Both readings are consistent with every theorem stated here.

---

## 12. HONEST SCOPE STATEMENT

This assembly is the **complete partial structure theorem of Erdős #404**: the master
reduction (all pairs), two unconditional zero-growth class laws spanning every prime, the
$p=2$ structure algebra, nine unconditional infinite classified families at $p = 2$, two
unconditional exact anchor values, the complete exact $p=2$ sweep to $a \le 60$ with both
monsters resolved, and the compactness bridge that converts every finite certificate into
a negative Q3 verdict. The named open remainder — the full two-variable classification,
with components (O1)/(O2)/(O3) of §8.5 — is stated precisely and is NOT claimed closed.
No result here is conditional, no numerics are dressed as proofs (the engine certificates
are two-sided with independently re-verified witnesses), and every Lean claim cites its
kernel, its axiom set, and its CI run.

**Target: Erdős #404. State: assembled. The engine never stops; it never lies.**
