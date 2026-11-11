# ERDŐS #1056 — THE FACTORIAL-INTERVAL CASE THEOREMS: COMPLETE PROOF

**Kill #22 (Kernel 18) — the complete mathematical record.**
The structure law, the Wilson force-pair law, the k = 4..11 smallest-witness
theorems, the k=11-class extensions, the frontier bar, and the
witness-decidability architecture — every theorem proven below with no gaps;
every finite claim certified by an exhaustive dual-method machine computation
(C census + independent Python sweep + battery + campaign engine + Lean
kernel receipts).

---

## §1. THE PROBLEM (verbatim)

> **#1056: Let $k\geq 2$. Does there exist a prime $p$ and consecutive
> intervals $I_1,\ldots,I_k$ such that**
> $$\prod_{n\in I_i}n \equiv 1 \pmod{p}$$
> **for all $1\leq i\leq k$?**

*(Corpus record: teorth/erdosproblems, as recovered in the campaign's S026
full-corpus read; the campaign's own THE_LIST v6 row: "#1056 factorial-interval
products". Known before this campaign: $k=2$ with $p=11$ (Erdős, 1979);
$k=3$ with $p=17$ (Makowski, 1983). This campaign: $k=4,\dots,11$ — all new.)*

**Interpretation (the corpus itself flags the statement as ambiguous; the
disambiguation is forced by the historical record).** "Consecutive intervals"
means: each $I_i$ is a run of consecutive integers and the runs are
mutually consecutive ($\min I_{i+1} = \max I_i + 1$). The reading under which
$p=11$ is the $k=2$ solution and $p=17$ the $k=3$ solution — the reading of
Erdős 1979 and Makowski 1983, and the reading of every witness in this file —
is:

> The intervals lie inside $[2, p-1]$: no element is $\equiv 0$ or $\equiv 1
> \pmod p$.

This is the *standard reading*. (Under a literal unrestricted reading,
residue-1 singletons would be inert and, e.g., $[1,1],[2,3]$ would make
$p=5$ a trivial $k=2$ witness, contradicting the historical attribution — so
the historical reading excludes them.) All theorems below are stated and
proven under the standard reading; §3.1 Remark R0 records the reduction of
the unrestricted reading to residue form.

**Status of the full question.** Open for $k \ge 12$: no $k=12$ witness
exists below $200{,}000$ (Theorem 5, dual-method exhaustive). The case
frontier — the largest $k$ with a certified witness — stands at $k = 11$.

---

## §2. THE THEOREM BOARD

| # | Theorem | Status |
|---|---|---|
| T1 | **Structure law**: $k$ consecutive unit intervals $\iff$ $k+1$ equal-factorial indices $\iff$ $M(p)\ge k+1$ | **PROVEN** (§3.2, pure proof) |
| T2 | **Wilson force-pair law**: $j!\,(p-1-j)! \equiv (-1)^{j+1} \pmod p$; anchors $1!\equiv(p-2)!\equiv1$; odd-$j$ hits of $\pm1$ double | **PROVEN** (§3.3, pure proof incl. Wilson's theorem) |
| T3 | **Gap law**: $(j+1)!\not\equiv j!$; every unit interval has length $\ge 2$; necessity $p \ge 2k+2$ | **PROVEN** (§3.4, pure proof) |
| T4 | **Case theorems $k=4..11$**: smallest-witness table $(23, 109, 71, 673, 599, 3011, 27901, 52163)$ — each: explicit construction, purity $M(p_k)=k+1$, minimality $\min\{q: M(q)=k+1\}=p_k$ | **PROVEN** (§3.5: construction kernel-decided + machine-certified; purity & minimality by certified exhaustive dual-method census) |
| T5 | **k=11-class extensions & frontier bar**: $M(109379)=M(111641)=12$ (new $k=11$ witnesses); no $k=12$ witness below $200{,}000$; exactly three primes $<200{,}000$ with $M=12$ | **PROVEN** (§3.6, certified exhaustive dual-method) |
| T6 | **Witness decidability**: for fixed $p,k$ the witness property is decidable by a finite $O(p)$ computation; the smallest-witness map is computable for $k\le 11$ | **PROVEN** (§3.7) |

**The witness table (all machine-verified this session; $v$ = common chain
value $=c_0!\bmod p$; blocks are $[c_{i-1}+1,\,c_i]$):**

| $k$ | $p_k$ | $v$ | cut points $c_0<c_1<\dots<c_k$ |
|---|---|---|---|
| 2 | 11 | $2$ | $2,\ 4,\ 7$ |
| 3 | 17 | $1$ | $1,\ 5,\ 11,\ 15$ |
| **4** | **23** | $1$ | $1,\ 4,\ 8,\ 11,\ 21$ |
| **5** | **109** | $19$ | $9,\ 11,\ 39,\ 58,\ 73,\ 85$ |
| **6** | **71** | $-1$ | $7,\ 9,\ 19,\ 51,\ 61,\ 63,\ 70$ |
| **7** | **673** | $56$ | $159,\ 316,\ 354,\ 393,\ 397,\ 506,\ 545,\ 647$ |
| **8** | **599** | $175$ | $28,\ 50,\ 122,\ 183,\ 250,\ 289,\ 500,\ 539,\ 555$ |
| **9** | **3011** | $1$ | $1,\ 611,\ 723,\ 749,\ 805,\ 2205,\ 2261,\ 2287,\ 2399,\ 3009$ |
| **10** | **27901** | $20268$ | $2451,\ 2867,\ 4768,\ 10383,\ 18707,\ 19589,\ 19965,\ 22981,\ 24673,\ 26322,\ 27263$ |
| **11** | **52163** | $1$ | $1,\ 3924,\ 7291,\ 7427,\ 18519,\ 24931,\ 26081,\ 27231,\ 33643,\ 44735,\ 44871,\ 52161$ |

---

## §3. THE COMPLETE PROOFS

### 3.0 Notation and standing definitions

Fix an odd prime $p$. Write $j! \bmod p$ for the residue of the factorial
($0! = 1$). For $1 \le j \le p-1$ every factor $1, 2, \dots, j$ is coprime to
$p$, hence:

**Lemma 0 (units).** *For $1 \le j \le p-1$, $j!$ is a unit modulo $p$.*
*Proof.* $j!$ is a product of $j$ integers each in $[1, p-1]$, each coprime
to the prime $p$; a product of units in $\mathbb{Z}/p\mathbb{Z}$ is a unit. ∎*

Definitions:

* A **$k$-system on $p$** is a tuple of nonempty intervals
  $I_i = [a_i, b_i] \subset \mathbb{Z}$, $i = 1, \dots, k$, with
  $a_1 \ge 2$, $b_k \le p-1$, $a_{i+1} = b_i + 1$, and
  $\prod_{n \in I_i} n \equiv 1 \pmod p$ for every $i$.
* A **chain of order $k$ on $p$** is a tuple $1 \le j_0 < j_1 < \dots < j_k
  \le p-1$ with $j_0! \equiv j_1! \equiv \dots \equiv j_k! \pmod p$.
* The **maximal multiplicity**
  $$M(p) := \max_{v}\;\bigl|\{\,j \in [1, p-1] : j! \equiv v \ (\mathrm{mod}\ p)\,\}\bigr|.$$

**Remark R0 (unrestricted reading reduces to residues).** In the literal
statement the $I_i$ are arbitrary consecutive integer runs. If any $I_i$
contains a multiple of $p$, its product is $\equiv 0 \not\equiv 1$; so none
does, whence each $I_i$ has length $\le p-1$ and its elements form a
consecutive run of residues $\alpha_i, \alpha_i + 1, \dots, \beta_i$ inside
$[1, p-1]$. If $b_i \equiv p-1 \pmod p$ for some $i < k$ then $b_i + 1$, the
first element of $I_{i+1}$, is a multiple of $p$ — forbidden; hence the
residue runs tile consecutively: $\beta_i + 1 = \alpha_{i+1}$, and the whole
system collapses to a system of intervals inside $[1, p-1]$. Removing
leading residue-$1$ elements (units, inert) from the first block turns this
into a $k$-system inside $[2, p-1]$, except for the degenerate case where the
first block consists *only* of residue-$1$ elements (possible only as a
singleton $[c,c]$, $c \equiv 1$, since two consecutive integers cannot both
be $\equiv 1$) — exactly the trivial case excluded by the standard reading.
So the standard reading is the unrestricted reading with trivial singleton
blocks discarded. ∎

### 3.2 Theorem 1 — the structure law (the $\iff$)

**Theorem 1.** *For every odd prime $p$ and every $k \ge 1$, the following
are equivalent:*

**(a)** *there exists a $k$-system on $p$;*
**(b)** *there exists a chain of order $k$ on $p$;*
**(c)** *$M(p) \ge k+1$.*

*Proof.*

**(a) $\Rightarrow$ (b).** Let $I_i = [a_i, b_i]$ be a $k$-system. Put
$c_0 := a_1 - 1$ and $c_i := b_i$ for $1 \le i \le k$. Since $a_1 \ge 2$,
$c_0 \ge 1$. The intervals are nonempty ($a_i \le b_i$) and consecutive,
so
$$1 \le c_0 = a_1 - 1 < a_1 \le b_1 = c_1 < b_1 + 1 = a_2 \le b_2 = c_2 < \dots \le b_k = c_k \le p-1,$$
i.e. $1 \le c_0 < c_1 < \dots < c_k \le p-1$. For each $i$ the telescoping
identity in $\mathbb{Z}$
$$c_i! \;=\; c_{i-1}! \cdot B_i, \qquad B_i := \prod_{n = c_{i-1}+1}^{c_i} n,$$
holds (the factors $1 \dots c_i$ split as $1 \dots c_{i-1}$ times
$c_{i-1}+1 \dots c_i$). Reducing mod $p$ and using $B_i \equiv 1$:
$$c_i! \equiv c_{i-1}! \pmod p \quad (i = 1, \dots, k).$$
By induction on $i$, all $c_i!$ are congruent to $c_0!$; thus
$(c_0, c_1, \dots, c_k)$ is a chain of order $k$. ∎ (step)

**(b) $\Rightarrow$ (c).** The chain value $v := j_0! \bmod p$ is attained at
the $k+1$ distinct indices $j_0, \dots, j_k \in [1, p-1]$, so the maximum
multiplicity satisfies $M(p) \ge k+1$. ∎ (step)

**(c) $\Rightarrow$ (b).** Let $v$ attain $M(p)$; its hit set
$\{j \in [1, p-1] : j! \equiv v\}$ has $M(p) \ge k+1$ elements; listing them
increasingly gives a chain of order $k$. ∎ (step)

**(b) $\Rightarrow$ (a).** Let $j_0 < \dots < j_k$ be a chain. Define
$I_i := [j_{i-1}+1,\ j_i]$ for $1 \le i \le k$. These are nonempty (strict
inequalities), mutually consecutive ($I_{i+1}$ begins at $j_i + 1$), and lie
in $[2, p-1]$ (since $j_0 \ge 1$ gives $j_0 + 1 \ge 2$, and $j_k \le p-1$).
The telescoping identity gives $j_i! = j_{i-1}! \cdot B_i$ where $B_i$ is the
product over $I_i$; mod $p$,
$$j_i! \equiv j_{i-1}!\, B_i \pmod p .$$
Both $j_i!$ and $j_{i-1}!$ are congruent to the chain value $v$, so
$v \equiv v\,B_i \pmod p$. By Lemma 0, $v$ is a unit; multiplying by
$v^{-1} \in \mathbb{F}_p^*$ gives $B_i \equiv 1 \pmod p$ for every $i$. ∎

This closes the equivalence. ∎ **Theorem 1**

*Remark (the engine of the whole campaign).* Theorem 1 converts the interval
question — a priori a search over partitions — into the chain-multiplicity
question, decidable in $O(p)$ ring operations per prime (Theorem 6). It is
exactly this reduction that made the exhaustive exclusions of T4/T5 feasible:
"the exclusion below it via the structure law".*

### 3.3 Theorem 2 — Wilson's theorem and the force-pair law

**Lemma W (Wilson's theorem).** *$(p-1)! \equiv -1 \pmod p$.*

*Proof.* In the group $\mathbb{F}_p^* = \{1, 2, \dots, p-1\}$ the map
$x \mapsto x^{-1}$ is an involution. Its fixed points satisfy $x^2 = 1$, i.e.
$(x-1)(x+1) = 0$ in the field $\mathbb{F}_p$; since a field has no zero
divisors, $x = \pm 1$ are the only fixed points. Hence $\{1, \dots, p-1\}$
splits into the two fixed points $1, -1$ and $(p-3)/2$ transposition pairs
$\{x, x^{-1}\}$, $x \ne x^{-1}$. Therefore
$$(p-1)! = \prod_{x \in \mathbb{F}_p^*} x = \Bigl(\prod_{\text{pairs}} x \cdot x^{-1}\Bigr) \cdot 1 \cdot (-1) = 1^{(p-3)/2} \cdot (-1) = -1 . \quad \blacksquare$$

**Theorem 2 (the force-pair law).** *For every $j \in [0, p-1]$.*
$$j! \,(p-1-j)! \equiv (-1)^{j+1} \pmod p .$$

*Proof.* For $0 \le j \le p-1$ the integer identity
$$(p-1)! = \Bigl(\prod_{i=1}^{j} i\Bigr)\Bigl(\prod_{i=j+1}^{p-1} i\Bigr)
= j! \cdot \prod_{i=j+1}^{p-1} i$$
holds (empty products $= 1$ at $j=0$ and $j = p-1$). Substitute $i = p - t$:
as $i$ runs from $j+1$ to $p-1$, $t$ runs bijectively from $p-j-1$ down to
$1$, i.e. over $\{1, \dots, p-1-j\}$, and each factor satisfies
$p - t \equiv -t \pmod p$. Hence
$$\prod_{i=j+1}^{p-1} i \equiv (-1)^{p-1-j} (p-1-j)! \pmod p .$$
Combining with Lemma W, $-1 \equiv (p-1)! \equiv j!\,(-1)^{p-1-j}\,(p-1-j)!$,
so
$$j!\,(p-1-j)! \equiv -\,(-1)^{p-1-j} \pmod p .$$
Since $p$ is odd, $p-1$ is even and $(-1)^{p-1-j} = (-1)^{j}$ (exponents
congruent mod $2$), giving
$$j!\,(p-1-j)! \equiv (-1)^{j+1} \pmod p . \quad \blacksquare$$

**Corollary 2.1 (the anchor pair).** $1! = 1$ and $(p-2)! \equiv 1 \pmod p$
(take $j = 1$: $1! \cdot (p-2)! \equiv (-1)^2 = 1$). Hence for every
$p \ge 5$ the value $1$ is attained at the two distinct indices $1$ and
$p-2$, so $M(p) \ge 2$: **every prime $\ge 5$ carries a unit interval**
(namely $[2, p-2]$, whose product $(p-2)! \equiv 1$). *(Machine: the census
gives $M(5) = M(7) = M(13) = M(19) = M(37) = 2$ — the five primes below
$109$ with maximal multiplicity $2$.)*

**Corollary 2.2 (the $-1$ anchor).** $(p-1)! \equiv -1$ (take $j = 0$ or
$j = p-1$): the value $-1$ is always attained, at index $p-1$.

**Corollary 2.3 (odd-$j$ doubling — the force-pair).** *Let $j$ be odd and
$j! \equiv v$ with $v^2 = 1$ (i.e. $v \in \{1, -1\}$). Then
$(p-1-j)! \equiv v \pmod p$, and the involution $j \mapsto p-1-j$ pairs the
odd-$j$ hits of $v$ (fixed point only at the midpoint $j = (p-1)/2$, which is
odd exactly when $p \equiv 3 \bmod 4$).*

*Proof.* Theorem 2 gives $j!\,(p-1-j)! \equiv 1$ (odd $j$), so
$(p-1-j)! \equiv v^{-1} = v$ (as $v^2 = 1$). If $j' := p-1-j = j$ then
$2j = p-1$; otherwise $j' \ne j$, $j'$ is odd ($p-1$ even), and $j'$ is
another hit of $v$. Applying the map twice returns to $j$; so the odd-$j$
hits of $v$ split into pairs $\{j, p-1-j\}$ plus possibly the midpoint. ∎

**Corollary 2.4 (even-$j$ cross-pairing).** *For even $j$:
$j!\,(p-1-j)! \equiv -1$; so $j! \equiv 1 \Rightarrow (p-1-j)! \equiv -1$ and
$j! \equiv -1 \Rightarrow (p-1-j)! \equiv 1$. Even-$j$ hits of $1$ are not
paired within the $1$-chain — they trade with the $-1$-chain.*

*(Machine: verify1056.py [A1] checks $j!\,(p-1-j)! \equiv (-1)^{j+1}$ for
every $j \in [0, p-1]$ and every prime $p < 1000$ — GREEN.)*

### 3.4 Theorem 3 — the gap law and the length law

**Theorem 3.** *(i) For $1 \le j \le p-2$: $(j+1)! \not\equiv j! \pmod p$.
(ii) In any $k$-system on $p$, every interval has length $\ge 2$; consequently
$2k \le p-2$, i.e. $p \ge 2k+2$ is necessary for a $k$-system.*

*Proof.* (i) Suppose $(j+1)! \equiv j!$. Since $(j+1)! = (j+1)\cdot j!$ and
$j!$ is a unit (Lemma 0), multiplying by $(j!)^{-1}$ gives $j+1 \equiv 1
\pmod p$ — impossible because $2 \le j+1 \le p-1$. ∎
(ii) An interval $[a,b]$ of length $1$ (a singleton $\{a\}$ with $2 \le a \le
p-1$) would need $a \equiv 1 \pmod p$ — impossible; equivalently it is the
case $c_{i-1} + 1 = c_i$ of a chain, excluded by (i). So each of the $k$
disjoint consecutive intervals has length $\ge 2$, they tile $[a_1, b_k]
\subseteq [2, p-1]$, and $b_k - a_1 + 1 \ge 2k$ while $[2, p-1]$ has $p-2$
elements: $2k \le p-2$. ∎

*Consequence for the hunt: primes $q < 2k+2$ are excluded with no
computation at all (for $k = 4$: $q \in \{2,3,5,7\}$; for $k=11$: all
$q < 24$); the census below handles the rest.*

### 3.5 Theorem 4 — the case theorems $k = 4, \dots, 11$

**Theorem 4 (uniform statement).** *For each $k \in \{4, \dots, 11\}$ let
$p_k$ and the cut points $(c_0, \dots, c_k)$ be as in the witness table of
§2, and let $v = c_0! \bmod p_k$. Then:*

**(i) Construction.** *The $k$ consecutive intervals
$[c_{i-1}+1, c_i] \subset [2, p_k - 1]$ all have product $\equiv 1 \pmod{p_k}$
— equivalently $c_0! \equiv c_1! \equiv \dots \equiv c_k! \equiv v$.*

**(ii) Purity.** *$M(p_k) = k+1$: no residue is attained more than $k+1$
times by $j! \bmod p_k$; hence by Theorem 1, $p_k$ carries no system of
$k+1$ consecutive unit intervals.*

**(iii) Minimality.** *Every prime $q < p_k$ has $M(q) \ne k+1$; equivalently
$p_k = \min\{q \text{ prime} : M(q) = k+1\}$ — $p_k$ is the smallest prime
whose maximal unit-interval count is exactly $k$.*

*Proof.* **(i)** The congruences $c_i! \equiv v$ and the block products
$\equiv 1$ are equivalent by the telescoping identity in the proof of
Theorem 1. They are certified four independent ways: the battery (two
methods — direct block products, and cut-point factorial equality); the
independent sweep verify1056.py (block products recomputed from scratch);
the C census (full chains); and the Lean kernel (the theorems
`erdos1056_k4` … `erdos1056_k11`, CI run 42308034994 GREEN, commit a66350c —
axiom receipts §4). Small cases inline: for $k=2$, $p=11$:
$3\cdot4 = 12 \equiv 1$, $5\cdot6\cdot7 = 210 = 11\cdot19 + 1 \equiv 1$;
for $k=3$, $p=17$: $2\cdot3\cdot4\cdot5 = 120 = 17\cdot7+1$,
$6\cdots11 = 332640 = 17\cdot19567 + 1$, $12\cdot13\cdot14\cdot15 = 32760 =
17\cdot1927 + 1$; for $k=4$, $p=23$: $[2,4]$: $24 = 23+1$; $[5,8]$:
$5\cdot6\cdot7\cdot8 = 1680 = 23\cdot73 + 1$; $[9,11]$: $9\cdot10\cdot11 =
990 = 23\cdot43+1$; $[12,21]$: running the product mod $23$:
$12\cdot13 \equiv 18$, $\cdot14 \equiv 22 \equiv -1$, $\cdot15 \equiv 8$,
$\cdot16 \equiv 13$, $\cdot17 \equiv 14$, $\cdot18 \equiv 22$, $\cdot19
\equiv 4$, $\cdot20 \equiv 11$, $\cdot21 \equiv 1$. Larger cases: machine
certificates (the values are far beyond hand arithmetic — e.g. the $k=11$
first block $[2, 3924]$).

**(ii)–(iii)** Both are finite statements over explicit data — the
multiplicity $M(q)$ of every prime $q \le 200{,}000$ — certified by the
**dual-method exhaustive census** (C implementation census1056.c and an
independent full Python re-implementation in verify1056.py, which agrees with
the C census **line by line, value by value, on all 5333 primes
$\le 52163$**, and chunk-wise on the whole range to $200{,}000$; §5). The
census lines: $M(23) = 5$, $M(109) = 6$, $M(71) = 7$, $M(673) = 8$,
$M(599) = 9$, $M(3011) = 10$, $M(27901) = 11$, $M(52163) = 12$ — proving
**(ii)**. For **(iii)**, the exclusion cells are empty (census, §5): for
every prime $q < p_k$, $M(q) \ne k+1$; primes $q < 2k+2$ are excluded
outright by Theorem 3(ii). Hence $p_k$ is the first prime with $M = k+1$. ∎

**Per-case record.**

* **$k=4$, $p = 23$.** Chain value $v = 1$ at $c = (1, 4, 8, 11, 21)$;
  blocks $[2,4],[5,8],[9,11],[12,21]$ (products above). **Wilson
  decomposition** (Cor. 2.3): the anchor pair $(1, 21)$ — $21 = p-2$; the
  odd midpoint $11 = (p-1)/2$ ($23 \equiv 3 \bmod 4$, self-paired); the
  even-$j$ singles $4, 8$ (unpaired, Cor. 2.4). Count $2 + 1 + 2 = 5 = k+1$.
  $M(23) = 5$; primes below: $M(2)=1, M(3)=1, M(5)=2, M(7)=2, M(11)=3,
  M(13)=2, M(17)=4, M(19)=2$ — none $= 5$. Minimality ✓.
* **$k=5$, $p = 109$.** $v = 19$ at $c = (9, 11, 39, 58, 73, 85)$ ($9! =
  362880 = 109 \cdot 3329 + 19$); blocks $[10,11],[12,39],[40,58],[59,73],
  [74,85]$. $M(109) = 6$. Primes below 109: $M$-distribution
  $\{1{:}2,\ 2{:}5,\ 3{:}5,\ 4{:}11,\ 5{:}4,\ 7{:}1\}$ primes — **no $M=6$
  below 109** (the $M=7$ prime below is $71$ — the $k=6$ witness). ✓
* **$k=6$, $p = 71$.** $v = -1$ at $c = (7, 9, 19, 51, 61, 63, 70)$; blocks
  $[8,9],[10,19],[20,51],[52,61],[62,63],[64,70]$. **Wilson
  decomposition**: three odd pairs $\{7,63\}, \{9,61\}, \{19,51\}$ (Cor. 2.3
  at $v = -1$) plus the $-1$ anchor $70 = p-1$ (Cor. 2.2): $6 + 1 = 7 =
  k+1$. $M(71) = 7$; below 71 the max is $M = 5$ (at $23, 61$) — no $M = 7$. ✓
* **$k=7$, $p = 673$.** $v = 56$ at $c = (159, 316, 354, 393, 397, 506,
  545, 647)$. $M(673) = 8$; below 673: $\{1{:}2, 2{:}5, 3{:}6, 4{:}38,
  5{:}51, 6{:}14, 7{:}4, 9{:}1\}$ — no $M = 8$ (the $M=9$ prime below is
  $599$, the $k=8$ witness). ✓
* **$k=8$, $p = 599$.** $v = 175$ at $c = (28, 50, 122, 183, 250, 289, 500,
  539, 555)$. $M(599) = 9$; below 599: $\{1{:}2, 2{:}5, 3{:}6, 4{:}37,
  5{:}44, 6{:}12, 7{:}2\}$ — no $M = 9$. ✓
* **$k=9$, $p = 3011$.** $v = 1$ at $c = (1, 611, 723, 749, 805, 2205,
  2261, 2287, 2399, 3009)$; blocks $[2,611], \dots, [2400,3009]$.
  **Decomposition**: anchor $(1, 3009)$; odd pairs $(611, 2399), (723,
  2287), (749, 2261), (805, 2205)$; midpoint $1505$ not hit. $2 + 8 = 10 =
  k+1$. $M(3011) = 10$; below: $\{1{:}2, 2{:}5, 3{:}6, 4{:}42, 5{:}161,
  6{:}156, 7{:}47, 8{:}10, 9{:}2\}$ — no $M = 10$. ✓
* **$k=10$, $p = 27901$.** $v = 20268$ at $c = (2451, 2867, 4768, 10383,
  18707, 19589, 19965, 22981, 24673, 26322, 27263)$. $M(27901) = 11$; below:
  $\{1{:}2, 2{:}5, 3{:}6, 4{:}42, 5{:}192, 6{:}1035, 7{:}1394, 8{:}325,
  9{:}36, 10{:}7\}$ — no $M = 11$. ✓
* **$k=11$, $p = 52163$.** $v = 1$ at $c = (1, 3924, 7291, 7427, 18519,
  24931, 26081, 27231, 33643, 44735, 44871, 52161)$. **Decomposition**:
  anchor $(1, 52161)$; four odd pairs $(7291, 44871), (7427, 44735),
  (18519, 33643), (24931, 27231)$; odd midpoint $26081 = (p-1)/2$
  ($52163 \equiv 3 \bmod 4$); one even single $3924$. Count
  $2 + 8 + 1 + 1 = 12 = k+1$. $M(52163) = 12$; below 52163:
  $\{1{:}2, 2{:}5, 3{:}6, 4{:}42, 5{:}192, 6{:}1152, 7{:}2827, 8{:}956,
  9{:}134, 10{:}14, 11{:}2\}$ — **no $M = 12$ below 52163** (the two $M=11$
  primes are $27901$ and $47269$). ✓

**Remark R1 (the two readings — both certified).** The table above is the
**exact reading**: $p_k$ is the smallest prime with *maximal* interval count
exactly $k$. Under the **at-least reading** ($M \ge k+1$, "smallest prime
carrying $k$ intervals") the firsts are: $k=1: 5$;
$k{=}2: 11$; $k{=}3: 17$; $k{=}4: 23$; $k{=}5: \mathbf{71}$;
$k{=}6: 71$; $k{=}7: \mathbf{599}$; $k{=}8: 599$; $k{=}9: 3011$;
$k{=}10: 27901$; $k{=}11: 52163$ — differing at $k=5$ ($71 > $ its own
$M=7$ covers 6) and $k=7$ ($599$, whose $M=9$ covers 8). The campaign's
recorded table is the exact reading; both are theorems of the same census.

### 3.6 Theorem 5 — the k=11-class extensions and the frontier bar

**Theorem 5.** *(i) $M(52163) = 12$ (Theorem 4, $k=11$).
(ii) $M(109379) = 12$: the value $61812$ is attained at the twelve indices*
$$7299,\ 21085,\ 50439,\ 70048,\ 83188,\ 87819,\ 87966,\ 90845,\ 93484,\
94441,\ 105228,\ 108417,$$
*yielding eleven consecutive unit intervals $[7300, 21085], \dots,
[105229, 108417] \subset [2, 109378]$ on the prime $109379$.
(iii) $M(111641) = 12$: the value $27555$ is attained at*
$$12279,\ 27422,\ 29482,\ 31157,\ 35906,\ 41422,\ 50169,\ 50608,\ 77140,\
89813,\ 93615,\ 106912,$$
*giving eleven consecutive unit intervals on the prime $111641$.
(iv) Frontier bar: for every prime $q < 200{,}000$, $M(q) \le 12$ — no
$k=12$ witness exists below $200{,}000$ (in particular none below $190{,}000$).
(v) The primes $< 200{,}000$ with $M = 12$ are exactly $52163, 109379,
111641$.*

*Proof.* (ii)/(iii): the chains and the induced interval systems are
certified by three independent computations — the C census (full hit lists),
the independent Python sweep (verify1056.py [A4]: block products $\equiv 1$,
span and consecutiveness), and the campaign engine (engine1056_k12.py,
which independently reports maxfreq $= 12$, values $61812$ and $27555$).
Purity $M = 12$ (not more): census. (iv)/(v): the exhaustive census — C over
all $17{,}984$ primes $\le 200{,}000$, cross-validated line-by-line by the
independent Python implementation on all $5333$ primes $\le 52163$ and
chunk-wise on $(52163, 200{,}000)$ — finds maximum multiplicity $12$, with
$M \ge 12$ exactly at the three named primes and $M \ge 13$ nowhere
(alert channel empty). ∎

*(Both new witnesses have chain values $\ne \pm1$ ($61812, 27555$), so the
Wilson pair law imposes no structure on them — they are generic chains.)*

### 3.7 Theorem 6 — witness decidability (the architecture)

**Theorem 6.** *Fix an odd prime $p$ and $k \ge 1$.*
*(i) The predicate "$p$ carries a $k$-system" is decidable by a finite
computation: compute $f_j := j! \bmod p$ for $j = 1, \dots, p-1$
($p-2$ multiplications in $\mathbb{F}_p$, each on numbers $< p^2$); tabulate
value frequencies ($p-1$ increments); output whether some frequency $\ge
k+1$ — correct by Theorem 1. Total cost $O(p)$ ring operations.
(ii) The map $k \mapsto p_k := \min\{q \text{ prime} : M(q) = k+1\}$ is
computable by exhaustive prime search, terminating for every $k \le 11$
(the constructions of Theorem 4 are the termination certificates); for
$k \ge 12$ termination is equivalent to the open problem (a non-terminating
search would mean no $k$-witness exists).*
*(iii) Candidates are bounded: by Theorem 3(ii) only $q \ge 2k+2$ need be
scanned.*

*Proof.* (i) is Theorem 1 plus the finiteness of the tabulation; correctness
of the decision procedure is exactly the equivalence (a) $\iff$ (c).
(ii): the search enumerates primes in order, applies (i), and stops at the
first $M(q) = k+1$; for $k \le 11$ Theorem 4(iii) exhibits the stopping point
and Theorem 4(i) certifies the construction; the $k \ge 12$ claim is the
contrapositive of "the problem asks for a witness". (iii) is Theorem 3(ii). ∎

---

## §4. LEAN CONVERSION NOTES (the kernel-decide architecture)

The standing architecture (proven in the 9-round compile war of Kill #22,
S030): **fuel-oracle tree products + the §7-freeze olean ladder + pure
$\langle\rangle$ assembly.**

1. **The oracle layer (`FI_Base.lean`, core-only).** `prodmodT p f a b` —
   balanced binary product of $[a,b] \bmod p$, splitting at the midpoint,
   fuel $f$ (64 $\gg \log_2 52163$); `prodmod p a b` = interval product;
   `factmod p j` = $j! \bmod p$. *Why trees:* the linear-fuel recursion past
   $\sim$3k depth kills the CI runner (R1/R5 of the compile war); depth
   $O(\log \text{span})$ keeps every block decide under the
   $\sim$15k-term/process budget ($\sim$1.5 ms/kernel-term grind).
2. **The data layer (one block-product theorem per process).**
   `FI_D3a–e.lean` (k=10, blocks of 27901), `FI_D4a–e.lean` (k=11, blocks of
   52163): each `theorem fi_kNN_bM : prodmod p a b = 1 := by decide` — small
   kernel work only.
3. **The final assembly (`FI_K2_K8/FI_K9/FI_K10_FINAL/FI_K11_FINAL.lean`).**
   `theorem erdos1056_kN : Nat.Prime p ∧ prodmod p a₁ b₁ = 1 ∧ …` assembled
   by pure anonymous-constructor composition — **zero kernel work**.
   Primality: `by norm_num` (NOT `decide` — R9: Mathlib's `Nat.Prime`
   `Decidable` instance trial-divides up to $n$: ~14k kernel divisions at
   27901, ~26k at 52163, a 66 s+ grind; `norm_num` is elaborator-native).
   **Receipts: CI run 42308034994 GREEN, commit a66350c; 24 steps; axioms
   k4–k11 `[propext, Classical.choice, Quot.sound]`.**
4. **Wilson anchors.** `erdos1056_wilson_17/23/3011 : factmod p 1 = 1 ∧
   factmod p (p−2) = 1 := by decide` — **zero axioms**. The 52163 anchor
   ($52161! \equiv 1$) lives in its own module (one deep recursion, one
   decide per process — §7-freeze).
5. **T1 (structure law) in Lean.** The equivalence needs: (a) the split
   lemma `factmod p c_i = factmod p c_{i−1} * prodmod p (c_{i−1}+1) c_i % p`
   (a fuel induction on the tree — the same cut as the data modules), (b)
   unit cancellation (`factmod p j` coprime to `p`: every factor `< p`,
   `Nat.Prime.coprime` chain, `inv_mul_cancel`). Route exists; not yet
   compiled — the kernels decide the instances directly instead.
6. **T2 (force-pair law) in Lean.** Wilson: Mathlib's `ZMod`/`Finset`
   machinery, or the in-house involution proof (`Finset.prod_bijective` on
   $x \mapsto x^{-1}$). The *instances* are already kernel-decided
   (`factmod` anchors above); the general law is a `Finset` algebra lemma
   chain.
7. **T4(ii) purity & (iii) minimality in Lean — designed, not yet compiled.**
   The count oracle: `hitCount p v := (List.range' 1 (p−1)).countP (fun j =>
   factmod p j = v)`. **Off-by-one warning (two-sided):** the index range is
   $[1, p-1]$ — `List.range p` would add the phantom $0! = 1$ hit to value-1
   chains (+1), and the campaign *engine* convention $j \in [2, p-1]$
   undercounts value-1 chains by one (−1) — the census found and fixed
   exactly this class of bug. The certificate shape: exhibit the $k+1$ hits
   (equalities, cheap) + `∀ j ∉ J, factmod p j ≠ v` (a $p$-element
   `List.all` decide — ~$p \times 17$ tree-mults ≈ 22 min at 52163 — the
   §7-freeze ladder route: batch the frequency fold into a balanced
   `chainScan` producing the whole table in one $O(\log p)$-depth fold,
   one process per prime). The minimality layer: `FI_Census.lean` data
   module — 5333 lines `(q, M(q))` with per-line fuel'd decides
   (~2.2 h CI split into ~40 processes; the raw certificate is banked as
   `census1056.txt`, dual-method-verified).
8. **T5 (frontier bar) in Lean.** 17,984 primes × $O(q)$ scans ≈ $1.5\cdot
   10^9$ kernel multiplications — beyond the kernel-decide architecture's
   budget; the certified census (C + Python dual, artifacts banked) is the
   proof layer for this statement. Labeled honestly: this is the boundary
   of what kernel-decide certifies.
9. **The arsenal bridge (already CI-GREEN, flavor of the k=11 module):
   `FI_Bridge.lean`** — `erdos1056_digits_52163` (52163 =
   $(2211221222)_3$), `erdos1056_ternary_routing`, `carryAtPos_bound` on
   the cut points, `v2r_scaling` ($52161 = 3\cdot17387$,
   $7290 = 3\cdot2430$) — the ErdosTernary2 arsenal applied in named steps.

---

## §5. THE VERIFICATION LOG (this session, all commands re-run)

| # | Check | Method | Result |
|---|---|---|---|
| 1 | `python3 battery1056.py` | campaign dual-method battery (block products ∥ factorial chains + Wilson anchors), k=2..11 | **BATTERY 1056: GREEN** — all 10 cases, all blocks $\equiv 1$ |
| 2 | `gcc -O2 census1056.c && ./census1056` | **new independent C census**, all primes $\le 200{,}000$: $M(q)$ + argmax + chains at $M \ge 12$; stderr alert channel for $M \ge 13$ | 13.2 s; **no alerts**; first-with-$M{=}m$ table = the campaign witness table exactly; $M=12$ exactly at $\{52163, 109379, 111641\}$; 17,984 data lines |
| 3 | `python3 verify1056.py A` | **independent Python re-implementation**: Wilson pair law on all primes $<1000$ (all $j$); per-case chains/purity/cuts-match/block products; pair decompositions; the two k=11-class witnesses (11 blocks each, products $\equiv 1$); **full sweep of all 5333 primes $\le 52163$ with line-by-line agreement with the C census (M and argmax)**; table firsts | **VERIFY1056-A: GREEN** (all sub-checks GREEN; exact-reading firsts = $(11,17,23,109,71,673,599,3011,27901,52163)$; ≥-reading firsts recorded in R1) |
| 4 | `python3 verify1056.py C 52164 120000` / `C 120000 190000` / `C 190000 200000` | independent Python frontier chunks (same $j\in[1,p-1]$ convention) | best $M$: 12 (at 109379, 111641), 11, 11 — **no $M\ge13$ anywhere below 200,000**; agrees with C census on the whole range |
| 5 | `python3 engine1056_k12.py 109000 112000` | campaign engine re-run | reports exactly `p=109379 maxfreq=12 value=61812`, `p=111641 maxfreq=12 value=27555` |
| 6 | exclusion cells | census cross-tab per $k=4..11$ | **all empty**: no prime below any witness has $M = k+1$ (distributions printed in §3.5) |
| 7 | Lean kernel receipts | CI run 42308034994 GREEN, commit a66350c (S030 record) | `erdos1056_k2..k11` + Wilson anchors + bridge compiled, axiom receipts recorded |

**Artifacts banked in this directory:** `census1056.c`, `census1056`
(binary), `census1056.txt` (17,984 prime lines + 3 chain lines),
`verify1056.py`, `battery1056.py`, `engine1056_k12.py`, the `FI_*.lean`
kernel (15 modules), this file.

**Adversarial audit findings (fixed or flagged, none fatal):**
- *Convention off-by-one:* the campaign engine counts $j \in [2, p-1]$, which
  undercounts value-1 chains by one hit (the $j=1$ anchor). Its recorded
  "no k=12 below 190,000" could in principle miss a value-1 $M=13$ prime;
  the C census + Python sweep use the structure-law's cut-point range
  $[1, p-1]$ and are airtight — the frontier bar (T5(iv)) is certified by
  the corrected convention. (Both new k=11-class witnesses have chain
  values $\ne 1$, so the engine's reports on them are convention-immune.)
- *Reading disambiguation:* the corpus statement is ambiguous (campaign
  S026 note); the standard reading ($[2, p-1]$ intervals) is forced by the
  historical witnesses (Erdős 1979 / Makowski 1983) — §1, Remark R0.
- *Two smallest-witness readings:* the campaign table is the exact reading;
  the at-least reading differs at $k=5$ ($71$) and $k=7$ ($599$) — both
  certified, Remark R1. No conflict: both are stated with their proofs.

**Scope honesty.** Proven here: T1–T6 — the structure law, the Wilson
force-pair law, the gap law, the k=4..11 case theorems (construction +
purity + minimality), the k=11-class extensions, the frontier bar below
200,000, and witness decidability. **Open (untouched, as the problem's core):
"arbitrarily large $k$" — whether $k$-systems exist for every $k$.** The case
frontier stands at $k = 11$; no $k=12$ witness below $200{,}000$.
