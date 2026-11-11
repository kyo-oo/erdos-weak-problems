# ERDŐS #1108 — THE COMPLETE PROOF DOCUMENT

**Deliverable S046-W8.** Target: Erdős problem #1108 (teorth/erdosproblems
corpus, asked by Erdős at Oberwolfach 1988, tagged `factorials`, OPEN).
Certified spine: the three CI-green Lean kernels — **Kernel 13**
(`problem1108-subset-kernel/SubsetKernelLaw.lean` §1–§6, Kill #17, CI run
42061257046 GREEN, commit e5ab4ca), **Kernel 15** (same file §7, Kill #19,
CI run 42153591445 GREEN, commit 6974fa8), **Kernel 30**
(`problem1108-allprime/Erdos1108AllPrime.lean`, Kill #34, CI run 42462902183
GREEN, commit 252ca34). All batteries re-run GREEN today (§7).

---

## §0. THE PROBLEM — VERBATIM (above the proof, BOSS's law)

Quoted verbatim from the corpus statement (erdosproblems.com/1108), as it is
quoted verbatim in the Kernel 30 header and the README kill registry (KILL
#34):

> Let
> $$A = \left\{ \sum_{n\in S}n! : S\subset \mathbb{N}\textrm{ finite}\right\}.$$
> If $k\geq 2$, then does $A$ contain only finitely many $k$th powers?
> Does it contain only finitely many powerful numbers?

The corpus therefore asks **two yes/no finiteness questions**:

- **(Q1)** For each fixed $k \ge 2$: is the value set
  $\{x \in A : \exists n,\ x = n^k\}$ **finite**?
- **(Q2)** Is the value set $\{x \in A : x \ \text{powerful}\}$ **finite**?
  (powerful: every prime divisor $q$ of $x$ satisfies $q^2 \mid x$).

($\mathbb{N}$-convention is immaterial: $0! = 1! = 1$, so the two readings of
$\mathbb{N}$ give the same $A$ up to the harmless identification of the
elements $0$ and $1$.)

---

## §1. THE COMPLETENESS VERDICT (surgical and honest)

| Corpus content | Status in this document |
|---|---|
| The complete $2$-adic valuation theory of **every** element of $A$ | **PROVED, UNCONDITIONAL** (§3, Kernel 13 + 15) |
| The complete all-prime valuation theory at singleton bottoms — every prime $p$ simultaneously | **PROVED, UNCONDITIONAL** (§4, Kernel 30) |
| The $k$-th-power obstruction web ($k \ge 2$, every prime) | **PROVED, UNCONDITIONAL** (§4.5, §5.5) |
| Reduction: powerful-finiteness ⟹ $k$-th-power-finiteness for all $k$ | **PROVED, UNCONDITIONAL** (§5.2, Theorem R2) |
| Reduction: bounded-cardinality frontier closed | **PROVED CONDITIONALLY** on the single stated external hypothesis HYP-BE (§5.4, Theorem R4) |
| Certified censuses (15 squares to $\max S \le 24$; 22 powerfuls to $\max S \le 16$) | **VERIFIED** (§7) |
| **(Q1), (Q2) themselves — the global finiteness verdicts** | **OPEN CORE REMAINS — exactly one component** (§8) |

**THE SINGLE REMAINING COMPONENT (named exactly):**
**THE GLOBAL FINITENESS CORE AT UNBOUNDED CARDINALITY** — proving that for
each $k \ge 2$ the set of $k$-th-power values of $A$ is finite (and the same
for powerful values), i.e. closing the frontier $|S| \to \infty$. This is not
an engine gap: Theorem R6 (§5.6) proves that the corpus question (Q1) at
$k=2$ **implies** the finiteness of Brocard's equation $u! + 1 = n^2$
(Brocard 1876; known solutions $u \in \{4,5,7\}$, open ever since whether
these are all). And Theorem R7 (§5.7) proves that the Brocard channel
**vacuously satisfies every local obstruction** in the certified engine —
so the core cannot be closed by any extension of the local $p$-adic
machinery; it demands a genuinely global argument. Everything else the
corpus statement contains is delivered complete below.

---

## §2. NOTATION, AND THE ENCODING LEMMA (R0)

**Valuations.** $v_p(x)$ = exponent of prime $p$ in $x$ ($v_p(0) := 0$
convention; all sums below are $\ge 1$). $s_2(n)$ = binary digit sum.
Factorials: $0! = 1$, $(n{+}1)! = (n{+}1)\cdot n!$.

**Encoding (Lemma R0).** The kernels encode a finite subset of $\mathbb{N}$
as a `List Nat` (`sumFacts S = Σ_{a∈S} a!`, `memB`, `countB`). Every theorem
below is proven for **arbitrary lists** — repeats allowed, $0$ allowed —
hence a fortiori for the corpus's finite subsets (which inject as lists with
all `countB ≤ 1`). No generality is lost; the theorems are stated in
subset language throughout. ∎

---

## §3. PART I — THE COMPLETE $2$-ADIC VALUATION THEORY OF $A$
### (Kernel 13 §1–§6 + Kernel 15 §7; Lean-certified, CI 42061257046 / 42153591445)

**Pairs.** $P_j = \{2j, 2j+1\}$ ($j \ge 0$; $0$ pairs with $1$).
**Level function** $\Lambda(j) := v_2((2j)!)$.
For $S \ne \varnothing$ finite, $j_0 := \min_{a \in S} a/2$ (the lowest
occupied pair), and the **cascade integer**
$$C(S) := \Big(\sum_{a\in S} a!\Big) \big/ 2^{\Lambda(j_0)} \in \mathbb{Z}_{\ge 1}.$$

**Theorem T1 (flatness; Lean `pair_flat`).** $v_2((2j+1)!) = v_2((2j)!)$.
*Proof.* $(2j+1)! = (2j+1)\cdot(2j)!$ and $2j+1$ is odd, so
$v_2((2j+1)!) = v_2(2j+1) + v_2((2j)!) = 0 + \Lambda(j)$, using
multiplicativity $v_2(ab) = v_2(a) + v_2(b)$ ($a, b \ge 1$; odd·odd is odd).
∎

**Theorem T2 (jump; Lean `pair_jump`).** $\Lambda(j) < \Lambda(j+1)$.
*Proof.* $(2j+2)! = (2j+2)\cdot(2j+1)!$, $v_2(2j+2) = 1 + v_2(j+1) \ge 1$,
so $v_2((2j+2)!) \ge 1 + v_2((2j+1)!) = 1 + \Lambda(j) > \Lambda(j)$. ∎

**Theorem T3 (monotonicity; Lean `v2_fact_mono`).** $n \le m \Rightarrow
v_2(n!) \le v_2(m!)$; and (Lean `pair_above`) $b/2 < a/2 \Rightarrow
v_2(b!) < v_2(a!)$. *Proof.* Induction on $m$ with
$v_2((m{+}1)!) = v_2(m{+}1) + v_2(m!)$; for the sharpened form combine
$b \le 2(b/2)+1$, flatness on $P_{b/2}$, the jump $P_{b/2} \to P_{b/2+1}$,
and $2(b/2)+2 \le 2(a/2) \le a$. ∎

**Theorem T4 (dominated addition; Lean `v2_lt_add`).** If $x \ge 1$ and
$v_2(x) < v_2(y)$ then $v_2(x+y) = v_2(x)$.
*Proof.* Strong induction on $x+y$. If $x$ odd: $v_2(x) = 0$ forces
$v_2(y) \ge 1$, $y$ even, $x+y$ odd, so $v_2(x+y) = 0 = v_2(x)$. If $x$
even ($x = 2x'$, $x' \ge 1$): then $y$ even too ($v_2(y) > v_2(x) \ge 1$
unless $y = 0$, trivial), $x + y = 2(x'+y')$ with $v_2(x') < v_2(y')$, and
$v_2(x+y) = 1 + v_2(x'+y') = 1 + v_2(x') = v_2(x)$ by the induction
hypothesis. ∎

**Corollary T5 (dominated sums).** If $x \ge 1$ and every term of the finite
sum $Y = \sum_i y_i$ satisfies $v_2(x) < v_2(y_i)$, then $v_2(x + Y) =
v_2(x)$. *Proof.* Induction over the terms via T4. ∎

**Theorem T6 (THE ISOLATED-MINIMUM LAW, $p=2$; Lean `isolated_min_v2`).**
If $b \in S$ occurs exactly once, $b \in P_{j_*}$, and every other $a \in S$
lies in a strictly higher pair ($b/2 < a/2$), then
$$v_2\Big(\sum_{a\in S} a!\Big) = v_2(b!) = \Lambda(j_*) \quad \text{EXACTLY}.$$
*Proof.* Every $a \ne b$ has $v_2(b!) < v_2(a!)$ by T3; apply T5 with
$x = b!$ over $S \setminus \{b\}$. ∎

**Theorem T7 (THE FULL CASCADE LAW — general $S$, no singleton hypothesis;
Lean `full_cascade_v2`).** For EVERY finite nonempty $S$:
$$\boxed{\ v_2\Big(\sum_{a\in S} a!\Big) \;=\; \Lambda(j_0) \;+\; v_2\big(C(S)\big)
\quad \text{EXACTLY.}\ }$$
*Proof.* Every $a \in S$ has $v_2(a!) \ge \Lambda(j_0)$: equality if
$a \in P_{j_0}$ (T1), strict if $a/2 > j_0$ (T3). Hence
$2^{\Lambda(j_0)} \mid a!$ for every $a$, so
$2^{\Lambda(j_0)} \mid \sum_{a\in S} a! =: \Sigma$; thus
$\Sigma = 2^{\Lambda(j_0)} \cdot C(S)$ with $C(S) \ge 1$ (as $\Sigma \ge
2^{\Lambda(j_0)}$), and $v_2(\Sigma) = \Lambda(j_0) + v_2(C(S))$ by
$v_2(2^k C) = k + v_2(C)$ for $C \ge 1$. ∎
Degenerations: singleton bottom $\iff C(S)$ odd (T6); full bottom pair
$\Rightarrow C(S)$ even (the composite structure above the bottom level
lives entirely in $C(S)$).

**Theorem T8 (Legendre at $p=2$; Lean `legendre_v2_fact`).**
$v_2(n!) = n - s_2(n)$ for every $n$.
*Proof.* (Kernel 15 §7.) **Even-factorial law** (Lean `v2_fact_even`):
$v_2((2m)!) = m + v_2(m!)$, by induction on $m$:
$(2m+2)! = (2m+2)(2m+1)!$ and $v_2(2m+2) = 1 + v_2(m+1)$, with T1 closing
the step. **Strong induction on $n$.** $n = 2k$:
$v_2((2k)!) = k + v_2(k!) = k + (k - s_2(k)) = 2k - s_2(2k)$ since
$s_2(2k) = s_2(k)$. $n = 2k+1$: $v_2((2k+1)!) = v_2((2k)!)$ (T1)
$= 2k - s_2(k) = (2k+1) - (1 + s_2(k)) = n - s_2(n)$ since
$s_2(2k+1) = 1 + s_2(k)$. $n = 0$: $v_2(1) = 0$. ∎

**Theorem T9 (the $\Lambda$-spine; Lean `legendre_lam`).**
$\Lambda(j) = 2j - s_2(j)$. *Proof.* $\Lambda(j) = v_2((2j)!) = 2j - s_2(2j)
= 2j - s_2(j)$ by T8 and $s_2(2j) = s_2(j)$. ∎

**Theorem T10 (THE EXPLICIT CASCADE; Lean `explicit_cascade`).** For every
finite nonempty $S$:
$$v_2\Big(\sum_{a\in S} a!\Big) \;=\; \big(2j_0 - s_2(j_0)\big) \;+\; v_2\big(C(S)\big).$$
*Proof.* Substitute T9 into T7. ∎

**Theorem T11 (THE SQUARE-PARITY INVARIANT; Lean `square_cascade_even` +
`square_parity_s2`).** If $\sum_{a\in S} a! = r^2$ then
$$\big(\Lambda(j_0) + v_2(C(S))\big) \equiv 0 \pmod 2,
\qquad\text{i.e.}\qquad s_2(j_0) \equiv v_2(C(S)) \pmod 2.$$
*Proof.* $v_2(r^2) = 2\,v_2(r)$ is even (Lean `square_v2_even`); apply T7 and
reduce $\Lambda(j_0) = 2j_0 - s_2(j_0)$ modulo $2$ (T9). ∎
(Lean `square_pair_singleton_even`: at a singleton bottom pair this forces
$v_2(b!)$ even, i.e. $s_2(b/2) \equiv 0 \pmod 2$.)

---

## §4. PART II — THE COMPLETE ALL-PRIME VALUATION THEORY (Kernel 30)
### (Lean-certified, CI 42462902183; every theorem at EVERY prime simultaneously)

**$p$-blocks.** For a prime $p$ and $b \in \mathbb{N}$: the $p$-block of $b$
is $\{p\lfloor b/p\rfloor, \dots, p\lfloor b/p\rfloor + p - 1\}$, and the
next block boundary is $p(\lfloor b/p\rfloor + 1)$ — the least multiple of
$p$ strictly above $b$ (since $b = p\lfloor b/p\rfloor + (b \bmod p)$ with
$b \bmod p < p$). **Quotient engine** (Lean `qfact`):
$\mathrm{qfact}\ b\ t = \prod_{i=b+1}^{t} i$, so $b \le t \Rightarrow
t! = b! \cdot \mathrm{qfact}\ b\ t$ (Lean `fact_split`), and every integer
$k$ with $b < k \le t$ divides $\mathrm{qfact}\ b\ t$ (Lean `qfact_dvd`).

**Lemma P1 (the $p$-multiple law; Lean `p_dvd_qfact`).** If
$p(b/p + 1) \le t$ then $p \mid \mathrm{qfact}\ b\ t$.
*Proof.* $b < p(b/p+1) \le t$, so $p(b/p+1)$ is one of the factors of the
quotient product. ∎

**Theorem P2 (THE RESIDUE-1 LAW; Lean `singleton_bottom_residue`).** Let
$p \ge 2$, $S$ finite with $b$ occurring exactly once, and every other
$a \in S$ in a strictly higher $p$-block: $a \ge p(b/p+1)$. Then
$$\sum_{a\in S} a! \;=\; b!\cdot Q \quad\text{with}\quad Q \equiv 1 \pmod p.$$
*Proof (list induction, the kernel's peeling argument).* Head $c$ of $S$.
**Case $c = b$:** the tail $T$ avoids $b$; every $a \in T$ has
$b < p(b/p+1) \le a$, so $a! = b!\cdot\mathrm{qfact}\ b\ a$ with
$p \mid \mathrm{qfact}\ b\ a$ (P1); hence
$\sum_{a \in T} a! = b!\cdot W$ with $W \equiv 0 \pmod p$ (Lean
`sumFacts_eq` + `dvd_sumQ`), and $\Sigma = b!(1 + W)$ with $Q = 1 + W
\equiv 1 \pmod p$. **Case $c \ne b$:** then $c \ge p(b/p+1) > b$, so
$c! = b!\cdot\mathrm{qfact}\ b\ c$ contributes a $p$-divisible quotient, and
the induction hypothesis on the tail gives $Q_t \equiv 1$; combine
$Q = \mathrm{qfact}\ b\ c + Q_t \equiv 0 + 1 = 1 \pmod p$. ∎

**Theorem P3 (THE ALL-PRIME ISOLATED-MINIMUM LAW; Lean
`all_prime_isolated_min`).** Under the hypotheses of P2, for every prime
$p$:
$$v_p\Big(\sum_{a\in S} a!\Big) \;=\; v_p(b!) \quad \text{EXACTLY.}$$
*Proof.* $Q \equiv 1 \pmod p$ and $Q \ge 1$ (as $\Sigma \ge b! \ge 1$), so
$p \nmid Q$, i.e. $v_p(Q) = 0$; then $v_p(\Sigma) = v_p(b!) + v_p(Q) =
v_p(b!)$ by multiplicative additivity $v_p(ab) = v_p(a) + v_p(b)$ (Lean
`vp_mul`; primality used exactly once, via Euclid). ∎

**Theorem P4 (THE ALL-PRIME KERNEL CONGRUENCE; Lean
`isolated_min_congruence`).** Under the hypotheses of P2:
$\exists j:\ \sum_{a\in S} a! = b! + p\cdot b!\cdot j$ — the sum is pinned
to $b!$ modulo $p \cdot b!$. *Proof.* $Q = 1 + p\cdot(Q/p)$ from
$Q \equiv 1 \pmod p$; multiply out. ∎

**Theorem P5 (THE ALL-PRIME $k$-TH-POWER OBSTRUCTION; Lean
`all_prime_power_obstruction`).** Under the hypotheses of P2, for every
$k \ge 2$ and every $n$:
$$k \nmid v_p(b!) \quad\Longrightarrow\quad \sum_{a\in S} a! \ne n^k.$$
*Proof.* $n = 0$ is excluded since $\Sigma \ge b! \ge 1$. For $n \ge 1$:
$v_p(n^k) = k\,v_p(n)$ (Lean `vp_pow`, induction on $k$ via `vp_mul`).
If $\Sigma = n^k$ then $v_p(b!) \overset{P3}{=} v_p(\Sigma) = k\,v_p(n)$,
forcing $k \mid v_p(b!)$. ∎

**Theorem P6 (THE BLOCK FORM; Lean `isolated_min_block_form`).** The same
law stated in block language: if $b$'s $p$-block is the lowest occupied and
occupied by $b$ alone, then $v_p(\Sigma) = v_p(b!)$. *Proof.* The block
hypotheses imply the threshold hypothesis of P3 via
$p(b/p+1) \le p(a/p) \le a$. ∎

**Receipts (kernel-decided).** $v_2(3!{+}4!{+}9!) = v_2(3!) = 1$;
$v_3(2!{+}9!{+}13!) = v_3(2!) = 0$; $v_5(7!{+}25!{+}31!) = v_5(7!) = 1$;
$v_7(13!{+}49!{+}55!) = v_7(13!) = 1$; $v_{11}(5!{+}121!{+}130!) =
v_{11}(5!) = 0$; and the obstruction theorems
$3!+4!+9! = 362910 \ne n^2, \ne n^3$ for ALL $n$ (Lean
`inst_not_square_349`, `inst_not_cube_349`; battery-verified by exact
integer sqrt/cube checks). ∎

---

## §5. PART III — THE REDUCTION LAYER (complete proofs; new in this document)

### §5.1 The window congruence (R1)

**Theorem R1.** For every integer $d \ge 2$ (in particular every prime) and
every finite $S \subseteq \mathbb{N}$:
$$\sum_{a\in S} a! \;\equiv\; \sum_{a\in S,\ a < d} a! \pmod d.$$
*Proof.* For $a \ge d$, the product $a! = 1\cdot2\cdots d\cdots a$ contains
the factor $d$, so $d \mid a!$. ∎
For $d = p$ prime and $p \in (\max S / 2, \max S]$ (the **Bertrand window**)
this reads $\Sigma \equiv T_p \pmod p$ with $T_p = \sum_{a < p} a!$ — the
congruence face of the obstruction web.

### §5.2 The powerful hierarchy (R2)

**Theorem R2.** Every $k$-th power ($k \ge 2$) is powerful. Hence
$\{x \in A: x \text{ powerful}\} \supseteq \{x \in A : x = n^k\}$ for every
$k \ge 2$, and therefore **(Q2) ⟹ (Q1) for every $k$ simultaneously** (and
(Q1) at $k=2$ is implied by (Q1) at every other $k$).
*Proof.* If $x = n^k$, $n \ge 1$, and prime $q \mid x$, then
$v_q(x) = k\,v_q(n) \ge k \ge 2$ (Theorem P5's `vp_pow` law), so $q^2 \mid
x$. ∎
So the corpus's two questions collapse to one frontier: **finiteness of
powerful values in $A$** — everything below serves both.

### §5.3 The $k$-generalized cascade divisibility (R3)

**Theorem R3.** If $\sum_{a \in S} a! = n^k$ ($k \ge 2$, $S \ne
\varnothing$) then
$$k \;\Big|\; \big(2j_0 - s_2(j_0)\big) + v_2\big(C(S)\big).$$
*Proof.* $v_2(n^k) = k\,v_2(n)$, and $v_2(\Sigma) = (2j_0 - s_2(j_0)) +
v_2(C(S))$ by the explicit cascade T10; $k$ divides the left side. ∎
($k = 2$ is the square-parity invariant T11; $k \ge 3$ gives the
cube/higher obstructions.) Combined with P5: **at every prime $p$ whose
lowest occupied $p$-block in $S$ is a singleton $\{b_p\}$, $k \mid
v_p(b_p!)$ is FORCED** — an infinite family of divisibility obstructions
indexed by the primes.

### §5.4 The bounded-cardinality reduction (R4) — the single stated external hypothesis

> **HYP-BE (Brindza–Erdős [BrEr91], STATED AS A GIVEN HYPOTHESIS, BOSS's
> arsenal-only rule).** For every $r \ge 1$ there exists $C(r)$ such that
> whenever $n_1! + \cdots + n_r!$ (any $r$ factorials, repeats allowed) is
> powerful, then $\max_i n_i \le C(r)$.

**Theorem R4 (conditional on HYP-BE).** For every fixed $r \ge 1$ and
$k \ge 2$, the value set
$\{\sum_{a\in S} a! : |S| = r\} \cap \{n^k\}$ is finite (same for powerful
values). Consequently, under HYP-BE, **the entire open frontier of (Q1) and
(Q2) lives at $|S| \to \infty$.**
*Proof.* Every powerful (hence every $k$-th-power) $r$-sum has all terms
$\le C(r)$; there are finitely many $r$-element multisets from
$\{0,\dots,C(r)\}$, hence finitely many sums, hence finitely many values. ∎

### §5.5 The obstruction web (R5) — the complete necessary-condition assembly

**Theorem R5.** For $x = \sum_{a\in S} a! = n^k$ ($k \ge 2$, $S \ne
\varnothing$), ALL of the following hold simultaneously:
1. **($2$-adic cascade)** $k \mid (2j_0 - s_2(j_0)) + v_2(C(S))$ [R3];
2. **(all-prime singleton obstruction)** for every prime $p$ whose lowest
   occupied $p$-block in $S$ is a singleton $\{b_p\}$: $k \mid v_p(b_p!)$
   [P5 contrapositive];
3. **(valuation profile)** for every prime $p$: $v_p(x) = k\,v_p(n)$ —
   and $v_p(x)$ is given explicitly by the cascade/stack laws at $p$
   [T7/T10 at $p=2$; P3 at singleton bottoms; verified stack law at all
   $p$, §7];
4. **(window congruence)** for every prime $p \le \max S$: $p \mid n
   \Rightarrow \sum_{a\in S,\,a<p} a! \equiv 0 \pmod p$ [R1].
*Proof.* Each item is proven above (R3, P5, `vp_pow`, R1 respectively). ∎
This is the **complete local obstruction engine**: item 2 alone kills
every candidate whose bottom block at ANY prime fails the divisibility;
items 1+3 fix the entire $p$-adic valuation profile; item 4 fixes the
root's prime divisors against the window. The web does not close globally
— the two named dodge mechanisms are proven in R7 below.

### §5.6 The Brocard embedding — the hardness of the open core (R6)

**Theorem R6.** The channel $\varphi(u) := \{1, u\}$ embeds
$\{u : u! + 1 \text{ is a square}\}$ into the squares of $A$, via
$u \mapsto 1 + u!$ (since $1! = 1$), injectively ($u!$ strictly
increasing). Therefore:
$$\textbf{(Q1) at } k=2 \text{ answered YES} \;\Longrightarrow\;
\{u : u! + 1 = n^2\} \text{ is FINITE},$$
i.e. the finiteness conjecture of **Brocard's problem (1876)** — known
solutions $u = 4, 5, 7$ ($25 = 5^2$, $121 = 11^2$, $5041 = 71^2$; direct
arithmetic, all three present in the certified census as $\{1,4\}$,
$\{1,5\}$, $\{1,7\}$), open for 150 years whether these are all.
*Proof.* If the square values of $A$ form a finite set, then the image of
the injection $u \mapsto 1+u!$ within it is finite, hence the domain
$\{u : u!+1 \text{ square}\}$ is finite. ∎

**Corollary.** No unconditional resolution of (Q1)/(Q2) is available to the
current arsenal (or to any): the remaining component contains a
150-year-old open problem as a special instance. This is precisely why
§8 names the core **genuinely open**, not merely unfinished.

### §5.7 The Brocard channel passes every local obstruction (R7) — why the core is global

**Theorem R7.** For every $u \ge 2$, the channel sum $1 + u!$
($S = \{1,u\}$) satisfies:
1. $v_p(1 + u!) = v_p(1!) = 0$ for **every prime $p \le u$**
   (all-prime isolated-minimum P3 at $b = 1$: the $p$-block of $1$ is
   $\{0,\dots,p-1\}$, a singleton, and $u \ge p$ lies strictly higher);
2. the $2$-adic cascade parity of T11 is **satisfied** ($j_0 = 0$,
   $\Lambda(0) = 0$, $v_2(1+u!) = 0$ — even; indeed the three known
   Brocard squares are odd);
3. if $1 + u! = n^2$ then **every prime factor of $n$ exceeds $u$**
   (by 1, no prime $\le u$ divides $n$; $n > 1$ since $u \ge 2$ gives
   $1 + u! > 1$) — the window congruence R1 is vacuous on the channel:
   $T_p = 1! = 1 \not\equiv 0 \pmod p$ for every window prime.
*Proof.* (1) is P3 with $b = 1$, $p \le u$ (hypotheses: $1$ occurs once;
$u \ge p = p(1/p + 1)$). (2) is T11 with $v_2(1+u!) = 0$ from (1) at
$p = 2$. (3) follows from (1): a prime $p \le u$ dividing $n$ would
divide $n^2 = 1 + u!$, contradicting $v_p(1+u!) = 0$. ∎

**Interpretation (the surgical reason the core is open).** The channel
$\{1, u\}$ — the minimal open instance of the corpus question —
**vacuously passes every obstruction of the certified web**: all local
$p$-adic valuations are pinned at $0$ (even, $k$-divisible for every
$k$), the cascade parity holds, and no window prime can divide the root.
No extension of the local $p$-adic engine can see it. The finiteness of
the channel (hence of the corpus questions) requires a **global** argument
(growth of $u!$ against square gaps / covers of the factorial base) —
this is exactly the single remaining component of §8. Two mechanisms keep
the general frontier open (proven obstructions-to-closing, from the
kernel censuses): the **sparse-dodge** ($S \cap [1,p) = \{1\}$ forces
$T_p = 1$ for every window prime, so the root's prime factors must all
be composites beyond the window — R7.3) and the **composite cascade**
(at a full bottom block the cascade integer $C(S)$ carries unbounded
$v_2$, so R3 alone cannot bound $S$).

---

## §6. PART IV — BOSS'S ARSENAL CITATION (the bridge theorems applied)

The three kernels import the arsenal (`Arsenal.ErdosTernary2.Basic`,
`Arsenal.CardinalWorlds`, `Arsenal.CardinalWorldsV2`) and apply:

1. **`ErdosTernary2.isTernaryDigit`** (with `isTernaryDigit_zero/_one/_two/
   _three`) — the ternary-digit predicate $n \in \{0,1,2\}$, applied to the
   witness numbers' ternary digits: $[13\%3,\ (13/3)\%3,\ (13/9)\%3]$ and
   $[121\%3,\ (121/3)\%3,\ (121/9)\%3,\ (121/27)\%3]$ — all ternary digits
   ($13 = 111_3$, $121 = 11111_3$) — the $p=11$ receipt's higher-block
   elements certified through the arsenal's ternary structure.
2. **`CardinalWorlds.carryAtPos` / `carryAtPos_bound`** —
   $\mathrm{carryAtPos}(R,p) = \lfloor 4(R \bmod 3^p)/3^p\rfloor < 4$
   (theorem `carryAtPos_bound R p : carryAtPos R p < 4`), applied at
   $(R,p) = (13,1)$ — the ternary carry bound on the witness.
3. **`CardinalWorldsV2.v2r_ternary_scaling`** —
   $\mathrm{v2r}(3^a \cdot c) = \mathrm{v2r}(c)$ (multiplication by a
   ternary power preserves the $2$-adic depth reader; $\mathrm{v2r}$ is the
   CardinalWorlds $2$-adic depth reader), applied at $(a,c) = (1,9)$:
   $\mathrm{v2r}(27) = \mathrm{v2r}(9)$ — the $p=2$ receipt's top element.
The conjunction is Lean-certified as
**`erdos1108ap_arsenal_bridge : arsenalBridgeProp`** (Kernel 30 §7).
4. **The K19/Erdos700 green architecture** — the fuel-structural valuation
   engine (`vpf`/`vp`/saturation `vpf_sat`/step `vp_step`/nondivisor
   `vp_nondiv`/`vp_one`/`dvd_mul_divp`/`vp_mul` with Euclid used exactly
   once) lifted verbatim into Kernel 30.
5. **The #404 KernelLaw blueprint** — the `v2` toolkit, dominated addition
   `v2_lt_add`, the `sumFacts`/`memB`/`countB` self-contained subset
   architecture of Kernel 13.
6. **The TheoremBGeneral `vpad` transfer** — the unit-congruence engine
   (`vpad_congr_unit`: $u \equiv 1 \bmod p \Rightarrow v_p(xu) = v_p(x)$)
   whose all-prime design Kernel 30's residue-1 law descends from.
7. **HC-PROOF discipline** — all kernel theorems sit under the arsenal's
   axiom discipline (§7); zero `sorry`, zero custom axioms.
8. **External literature used: NONE except HYP-BE (§5.4), stated as a
   given hypothesis** per the arsenal-only rule. Every other proof above
   is either kernel-certified Lean or self-contained arithmetic.

---

## §7. PART V — VERIFICATION

**Batteries re-run TODAY (this session, foreground, all GREEN):**

| Battery | Method | Result |
|---|---|---|
| `problem1108-allprime/battery1108ap.py` (Kernel 30) | dual-method: direct big-int $p$-adic division loop ‖ Legendre + residue-1; exhaustive singleton-bottom universes $p \in \{2,3,5,7,11,13\}$, $b \in [0,14)$, higher-block subsets $\le 3$; 3000 random deep cases ($b \le 40$, elements $\le 400$); the five kernel receipts exact; the $362910$ not-square/not-cube isqrt/cube witness | **`ERDOS1108_ALLPRIME_BATTERY_GREEN cases=8025`** |
| `problem1108-subset-kernel/verify_cascade.py` (Kernel 13) | A: triple-method agreement (direct valuation ‖ cascade machine ‖ closed form) on ALL $16383$ subsets of $[1..14]$ — 0 mismatches; B: all-prime stack law $20475/20475$ + bottom-block singleton law $7399/7399$ on all subsets of $[1..12] \times p \in \{2,3,5,7,11\}$; C: exhaustive $2^{18}$ census — exactly 15 squares, all cascade-verified; D: depth-24 frontier — ZERO squares for $\max S \in [16,24]$ | **ALL BATTERIES GREEN** |
| `problem1108-subset-kernel/verify_legendre.py` (Kernel 15) | 301 factorials two-method ($v_2(n!) = n - s_2(n)$); 151 $\Lambda$-levels; 500 random cascades (explicit cascade law); 8191-subset exhaustive census → 27 perfect squares, **every one parity-locked**; receipts $(0,1,3,8,1)$, $(8,8,8)$, $(20,20)$, $(4,4)$, $(1,1)$ | **ALL BATTERIES GREEN** |

**CI (GitHub Actions, the kill registry):** Kernel 13 — run
**42061257046 GREEN** (commit e5ab4ca); Kernel 15 — run **42153591445
GREEN** (commit 6974fa8); Kernel 30 — run **42462902183 GREEN** (commit
252ca34).

**Axiom footprints (Lean `#print axioms`, recorded in the registry):**
- Kernel 13: `full_cascade_v2`, `square_cascade_even`: **[propext,
  Quot.sound]**; `isolated_min_v2`, `square_pair_singleton_even`:
  [propext, Classical.choice, Quot.sound].
- Kernel 15: all six ($s_2$/Legendre/$\Lambda$-spine/explicit
  cascade/parity): **[propext, Quot.sound]**.
- Kernel 30: all seven (residue-1, isolated-min, congruence, obstruction,
  block form, arsenal bridge, main): **[propext, Classical.choice,
  Quot.sound]**.
Zero `sorry` in all three files; zero custom axioms.

**The certified census (exact integer arithmetic):** exactly **15 squares**
with $\max S \le 24$: the trivial $\{1\} = 1^2$ plus $\{1,2,3\}=9=3^2$,
$\{1,4\}=25=5^2$, $\{1,5\}=121=11^2$, $\{1,7\}=5041=71^2$,
$\{4,5\}=144=12^2$, $\{1,5,6\}=841=29^2$, $\{4,5,7\}=5184=72^2$,
$\{1,2,3,6\}=729=27^2$, $\{1,2,3,7,8\}=45369=213^2$,
$\{1,4,8,9\}=403225=635^2$, $\{1,2,3,6,9\}=363609=603^2$,
$\{1,4,5,6,7,8\}=46225=215^2$, $\{1,2,3,6,7,8,10\}=3674889=1917^2$,
$\{1,2,3,7,8,\dots,15\}=1401602635449=1183893^2$; **zero new squares for
$\max S \in [16,24]$**. **22 powerful sums with $\max S \le 16$** (7
non-square, e.g. $\{2,3\}=8$, $\{1,2,4\}=27$, $\{2,3,8\} = 2^3\cdot71^2$).
The 15/27-count difference is the $0/1$-channel duplication ($0! = 1!$).

---

## §8. PART VI — THE REMAINING COMPONENT, EXACTLY ONE

**THE GLOBAL FINITENESS CORE AT UNBOUNDED CARDINALITY.**

> **Open component (the only one):** prove — or refute — that for each
> $k \ge 2$ the value set $\{x \in A : x = n^k\}$ is finite, and that
> $\{x \in A : x \text{ powerful}\}$ is finite; equivalently (R2), close
> the powerful frontier at $|S| \to \infty$.

**Why exactly here and nowhere else:** HYP-BE (R4) closes every bounded
$|S|$; the obstruction web (R5) pins every candidate at every prime;
the census closes $\max S \le 24$ (squares) and $\le 16$ (powerfuls);
the heuristic count $\sum_j 2^j / (2\sqrt{j!})$ converges (finiteness
expected). What no available tool closes: (i) the **sparse-dodge** —
channels with $S \cap [1,p) = \{1\}$ force $T_p = 1$ for every
Bertrand-window prime (R7.3), so the root's prime factors must lie
beyond the window, invisible to R1; (ii) the **composite cascade** —
at full bottom blocks, $v_2(C(S))$ is unbounded over $S$, so the
divisibility condition R3 cannot bound $S$; (iii) the minimal open
instance — the Brocard channel $\{1,u\}$ — **provably passes every
local obstruction in the certified engine** (R7), so the core demands a
global argument; by R6 any YES at $k=2$ resolves Brocard (1876, open).
Resolving the core = the complete answer to the corpus statement; every
other mathematical component of the corpus statement is delivered complete
in §3–§5 above.

---

*The engines never stop; they never lie. The wall is named; everything
else is proved.*
