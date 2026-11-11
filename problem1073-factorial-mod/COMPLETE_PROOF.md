# COMPLETE_PROOF.md — Erdős #1073: THE FACTORIAL-MOD COMPOSITE CENSUS

**W9 strike (Kernel 34, S046 volley).** Engine: MATHS/berserker. Spine: the CI-green
kernel `problem1073-factorial-mod/Erdos1073.lean` (CI run 42552313506 ALL GREEN, kill #38
registered, the 7-round compile war won — receipts §8). This document assembles the
complete theorem package with full mathematical proofs, states the corpus ask verbatim,
closes every finite gap the ask involves, and names the single remaining component
(the asymptotic law itself) with everything else complete.

---

## §0. THE PROBLEM (verbatim, erdosproblems.com/1073 — Erdős, with Hardy–Subbarao [HaSu02])

> Let $A(x)$ count the number of composite $u<x$ such that
> $n!+1\equiv 0 \pmod{u}$ for some $n$. Is it true that $A(x)\leq x^{o(1)}$?

The sequence of such $u$ begins $25, 121, 169, 437, \ldots$ (OEIS A256519).

**Interpretation (fixed throughout; identical to the Lean kernel `Erdos1073.lean` §0).**

$$A(x)\ :=\ \#\{\,u\in\mathbb N:\ u<x,\ u\ \text{composite},\ \exists\, n\ge 1:\ u\mid n!+1\,\}.$$

"Composite" means $u=ab$ with $1<a\le b<u$, i.e. $u\ge 4$ and $u$ not prime. The witness
$n$ is a *positive* integer ($n=0$ would give $0!+1=2$, never divisible by any $u\ge 4$).

**Why the word "composite" is the entire content (context remark).** For *prime* $u=p$,
Wilson's theorem gives $(p-1)!\equiv -1\pmod p$ for **every** prime $p$: the prime layer of
the divisibility relation is all of it, with count $\pi(x)\sim x/\log x = x^{1-o(1)}$ —
**not** $x^{o(1)}$. The conjecture is therefore exclusively about the composite layer:
the composite divisors of the factorial-shift sequence $n!+1$ must be sparse even though
the prime divisors are dense. The kernel's Wilson channel (§5.1) is the composite echo of
Wilson's theorem (Wilson *primes*: $p^2\mid(p-1)!+1$ — rare, squares are hits).

**The ask, decomposed.** The corpus sentence asks one thing: a yes/no answer, with proof,
for the asymptotic law $\lim_{x\to\infty}\frac{\log A(x)}{\log x}=0$
(equivalently: for every $\varepsilon>0$, $A(x)\le x^{\varepsilon}$ for all large $x$).
Everything that the definition of $A$ involves — the structure of the hit set, its exact
finite values, its decidability, its channels — is **completely proved below** (§3–§6);
the asymptotic law is **named as the single remaining component** (§7), with the complete
reduction of the conjecture to that single statement (Theorem 6.1 / §7.2).

---

## §1. THE THEOREM BOARD

| # | Theorem | Content | Status |
|---|---|---|---|
| **T1** | **THE GCD/WINDOW LAW** | $u\ge 2,\ u\mid n!+1\Rightarrow$ every prime $p\mid u$ has $n<p$; witness window $=[1,P(u))$, $P(u)$ = least prime factor | **PROVEN** (§3.1; Lean `erdos1073_window`) |
| **T2** | **THE SATURATION LAW** | For $n\ge P(u)$, $u\nmid n!+1$ — the window never re-opens | **PROVEN** (§3.2; Lean `erdos1073_saturation`) |
| **T3** | **THE SMALL-PRIME-DIVISOR LAW** | Every composite $4\le u\le B^2$ has a prime divisor $q\le B$ (the $p/a$ case-split engine) | **PROVEN** (§3.3; Lean `small_prime_divisor`) |
| **T4** | **THE MASTER CHARACTERIZATION** | $u$ is a hit $\iff u$ composite and $u\mid n!+1$ for some $n<\sqrt u$; $A(x)$ is finitely decidable at every scale | **PROVEN** (§3.4, from T1+T3) |
| **T5** | **THE CLUSTER DECOMPOSITION** | $A(x)=\bigl\lvert\bigcup_{n<\sqrt x}C_n(x)\bigr\rvert$ with $C_n(x)=$ composite divisors $<x$ of $n!+1$; every such divisor is automatically $n$-rough; $A(x)\le\sum_{n<\sqrt x}d(n!+1)$ | **PROVEN** (§3.5–§3.6, from T1) |
| **T6** | **THE COMPLETE CENSUS AT $10^4$** | Composite hits $u\in[4,10^4]$ are **exactly** the 28-element table T28 (A256519 prefix); $A(10^4)=28$, $A(10^3)=7$ — **both directions** | **PROVEN** (§4.1; Lean `erdos1073_census`, `erdos1073_A10k`, 21 chunk decides) |
| **T7** | **THE 131-WITNESS TABLE AT $10^6$** | All 131 rows genuine: $4\le u<10^6$ composite, $1\le n\le 918$, $u\mid n!+1$ (incl. $563^2\!\mid\!562!+1$, $888673\!\mid\!918!+1$); completeness engine-certified dual-method | **PROVEN (soundness: kernel-decided; completeness: engine, §4.2)** |
| **T8** | **THE WILSON CHANNEL** | Wilson prime $p\Rightarrow p^2$ hit with witness $p-1$; instances $5^2\mid4!+1$, $13^2\mid12!+1$, $563^2\mid562!+1$ | **PROVEN** (§5.1; Lean `erdos1073_wilson`) |
| **T9** | **THE BROCARD CHANNEL** | Brocard pair $n!+1=m^2\Rightarrow m^2$ hit with witness $n$; instances $4!+1=5^2$, $5!+1=11^2$, $7!+1=71^2$ | **PROVEN** (§5.2; Lean `erdos1073_brocard`) |
| **T10** | **THE ARSENAL BRIDGE** | The witness numbers certified inside BOSS's arsenal world: `isTernaryDigit` digits of 563 and 316969, `carryAtPos_bound`, `v2r_ternary_scaling` | **PROVEN** (§6; Lean `erdos1073_arsenal_bridge`) |
| — | **THE ASYMPTOTIC LAW** $A(x)\le x^{o(1)}$ (Hardy–Subbarao) | The growth law for all $x$ | **OPEN — the single remaining component** (§7) |

**Completeness verdict.** Every finite and structural demand of the corpus statement is
completely proved (T1–T10); the answer to the corpus's asymptotic *question* is the
single remaining component named in §7. No sub-case is dressed as the answer.

---

## §2. NOTATION AND THE HIT PREDICATE

- $P(u)$ := least prime factor of $u\ge 2$ (Lean `Nat.minFac`; $P(u)$ is prime and $P(u)\mid u$).
- $d(N)$ := number of positive divisors of $N$; $n!$ := `Nat.factorial n`.
- **Hit$(u)$** :$\iff$ $u$ composite and $\exists\, n\ge 1:\ u\mid n!+1$. Then
  $A(x)=\#\{u<x:\mathrm{Hit}(u)\}$.
- **Witness window** of $u$: $W(u):=\{n\ge 1: u\mid n!+1\}$.

---

## §3. THE STRUCTURE THEORY — COMPLETE PROOFS (THE KERNEL SPINE)

### §3.1. T1 — THE GCD/WINDOW LAW

**Theorem 1.1 (Lean `erdos1073_window`, general).** If $u\ge 2$ and $u\mid n!+1$, then
every prime $p\mid u$ satisfies $n<p$. Consequently $W(u)\subseteq[1,P(u))$ and
$\gcd(u,n!)=1$.

*Proof.* Let $p$ be prime with $p\mid u$. Since $u\mid n!+1$ and $p\mid u$, transitivity
gives $p\mid n!+1$. Suppose, for contradiction, $p\le n$. Then $p$ appears among the
factors $1,2,\ldots,n$ of $n!$, so $p\mid n!$ (kernel `prime_dvd_fact`: induction on $k$ —
if $p\le k+1$ then either $p\le k$ and $p\mid k!\Rightarrow p\mid(k+1)\cdot k!$, or $p=k+1$
and $p$ is the last factor). Hence $p$ divides $(n!+1)-n! = 1$, forcing $p\le 1$ —
impossible for a prime ($p\ge 2$). Therefore $n<p$.
Applied to $p=P(u)$ (prime, divides $u$): every witness satisfies $n<P(u)$, i.e.
$W(u)\subseteq[1,P(u))$.
For the gcd form: $g:=\gcd(u,n!)$. Then $g\mid u\mid n!+1$ and $g\mid n!$, so $g\mid 1$;
hence $\gcd(u,n!)=1$, and no prime $p\mid u$ divides $n!$ — i.e. every $p\mid u$ exceeds
$n$ (for prime $p$: $p\mid n!\iff p\le n$). ∎

### §3.2. T2 — THE SATURATION LAW

**Theorem 1.2 (Lean `erdos1073_saturation`).** If $p$ is a prime divisor of $u$ and
$p\le n$, then $u\nmid n!+1$.

*Proof.* Suppose $u\mid n!+1$. Since $p\mid u$, $p\mid n!+1$. But $p\le n$ gives $p\mid n!$
(Theorem 1.1's factor argument), whence $p\mid 1$ — contradiction. (This is the
contrapositive of Theorem 1.1; the kernel proves it as stated, handling $u=0$ vacuously
via $\%0$.) ∎

**Consequence (the window never re-opens).** For fixed $u$, divisibility $u\mid n!+1$ is
impossible for **every** $n\ge P(u)$: the hit status of $u$ is decided entirely by the
finite window $[1,P(u))$.

### §3.3. T3 — THE SMALL-PRIME-DIVISOR LAW

**Theorem 1.3 (Lean `small_prime_divisor`, general).** Every $u$ with $4\le u\le B\cdot B$
that is not prime has a prime divisor $q\le B$.

*Proof.* Let $p:=P(u)$ (prime, $p\mid u$) and write $u=p\cdot a$ with $a=u/p\ge 2$ —
indeed $a\in\{0,1\}$ would force $u=0$ or $u=p$ prime, both excluded.
- If $p\le B$, take $q:=p$.
- If $p>B$: claim $a\le B$. Otherwise $a\ge B+1$ and $p\ge B+1$, so
  $(B+1)^2\le p\cdot a=u\le B^2$ — impossible since $(B+1)^2>B^2$. So $a\le B$, and
  $q:=P(a)$ is prime, divides $a$, hence divides $u$, and $q\le a\le B$. ∎

**Corollary 1.4 (the square-root window).** Every composite $u$ has $P(u)\le\sqrt u$.

*Proof.* $u=p\cdot a$ with $p=P(u)$; every prime factor of $a$ is $\ge p$, so $a\ge p$
and $u\ge p^2$. (Alternatively: Theorem 1.3 with $B:=\lceil\sqrt u\rceil$.) ∎

### §3.4. T4 — THE MASTER CHARACTERIZATION (the definitional reduction)

**Theorem 1.5 (hit criterion + decidability).** For every composite $u\ge 4$:

$$\mathrm{Hit}(u)\iff \exists\, n\in[1,P(u)):\ u\mid n!+1\iff \exists\, n<\sqrt u:\ u\mid n!+1.$$

Consequently, for every $x$:
$$A(x)=\#\{u<x:\ u\text{ composite},\ \exists\, n<\sqrt u,\ u\mid n!+1\},$$
a **finite, terminating scan** — the unbounded quantifier $\exists n\in\mathbb N$ in the
corpus definition is provably collapsible to the window $[1,\sqrt u)$.

*Proof.* ($\Rightarrow$) Theorem 1.1 gives every witness $n<P(u)$; Corollary 1.4 gives
$P(u)\le\sqrt u$. ($\Leftarrow$) A witness $n\ge 1$ with $u\mid n!+1$ is exactly the
definition of Hit$(u)$. The last display follows by substitution. Termination: the scan
runs $u$ over $[4,x)$ and $n$ over $[1,\sqrt u)$ — finitely many pairs. ∎

This theorem is the engine of every census below: **no unbounded search hides anywhere**.

### §3.5. T5 — THE CLUSTER DECOMPOSITION (the counting identity behind $x^{o(1)}$)

For $n\ge 1$ and $x>4$ define the **cluster**
$$C_n(x):=\{u:\ u\text{ composite},\ u<x,\ u\mid n!+1\}.$$

**Theorem 1.6 (auto-roughness).** Every divisor $u\ge 2$ of $n!+1$ has **all** prime
factors $>n$; every **composite** divisor of $n!+1$ exceeds $n^2$.

*Proof.* If $p\mid u\mid n!+1$ then Theorem 1.1 (with the roles $u\mapsto u$, witness
$n$) gives $p>n$. A composite divisor has at least two prime factors (with multiplicity),
each $>n$, so $u\ge(n+1)^2>n^2$. ∎

**Theorem 1.7 (cluster decomposition of $A$).** For every $x>4$:
$$A(x)=\Bigl\lvert\bigcup_{1\le n<\sqrt x}C_n(x)\Bigr\rvert\le\sum_{1\le n<\sqrt x}d(n!+1),$$
and the union is finite with a **provably complete** index set: every hit $u<x$ has a
witness $n<\sqrt u<\sqrt x$.

*Proof.* ($\subseteq$) A hit $u<x$ has a witness $n<\sqrt u<\sqrt x$ (Theorem 1.5); then
$u\in C_n(x)$. ($\supseteq$) $u\in C_n(x)$ means $u$ composite and $u\mid n!+1$ — a hit.
For the bound: $C_n(x)\subseteq$ the divisor set of $n!+1$, so $|C_n(x)|\le d(n!+1)$. ∎

**Theorem 1.8 (cluster saturation).** For fixed $n$, $C_n(x)$ is **eventually constant**
in $x$: $C_n(x)\subseteq$ divisor set of $n!+1$, so for all $x>n!+1$,
$C_n(x)=\{u\text{ composite}:\ u\mid n!+1\}$. Hence $A(x)$ is a step function that grows
**only** by the arrival of new clusters $n$ — each contributing at most $d(n!+1)$ members,
all $>n^2$ (Theorem 1.6).

*Proof.* Immediate from the definitions. ∎

This is the exact finite reformulation of the Hardy–Subbarao conjecture: the growth of
$A$ is precisely the **arrival stream of rich factorizations $n!+1$** (§7).

### §3.6. The bounds ladder (what the spine alone yields — the honest ceiling)

**Proposition 1.9 (elementary divisor bound).** $d(N)\le N$ for every $N\ge 1$.

*Proof.* $N=\prod p_i^{e_i}$ and $d(N)=\prod(e_i+1)$; each factor $e_i+1\le p_i^{e_i}$
(because $p_i\ge 2$ and $e+1\le 2^e\le p^e$ for $e\ge1$, while $e=0$ gives $1\le1$);
multiply. ∎

**Corollary 1.10 (the trivial growth bound).** $A(x)\le\sqrt x\cdot\bigl(\lfloor\sqrt x\rfloor!+1\bigr)$.

*Proof.* Theorems 1.7 + 1.9: at most $\sqrt x$ clusters, each contributing at most
$n!+1\le(\lfloor\sqrt x\rfloor)!+1$ divisors. ∎

This is $\exp\!\bigl(\tfrac12\sqrt x\log x\,(1+o(1))\bigr)$ — **exponentially** far from
$x^{o(1)}$. The spine closes every finite question but cannot, by itself, close the
asymptotic (§7).

---

## §4. THE CENSUS THEOREMS — EXACT, BOTH DIRECTIONS

### §4.1. T6 — THE COMPLETE CENSUS AT $10^4$ (kernel-decided, both directions)

**The 28-element table (the A256519 prefix):**
$$\mathrm{T28}:=\begin{aligned}[t](&25, 121, 169, 437, 551, 667, 721, 1037, 1159, 1273, 1349, 1403, 1541,\\
&1769, 1943, 2209, 2329, 2363, 2419, 3071, 3713, 4087, 5041, 5111,\\
&7313, 8357, 8479, 9017).\end{aligned}$$

**Theorem 2.1 (faithfulness of the bounded hit test on $[4,10^4]$).** For every
$u\in[4,10^4]$, the bounded test — "$u\ge4$, some $d\in[2,100]$ with $d\mid u$ and $d<u$,
and some $n\in[1,99]$ with $u\mid n!+1$" — is **equivalent** to $\mathrm{Hit}(u)$.

*Proof.* ($\Leftarrow$, soundness) The bounded test produces a proper divisor $2\le d<u$
(hence $u$ composite — kernel `not_prime_of_comp`) and a witness $n\ge1$ with
$u\mid n!+1$: exactly $\mathrm{Hit}(u)$.
($\Rightarrow$, completeness) Let $\mathrm{Hit}(u)$ with witness $n$. Theorem 1.3 at
$B=100$ ($u\le10^4=100^2$, $u$ composite) gives a prime $q\mid u$ with $q\le100$; $q\ne u$
(so $q<u$: $q=u$ would make $u$ prime), hence the divisor scan finds $q\in[2,100]$.
Theorem 1.1 gives $n<q\le100$, i.e. $n\le 99$: the witness scan over $[1,99]$ finds it. ∎

**Theorem 2.2 (the 21 chunk certificates).** For $c=0,\dots,19$ the chunk statement
$$\textit{chunkScanF}(c)=\text{true}:\quad\forall j<480:\ \text{hit test}\bigl(480c+j+4\bigr)=\text{T28 membership}\bigl(480c+j+4\bigr)$$
and the closing statement for $j<397$ at $u=9600+j+4$ — all **kernel-decided**
(`by decide`; 480-element NO-OOM discipline, fuel-structured divisor loop, no deep
ranges). Together they cover **every** $u\in[4,10^4]$: $20\cdot480+397=9997=10^4-4+1$.

**Theorem 2.3 (THE COMPLETE CENSUS; Lean `erdos1073_census`).** For every $u\in[4,10^4]$:
$$\mathrm{Hit}(u)\iff u\in\mathrm{T28}.$$

*Proof.* Theorem 2.1 reduces both sides to the bounded test; Theorem 2.2 decides the
bounded test against T28 membership on every $u$ in range; the kernel assembles the 21
chunks into the single $\forall$-statement (`census_all`) and exports the iff
(`erdos1073_census`): the forward direction by Theorem 2.1 completeness, the backward
direction by Theorem 2.1 soundness plus the T28 membership translation. Both directions
are kernel-proved; the finite content of each chunk is a kernel decide. ∎

**Theorem 2.4 (the counts; Lean `erdos1073_A10k` + machine).** $A(10^4)=28$ and
$A(10^3)=7$.

*Proof.* T28 has 28 entries, pairwise distinct and all $\le10^4$ (max $9017$; distinctness
and bounds machine-certified, battery receipt §8; length kernel-decided). By Theorem 2.3
the hit set below $10^4$ is exactly $\mathrm{T28}$; moreover $u=10^4$ itself is a
non-hit ($P(10^4)=2$, window $\{1\}$, $10^4\nmid1!+1=2$), so the count for $u<10^4$
equals the count for $u\le10^4$. Hence $A(10^4)=28$. Entries below $10^3$:
$25,121,169,437,551,667,721$ — exactly $7$. ∎

The 19-element A256519 prefix match ($25,121,169,\dots,2419$) is battery-verified;
the full 28-row identity is the kernel theorem.

### §4.2. T7 — THE 131-WITNESS TABLE AT $10^6$

**The kernel table `W131`** (131 rows $(u,n)$; full list in the kernel file
`Erdos1073.lean` §0 and `census1073_1e6.txt`, cross-checked identical by battery1073b)
begins
$$(25,4),(121,5),(169,12),(437,18),(551,18),(667,18),(721,6),(1037,16),\ldots$$
and ends $\ldots,(773053,18),(849091,18),(888673,918),(958649,191),(997501,400)$.
Witness range $n\in[4,918]$; $u$ range $[25,997501]$.

**Theorem 2.5 (soundness at $10^6$; Lean `erdos1073_witnesses`, kernel-decided).** Every
row $(u,n)\in\mathrm{W131}$ satisfies: $4\le u$, $u$ composite, $1\le n$, $u\mid n!+1$ —
including the Wilson row $(316969,562)$ ($562!+1$ has 1304 digits; kernel doc-comment
says "1330" — the theorem content is unaffected) and the deepest row $(888673,918)$
($918!+1$ has 2324 digits).

*Proof.* The single kernel decide `witScan = true` (the 131-row conjunction
`W131.all witOK`) is certified by the Lean kernel; the per-row composite test is a
proper divisor in $[2,1000]$, complete for composite $u\le10^6=1000^2$ by Theorem 1.3
at $B=1000$; `erdos1073_witnesses` unpacks the conjunction into the four stated
properties. ∎

**Theorem 2.6 (completeness at $10^6$; engine-certified, dual/triple method).** The
composite $u<10^6$ with a witness are **exactly** the $u$ of $\mathrm{W131}$; each has
**exactly one** witness in its window (zero multi-witness $u$).

*Proof.* Method 1 (the exhaustive cascade): for every composite $u<10^6$ the engine scans
the **full** window $[1,P(u))$ (spf-sieve), computing $n!\bmod u$ by successive
multiplication — by Theorem 1.5 this scan is provably exhaustive **given the sieve**;
it finds exactly the 131 rows (census size 131). Method 2 (independent big-int):
$(n!+1)\bmod u=0$ recomputed with exact integers for all 131 rows — zero violations.
Method 3 (uniqueness rescan): full-window recount of witnesses per hit — exactly one
each, zero multi-witness $u$. Receipts §8 (battery1073: GREEN, this session). ∎

**Honest split.** Soundness of the 131 rows is **kernel-decided** (Theorem 2.5);
exclusiveness at $10^6$ (no other composite $u<10^6$ is a hit) is **engine-certified**
(the $10^6$ cascade; the $10^4$ sub-range is kernel-decided by Theorem 2.3 and
independently rescanned by battery1073b with Miller–Rabin primality). This is the only
non-kernel certificate in the assembly, and it rests on the kernel-proved window
theorem T4 (the scan is provably total).

**Growth table (the $x^{o(1)}$ evidence base; recomputed this session from the census):**

| $x$ | $A(x)$ | $\alpha(x)=\log A/\log x$ |
|---|---|---|
| $10^3$ | 7 | 0.2817 |
| $10^4$ | 28 | 0.3618 |
| $10^5$ | 60 | 0.3556 |
| $3\cdot10^5$ | 84 | 0.3513 |
| $10^6$ | 131 | 0.3529 |

Read honestly (§7): the exponent is **flat $\approx0.35$** over $[10^4,10^6]$ — the data
neither proves nor refutes the $o(1)$ law on six decades.

---

## §5. THE STRUCTURAL CHANNELS — COMPLETE LAWS AND INSTANCES

### §5.1. T8 — THE WILSON CHANNEL

**Theorem 3.1 (the general Wilson-prime law).** If $p$ is prime and $p^2\mid(p-1)!+1$
($p$ a Wilson prime), then $u=p^2$ is a hit with witness $n=p-1$.

*Proof.* $p\ge2\Rightarrow p^2$ composite; the witness $n=p-1\ge1$ satisfies
$u\mid n!+1$ by hypothesis; the window law (Theorem 1.1) is consistent:
$p-1<p=P(p^2)$. ∎

**Theorem 3.2 (the three instances; Lean `erdos1073_wilson`, kernel-decided).**
$$5^2\mid 4!+1,\qquad 13^2\mid 12!+1,\qquad 563^2\mid 562!+1.$$
All three squares are census rows: $(25,4),(169,12),(316969,562)\in\mathrm{W131}$ — the
three known Wilson primes ($5,13,563$) all appear. Numerics: $12!+1=479001601=13^2\cdot2834329$;
$563^2=316969$; $562!+1$ has 1304 digits.

*Proof.* Single kernel decide (exact Nat arithmetic). Theorem 3.1 supplies the
generality; the census membership is Theorem 2.5/2.6. ∎

**The Wilson-quotient lift layer (engine-observed, battery-witnessed).** Beyond the
Wilson primes: $47^2=2209\mid 23!+1$ (witness $23\ll 46=p-1$) and
$613^2=375769\mid 229!+1$ (witness $229\ll 612$) — $47,613$ are **not** Wilson primes;
their Wilson quotients lift to early square hits. Both are W131 rows
$(2209,23),(375769,229)$.

### §5.2. T9 — THE BROCARD CHANNEL

**Theorem 3.3 (the general Brocard law).** If $n!+1=m^2$ with $n\ge1$ (a
Brocard/Brown pair), then $u=m^2$ is a hit with witness $n$.

*Proof.* $u=m^2=n!+1$ divides $n!+1$ (itself), $u$ composite, witness $n\ge1$; the window
law then automatically forces $n<P(m^2)$ (Theorem 1.1). ∎

**Theorem 3.4 (the three instances; Lean `erdos1073_brocard`, kernel-decided).**
$$4!+1=5^2=25,\qquad 5!+1=11^2=121,\qquad 7!+1=71^2=5041.$$
All three squares are census rows: $(25,4),(121,5),(5041,7)$. These are the three known
Brocard numbers; the #1108 arsenal census (exactly $\{4,5,7\}$ to depth 22) transfers
verbatim (the campaign confluence: #1072 Wilson-pair law + #1108 vp-engine +
#404 factorial-sum machinery).

*Proof.* Single kernel decide. ∎

**The square layer (machine-certified this session).** The prime-square hits below
$10^6$ are exactly
$$25=5^2,\ 121=11^2,\ 169=13^2,\ 2209=47^2,\ 5041=71^2,\ 316969=563^2,\ 375769=613^2$$
— 7 rows: 3 Brocard squares, 2 Wilson-prime squares ($169,316969$), 2 Wilson-quotient
lifts ($2209,375769$); $25=5^2$ is both Brocard and Wilson.

**The cluster exhibit (the arrival mechanism of §3.5, fully verified this session).**
$$18!+1=6402373705728001=19\cdot23\cdot29\cdot61\cdot67\cdot123610951$$
(all six factors prime). The five small factors generate **exactly 22** composite
products below $10^6$: the 10 **pairs** $437,551,667,1159,1273,1403,1541,1769,1943,4087$
— every one in T28 — the 10 **triples** $12673,26657,29279,33611,36917,40687,44689,77653,94001,118523$,
and the 2 **quads** $773053,849091$ — all 22 are W131 rows with witness $n=18$. Similarly
$23!+1\ni47^2\cdot79\cdot(\ldots)$ gives $2209,3713=47\cdot79,174511=47^2\cdot79$
(3 rows, witness 23), and $9!+1=362881$ is itself a hit (row $(362881,9)$). The census
**is** the arrival stream of these clusters — Theorem 1.7/1.8 in the flesh.

---

## §6. T10 — THE ARSENAL BRIDGE (BOSS's mathematics, explicit citations)

The kernel's `erdos1073_arsenal_bridge` welds the #1073 witness numbers into the
arsenal's certified world (the 16,121-theorem monorepo; imports
`Arsenal.ErdosTernary2.Basic`, `Arsenal.CardinalWorlds`, `Arsenal.CardinalWorldsV2`):

1. **`ErdosTernary2.isTernaryDigit`** (`Arsenal/ErdosTernary2/Basic.lean`, def l.44, with
   the refl laws `isTernaryDigit_zero/one/two`, `isTernaryDigit_three`): the ternary-digit
   predicate. Bridge instance: the first three base-3 digits of **563** and of
   **316969** ($=563^2$, the Wilson row) are ternary digits — kernel-decided:
   $[563\%3,\ (563/3)\%3,\ (563/9)\%3]=[2,1,2]$,
   $[316969\%3,\ (316969/3)\%3,\ (316969/9)\%3]=[1,2,1]$.
2. **`CardinalWorlds.carryAtPos`** (def, `Arsenal/CardinalWorlds.lean` l.103) and
   **`CardinalWorlds.carryAtPos_bound`** (l.108): $\forall R\,p:\ \textit{carryAtPos}\ R\ p<4$
   — the carry of $4R$ at any ternary position is bounded by 4. Bridge instance:
   `carryAtPos 316969 1 < 4`; refined by **`CardinalWorldsV2.carryAtPos_one_exact`**
   (l.53): $\textit{carryAtPos}\ R\ 1=R\%3$, so the first carry of the Wilson square is
   exactly $316969\%3=1$.
3. **`CardinalWorldsV2.v2r_ternary_scaling`** (l.71; built on
   `Arsenal.CardinalWorlds.v2r_mul_three_pow`): $\forall a\,c:\ \textit{v2r}(3^a\cdot c)=\textit{v2r}\ c$
   — multiplication by ternary powers preserves the 2-adic-depth reader `v2r`.
   Bridge instance: $\textit{v2r}(3^2\cdot25)=\textit{v2r}\,25$ (the Brocard square 25).

*Role, stated honestly.* The bridge is a **weld**, not an asymptotic step: it certifies
that the census's witness numbers (the Wilson prime 563, its square 316969, the Brocard
square 25) live inside the same certified ternary/carry/`v2r` architecture as the #404
ternary-power and #1108 fronts. It carries no growth content and is not counted toward
the remaining component.

---

## §7. THE GAP AUDIT — THE SINGLE REMAINING COMPONENT

### §7.1. What the corpus ask demands vs. what is proved

**The ask (verbatim):** "Is it true that $A(x)\le x^{o(1)}$?" — a yes/no answer with proof
for the **asymptotic law for all $x$**:
$$\lim_{x\to\infty}\frac{\log A(x)}{\log x}=0\quad\bigl(\iff\forall\varepsilon>0\ \exists x_0\ \forall x\ge x_0:\ A(x)\le x^{\varepsilon}\bigr).$$

**Proved and certified (this document + Kernel 34):** the complete structure theory
(T1–T5: window, saturation, small-prime-divisor, master characterization, cluster
decomposition — all general $\forall$-statements); the complete both-directions census at
$10^4$ ($A(10^4)=28$, $A(10^3)=7$ — kernel-decided, Theorem 2.3); the soundness of the
full 131-row census at $10^6$ (kernel-decided, Theorem 2.5) plus engine-certified
exclusiveness and witness uniqueness (Theorem 2.6); the Wilson and Brocard channels with
their general laws and all instances (Theorems 3.1–3.4); the arsenal bridge (T10).

**The exact gap — ONE component:**

> **THE ASYMPTOTIC LAW (the Hardy–Subbarao growth conjecture).** An unconditional proof
> (or disproof) of $\ \bigl\lvert\bigcup_{n<\sqrt x}C_n(x)\bigr\rvert\le x^{o(1)}$.

Everything else the corpus sentence involves is closed. There is no second component:
no definitional ambiguity (§0), no unbounded-search gap (T4 closes decidability at every
scale), no missing finite census row (T6/T7), no unproved channel (T8/T9).

### §7.2. Why the spine does not close it (the honest obstruction)

1. **The trivial ladder tops out exponentially** (Corollary 1.10):
   $A(x)\le\sqrt x\,(\lfloor\sqrt x\rfloor)!+1$ — no $\varepsilon$ in sight.
2. **Cluster saturation gives structure, not rate** (Theorem 1.8): each cluster $C_n$
   eventually stops growing (size $\le d(n!+1)$, all members $>n^2$); all growth is the
   **arrival** of new rich $n$. The conjecture is exactly the claim that the arrival
   stream's divisor-pairs decode sub-polynomially — no unconditional technique controls
   either the arrival rate or the divisor richness of $n!+1$: these numbers are coprime
   to $n!$ (the window law itself) but their factorizations have no known multiplicative
   regularity ($18!+1$'s five small primes spawn 22 hits; a hypothetical $n!+1$ with
   $\sim c\log x/\log\log x$ small-ish prime factors would spawn $x^{c'}$ pairs).
3. **The empirical exponent is flat, not decaying**: $\alpha\approx0.35$ on
   $[10^4,10^6]$ (§4.2 table) — six decades is far too short to indicate either the
   $o(1)$ collapse or its failure; each new cluster saturates, but new clusters keep
   arriving below $10^6$ (witnesses up to $918$).
4. **Corpus status:** the problem is carried as **open** in the erdosproblems corpus
   (Erdős, with Hardy–Subbarao [HaSu02]); the conjecture subsumes quantitative
   questions (Wilson-prime density, Brocard-type square sparsity, factorial-rough
   divisor structure) none of which has a known rate. The arsenal's certified laws
   (ternary digits, carries, `v2r` scaling — §6) address digital/architectural
   structure, not analytic growth of divisor sets.

**Verdict: NOT COMPLETE — the single remaining component is THE ASYMPTOTIC LAW
$A(x)\le x^{o(1)}$; every other demand of the corpus statement is completely proved
above, with the CI-green Kernel 34 as the certified spine.**

---

## §8. VERIFICATION (receipts)

**The Lean kernel (the certified spine).**
- File: `problem1073-factorial-mod/Erdos1073.lean` (Kernel 34; imports
  `Arsenal.ErdosTernary2.Basic`, `Arsenal.CardinalWorlds`, `Arsenal.CardinalWorldsV2`;
  depth headroom 262144 / 16M heartbeats). **CI run 42552313506 ALL GREEN** (Session 041
  close — 39 kills in one run); kill **#38** registered in `README.md`; the 7-round
  compile-war record in `WORKLOG.md` (r1 11 errors → r7 green: the minFac API archaeology,
  the Bool.and dot-resolution, the dvd-witness convention, omega division-atom gaps, the
  sympy-free CI runner). Zero `sorry`; zero admits; the kernel ends with
  `#print axioms` on all ten headline theorems (`erdos1073_window`,
  `erdos1073_saturation`, `small_prime_divisor`, `erdos1073_census`,
  `erdos1073_A10k`, `erdos1073_witnesses`, `erdos1073_wilson`, `erdos1073_brocard`,
  `erdos1073_arsenal_bridge`, `erdos1073_main`) and `#eval "ERDOS1073_KERNEL_GREEN"`.
- Census architecture: 20 full 480-element chunk decides + 1 closing 397-element decide
  ($20\cdot480+397=9997=10^4-4+1$ — complete cover of $[4,10^4]$), assembled by
  `census_all`; the 131-row `witScan` decide; the Wilson/Brocard/bridge decides.

**The batteries (run THIS session, foreground, from the repo root):**
- `python3 problem1073-factorial-mod/battery1073.py` — **GREEN** (wall 3.0 s):
  `census size: 131 (expect 131)`, `multi-witness: 0`,
  `A(10^3),A(10^4),A(10^5),A(10^6) = 7 28 60 131`, `BATTERY1073: GREEN`.
  Methods: spf-sieve mod-cascade window scan (exhaustive by T4), independent big-int
  divisibility, full-window uniqueness rescan, Wilson/Brocard channel checks, A256519
  prefix check.
- `python3 problem1073-factorial-mod/battery1073b.py` — **GREEN** (wall 0.14 s):
  `census at 1e4: 28 hits == T28 -> A(10^4) = 28`, `BATTERY1073B: GREEN`.
  Independent of both the engine cascade and the Lean kernel: deterministic
  Miller–Rabin primality, direct big-int divisibility, W131 cross-loaded from
  `census1073_1e6.txt` (131 rows), T28 bounds/composite/witness per row, 200-random-u
  window-law spot check, growth-count consistency.

**The W9 independent audit (this session, pure Python 3):**
$562!$ has 1304 digits and $562!+1\equiv0\pmod{316969}$; $918!+1\equiv0\pmod{888673}$;
$12!+1=479001601=13^2\cdot2834329$ ($2834329$ prime); $18!+1=19\cdot23\cdot29\cdot61\cdot67\cdot123610951$
($123610951$ prime) with **exactly 22** of its 5-prime sub-products below $10^6$, all
W131 rows with witness 18; $23!+1$ divisible by $2209=47^2$, $3713=47\cdot79$,
$174511=47^2\cdot79$; the prime-square layer is exactly the 7 squares of §5.2; all 131
census rows satisfy $n<P(u)$ (T1) with zero divisibility violations; the $\alpha$-table
reproduced to 4 decimals; $A(10^3)=7$, $\max\mathrm{T28}=9017$, $10^4$ itself a non-hit.

**Files:** kernel `Erdos1073.lean`; derivation `DERIVATION.md`; engines
`engine1073_round1.py` ($2\cdot10^5$ census + L1), `engine1073_round2.py` ($10^6$
census, factorization exhibits, multi-witness hunt, growth table); census
`census1073_1e6.txt` (131 rows: $u\ n\ P(u)$); batteries `battery1073.py`,
`battery1073b.py`; this document `COMPLETE_PROOF.md`.

---

## §9. THE PROOF ARCHITECTURE (5 lines)

1. **Window law (T1):** $u\mid n!+1\Rightarrow$ every prime $p\mid u$ has $p>n$ — the
   witness window is $[1,P(u))$, and saturation (T2) never re-opens it.
2. **Reduction (T3/T4):** composite $u\le B^2$ has a prime divisor $\le B$
   (the $(B{+}1)^2\le pa\le B^2$ case-split), so every witness is $<\sqrt u$: the
   unbounded $\exists n$ of the corpus collapses to a terminating scan at every scale.
3. **Census (T6/T7):** at $10^4$ the 21 kernel chunk-decides decide the bounded test for
   every $u$ — hits are exactly T28, $A(10^4)=28$, both directions; at $10^6$ the 131
   rows are kernel-decided genuine and the cascade certifies exclusiveness/uniqueness.
4. **Channels (T8/T9) + bridge (T10):** Wilson primes' squares and Brocard squares are
   hits (general laws + kernel-decided instances); the arsenal laws
   (`isTernaryDigit`/`carryAtPos_bound`/`v2r_ternary_scaling`) weld the witness numbers
   into BOSS's certified world.
5. **The named core (§7):** $A(x)=\lvert\bigcup_{n<\sqrt x}C_n(x)\rvert$ (cluster
   decomposition, T5) — the Hardy–Subbarao law $A(x)\le x^{o(1)}$ is the single
   remaining component; everything else is complete and certified.
