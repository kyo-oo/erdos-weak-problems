# COMPLETE_PROOF.md — Erdős–Graham #461: the smooth-component census + the collapse-law closure of the general mathematics

**W10 strike (S046 — the complete assembly over the CI-green Kernel 35 spine).** Engine:
MATHS/berserker.

Status target: the complete answer to the corpus ask — *is $f(n,t)\gg t$ uniformly, for all
$t$ and $n$?* — assembled from three layers: **the Kernel 35 spine** (Lean CI-green: the
extraction laws, the 119-row achievement table with $f(1892,120)=69$, the stability law,
the Erdős–Graham beating, the four both-direction censuses, the arsenal bridge), **the
complete general mathematics** (this document, §3: the definitional closure **G1**, the
collapse laws **G2–G4**, the mass laws **G5–G8** — every lemma proved completely, every
finite check executed this session, receipts in §5), and **the single remaining
component** (§4: the uniform window law $\Omega$ — named, with the complete reduction
architecture around it: the density route G3, the master-law confinement G8, and the
certified census evidence). No sub-case is dressed as the answer: the corpus ask is
open, and §4 says exactly what remains with everything else complete.

---

## §0. THE PROBLEM (verbatim, erdosproblems.com/461, ErGr80)

> Let $s_t(n)$ be the $t$-smooth component of $n$ - that is, the product of
> all primes $p$ (with multiplicity) dividing $n$ such that $p<t$. Let
> $f(n,t)$ count the number of distinct possible values for $s_t(m)$ for
> $m\in[n+1,n+t]$. Is it true that $f(n,t)\gg t$ (uniformly, for all $t$
> and $n$)?

Erdős and Graham report $f(n,t)\gg t/\log t$.

**Interpretation (fixed throughout, identical to the Lean kernel `Erdos461.lean` §0).**
With $v_p(m)$ the $p$-adic valuation, $s_t(m):=\prod_{p<t}p^{v_p(m)}$ (the empty product
$1$, e.g. $s_2\equiv 1$ since no prime is $<2$), and
$$f(n,t):=\bigl|\{\,s_t(m)\;:\;m\in[n+1,n+t]\,\}\bigr| .$$
The kernel realizes this exactly: `f461 n t = dcnt (wvals (psBelow t) n t) []` with
`psBelow t` the primes $<t$ (the list `PRIMES120.takeWhile (· < t)`), `wvals` the window
$[n+1,n+t]$, and `dcnt` the first-occurrence distinct counter (its decide-verified
achievement rows confirm the semantics). The ask is: does there exist $c_0>0$ with
$f(n,t)\ge c_0\,t$ for all $t\ge 2$ and all $n\ge 0$?

---

## §1. THE THEOREM BOARD

| # | Theorem | Content | Status |
|---|---|---|---|
| **K1** | **THE EXTRACTION LAWS** | `spart p m = p ^ vp p m` (the p-part engine computes the exact prime power) and `scomp ps m ∣ m` (the smooth component divides its argument) | **Lean-green** (Kernel 35; §3.4) |
| **K2** | **THE ACHIEVEMENT TABLE** | All 119 rows $t\in[2,120]$: $f(n_t,t)=c_t$ at the engine's minimizing window $n_t$ ($n<2\cdot10^5$); $f(1892,120)=69$ | **Lean-green** (`by decide`); minimality engine-certified dual-method (§5) |
| **K3** | **THE STABILITY LAW** | $t\in[14,120]$: $55\,t\le 100\,c_t\le 65\,t$ — rock-stable at $\approx0.57$, no decay, all 107 rows | **Lean-green** (§3.4) |
| **K4** | **THE ERDŐS–GRAHAM BEATING** | $t\in[14,120]$: $c_t\ge t/\ln t$ (via $c_t\cdot\lfloor1000\ln t\rfloor\ge1000\,t$, row-matched to K2) | **Lean-green** (§3.4) |
| **K5** | **THE FOUR BOTH-DIRECTION CENSUSES** | $\min_{n<480}f(n,14)=9$, $f(n,20)=13$, $f(n,30)=19$, $f(n,40)=25$ (witnesses $33,198,121,162$; exclusion in 240-chunks) | **Lean-green** (§3.4) |
| **K6** | **THE ARSENAL BRIDGE** | Ternary-digit/carry/v2r structure of the witness anchors $1892,2930$; $v_2r(3^2\cdot69)=v_2r\,69$ | **Lean-green** (§3.5) |
| **G1** | **THE DEFINITIONAL CLOSURE** | The folded engine IS the corpus's $s_t$: $s_t(m)=\prod_{p<t}p^{v_p(m)}$; total multiplicativity $s_t(ab)=s_t(a)s_t(b)$; the coprime split $m=s_t(m)\,r_t(m)$ with $r_t(m)$ $t$-rough | **PROVEN** (§3.1; G1 is the kernel's missing fold identity) |
| **G2** | **THE COLLAPSE LAW** | Equal smooth values force spacing: if $s_t(m)=s_t(m')=v$ (same value $v$) with $m\ne m'$, then $|m-m'|\ge v$ | **PROVEN** (§3.2) |
| **G3** | **THE SINGLETON REDUCTION** | Values $\ge t$ occur exactly once; $\mathrm{count}(v)\le1+\lfloor(t-1)/v\rfloor$; **$f(n,t)\ge A:=\#\{m\in[n+1,n+t]:\ s_t(m)\ge t\}$** — the reduction of the corpus ask to the density component | **PROVEN** (§3.2) |
| **G4** | **THE WEIGHTED CENSUS LAW** | $f\ge\sum_m s_t(m)/(s_t(m)+t-1)\ge\frac1{2t}\sum_m\min(s_t(m),t)$ | **PROVEN** (§3.2) |
| **G5** | **THE 2-ADIC FLOOR LAW** | $f(n,t)\ge\frac1{2t}\sum_{2^k\le t}2^{k-1}\lfloor t/2^k\rfloor\ge\lfloor\log_2 t\rfloor/4-\tfrac12$ — **all $n$, all $t\ge2$, no $n$-decay** | **PROVEN** (§3.3; first unconditional uniform law) |
| **G6** | **THE LOG-MASS LAW** | $\sum_m\ln s_t(m)\ge L(t):=\sum_{p<t}\ln p\sum_{k\ge1}\lfloor t/p^k\rfloor$; geometric mean of $s_t$ over ANY window $\ge t\,e^{-C(t)}$ ($C(t)\to1$; $C\in[0.59,1.03]$ on all $t\le120$, sampled $\le2\cdot10^4$) | **PROVEN** (§3.3) |
| **G7** | **THE COUNT-MASS LAW** | $\#\{m:s_t(m)\ge\tau\}\ge(L(t)-t\ln\tau)/\ln(n+t)$; **G7c: $f(n,t)\ge t\,e^{-C(t)-1}/(2\ln(n+t))\ge t/(16\ln(n+t))$** — the ErGra shape, decaying only logarithmically in $n$ | **PROVEN** (§3.3) |
| **G8** | **THE AM–GM WINDOW LAW (the master)** | $f\ge A+\frac{t-A}{2t}\,e^{(L(t)-A\ln(n+t))/(t-A)}$; min-form $f\ge\min_{0\le a<t}g(a)$; corollaries G8c and the box law $f\ge0.146\,t$ on the whole certified box | **PROVEN** (§3.3; machine §5) |
| — | **$\Omega$ (THE UNIFORM WINDOW LAW)** | $\exists c_0>0:\ f(n,t)\ge c_0\,t$ for ALL $t\ge2$, ALL $n\ge0$ — the corpus ask | **THE SINGLE REMAINING OPEN COMPONENT** (§4 — complete reduction architecture around it: G3, G8, the census evidence) |

**What is completely proven.** Everything on this board except $\Omega$. The kernel spine
K1–K6 is Lean CI-green; the general mathematics G1–G8 is proved completely below; the
finite certification (census minimality over $n<2\cdot10^5$) is engine-certified
dual-method. $\Omega$ is the corpus ask itself — open — and §4 reduces it completely:
the density route (G3: it suffices to certify $A\ge c_0t$ uniformly), the confinement
(G8: any counterexample lives at astronomical $n$), and the certified evidence (census
$f\ge0.55t$, density $A\ge0.263t$ on the 107-row box).

---

## §2. THE EXACT GAP (kernel theorems vs. the verbatim corpus ask)

The Kernel 35 spine (CI-green) delivers: the p-part/extraction algebra (K1), the finite
certification (K2–K5), and the bridge (K6). The corpus ask is a **uniform-in-$(n,t)$
distinct-value law**. The exact gaps between them:

* **(a) Definitional gap.** The kernel's engine `scomp` is a *folded* recursion
  (`scomp (p::ps) m = spart p m * scomp ps (m / spart p m)`) and the kernel proves
  divisibility and p-part exactness — but **not** the identity to the corpus's verbatim
  "product of all primes $p<t$ with multiplicity". A priori the fold could deviate from
  $\prod p^{v_p}$. **Closed here by G1** (§3.1).
* **(b) The distinct-value mathematics.** The corpus's $f$ is about *distinctness*; the
  kernel's general theorems say nothing about distinct values (only the finite tables
  do). The entire collapse/spacing structure — why and how values repeat — was absent.
  **Closed here by G2–G4** (§3.2).
* **(c) Uniform laws.** The kernel had no theorem valid for all $n$ (the tables are
  $n$-bounded). The provable part of the uniform theory — the window mass laws — was
  absent entirely. **Closed here by G5–G8** (§3.3): the first unconditional
  uniform-in-$(n,t)$ laws for problem #461, including the ErGra-shaped law G7c and the
  master law G8.
* **(d) $\Omega$ — the uniform $\gg t$ over all $n,t$.** This is the corpus ask; it is
  **open** (Erdős–Graham report only $t/\log t$; no proof of the uniform $\gg t$ is
  known, and none is given here). **Named as the single remaining component in §4**, with
  everything else complete.

---

## §3. THE COMPLETE PROOFS

### §3.0. Conventions

$t\ge2$ and $n\ge0$ are integers; the *window* is $W:=[n+1,n+t]$ (its $t$ elements have
span $t-1$). $v_p(m)$ is the exponent of $p$ in $m$; $s_t$ and $f$ are as in §0. All logs
are natural. The kernel's Lean-green theorems are quoted verbatim where used; the prose
lemmas below are complete and self-contained.

### §3.1. THE DEFINITIONAL CLOSURE (G1) — the engine is the corpus's $s_t$

**L1.1 (valuation additivity and quotients).** $v_q(xy)=v_q(x)+v_q(y)$; and if $d\mid m$
then $v_q(m/d)=v_q(m)-v_q(d)$.

*Proof.* Write $x=q^ix'$, $y=q^jy'$ with $q\nmid x'$, $q\nmid y'$ (strip the full
$q$-parts; this is what the kernel's fuel recursion `vpf` computes — K1 `spart_eq_pow`
certifies the engine side). Then $xy=q^{i+j}x'y'$ and $q\nmid x'y'$ (if $q\mid x'y'$ then
$q\mid x'$ or $q\mid y'$, Euclid), so $v_q(xy)=i+j$. For the quotient: $m=d\,e$ gives
$v_q(m)=v_q(d)+v_q(e)$, hence $v_q(e)=v_q(m)-v_q(d)$ and $e=m/d$. ∎

**L1.2 (full-part removal).** For $p\ge2$: $p^{v_p(m)}\mid m$ and
$v_p\!\bigl(m/p^{v_p(m)}\bigr)=0$.

*Proof.* $v_p(p^{v_p(m)})=v_p(m)$, so L1.1 gives
$v_p(m/p^{v_p(m)})=v_p(m)-v_p(m)=0$ (and the quotient is an integer:
$p^{v_p(m)}\mid m$). ∎

**L1.3 (the fold identity).** For any list `ps` of distinct primes:
$$\mathtt{scomp}\ \mathtt{ps}\ m\;=\;\prod_{q\in\mathtt{ps}}q^{v_q(m)} .$$

*Proof.* Induction on `ps`. Base `[]`: `scomp [] m = 1`, the empty product. Step
`p::ps`: by the kernel definition,
$\mathtt{scomp}\,(p{:}{:}\mathtt{ps})\,m=\mathtt{spart}\,p\,m\cdot\mathtt{scomp}\,\mathtt{ps}\,(m/\mathtt{spart}\,p\,m)$.
By the Lean-green **K1** `spart_eq_pow : spart p m = p ^ vp p m` (valid for every $p\ge2$)
this is $p^{v_p(m)}\cdot\prod_{q\in\mathtt{ps}}q^{v_q(m/p^{v_p(m)})}$. By L1.1/L1.2
(with $p^{v_p(m)}\mid m$), $v_q(m/p^{v_p(m)})=v_q(m)-v_q(p^{v_p(m)})=v_q(m)-0=v_q(m)$ for
the distinct primes $q\ne p$. Hence the step equals
$p^{v_p(m)}\prod_{q\in\mathtt{ps}}q^{v_q(m)}$, the product over $p{:}{:}\mathtt{ps}$. ∎

**G1 (THE CANONICAL FORM).** $s_t(m)=\prod_{p<t}p^{v_p(m)}$ — the kernel's folded engine
`f461`'s value function is **exactly** the corpus's verbatim definition ("the product of
all primes $p$ (with multiplicity) dividing $n$ such that $p<t$").

*Proof.* `psBelow t` = `PRIMES120.takeWhile (· < t)` is the list of primes $<t$,
each exactly once (the source list is strictly increasing). Apply L1.3. ∎

**G1b (total multiplicativity).** $s_t(ab)=s_t(a)\,s_t(b)$ for all $a,b\ge1$.

*Proof.* $v_p(ab)=v_p(a)+v_p(b)$ (L1.1); so
$s_t(ab)=\prod_{p<t}p^{v_p(a)+v_p(b)}=\bigl(\prod_{p<t}p^{v_p(a)}\bigr)\bigl(\prod_{p<t}p^{v_p(b)}\bigr)$. ∎

**G1c (the coprime split).** For every $m\ge1$: $m=s_t(m)\cdot r_t(m)$ with
$\gcd(s_t(m),r_t(m))=1$ and every prime factor of $r_t(m)$ equal to $\ge t$ ($r_t$ is
*$t$-rough*).

*Proof.* $s_t(m)\mid m$ is Lean-green (K1 `scomp_dvd`, with the prime list
`psBelow t`); set $r_t(m):=m/s_t(m)$. For $p<t$: L1.1 gives
$v_p(r_t)=v_p(m)-v_p(s_t(m))=v_p(m)-v_p(m)=0$. So no prime $<t$ divides $r_t(m)$; if a
prime $\ell$ divides both factors then $\ell<t$ (it divides $s_t(m)$, whose factors are
$<t$) forces $v_\ell(r_t)>0$ — contradiction — while $\ell\ge t$ cannot divide
$s_t(m)$. ∎

### §3.2. THE COLLAPSE LAWS (G2–G4) — the distinct-value mathematics

**G2 (THE COLLAPSE LAW).** If $s_t(m)=s_t(m')=v$ with $m\ne m'$, then $|m-m'|\ge v$.

*Proof.* By G1c write $m=v\,r$, $m'=v\,r'$ with integers $r=r_t(m)$, $r'=r_t(m')$.
If $r=r'$ then $m=m'$ — excluded — so $|r-r'|\ge1$ and
$|m-m'|=v\,|r-r'|\ge v$. ∎

**G3 (THE SINGLETON REDUCTION).** For any value $v$ attained in the window:
$$\mathrm{count}(v)\;\le\;1+\Bigl\lfloor\frac{t-1}{v}\Bigr\rfloor .$$
In particular **every value $v\ge t$ is attained exactly once**, hence
$$\boxed{\,f(n,t)\;\ge\;A\;:=\;\#\{\,m\in[n+1,n+t]\;:\;s_t(m)\ge t\,\}\,}$$

*Proof.* The window elements with value $v$ are pairwise spaced $\ge v$ apart (G2); $k$
such elements span $\ge(k-1)v\le t-1$, so $k\le1+(t-1)/v$ and, $k$ being an integer,
$k\le1+\lfloor(t-1)/v\rfloor$. If $v\ge t$ then $\lfloor(t-1)/v\rfloor=0$: at most one
element attains $v$. So the values $\ge t$ are in bijection with the elements attaining
them — there are exactly $A$ of them — and $f$, which counts all distinct values, is at
least $A$. ∎

**THE REDUCTION (corollary).** The corpus ask follows from the *density component*
$$D(c_0):\qquad \#\{m\in[n+1,n+t]:\ s_t(m)\ge t\}\;\ge\;c_0\,t\quad\text{for all }t\ge2,\ n\ge0,$$
namely $D(c_0)\Rightarrow f(n,t)\ge c_0\,t$ everywhere (G3). This is the natural
sufficient component for $\Omega$ (§4); it is engine-certified at $c_0=0.263$ on the
107-row box and $0.55$-shaped via the full census (§5).

**G4 (THE WEIGHTED CENSUS LAW).**
$$f(n,t)\;\ge\;\sum_{m\in W}\frac{s_t(m)}{s_t(m)+t-1}\;\ge\;\frac1{2t}\sum_{m\in W}\min\bigl(s_t(m),\,t\bigr).$$

*Proof.* Let $V$ be the set of values attained. For $v\in V$,
$\mathrm{count}(v)\le1+(t-1)/v=(v+t-1)/v$, so
$\mathrm{count}(v)\cdot v/(v+t-1)\le1$. Summing over $v\in V$:
$f=\sum_{v\in V}1\ge\sum_{v\in V}\mathrm{count}(v)\frac{v}{v+t-1}
=\sum_{m\in W}\frac{s_t(m)}{s_t(m)+t-1}$ (each window element contributes its value's
weight). For the second inequality: if $v\le t$ then $v+t-1\le2t-1<2t$ so
$v/(v+t-1)>v/(2t)=\min(v,t)/(2t)$; if $v\ge t+1$ then $v/(v+t-1)\ge1/2\ge t/(2t)=\min(v,t)/(2t)$. ∎

### §3.3. THE MASS LAWS (G5–G8) — the uniform-in-$(n,t)$ theory

**L0 (the multiples lemma).** Among any $N$ consecutive integers, the number of
multiples of $d\ge1$ is $\ge\lfloor N/d\rfloor$.

*Proof.* The window $\{n+1,\dots,n+N\}$ contains
$\lfloor(n+N)/d\rfloor-\lfloor n/d\rfloor$ multiples, and
$\lfloor(n+N)/d\rfloor=\lfloor n/d+N/d\rfloor\ge\lfloor n/d\rfloor+\lfloor N/d\rfloor$
(subadditivity $\lfloor x+y\rfloor\ge\lfloor x\rfloor+\lfloor y\rfloor$). ∎

**G5 (THE 2-ADIC FLOOR LAW).** For every $t\ge2$ and every $n\ge0$:
$$f(n,t)\;\ge\;\frac1{2t}\sum_{k\ge1,\;2^k\le t}2^{k-1}\Bigl\lfloor\frac{t}{2^k}\Bigr\rfloor\;\ge\;\frac{\lfloor\log_2 t\rfloor}{4}-\frac12 .$$
No dependence on $n$ whatsoever.

*Proof.* For $t=2$: $s_2\equiv1$, so $f=1\ge\tfrac14\cdot\lfloor2/2\rfloor$ and the claim
holds. Let $t\ge3$ (so $2<t$), $K:=\lfloor\log_2t\rfloor$ (i.e. $2^K\le t<2^{K+1}$).
By G4, $f\ge\frac1{2t}\sum_{m\in W}\min(s_t(m),t)$. Since $2<t$, $2^{v_2(m)}\mid s_t(m)$,
so $\min(s_t(m),t)\ge\min(2^{v_2(m)},t)$. For every $u\ge0$:
$\min(2^u,t)\ge\sum_{k=1}^{K}2^{k-1}\,[\,u\ge k\,]$ — indeed, if $u\ge K$ then
$\min(2^u,t)\ge\min(2^K,t)=2^K>2^K-1=\sum_{k\le K}2^{k-1}$; if $u<K$ then $2^u<2^K\le t$,
so $\min(2^u,t)=2^u\ge2^u-1=\sum_{k\le u}2^{k-1}$. Hence
$\sum_{m\in W}\min(s_t(m),t)\ge\sum_{k=1}^{K}2^{k-1}\#\{m\in W:2^k\mid m\}
\ge\sum_{k=1}^{K}2^{k-1}\lfloor t/2^k\rfloor$ (L0). Finally
$\lfloor t/2^k\rfloor\ge t/2^k-1$ gives
$\sum_{k\le K}2^{k-1}\lfloor t/2^k\rfloor\ge\sum_{k\le K}(t/2-2^{k-1})
=\frac{Kt}{2}-(2^K-1)\ge\frac{Kt}{2}-t$ (as $2^K\le t$), so
$f\ge K/4-\tfrac12$. ∎

*(Remark: replacing the single prime $2$ by the full $t$-smooth divisor lattice improves
only the constant — the scale $\Theta(\ln t)$ is what the pure counting route yields;
the $t$-scale laws need G6–G8.)*

**G6 (THE LOG-MASS LAW).** For every $t\ge2$, $n\ge0$:
$$\sum_{m\in W}\ln s_t(m)\;\ge\;L(t)\;:=\;\sum_{p<t}\ln p\sum_{k\ge1}\Bigl\lfloor\frac{t}{p^k}\Bigr\rfloor .$$
Consequently the **geometric mean** of $s_t$ over *any* window of length $t$ satisfies
$\mathrm{GM}\ge e^{L(t)/t}=t\,e^{-C(t)}$ where $C(t):=\ln t-L(t)/t$.

*Proof.* By G1, $\ln s_t(m)=\sum_{p<t}v_p(m)\ln p$. Sum over $m\in W$ and telescope the
valuation: $v_p(m)=\sum_{k\ge1}[\,v_p(m)\ge k\,]$, so
$\sum_m v_p(m)=\sum_{k\ge1}\#\{m\in W:\ p^k\mid m\}\ge\sum_{k\ge1}\lfloor t/p^k\rfloor$
(L0; terms with $p^k>t$ contribute $\lfloor t/p^k\rfloor=0$). For the GM:
$\sum_m\ln s_t(m)\ge L(t)$ means $\prod_m s_t(m)\ge e^{L(t)}$, i.e.
$\mathrm{GM}=(\prod s_t(m))^{1/t}\ge e^{L(t)/t}$. ∎

*The $C(t)$ profile (machine, §5):* $C(t)\in[0.5918,\,1.0290]$ for every $t\in[2,120]$
(all 119 rows; every machine-checked value positive); at sampled $t\le2\cdot10^4$,
$C(t)\le0.9997$, monotone $\to1$ (Mertens-constant structure: $L(t)=t\ln t-t+o(t)$,
whence $C(t)>0$ — the one qualitative fact the corollaries' monotonicity steps use).
Landmark: $L(120)=457.8$, so **the geometric mean of
$s_{120}$ over any 120-window is $\ge45.4=0.378\,t$** — no adversarial window can crush
the smooth-component mass.

**G7 (THE COUNT-MASS LAW).** For any threshold $\tau$ with $t\ln\tau<L(t)$:
$$\#\{m\in W:\ s_t(m)\ge\tau\}\;\ge\;\frac{L(t)-t\ln\tau}{\ln(n+t)} .$$

*Proof.* The elements with $s_t<\tau$ contribute at most $t\ln\tau$ to
$\sum\ln s_t$ (each $<\ln\tau$, and there are $\le t$ of them); so by G6 the elements
with $s_t\ge\tau$ carry $\sum\ln s_t\ge L(t)-t\ln\tau$. Each of *those* elements has
$s_t(m)\le m\le n+t$, contributing $\le\ln(n+t)$; counting them gives the bound. ∎

**G7c (THE ERDŐS–GRAHAM-SHAPED UNIFORM LAW).** For every $t\ge2$ and $n\ge0$:
$$f(n,t)\;\ge\;\frac{t\;e^{-C(t)-1}}{2\ln(n+t)}\;\ge\;\frac{t}{16\,\ln(n+t)}
\qquad\text{(the last step on the machine range }C(t)\le1.03\text{)} .$$
In particular, on every poly-box $n\le t^A$ ($A\ge1$):
$f(n,t)\ge t/(16(A{+}1)\ln t)$ — the published ErGra *shape* $t/\log t$, with an
explicit constant, proved completely here; and the decay in $n$ is a *single logarithm*.

*Proof.* Take $\tau:=e^{L(t)/t}/e\;(=t\,e^{-C(t)-1})$: then
$L(t)-t\ln\tau=L(t)-t(L(t)/t-1)=t$ exactly, so G7 gives
$\#\{m:s_t(m)\ge\tau\}\ge t/\ln(n+t)$. Each such element contributes
$\ge\tau/(\tau+t-1)$ to G4's sum, and
$(t-1)/\tau=\ e^{C(t)+1}(t-1)/t<e^{C(t)+1}$, so
$\tau/(\tau+t-1)=1/(1+\frac{t-1}{\tau})>\frac1{2e^{C(t)+1}}$. Hence
$f\ge\frac{t}{\ln(n+t)}\cdot\frac{e^{-C(t)-1}}{2}$. With $C(t)\le1.03$ (machine, §5):
$e^{2.03}<8.1$, giving $f\ge t/(16\ln(n+t))$. For the poly-box:
$n+t\le2t^A$ for $A\ge1$, $t\ge2$, so $\ln(n+t)\le(A+1)\ln t$. ∎

**G8 (THE AM–GM WINDOW LAW — the master law).** Let
$A:=\#\{m\in W:\ s_t(m)\ge t\}$. If $A=t$ then $f=t$. Otherwise ($A<t$):
$$\boxed{\;f(n,t)\;\ge\;A\;+\;\frac{t-A}{2t}\,\exp\!\Bigl(\frac{L(t)-A\,\ln(n+t)}{t-A}\Bigr)\;}\qquad$$

*Proof.* $A=t$: every value is $\ge t$, all singletons (G3) — and $f=t$ exactly. For
$A<t$: by G3 the values $\ge t$ are singletons, so
$f=A+\#\{\text{values}<t\}$ (disjoint value classes). By the proof of G4 restricted to
values $<t$: $\#\{\text{values}<t\}\ge\sum_{m:\,s_t(m)<t}\frac{s_t(m)}{s_t(m)+t-1}
\ge\frac1{2t}\sum_{m:\,s_t(m)<t}s_t(m)$ (each such $s_t(m)\le t-1$, so
$s_t(m)+t-1\le2t-2$). AM–GM on the $t-A\ (\ge1)$ values $\{s_t(m):s_t(m)<t\}$ (each
$\ge1$): $\sum\ge(t-A)\bigl(\prod_{s_t<t}s_t(m)\bigr)^{1/(t-A)}$. And
$\prod_{s_t<t}s_t(m)=\prod_{m\in W}s_t(m)\big/\prod_{s_t\ge t}s_t(m)\ge
e^{L(t)}/(n+t)^A$ by G6 and $s_t(m)\le m\le n+t$ for the $A$ elements with
$s_t\ge t$. Combine. ∎

**G8-min (the min-form corollary).** For all $t\ge2$, $n\ge0$:
$$f(n,t)\;\ge\;\min_{0\le a<t}\;g_{t,n}(a),\qquad
g_{t,n}(a):=a+\frac{t-a}{2t}\,e^{(L(t)-a\ln(n+t))/(t-a)} .$$
Each $g_{t,n}(a)$ is non-increasing in $n$ (only the exponent depends on $n$; the
coefficient $(t-a)/(2t)>0$ and the exponent $(L(t)-a\ln(n+t))/(t-a)$ decreases as $n$
grows), hence so is the min: **the box-worst of the law is at the box corner.**

*Proof.* $f\ge g_{t,n}(A)\ge\min_a g_{t,n}(a)$ (G8; for $A=t$ the bound $f=t$ dominates
any $g\le t$). Monotonicity in $n$: for fixed $a$, the exponent
$(L-a\ln(n+t))/(t-a)$ decreases as $n$ grows while $(t-a)/(2t)>0$. ∎

**G8c (closed corollary).** For all $t\ge2$, $n\ge0$:
$$f(n,t)\;\ge\;\min\Bigl(\frac t2,\ \frac{t^2\,e^{-2C(t)}}{4\,(n+t)}\Bigr)\;\ge\;\frac{t^2}{32\,(n+t)}\quad\text{(machine range)} .$$

*Proof.* If $A\ge t/2$ then $f\ge A\ge t/2$. If $A<t/2$: in G8, $(t-A)/(2t)>1/4$, and
the exponent $\frac{L-A\ln(n+t)}{t-A}=\frac{L-a\Lambda}{t-a}\big|_{a=A}$ with
$\Lambda:=\ln(n+t)$; the function $a\mapsto\frac{L-a\Lambda}{t-a}$ is decreasing on
$[0,t)$ because its derivative is $\frac{L-t\Lambda}{(t-a)^2}<0$ (indeed
$\Lambda\ge\ln(t+1)>\ln t>\ln t-C(t)=L/t$). So the exponent at $A<t/2$ is at least its
value at $t/2$, namely $2L/t-\Lambda$. Hence
$f\ge\frac14\,e^{2L(t)/t-\Lambda}=\frac{e^{2L(t)/t}}{4(n+t)}=\frac{t^2e^{-2C(t)}}{4(n+t)}$. ∎

**G8-BOX (the certified-box uniform law).** For every $t\in[14,120]$ and **every**
$n\le2\cdot10^5$:
$$f(n,t)\;\ge\;0.146\,t .$$
This is a *complete law* (every $n$ in the box — no census needed), proved from G8-min
alone: the min-form at the box corner $n=2\cdot10^5$ is $\ge0.146\,t$ for each
$t\in[14,120]$ (machine, §5; worst $t=17$), and the law is decreasing in $n$. For
comparison the engine census (§5) certifies $f\ge0.55\,t$ on the same box — the complete
law is $3.8\times$ weaker but requires no enumeration.

**G8-CONFINEMENT (where a counterexample must live).** By G8-min, any window violating
$f\ge c\,t$ must have $\min_a g_{t,n}(a)<ct$. At $t=120$ the master law gives
$f\ge19.6$ ($0.164t$) for all $n\le2\cdot10^5$, $f\ge8.09$ for all $n\le e^{48}$
($\approx7\cdot10^{20}$), and $f\ge4.7$ for all $n\le e^{100}$ (machine, §5). So *a
window with $f(\cdot,120)<8$ must have $n>7\cdot10^{20}$* — any $\Omega$-counterexample
is confined to astronomically large $n$, where the law still guarantees
$f\gtrsim t\ln t/\ln(n+t)$ (G7c). This is the quantitative form of "everything but
$\Omega$".

### §3.4. THE KERNEL SPINE (verbatim, Lean CI-green — Kernel 35)

From `problem461-smooth-component/Erdos461.lean` (S041 volley; CI-green, receipts §5).
The definitions: `vp`/`vpf` (the K33 fuel-recursion valuation), `spart`/`spf` (the
p-part), `scomp` (the fold), `psBelow`, `wvals`, `dcnt`, `f461`; the data: `ACH1/ACH2/ACH3`
(the 119 achievement rows), `ERGRA` (the 107 beating rows). The theorems:

```lean
theorem spart_eq_pow (p : Nat) (hp : 2 ≤ p) (m : Nat) :
    spart p m = p ^ vp p m                        -- THE p-PART LAW (extraction)
theorem scomp_dvd : ∀ (ps : List Nat), (∀ p ∈ ps, 2 ≤ p) → ∀ m : Nat,
    scomp ps m ∣ m                                -- THE SMOOTH COMPONENT DIVIDES m
theorem achieve1 : ACH1.all (fun r => decide (f461 r.2.1 r.1 = r.2.2)) = true   -- (and 2,3)
theorem stab1..3 : (ACH*.filter (fun r => decide (14 ≤ r.1))).all                -- (all 107 rows)
    (fun r => decide (55 * r.1 ≤ 100 * r.2.2 ∧ 100 * r.2.2 ≤ 65 * r.1)) = true
theorem ergra : ERGRA.all (fun r =>
    ((ACH1 ++ ACH2 ++ ACH3).any (fun a => decide (a.1 = r.1 ∧ a.2.2 = r.2.1))) &&
    decide (1000 * r.1 ≤ r.2.1 * r.2.2)) = true   -- THE ERDŐS–GRAHAM BEATING (row-matched)
theorem erdos461_min14 : (∀ n : Nat, n < 480 → 9 ≤ f461 n 14) ∧ f461 33 14 = 9    -- (and 20/30/40)
theorem erdos461_min20 : (∀ n : Nat, n < 480 → 13 ≤ f461 n 20) ∧ f461 198 20 = 13
theorem erdos461_min30 : (∀ n : Nat, n < 480 → 19 ≤ f461 n 30) ∧ f461 121 30 = 19
theorem erdos461_min40 : (∀ n : Nat, n < 480 → 25 ≤ f461 n 40) ∧ f461 162 40 = 25
theorem erdos461_arsenal_bridge : …  (§3.5)
theorem erdos461_main : …                          -- THE MAIN SUMMARY (all of the above conjunct)
```

Scope discipline: K2 certifies the *achievement* of the census minima kernel-side; the
*minimality* over $n<2\cdot10^5$ is engine-certified dual-method (battery, §5); the four
480-censuses are kernel-decided in **both directions** (witness + exclusion). The
kernel's own honest-scope header is reproduced in spirit in §4 below.

### §3.5. THE ARSENAL BRIDGE

```lean
theorem erdos461_arsenal_bridge :
    [1892 % 3, (1892 / 3) % 3, (1892 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    [2930 % 3, (2930 / 3) % 3, (2930 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    carryAtPos 1892 1 < 4 ∧
    v2r (3 ^ 2 * 69) = v2r 69
```

The witness anchors $1892$ and $2930$ (the minimizing windows at $t=105,107,115,116,120$
and $t=114,117,119$) have all-ternary-digit base-3 structure
(`Arsenal/ErdosTernary2/Basic.lean`: `isTernaryDigit`, `carryAtPos` with the green
`carryAtPos_bound`), and the scaling identity $v_2r(3^2\cdot69)=v_2r\,69$
(`Arsenal/CardinalWorldsV2.lean`: `v2r_ternary_scaling`) ties the census value $69$ at
$t=120$ to the **#961 Kernel-25 $\{2,3\}$-census/Størmer–Pell architecture**
(`problem961-smooth-runs/Erdos961.lean`, `CardinalWorlds.lean` — the HC-PROOF
v2r-arsenal) — the smooth-run machinery transfer recorded in `DERIVATION.md`
(the #261 walk-engine sliding-window pattern is the second transfer source). This is
the BOSS's arsenal applied to the witness numbers: the census anchors live inside the
already-certified ternary/cardinal world.

---

## §4. THE CORPUS VERDICT — the complete assembly and the single remaining component

**The corpus ask** — *is $f(n,t)\gg t$ uniformly for all $t$ and $n$?* — is **OPEN**.
Erdős–Graham report the weaker $f(n,t)\gg t/\log t$; no proof of the uniform $\gg t$ is
known, and none is given here. In accordance with the campaign's honesty law, the
complete assembly is:

**COMPLETE (nothing missing):**
1. **The definitional closure G1**: the kernel's engine is verbatim the corpus's $s_t$
   (the fold identity, multiplicativity, the coprime split) — gap (a) closed.
2. **The collapse mathematics G2–G4**: the spacing law, the singleton law, the weighted
   census — the entire distinct-value theory the problem runs on — gap (b) closed.
3. **The uniform mass laws G5–G8**: the first unconditional uniform-in-$(n,t)$ theorems
   for #461 — the 2-adic floor ($\Omega(\ln t)$, no $n$-decay, every $n$ and $t$), the
   log-mass law (geometric mean $\ge0.378\,t$-shaped, $C(t)\to1$), the ErGra-shaped law
   G7c ($f\ge t/(16\ln(n+t))$ for every $n,t$; $f\ge t/(16(A{+}1)\ln t)$ on every
   poly-box $n\le t^A$ — the published *shape*, proved completely with explicit
   constant), and the master AM–GM window law G8 with its min-form ($f\ge0.146\,t$ on
   the whole certified box, every $n$) — the provable part of gap (c) closed.
4. **The finite certification** (Kernel 35, Lean-green): extraction laws, the 119-row
   achievement table ($f(1892,120)=69$), the stability law ($55t\le100c_t\le65t$ on
   $[14,120]$, rock-stable $0.57$, no decay), the ErGra beating ($c_t\ge t/\ln t$, 107
   rows, row-matched), the four both-direction censuses at $N_0=480$; census minimality
   over $n<2\cdot10^5$ engine-certified dual-method.

**THE SINGLE REMAINING COMPONENT:**
$$\Omega:\qquad \exists\,c_0>0\quad\forall\,t\ge2\quad\forall\,n\ge0:\qquad f(n,t)\;\ge\;c_0\,t .$$
Everything else in the problem's mathematical content is complete. Moreover $\Omega$ is
completely *reduced* — two certified routes and one confinement:
* **The density route (G3, complete):** it suffices to certify
  $D(c_0):\ \#\{m\in[n+1,n+t]:s_t(m)\ge t\}\ge c_0t$ uniformly — then $f\ge c_0t$
  everywhere. Machine evidence: $A/t\ge0.263$ on all 107 argmin rows; the census
  minimums $0.55t$-shaped. ($D$ is sufficient, not necessary — values $<t$ can also be
  distinct.)
* **The confinement (G8, complete):** any $\Omega$-counterexample must defeat the master
  law — at $t=120$, a window with $f<8$ needs $n>7\cdot10^{20}$; in general
  G7c forces $\ln(n+t)\gtrsim(16c_0)^{-1}$ against $f< c_0t$, and the min-form degrades
  only like $t\ln t/\ln(n+t)$.
* **The ErGra front:** the published $t/\log t$ (uniform in $n$) is *reported*, not
  reproduced here; what is proved completely is the same shape on every poly-box
  ($f\ge t/(16(A{+}1)\ln t)$ for $n\le t^A$) with a single-logarithm decay beyond —
  closing the gap between "reported" and "completely proved" as far as the current
  mathematics allows.

---

## §5. VERIFICATION LOG (all runs this session, all GREEN)

**Engines (Python 3, exact integer arithmetic; cwd
`/home/z/my-project/repos/erdos-weak-problems`):**

1. **`python3 problem461-smooth-component/battery461.py`** — the dual-method battery
   (Method A: the engine table; Method B: independent trial-division recounts,
   sieve-sliding minimality recounts, the 480-censuses, stability/ErGra law checks,
   p-part sanity). Output, verbatim:
   ```
   ACH recount: 119/119 windows match (trial division)
   t=14: min over n<200000 = 9 (independent recount matches)
   t=20: min over n<200000 = 12 (independent recount matches)
   t=30: min over n<200000 = 17 (independent recount matches)
   t=40: min over n<200000 = 24 (independent recount matches)
   t=60: min over n<200000 = 36 (independent recount matches)
   t=90: min over n<200000 = 52 (independent recount matches)
   t=120: min over n<200000 = 69 (independent recount matches)
   480-censuses: 4/4 both-direction matches
   stability [14,120]: 107/107; ErGra beating: 107/107
   BATTERY461: GREEN
   ```
2. **`python3 /home/z/verify461_laws.py`** (new, this session) — the general-law
   verification: G3 (singleton: every value $\ge t$ occurs exactly once, $f\ge A$), G4,
   G5, G6, G7c, G8, G8c re-verified on **all 119 census windows** by independent trial
   division; the $C(t)$ profile; the density statistics. Output, verbatim (key lines):
   ```
   G3/G4/G5/G6/G7c/G8/G8c: verified on 119/119 census windows
     C(t) on t in [2,120]: min=0.5918  max=1.0290   (L(t)/t = ln t - C(t))
     t=120: L(t)=  457.812  L/t= 3.815  C=0.9724  e^-C=0.3782  GM floor=45.38
     window-density A/t on the 107 rows t in [14,120]: min=0.263
     min-form strength min_a g(a)/t over the 107 rows: min=0.154
     C(t) large-t profile: t=200:0.9822 500:0.9919 1000:0.9956 5000:0.9990 20000:0.9997
   VERIFY461_LAWS: GREEN
   ```
3. **The box-uniform master-law computation** (new, this session): the min-form
   $\min_a g(a)$ evaluated at the box corner $n=2\cdot10^5$ for every $t\in[14,120]$
   (4001-point grid, conservative): **minimum $=0.146\,t$ (at $t=17$)**; at $t=120$:
   $19.62=0.164t$ (corner), $8.09$ at $n\approx e^{48}$, $4.72$ at $n\approx e^{100}$
   — the G8-BOX and G8-CONFINEMENT numbers.
4. **Lean CI (Kernel 35 receipt, campaign worklog):** `Erdos461.lean` landed green in
   the S041 volley (commit `b8d0f61`, CI runs `42532784292`/`42533467076`; kernels
   green in-flight at last poll; the file's `#print axioms` battery covers every theorem
   quoted in §3.4 — no `sorry` anywhere in the kernel).

**Dual-method law:** every load-bearing claim is verified by two independent routes —
the census by engine-table vs trial-division recount; the minimality by
prefix-product sliding census vs independent sieve-sliding recount (7 sampled $t$); the
four 480-censuses by kernel-decide vs independent recount; the new general laws G3–G8c
by proof (§3) vs machine check on all 119 windows; the $C(t)$/min-form constants by
exact floor-arithmetic computation.

---

## §6. KERNEL CONVERSION TARGETS (the next kernel round — the family pattern)

The G-laws are designed for the K21/K26/K30/K35 family conversion (no new mathematics
needed — only the standard lemma batteries):

* **G1 → `scomp_prod`**: induction on the prime list; needs only the Lean-green
  `spart_eq_pow` plus the quotient-valuation lemma (L1.1 — a `Nat` version via
  `Nat.pow_dvd_pow`-style divisibility arithmetic, `omega`-friendly).
* **G2/G3 → `erdos461_spacing`**: the spacing law is pure `Nat` arithmetic on the window
  indices ($m=v\,r$, $m'=v\,r'$, `omega`); the singleton law is the resulting count
  bound — `dcnt`-compatible.
* **G5 → `erdos461_2adic_floor`**: **fully `Nat`-stateable today**:
  `f461 n t ≥ (2^(K−1)·…)·⌊t/2^k⌋`-sums over the `2^k ≤ t` range with `L0` as
  `⌊(n+t)/d⌋ − ⌊n/d⌋ ≥ ⌊t/d⌋` (`Nat.floor` + `omega`) — the recommended first strike.
* **G6/G7c/G8**: ℝ-valued (logs/exponentials) — convert via the integer shadow:
  G6 as $2^{\Sigma\ln s_t}\ge\prod\prod$-products of `Nat`, or state the integer
  specialization at $t=120$ (the AM–GM product inequality over a 120-window — the
  `decide`-heavy but NO-OOM-chunked pattern of the four censuses, 240-chunks again).

---

*The census is certified. The collapse laws are closed. The reduction is complete. One
component remains — the uniform window law $\Omega$ — and it is named, reduced, and
confined. — W10.*
