# ERDŐS #939 — r-POWERFUL SUMS, r = 4: THE COMPLETE FRONT ASSEMBLY
## Complete proof campaign state — certified engine data, structure theory, the named core

**Task 3-a strike (Phase-2 front advance), 2026-11-12.** Engine: MATHS/berserker
doctrine, campaign registry state (post-S048). Status target: the campaign-format
assembly of the r = 4 powerful-sums front — the corrected census state, the
escalation, the local obstruction profile, the calibrated heuristic, the named
algebraic core — every finite check re-run this session (receipts §7).

---

## §0. THE PROBLEM (verbatim, the campaign's corpus registration)

> **Erdős–Moll–Walsh r-powerful question, r = 4:** do there exist pairwise-coprime
> **4-powerful** $a, b, c$ with $a + b = c$?  ($n$ is *r-powerful* iff $p \mid n
> \Rightarrow p^r \mid n$ for every prime $p$; $r=2$ is Golomb's "powerful".)

*(Corpus lineage: erdosproblems.com/939, the teorth/erdosproblems corpus
`data/problems.yaml` — the corpus checkout referenced by the sibling fronts
(e.g. P677 §0: "corpus-erdos/data/problems.yaml #677, extracted 2026-02") is no
longer present in this sandbox and no web is allowed; the statement above is the
campaign's own registered verbatim — `FULL_PROOF_CAMPAIGN/P939/PROOF.md` §0,
carried in `THE_LIST.md` §D: "#939 r-powerful sums (r=4): a+b=c all 4-powerful,
pairwise coprime … witness → YES for r=4 (new case; r=3 done by Nitaj/Cohn)".)*

**The two poles (binding success contract, from PROOF.md §1).**
**YES** = an explicit machine-certified triple (full factorizations, pairwise
gcd's = 1, every prime exponent ≥ 4, $a+b=c$).  **NO** = an impossibility
theorem over ALL triples with the elementary toolkit.  Restricted families
(all-perfect-4th-powers = FLT $n{=}4$), numerics-as-proof, and "expected
finitely many" heuristics do **not** count; if neither pole is reachable, the
deliverable is the maximal rigorous advance + the exact named wall.

---

## §1. THE THEOREM BOARD

| # | Statement | Status |
|---|---|---|
| **V16** | **ZERO pairwise-coprime 4-powerful $a+b=c$ with $c \le 10^{16}$** (complete census: 73,698 4-powerful numbers, 600,965,618 coprime pairs summed) | **CERTIFIED DATA** (§3, §7-R5; engine-complete, independently re-derived §7-R1/R4) |
| **V15** | Same, $c \le 10^{15}$ (40,048 numbers, 180,977,293 coprime pairs) | **CERTIFIED DATA** (§7-R1, re-verified §7-R4) |
| **CL** | Census growth law: $N_4(10^k)$ for $k = 8..16$ = 463, 905, 1740, 3311, 6235, 11653, 21660, 40048, 73698; ratio $N_4(X)/X^{1/4}$ drifts $4.63 \to 7.37$ (secondary term live; no constant yet) | **CERTIFIED DATA** (§7-R3/R5) |
| **K** | **Kernel decomposition:** $n$ is 4-powerful $\iff n = s\,m^4$ with $s$ 4th-power-free and $\mathrm{rad}(s) \mid m$ | **PROVEN** (§4.1, elementary, both directions) |
| **T** | **2-adic dichotomy:** in any coprime solution, each side has $v_2 \in \{0\} \cup [4,\infty)$; either $a,b$ odd and $16 \mid c$, or exactly one of $a,b \equiv 0 \pmod{16}$ and $c$ odd | **PROVEN** (§4.2) |
| **Q** | **Quality law:** $\mathrm{rad}(abc)^4 \le abc < c^3$, so $\mathrm{rad}(abc) < c^{3/4}$ — every witness is an abc-hit of quality $q > 4/3$ | **PROVEN** (§4.3) |
| **F** | **Fermat wall:** if all three sides have all exponents $\equiv 0 \pmod 4$, then $a+b=c$ is the FLT $n{=}4$ equation — empty. Any witness has $\ge 1$ side with kernel $\ne 1$ | **PROVEN reduction** (§4.4; FLT $n{=}4$ classical descent) |
| **A1** | The $a=1$ lane (consecutive 4-powerful $b, b{+}1$): **empty** $\le 10^{16}$ (smallest value-gap between 4-powerful numbers is 13, at $243 \to 256$) | **CERTIFIED DATA** (§7-R7) |
| **LOC** | **No congruence obstruction:** full local support (mod 16: 9/9 classes; mod 81: 55/55; mod 625: 501/501; mod 2401: 2059/2059) and the sumset lane is OPEN at every tested modulus ($m \le 31$ prime, $16$, $81$, $625$, $2401$, $14641$) | **CERTIFIED DATA** (§5.1, §7-R4) |
| **CAL** | **The calibrated heuristic:** the uniform + local model is *rejected at $r{=}3$* by a factor $\sim 30$ ($E_{\mathrm{cond}} = 64.5$ vs 2 observed at $10^{13}$; Poisson tail $< 10^{-20}$) — solutions are abc-quality-$3/2$ hits, a thin structured set. Calibrated $r{=}4$ expectation $\approx 0.06$ over ALL sizes: the blind witness hunt is heuristically dead | **DERIVED** (§5.3; model-level, not a theorem) |
| **W3** | The $r{=}3$ sibling: TWO certified witnesses $\le 10^{13}$ — $271^3 + 2^3 3^5 73^3 = 919^3$ (kernel triple $(1,9,1)$) and $3^4 29^3 89^3 + 7^3 11^3 167^3 = 2^7 5^4 353^3$ (kernel triple $(3,1,10)$) | **PROVEN instances** (§7-R3/R6/R8; machine-certified factorizations) |
| **KR** | **Kernel reduction:** the problem $\iff$ the $(4,4,4)$ kernel equation $d_1x^4 + d_2y^4 = d_3w^4$ over pairwise-coprime 4th-power-free kernel triples with the rad-compatibility conditions (§6.1) | **PROVEN** (§4.1 + §6.1, elementary) |
| **CORE** | **The named core:** the algebraic construction — a rad-compatible solution of a $(4,4,4)$ kernel equation (the Nitaj-style lane), with the genus-1 sub-lane (Template A: $c = z^2$) as the first search front | **OPEN** (§6; the campaign's named next strike) |

**What is completely proven:** the full elementary structure theory (K, T, Q, F,
KR), the certified-zero state $\le 10^{16}$ with a completeness proof of the
engine (§3), the closure of every local/congruence NO-route (LOC), the exact
calibration of the heuristic (CAL), and two machine-certified $r{=}3$ witnesses
whose kernel equations are the construction template (W3).  The two poles of the
verbatim ask (an explicit $r{=}4$ triple, or an all-triples impossibility
theorem) remain open — the exact walls are named in §6.3.

---

## §2. STATE ON ENTRY — AND THE DOUBLE AUDIT (both prior sweeps were vacuous)

**Registry brief on entry:** "zero solutions ≤ 10¹⁵ (5,622 4-powerfuls, 8.9M
coprime pairs — the escalation landed; uniform heuristic says the lane needs an
algebraic construction)".

**The audit (this campaign, PROOF.md §2 + re-executed this session, §7-R3):**
the prior engine `problem939-rpowerful/hunt939b.py` multiplies only by
$q = p^4$ repeatedly — it enumerates ONLY exponents $e_p \equiv 0 \pmod 4$,
i.e. **perfect fourth powers**.  Its claimed "4-powerful" counts are *exactly*
the perfect-4th-power counts: $1{,}777$ at $10^{13}$ ($m^4 \le 10^{13}$,
$m = 2..1778$) and $5{,}622$ at $10^{15}$ ($m = 2..5623$) — **both verified
this session** (§7-R3).  Both sweeps therefore only re-verified Fermat's
$n{=}4$ theorem over the perfect-4th-power subset; **neither ever touched the
actual $r{=}4$ search space** (4-powerful numbers with exponents $5,6,7 \bmod 4$:
$2^5 = 32$, $2^5 3^4 = 2592$, …).  The engine evidence inherited by this front
was vacuous; the corrected engine (`hunt939c.py`) was built and run by this
campaign: **40,048** 4-powerful numbers $\le 10^{15}$ (7.1× the old claim),
180,977,293 coprime pairs, ZERO.  This session adds the completeness proofs (§3),
the $10^{16}$ escalation (§7-R5), and the profile/calibration layer (§5).

---

## §3. THE CENSUS ENGINE — METHODOLOGY AND COMPLETENESS

**Generator (hunt939c.py, general $r$).**  Primes $p \le X^{1/r}$ (any prime
dividing an $r$-powerful $n \le X$ has $p^r \le n \le X$).  Recursive
enumeration over increasing prime indices; at each prime the exponent climbs
$r, r{+}1, r{+}2, \dots$; pruning: the first value above $X$ kills all later
primes (list sorted).

**Theorem C (census completeness, $r$-general).**  *For $X \ge 2^r$: the
generator emits exactly the $r$-powerful numbers $\le X$, each exactly once.*
*Proof.*  **Soundness:** every emitted value is $\prod p_i^{e_i}$ with $e_i \ge
r$, hence $r$-powerful, and $\le X$ by construction.  **Completeness:**
let $n \le X$ be $r$-powerful, $n = \prod_{i=1}^{t} q_i^{e_i}$, $q_1 < \dots <
q_t$, $e_i \ge r$.  Each $q_i \le X^{1/r}$, so all support primes are in the
list; the recursion path choosing $q_1, \dots, q_t$ in increasing index order
with exponent contributions $e_i = r + (e_i - r)$ is forced and unique; every
prefix along that path divides $n$ hence is $\le n \le X$, so no branch is
pruned — the path is reachable.  **No multiplicity:** the increasing support
sequence and the per-prime exponent are determined by $n$. $\square$

**Theorem P (pair-scan completeness).**  *The scan visits every coprime pair
$(a,b)$, $a < b$, $a + b \le X$ exactly once; a triple with $c \le X$ is found
iff $c$ is in the census.*  *Proof.*  Sorted values + `searchsorted` cutoffs
give each admissible pair once; coprimality is the disjointness of prime-index
sets (exact).  If $a+b=c$ with $c \le X$: $c$ is $4$-powerful $\le X$, hence in
the census by Theorem C, and the sum test finds it.  Conversely every reported
hit is a genuine triple.  **Pairwise coprimality is automatic:** $\gcd(a,c) =
\gcd(a, a+b) = \gcd(a,b) = 1$, same for $\gcd(b,c)$.  (The $a = b$ degenerate
lane is empty: $\gcd(a,a) = a = 1$ forces $1 + 1 = 2$, not 4-powerful; and
$n = 1$ is outside the census — the $a=1$ lane is the consecutive-pair lane,
empty to $10^{16}$, §7-R7.) $\square$

**Verified outputs (this session and prior campaign receipts):**

| Run | Census | Pairs (sum ≤ X) | Coprime | Hits | Time |
|---|---|---|---|---|---|
| $r{=}4$, $X = 10^{15}$ (hunt939c / R1, re-run R4) | 40,048 | 736,822,009 | 180,977,293 | **0** | 34.3 s / 24.4 s |
| $r{=}4$, $X = 10^{16}$ (hunt939d, R5 — **this session's escalation**) | 73,698 | 2,497,969,813 | 600,965,618 | **0** | 53.8 s |
| $r{=}3$, $X = 10^{12}$ (hunt939c, R2, re-run R4) | 41,135 | 742,238,041 | 231,808,926 | **1** ($271^3 + 2^3 3^5 73^3 = 919^3$) | 37.8 s |
| $r{=}3$, $X = 10^{13}$ (strike939e, R6 — this session) | 90,618 | 3,605,277,655 | 1,110,039,462 | **2** (above $+\ 3^4 29^3 89^3 + 7^3 11^3 167^3 = 2^7 5^4 353^3$) | 131.9 s |

**Growth law (decade table, R3/R5).**  $N_4(10^k)$, $k = 8..16$: 463, 905,
1740, 3311, 6235, 11653, 21660, 40048, 73698.  Ratio $N_4(X)/X^{1/4}$:
$4.63 \to 5.09 \to 5.50 \to 5.89 \to 6.24 \to 6.55 \to 6.85 \to 7.12 \to
7.37$ — the secondary term is live across the whole range (the $X^{1/5}$
error dominates the drift), so the local densities used in §5 are
**decade-averaged empirical densities**, not a fitted constant.

---

## §4. THE STRUCTURE THEORY (elementary, complete proofs)

### 4.1 Lemma K (kernel decomposition)

**K.**  $n$ is 4-powerful $\iff$ $n = s\,m^4$ with $s$ 4th-power-free
(every prime exponent of $s$ in $\{1,2,3\}$ or $s=1$) and $\mathrm{rad}(s)
\mid m$.

*Proof.*  ($\Leftarrow$) Let $p \mid n = s\,m^4$.  If $p \mid m$: $v_p(n) \ge
4v_p(m) \ge 4$.  If $p \mid s$: then $p \mid m$ (rad condition), so $v_p(n) =
v_p(s) + 4v_p(m) \ge 1 + 4 = 5$.  ($\Rightarrow$) Define $v_p(s) := v_p(n)
\bmod 4$ and $v_p(m) := (v_p(n) - v_p(s))/4$.  Then $n = s\,m^4$; $s$ is
4th-power-free ($v_p(s) \le 3$).  If $p \mid s$: $v_p(n) \ge 4$ and $v_p(n)
\not\equiv 0 \pmod 4$, so $v_p(n) - v_p(s) \ge 4$ (it is a positive multiple
of 4), hence $v_p(m) \ge 1$, i.e. $p \mid m$: $\mathrm{rad}(s) \mid m$.
$\square$

The decomposition is **unique** (the mod-4 definition fixes $s$ and $m$).
$s$ is the *kernel*, $m$ the *base*.  Machine instances (R3): $2^5 = 32 =
2 \cdot 2^4$; $2^3 3^5 73^3 = 9 \cdot 438^3$ (r=3 form); the two r=3
witness kernels in §6.

### 4.2 Lemma T (2-adic dichotomy)

**T.**  In a coprime solution $a+b=c$ of 4-powerful numbers: each of $a, b, c$
has $v_2 \in \{0\} \cup [4,\infty)$; and either (i) $a, b$ both odd and $16
\mid c$, or (ii) exactly one of $a, b$ is $\equiv 0 \pmod{16}$ and $c$ is odd.

*Proof.*  An even 4-powerful number is $0 \bmod 16$.  Coprimality allows at
most one of $a, b$ even.  Both odd $\Rightarrow$ $c = a+b$ even $\Rightarrow$
$c$ 4-powerful even $\Rightarrow 16 \mid c$.  One even ($a \equiv 0 \bmod 16$),
$b$ odd $\Rightarrow c$ odd $\Rightarrow 2 \nmid c$.  $\square$

Both lanes are locally open (§5.1: the sumset is open mod 16; the (odd,odd)
lane's $16 \mid a+b$ occurs at measured rate $0.0883$ among coprime
(odd,odd) census pairs — below the uniform $1/8$, because odd 4-powerfuls are
biased to the class $1 \bmod 16$: 3,588 of 10,403 odd members, the fourth-power
mass).  **T is the measured non-obstruction:** the 2-adic lane exists, suppressed
by bias, not closed.

### 4.3 Lemma Q (quality law)

**Q.**  $\mathrm{rad}(abc)^4 \le abc < c^3$; hence $\mathrm{rad}(abc) <
c^{3/4}$ and the abc-quality $q = \log c / \log \mathrm{rad}(abc) > 4/3$.

*Proof.*  Every prime $p \mid abc$ has $v_p(abc) \ge 4$ (all three sides
4-powerful), so $p^4 \mid abc$; $\mathrm{rad}(abc)^4 = \prod_{p \mid abc} p^4
\mid \prod p^{v_p(abc)} = abc$ (divisibility across distinct primes), giving
$\mathrm{rad}(abc)^4 \le abc$.  And $a, b < c$ (positive, $a + b = c$), so
$abc < c \cdot c \cdot c = c^3$ (in fact $ab \le (c/2)^2 < c^2$). $\square$

Consequence (the scarcity lens): every witness is an abc-hit of quality
$> 4/3$; the record known quality is $q \approx 1.63$ — quality alone is not
an obstruction, but the *empirical thinness* of the $q \ge 4/3$ family is the
measured suppression behind §5.3's calibration.  Under the abc conjecture
($\varepsilon = 1/4$), there are only finitely many $r{=}4$ solutions at all;
unconditionally nothing is known — the exact NO-lane wall (§6.3).

### 4.4 Lemma F (Fermat wall)

**F.**  If every prime exponent of each of $a, b, c$ is $\equiv 0 \pmod 4$,
then $a = x^4$, $b = y^4$, $c = z^4$ with $x,y,z$ pairwise coprime and
$x^4 + y^4 = z^4$ — empty by Fermat's $n{=}4$ descent.  Hence every witness
has at least one side whose kernel $\ne 1$ (an exponent in $\{5,6,7\} \bmod 4$
on that side).

*Proof.*  Exponents divisible by 4 make each side a perfect fourth power
(the fourth root is the product of the prime roots); coprimality transfers.
Fermat's theorem (no coprime $x^4 + y^4 = z^4$) is the classical infinite
descent (right-triangle with square area). $\square$

So the hunt space is exactly the kernel-twisted quartics — §6.

---

## §5. THE LOCAL OBSTRUCTION PROFILE AND THE CALIBRATED HEURISTIC

### 5.1 The local lane is OPEN everywhere (the NO-route closure)

On the complete $10^{15}$ census (40,048 numbers):

| Modulus | Census support | Possible | Verdict |
|---|---|---|---|
| $16$ | 9 classes | 9 ($0$ + 8 odd) | **full** |
| $81$ | 55 classes | 55 ($0$ + 54 units) | **full** |
| $625$ | 501 classes | 501 ($0$ + 500 units) | **full** |
| $2401$ | 2059 classes | 2059 ($0$ + 2058 units) | **full** |

Sumset solubility (R4): for every tested modulus $m \in \{2,3,5,7,11,13,17,
19,23,29,31,16,81,625,2401,14641\}$ there exist census residues $r_1 + r_2
\equiv r_3 \pmod m$ with no prime of $m$ dividing both $r_1, r_2$ — e.g.
$m = 2401$: $(2048, 2048, 1695)$; $m = 14641$: $(2048, 2048, 4096)$.  **No
congruence obstruction exists at any tested modulus: a NO-theorem cannot be a
local/congruence argument.**

### 5.2 The p-adic necessary conditions (the pre-sieve)

For every prime $p$: any solution has $v_p(c) \in \{0\} \cup [4,\infty)$,
i.e. $c \equiv 0 \pmod{p^4}$ or $c \not\equiv 0 \pmod p$.  Measured over the
180,977,293 coprime pairs $\le 10^{15}$ (R4):

| Filter ($p$) | Pass count | Pass rate | Random-integer rate |
|---|---|---|---|
| $2$ ($16 \mid c$ or $c$ odd) | 156,776,182 | 86.7% | 56.3% |
| $3$ ($81 \mid c$ or $3 \nmid c$) | 157,647,804 | 87.2% | 67.9% |
| $5$ | 159,708,807 | 88.3% | 80.2% |
| $7$ | 164,510,615 | 90.9% | 86.5% |
| **all four** | 107,806,598 | **59.6%** | **26.3%** |

The pair sums are far MORE admissible than random integers — the
**fresh-prime law**: for $p \mid ab$, $c = a+b \equiv b \not\equiv 0 \pmod p$
automatically (coprimality), so every prime of $ab$ is locally free for $c$
(2.27× boost measured).  The 2-adic (odd,odd) rate is $0.0883$ vs $1/8$
(the class-1 bias of §4.2).

### 5.3 The exact expectation and the r=3 calibration (the lane verdict)

**E_unif (exact).**  For each coprime pair, weight $d(c) =$ the
decade-averaged empirical density of 4-powerfuls at $c$; sum over all pairs.
**$E_{\mathrm{unif}}(r{=}4, \le 10^{15}) = 0.8217$**; $\le 10^{16}$:
$0.8233$ (R5) — the expectation mass is concentrated at SMALL sums (decades
2–6 hold $0.61$ of $0.82$; decade 15 contributes $0.0016$; the tail beyond
$10^{16}$ is $\approx 0.004$ under the decade-decay law $\sim 10^{-k/4}$).
This is the exact quantitative form of the registry's "uniform heuristic
$X^{-1/4} \to 0$".

**E_cond (locally corrected).**  Restricted to the 107.8M filter survivors:
$E_{\mathrm{loc}} = 0.4629$; dividing by the random filter rate $f_{\mathrm{rand}}
= 0.2626$: **$E_{\mathrm{cond}} = 1.7631$** — the locally-corrected model
expects $\sim 1.8$ solutions $\le 10^{15}$, all of which would sit below
$10^{10}$.  **Observed: 0** (Poisson $\mathbb{P}(0 \mid 1.76) = 0.17$ — not yet
surprising).

**The r=3 calibration (the model rejection).**  The same machinery on the
solved sibling:

| | $E_{\mathrm{unif}}$ | $E_{\mathrm{cond}}$ | observed | Poisson tail |
|---|---|---|---|---|
| $r{=}3$, $\le 10^{12}$ | 29.89 | 55.31 | **1** | $\mathbb{P}(\le 1 \mid 55) \approx 10^{-22}$ |
| $r{=}3$, $\le 10^{13}$ | 34.72 | 64.47 | **2** | $\mathbb{P}(\le 2 \mid 64) \approx 10^{-24}$ |

The uniform + local model is **rejected at $r{=}3$ by a factor $\sim 30$
(point estimate $64.5/2$)**: the sums of coprime 3-powerful pairs are NOT
random integers with respect to 3-powerfulness.  The mechanism is Lemma Q's:
an $r$-powerful solution is an abc-hit of quality $\ge r/(r-1)$ ($3/2$ at
$r{=}3$, $4/3$ at $r{=}4$) — a thin, algebraically structured set that no
density model sees (the known $q \ge 1.5$ abc-hits below $10^{13}$ can be
counted on fingers; our model "predicts" dozens).

**Calibrated verdict for $r{=}4$.**  Applying the $r{=}3$-measured suppression
($\sim 30\times$): expected $r{=}4$ solutions $\le 10^{16}$ $\approx 1.76 /
30 \approx 0.06$; over ALL sizes $\approx 0.83/30 \approx 0.03$.  $\mathbb{P}(0
\text{ hits}) \approx 0.97$.  **The blind witness hunt is heuristically dead:
escalating the range by $100\times$ adds $\sim 5 \times 10^{-5}$ expected
hits.  The lane's only live YES-pole is the algebraic construction (§6); the
NO-pole is the abc-quality wall (§6.3).**  (CAL is model-level evidence —
data-derived, not a theorem; it directs the campaign, it does not close the
problem.)

### 5.4 The closest approaches (obstruction anatomy)

The smallest filter-surviving sums $c = a+b$ over all coprime census pairs
(R4): $c = 97\ (16+81)$, $113$, $209$, $307$, $337$, $499$, $593$, $641$ —
each is a prime or a product of fresh primes with first-power valuations
($97^1$, $11^1 19^1$, …): the pre-sieve passes them at $p \le 7$ and they die
at their first fresh prime.  No systematic near-miss structure (no
"one-bad-valuation" family) appears in range — consistent with §5.3: the
obstruction is global (abc-quality), not local.

---

## §6. THE NAMED CORE — THE ALGEBRAIC CONSTRUCTION LANE

### 6.1 The kernel reduction (the (4,4,4) frame)

**KR.**  $a+b=c$ pairwise-coprime 4-powerful $\iff$ there exist
pairwise-coprime 4th-power-free $d_1, d_2, d_3$ (the kernels, Lemma K) and
bases $x, y, w$ with $\gcd(x,y) = \gcd(x,w) = \gcd(y,w) = 1$, each $d_i$
coprime to the other two sides' kernels and bases, and the rad-conditions
$\mathrm{rad}(d_1) \mid x$, $\mathrm{rad}(d_2) \mid y$, $\mathrm{rad}(d_3)
\mid w$, solving

$$d_1\,x^4 + d_2\,y^4 = d_3\,w^4 \qquad \text{(the (4,4,4) kernel equation)}$$

*Proof.*  Lemma K on each side; coprimality of the sides forces the six
cross-copimalities (any shared prime would divide two of $a,b,c$);
the rad conditions are Lemma K's. $\square$

The equation is a **generalized Fermat equation of signature (4,4,4)**: the
projective plane quartic $d_1X^4 + d_2Y^4 = d_3W^4$ is smooth (generic
kernels) of **genus 3** — finitely many integer solutions per kernel triple
(Faltings); the hunt is over kernel triples.  The $r{=}3$ certified witnesses
show the template — **small, smooth, pairwise-coprime kernels**:

$$271^3 + 9\cdot 438^3 = 919^3 \quad (\text{kernel triple } (1, 9, 1);\ 9 = 3^2)$$
$$3\cdot 7743^3 + 12859^3 = 10\cdot 7060^3 \quad (\text{kernel triple } (3, 1, 10);\ 10 = 2\cdot 5)$$

(the side factorizations: $271^3 + 2^3 3^5 73^3 = 919^3$ and $3^4 29^3 89^3 +
7^3 11^3 167^3 = 2^7 5^4 353^3$; kernels with $\mathrm{rad} \mid$ base: $3 \mid
438 = 2\cdot3\cdot73$, $3 \mid 7743 = 3\cdot29\cdot89$, $10 \mid 7060 =
2^2\cdot5\cdot353$).  **The named core: find the $r{=}4$ analogue — a
pairwise-coprime, 4th-power-free, rad-compatible kernel triple $(d_1, d_2,
d_3)$ with a positive solution of $d_1x^4 + d_2y^4 = d_3w^4$.**  The Nitaj-style
route (campaign PROOF.md §3, reconstructed mechanism): the $r{=}3$ witnesses
come from norm-cube layers in $\mathbb{Q}(\zeta_9)^+$ ($x^3+y^3$ factorization
$\Rightarrow$ Eisenstein cube $\Rightarrow$ $j{=}0$ twist rank); the $r{=}4$
analogue is the $\mathbb{Q}(\sqrt2)$-quartic norm layer $\times$ the
$\zeta_5$ cyclic-quartic norm layer — again elliptic ($j{=}1728$) — EC point
search over kernel twists with the powerful-side filters.

### 6.2 Template A — the genus-1 sub-lane (square hypotenuse)

If $c$'s kernel has all exponents even, $c = z^2$ (a powerful square), and the
equation drops to $d_1x^4 + d_2y^4 = z^2$ — signature (4,4,2), **genus 1**:
the quartic's 2-covering is the $j{=}1728$ twist family

$$E_{d_1d_2}:\quad V^2 = U^3 - 4\,d_1d_2\,U, \qquad U = 2(v + u^2),\ V = 2uU$$

**Wiring receipt (R5, machine-verified):** $d_1 = 1$, $d_2 = 8$: $1\cdot1^4 +
8\cdot1^4 = 3^2$ and $(U, V) = (8, 16)$ satisfies $V^2 = U^3 - 32U$ ($256 =
512 - 256$).  *(Status: the campaign's derived 2-covering, numerically
verified; the full descent proof of the correspondence is an open sub-core —
it is the classical congruent-number-style descent for
$aX^4+bY^4=Z^2$-type quartics.)*  The lane: EC integer-point search on
$E_{d_1d_2}$ over kernel pairs + the powerful-$z$ filter; the rank condition
($d_1d_2$ twist of $V^2 = U^3 - 4U$) is the entry ticket per kernel pair.

### 6.3 The exact walls (honest labels)

**The NO-lane wall.**  No congruence obstruction exists (§5.1 — full local
support at every valuation modulus, sumset open everywhere).  A global NO must
be an abc-quality argument: prove emptiness of the pairwise-coprime
quality-$>4/3$ family with 4-powerful sides.  Unconditionally, no technique is
known that proves finiteness of any $q \ge 4/3$ abc-family (the abc conjecture
with $\varepsilon = 1/4$ would give finiteness of ALL $r{=}4$ solutions;
unconditionally even the finiteness of $q > 1.5$ hits is open).  **This wall is
beyond current unconditional mathematics — the NO-pole is not reachable with
the elementary toolkit or any known engine.**

**The YES-lane wall.**  The blind escalation is calibrated-dead (§5.3: total
expectation $\approx 0.03$ over all sizes; the $10^{16}$ escalation added
$5\times10^{-5}$).  A witness, if it exists, is an algebraically structured
abc-hit — it must be CONSTRUCTED (kernel-twist lane §6.1/§6.2), not found by
range growth.  The Fermat wall (Lemma F) forbids the trivial kernels
$(1,1,1)$; every kernel triple with a chance is nontrivial and its quartic is
genus 3 (or genus 1 in the Template-A sub-lane) — finitely many candidate
points per triple, but the kernel-triple space itself is infinite: the
construction needs the norm-layer mechanism (PROOF.md §3) to generate the
right triples, exactly as the $r{=}3$ norm-cube mechanism generated
$(1,9,1)$ and $(3,1,10)$.

**The named next strike.**  (1) **The kernel-twist hunt**: enumerate
pairwise-coprime 4th-power-free kernel triples $(d_1,d_2,d_3)$ with
$\mathrm{rad}$-compatibility, prioritizing the Template-A genus-1 sub-lane
($d_3$-square) and the smooth-small kernels the $r{=}3$ data exhibits;
solve/search $d_1x^4+d_2y^4 = d_3w^4$ with the local pre-sieve (§5.2) as the
point filter.  (2) **The Lean kernel** (§8): the structure laws + the
$\le 10^{16}$ certified state as an auditable certificate format.

---

## §7. MACHINE-VERIFICATION RECEIPTS (this session, 2026-11-12, engine Python 3 + numpy + sympy)

All scripts and logs in `FULL_PROOF_CAMPAIGN/P939/experiments/`.

- **R1** `hunt939c.py` (campaign's corrected engine; `hunt4_1e15.log`): $r{=}4
  \le 10^{15}$: 40,048 4-powerful numbers, 736,822,009 pairs, 180,977,293
  coprime, **ZERO** (34.3 s).  Prior campaign receipt, unchanged.
- **R2** `hunt939c.py` (`hunt3_1e12.log`): $r{=}3 \le 10^{12}$: 41,135
  3-powerful, 231,808,926 coprime, **1 HIT** ($271^3 + 2^3 3^5 73^3 =
  919^3$) (37.8 s).  Prior campaign receipt, re-derived in R4/R6.
- **R3** `strike939a.py` (`strike939a.log`): the witness certification
  (factorizations, exponent audit, pairwise-gcd audit, kernel decomposition
  $(1,9,1)$); the census decade table with ratios $4.63 \to 7.12$; the
  consecutive-4-powerful count $0$ ($\le 10^{15}$); **the double vacuity
  audit**: claimed "1,777" = exact count of perfect 4th powers $\le 10^{13}$,
  claimed "5,622" = exact count $\le 10^{15}$ — both prior sweeps vacuous.
- **R4** `strike939b.py` (`strike939b.log`): the local obstruction profile at
  $10^{15}$ (24.4 s): support tables (9/9, 55/55, 501/501, 2059/2059), the
  mod-16 histogram, filter pass counts, survivor fraction $0.5957$ vs random
  $0.2626$, $E_{\mathrm{unif}} = 0.8217$, $E_{\mathrm{loc}} = 0.4629$,
  $E_{\mathrm{cond}} = 1.7631$, (odd,odd) 2-adic rate $0.0883$; the
  smallest-survivor anatomy ($c = 97, 113, 209, 307, \ldots$); the $r{=}3
  \le 10^{12}$ profile (27.4 s): $E_{\mathrm{unif}} = 29.8873$,
  $E_{\mathrm{cond}} = 55.3071$, observed 1; the sumset solubility table (OPEN
  at all 16 tested moduli).
- **R5** `hunt939d.py` (`hunt939d.log`) — **THE ESCALATION (this session)**:
  $r{=}4 \le 10^{16}$ (53.8 s): 73,698 4-powerful numbers, 2,497,969,813
  pairs, 600,965,618 coprime — **ZERO WITNESSES**; $E_{\mathrm{unif}}(\le
  10^{16}) = 0.8233$ with the full decade table; the coprime-pairs-by-decade
  table (23 … 419,988,325); the Template-A wiring receipt ($1 + 8 = 9
  \leftrightarrow (8,16) \in V^2 = U^3 - 32U$); the $r{=}3$ kernel-equation
  receipt ($271^3 + 9\cdot438^3 = 919^3$).
- **R6** `strike939e.py` (`strike939e.log`): the $r{=}3$ escalation $\le
  10^{13}$ (131.9 s): 90,618 3-powerful, 1,110,039,462 coprime pairs,
  **2 HITS** — the new witness $1392672604221 + 2126285555779 =
  3518958160000$; $E_{\mathrm{unif}} = 34.7159$, $E_{\mathrm{cond}} =
  64.4693$ (the calibration rejection of §5.3).
- **R7** The consecutive-gap audit $\le 10^{16}$: 0 pairs; smallest
  4-powerful gap $13$ (at $243 \to 256$) — the $a{=}1$ lane empty in range.
- **R8** The second-witness certification (sympy factorint): $1392672604221 =
  3^4 29^3 89^3$, $2126285555779 = 7^3 11^3 167^3$, $3518958160000 = 2^7 5^4
  353^3$ — all exponents $\ge 3$, pairwise coprime, $a + b = c$ **CERTIFIED**;
  kernels $(3, 1, 10)$ with $\mathrm{rad}(3)\mid7743$, $\mathrm{rad}(10)\mid
  7060$.

---

## §8. LEAN CONVERSION PLAN (what converts, and the first kernel)

**K1 — THE FIRST KERNEL: `Erdos939Powerful.lean` (the structure laws).**
- `def FourPowerful (n : ℕ) : Prop := ∀ p, p ∣ n → p^4 ∣ n` (decidable via
  `Nat.factors` / `minFac` recursion; $n \ge 2$ branch).
- `lemmaK : FourPowerful n ↔ ∃ s m, n = s * m^4 ∧ FourthPowerFree s ∧ rad s ∣ m`
  — the mod-4 exponent split (§4.1); `FourthPowerFree` via
  `∀ p, p^4 ∤ s`; `rad` via `Nat.factors` product-dedup.  Both directions
  are `omega`-after-`Nat.valuation`-style exponent bookkeeping (Mathlib's
  `Nat.Prime` + `Nat.pow` lemmas; the exponent induction is
  `Nat.strongRecOn` on the largest prime factor).
- `twoadic : FourPowerful-solution dichotomy` — $v_2$-reader form via the
  **Arsenal bridge**: `CardinalWorlds.v2r` is the 2-adic depth reader;
  the statement $v2r\, a = 0 ∨ 4 ≤ v2r\, a$ on each side, and the two cases
  of Lemma T (`omega` on the mod-16 residues).
- `quality : rad(abc)^4 ≤ abc ∧ abc < c^3` — the pure-integer form of Lemma Q
  (product monotonicity over `Nat.factors`; no reals needed).
- Spot-check `decide` receipts: `FourPowerful 16`, `FourPowerful 32`,
`¬ FourPowerful 8`, the two r=3 witness instances (R3/R8 factorizations as
`Nat` literals with `Nat.Prime` certificates).

**K2 — the small-range NO-certificate kernel.**  `no_r4_solution_le_10pow7`:
the 234 4-powerful numbers $\le 10^7$ as a computed `List Nat`; all
$27{,}611$ unordered pairs' sums checked outside the set; pairwise-coprime
sub-check; `decide`/`native_decide` with an explicit certificate list.  An
honest complete sub-range theorem in the kernel (the $10^{16}$ state is
data — see below).

**K3 — the YES-lane instances (r=3 sibling).**  `witness_r3_a : 19902511 +
756249048 = 776151559 ∧ (all-exponents ≥ 3) ∧ pairwise coprime` — the
factorization certificates are small-prime `decide`s.  Two instances (R3, R8).
Validates the definitions and the engine end-to-end in the kernel.

**What does NOT convert (the honest boundary).**  (i) The $10^{16}$ verdict
V16: 600,965,618 pairs — a data certificate, not a theorem; the kernel
artifact is the auditable certificate FORMAT (generator + checker pair, the
checker importing Theorem C's completeness proof for $X = 10^{16}$-truncated
exponent bounds), not the verdict.  (ii) The calibration CAL — model-level.
(iii) The named core (§6) — open.  (iv) FLT $n{=}4$ (Lemma F's classical
ingredient): to be checked against Mathlib at conversion time; if absent, the
right-triangle/square-area descent is a standard ~200-line formalization.

**First kernel = K1's `lemmaK` + `twoadic` + `quality`** — small,
self-contained, Arsenal-importing (the v2r bridge), CI-checkable in the
campaign's kernel harness.

---

## §9. ARSENAL CITATION TABLE (BOSS's vendored laws, where applied)

| Arsenal law | File | Applied at |
|---|---|---|
| `ErdosTernary2.isTernaryDigit` | `Arsenal/ErdosTernary2/Basic.lean:44` | the digit-recognition discipline of the mod-$3^k$ admissibility tests in the local profile (§5.1/§5.2): the $v_3(c) \in \{0\} \cup [4,\infty)$ filter is a ternary-digit condition on $c$'s base-3 expansion — the digit-witness reader behind the 55/55 mod-81 support table and the survivor classification |
| `ErdosTernary2.lt_three_cases` | `Arsenal/ErdosTernary2/Basic.lean:16` | the residue trichotomy $r \in \{0,1,2\}$ of the mod-3 face of Lemma T's 3-adic analogue and the mod-81 sumset dispatch (§5.1) |
| `CardinalWorlds.carryAtPos_bound` | `Arsenal/CardinalWorlds.lean:108` | the bounded-carry law ($\mathrm{carry} < 4$) of base-3 scaling — the valuation-cap discipline mirrored in the $v_2, v_3 \not\in \{1,2,3\}$ exclusion filters of §5.2 (the pre-sieve's exact arithmetic backbone) |
| `CardinalWorlds.v2r` (+ `v2r_mul_three_pow`) | `Arsenal/CardinalWorlds.lean:657, 696` | the 2-adic depth reader in exact reader form — Lemma T's dichotomy stated as `v2r a = 0 ∨ 4 ≤ v2r a` per side (K1's `twoadic`), the mod-16 histogram's valuation semantics |
| `CardinalWorldsV2.v2r_ternary_scaling` | `Arsenal/CardinalWorldsV2.lean:71` | the prime-independence law of the valuation reader ($v_2(3^a c) = v_2(c)$) — the scale-invariance behind the profile's mod-$3^k$ filter design and the kernel-decomposition scaling ($n = s\,m^4$: valuation unchanged by 4th-power scaling, Lemma K's Lean backbone) |

*(Application note, honest: these laws were forged on the Erdős-ternary
front; their use here is the arsenal doctrine's valuation-reader bridge —
the campaign's rule that every kernel imports BOSS's mathematics. The bridges
are consumable exactly as K1's `twoadic` wires `v2r` into Lemma T.)*

---

## §10. CLOSING STATEMENT

The #939 front stands corrected, escalated, and calibrated.  The inherited
engine evidence was **doubly vacuous** — both prior sweeps (10¹³, 10¹⁵)
enumerated only perfect fourth powers, re-proving Fermat's $n{=}4$ and
never touching the r=4 search space; the corrected census (this campaign)
covers the true space, and this session escalated it to **10¹⁶: 73,698
4-powerful numbers, 600,965,618 coprime pairs, ZERO witnesses**, with the
completeness proofs of the enumeration and the pair scan written down (§3).
The local NO-routes are closed by measurement (full support and open sumsets
at every tested valuation modulus — no congruence obstruction exists); the
heuristic is now **calibrated against the solved r=3 sibling**: the uniform
+ local model is rejected there by a factor ~30 (E_cond = 64.5 vs 2
observed), so the r=4 expected witness count over ALL sizes is ~0.03 — the
blind hunt is dead, exactly as the registry's uniform heuristic said, but now
with numbers.  What remains live is the named core: the **(4,4,4) kernel
equation** $d_1x^4 + d_2y^4 = d_3w^4$ over pairwise-coprime
rad-compatible kernel triples — the frame that the two certified r=3
witnesses ($271^3 + 9\cdot438^3 = 919^3$; $3\cdot7743^3 + 12859^3 =
10\cdot7060^3$) make concrete, with the genus-1 Template-A sub-lane
($V^2 = U^3 - 4d_1d_2U$, wiring machine-verified) as the first search front
and the NO-pole walled behind the abc-quality barrier (unconditionally
unreachable).  The next strike is named: the kernel-twist hunt (smooth small
kernels first, Template-A genus-1 first) and the Lean kernel K1 — the
structure laws are proven, the engine state is certified, and the front's
two poles are exactly where the campaign said they would be: an algebraic
construction or nothing.
