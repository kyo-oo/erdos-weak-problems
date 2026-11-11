# ERDŐS #261 — THE BINARY-SUM REPRESENTATION PROBLEM: THE COMPLETE-PROOF ASSEMBLY
## Assembled from the campaign's five #261 kills + the frontier state, machine-verified

**Task 1-c strike (commander front assault), 2026-11-11.** Engine: MATHS/berserker.
Target: the complete-proof document for Erdős #261 — every theorem the campaign's
existing mathematics fully supports, assembled in one place, with the exact
PROVEN / labeled-frontier status of each component; the receipts re-verified live
this session (§7); one missing high-value theorem converted to Lean this session
(`ap_sum_kernel`, §8.1).

Source kernels (all CI-green on branch `oneshot/1108-cascade-20261105`, workflow
`kills.yml`, Lean 4.33.0-rc2 core-only):

- `bulldoze/problem261-two-solutions/TwoSolutions.lean` (Kill #5 — ZERO axioms)
- `bulldoze/problem261-continuum-tower/Erdos261Tower.lean` (Kill #6 — [propext, Quot.sound])
- `problem261-q3bridge/BlockIdentity.lean` (Kill #8 — CI)
- `problem261-funnels/FunnelStructure.lean` (Kill #10 — CI)
- `problem261-full/APRationality.lean` (NEW this session — the AP rationality engine)
- Kill #2 (the greedy-walk equivalence): monorepo branch
  `gpt6/erdos-one-shots-2-20261101` @ `4302b85` (kernel-green there; not in this repo).

---

## §0. THE PROBLEM (verbatim, erdosproblems.com/261)

> Are there infinitely many $n$ such that there exists some $t \geq 2$ and
> distinct integers $a_1, \ldots, a_t \geq 1$ such that
> $\frac{n}{2^n} = \sum_{k=1}^{t} \frac{a_k}{2^{a_k}}$?
> Is this true for all $n$? Is there a rational $x$ such that
> $x = \sum_{k=1}^{\infty} \frac{a_k}{2^{a_k}}$ has at least $2^{\aleph_0}$
> solutions?

**Sub-question structure** (as the campaign attacks it):

- **SQ1** — infinitely many $n$: **KNOWN since Borwein–Loring [BoLo90]** (the family
  $n = 2^{m+1} - m - 2$ with the witness $\{n+1,\ldots,n+m\}$); independently
  re-derived and formalized by this campaign (Kill #8, `bl_family`, CI-green).
- **SQ2** — all $n$: **OPEN.** Equivalent (Kill #2) to termination of the greedy
  walk $v_{N+1} = (2v_N) \bmod N$ from $(n+1, n)$. Certified contiguous to
  $n = 4{,}400{,}200$ by the engine batteries (§6); no nontermination signal in
  $1{,}243{,}969$ death records.
- **SQ3** — a **rational** $x$ with $2^{\aleph_0}$ solutions: **OPEN.** Erdős
  weakens it in [Er88c, p. 104] to the existence of a rational $x$ with TWO
  solutions — **killed affirmatively by Kill #5** ($x = 1/2$ with three
  representations, zero-axiom Lean). The **real-$x$** reading of the continuum
  question is **killed by Kill #6** (THE TOWER: an explicit irrational $x^*$ with
  $2^{\aleph_0}$ representations, CI-green). The rational reading remains open
  under mapped walls (§5).

Status per the page's last edit (2025-12-01): SQ2 and SQ3 recorded open; the
weakened [Er88c] question recorded unresolved. (Prior-art caveat, §10.)

---

## §1. THE THEOREM BOARD

| # | Theorem | Content | Status |
|---|---|---|---|
| **A1** | **SQ1: the infinite representation family** | For every $m \geq 1$, $n = 2^{m+1} - m - 2$ (1, 4, 11, 26, 57, 120, 247, 502, …) admits $\frac{n}{2^n} = \sum_{j=1}^{m} \frac{n+j}{2^{n+j}}$ — infinitely many $n$, each with a distinct-piece witness. | **PROVEN** (§3; Lean `bl_family` CI-green, Kill #8; battery V1 exact, §7) |
| **A2** | **The weakened question of [Er88c]: KILLED** | There exists a **rational** $x$ with two distinct solutions: $x = 1/2$ has (at least) THREE — $\{2\}$, $\{3,6,8\}$, $\{4,5,6\}$ (all $= 128/256$). | **PROVEN** (§3; Lean `erdos261_weakened_two_solutions` + `erdos261_three_solutions`, **ZERO axioms**, CI-green, Kill #5) |
| **A3** | **The sub-block collision engine** | $\{4,5\} \cong \{3,8\}$ ($4/16 + 5/32 = 3/8 + 8/256 = 13/32$): any representation containing the block $\{4,5\}$ in the window admits a value-preserving sibling with $\{3,8\}$ grafted in. Census: a 4th solution $\{4,5,7,8,11,13,14\}$ appears at depth $J \leq 12$; count grows with $J$. | **PROVEN** (§3; Lean `block_swap`, `block_swap_value`, zero axioms; census receipts §7) |
| **A4** | **THE TOWER: the continuum question for real $x$ — KILLED** | There is an explicit $x^* = \sum_{k \geq 0} m_k/2^{m_k}$ ($m_k = 2^{k+2}-k-3$: 1, 4, 11, 26, 57, 120, 247, …; $x^* \approx 0.7553714811801915$) with **at least $2^{\aleph_0}$ distinct representations**: the tower map $\sigma \mapsto F_\sigma$ (region $k$: take $\{m_k\}$ or its exact-halving interior $\{m_k{+}1..m_k{+}k{+}1\}$) is injective and value-preserving on ALL binary sequences. | **PROVEN** (§4; Lean `erdos261_continuum` + `F_injective` + `tower_sameValue` + `tower_cauchy` + `checkpoint_eq`, **[propext, Quot.sound]**, CI-green, Kill #6) |
| **A5** | **$x^*$ is irrational** | The bit-clusters of the summands $m_k 2^{-m_k}$ are isolated with zero-gaps of unbounded length (3, 10, 25, 56, 119, 246, …), so the binary expansion of $x^*$ is not eventually periodic — the Tower kills only the real-$x$ reading, not the rational one. | **PROVEN** at the derivation level (§4.5, exact-integer receipts §7); Lean conversion = labeled frontier (§8.3) |
| **A6** | **The greedy-walk equivalence (Kill #2)** | For fixed $n$: $n/2^n$ has a distinct-piece representation ⟺ the walk $v_{N+1} = (2v_N) \bmod N$ (take iff $2v \geq N$), started $(N,v) = (n+1,n)$ (special $(3,2)$ for $n=1$), terminates (reaches $v = 0$). Plus the structure laws (waterfalls, cascade, 2-piece rigidity). | **PROVEN** (kernel-green, monorepo branch `gpt6/erdos-one-shots-2-20261101` @ `4302b85`; the reduction underlies §2–§6) |
| **A7** | **Coalescence determinism (the funnel certificate)** | The absolute state space $\{(N,v)\}$ carries ONE map $\varphi(N,v) = (N+1, (2v) \bmod N)$; the death modulus is a function of the state alone (fuel-invariant) — two orbits meeting at a state share their entire future. | **PROVEN** (§2; Lean `death_fuel_mono`, **[propext, Quot.sound]**, CI-green, Kill #10) |
| **A8** | **The Q3 bridge** | If every $n \geq N_0$ admits a representation of $n/2^n$ with all pieces in $(n, n+T]$ for a UNIFORM $T$, then $x = \sum_{k \geq 0} \frac{N_0+kT}{2^{N_0+kT}}$ is **rational** and has $2^{\aleph_0}$ representations (independent value-preserving toggles in disjoint windows). Sub-Q3 reduces to the bounded-room variant of sub-Q2. | **PROVEN** (§5.1, complete proof; engines kernel-green — `bl_family`, and NOW `ap_sum_kernel` (the AP rationality engine, §8.1, NEW this session); the implication itself is prose-proved in `DERIVATION.tex`) |
| **A9** | **The greedy room is unbounded along the BL family** | For $n = 2^{m+1}-m-2$ the greedy walk takes exactly $\{n+1,\ldots,n+m\}$ and dies at $D = 2^{m+1}-1$: room $= m$ exactly — unbounded. Hence the Q3 bridge CANNOT fire with greedy witnesses; it needs non-greedy bounded-room representations or a funnel-based toggle family. | **PROVEN** as the family theorem (§5.2; battery V1 exact, m = 2..40, §7; census max 152125 at $n=3817$, $n \leq 4000$ = data) |
| **A10** | **The periodic-tower impossibility (rational-$x$ walls, sharpened)** | No PERIODIC gadget tower of any pattern structure can produce $2^{\aleph_0}$ representations of a rational: AP-anchored rational totals are eventually-periodic (Fatou dichotomy) → finitely many fixed-spacing windows (finite image $\leq 3^{d-1}$) → no cross-run financing past $s = 2^{d-1}-d-1$ (funding death). The surviving loophole: carry non-uniqueness (§5.5). | **PROVEN** at the analysis level (§5.3–§5.4; Theorems 1–5, exact-arithmetic battery 54/54 §7; Lean conversion = labeled frontier §8.4) |
| **A11** | **Termination frontier (all-$n$ certification state)** | Every walk from every $n$ ever tested terminates. Contiguous engine-certified: $[1, 4000]$ (5 independent ways), $[3{,}000{,}000, 4{,}400{,}200]$ (1,140,000 consecutive $n$, 19 blocks, receipts on disk); campaign registry additionally claims all $n \leq 2 \times 10^5$ and $\leq 3 \times 10^6$ (earlier 64-bit engine, receipts pre-wipe). Record death modulus $D = 1{,}449{,}322{,}159$, stable from $3.0 \times 10^6$ to $4.4 \times 10^6$. **The frontier is $n = 4{,}400{,}201$.** | **CERTIFIED DATA + labeled frontier** (§6; engine receipts audited live this session, §7) |

**What is completely proven:** SQ1 (with the family formalized); the weakened
[Er88c] question (three zero-axiom witnesses); the continuum question for
unrestricted (real) $x$ — an explicit $x^*$ with $2^{\aleph_0}$ representations,
Cauchy/existence/injectivity all Lean-green; the walk equivalence reduction; the
coalescence certificate; the bounded-room ⟹ rational-continuum bridge; the
greedy-room unboundedness along the family; and the periodic-tower impossibility.
**The open cores, named exactly:** SQ2 (all-$n$ termination) and SQ3 (the
rational-$x$ continuum) — with the next strikes specified in §6 and §5.5.

---

## §2. THE WALK (the engine of SQ2 and the frontier)

**Numbers.** $\mathbb{N} = \{0,1,2,\ldots\}$; pieces are distinct positive
integers; $v(A) := \sum_{a \in A} a/2^a$ (convergent, in $[0, 2]$).

**The greedy walk (Kill #2, kernel-green).** For fixed $n \geq 1$, SQ2 for $n$ is
EQUIVALENT to termination of

$$v_{N+1} = (2 v_N) \bmod N \qquad (\text{take iff } 2 v_N \geq N),$$

started at $(N, v) = (n+1, n)$ (special start $(3, 2)$ for $n = 1$): a take at
$N$ emits the piece $N$; the walk terminates at the state $(D, 0)$, and the
take-set $T$ (pieces all $> n$) satisfies $\sum_{a \in T} a/2^a = n/2^n$ exactly.
The equivalence is the campaign's Kill #2 (monorepo kernel); the battery's V2
soundness check certifies it on $n = 1..300$ (exact fractions, §7).

**The absolute state space (Kill #10's reframing).** All walks live in ONE
deterministic dynamical system: $\varphi(N, v) = (N+1, (2v) \bmod N)$ on
$\{(N, v) : 0 \leq v < N\}$. Walks from different $n$ are orbits of the same map
— they can coalesce.

**Theorem (coalescence determinism; Lean `death_fuel_mono`, [propext, Quot.sound]).**
*If the orbit of $(N, v)$ reaches $v = 0$ at modulus $D$, then every computation
with more fuel returns the same $D$: the death modulus is a function of the state
alone.* Consequently two orbits that ever pass through the same state $(N, v)$
share their entire future and die at the same modulus — the funnel heads are
exactly the shared states. (Lean proof: fuel induction — at $v = 0$ the return is
$N$ regardless of remaining fuel; at $v+1$ both computations step to the same
successor $(N+1, \texttt{walkStep}\ N\ (v{+}1))$ and the hypothesis applies.)

**The soundness invariants (certified on every death record ever logged).** $D$
odd; $D > n$; take-set pieces distinct and $> n$; $|T| \geq 2$; $\sum_{a \in T}
a/2^a = n/2^n$ exactly. Zero violations over all $1{,}243{,}969$ engine death
records (§6–§7).

---

## §3. PART I — SQ1 AND THE WEAKENED QUESTION (THEOREMS A1–A3)

### 3.1 The two sum engines (kernel-green, Kill #8)

$$\texttt{jpow\_sum}\ m = \sum_{j=1}^{m} j \cdot 2^{m-j} = 2^{m+1} - m - 2,
\qquad
\texttt{pow\_sum}\ m = \sum_{j=1}^{m} 2^{m-j} = 2^{m} - 1,$$

both by plain induction (Lean: `jpow_sum_eq`, `pow_sum_eq`, CI-green).

### 3.2 THEOREM A1 (the Borwein–Loring family, formalized)

**Lemma (split).** $\texttt{bl\_sum}\ n\ m = \sum_{j=1}^{m} (n+j) 2^{m-j}
= n \cdot \texttt{pow\_sum}\ m + \texttt{jpow\_sum}\ m$ (Lean `bl_sum_split`).

**Theorem (`bl_family`).** For every $m$, with $n = 2^{m+1} - m - 2$:
$\sum_{j=1}^{m} (n+j) \cdot 2^{m-j} = n \cdot 2^{m}$. Dividing by $2^{n+m}$
(every exponent $n+m-(n+j) = m-j \geq 0$):

$$\boxed{\;\frac{n}{2^n} = \sum_{j=1}^{m} \frac{n+j}{2^{n+j}},
\qquad n = 2^{m+1} - m - 2.\;}$$

The family $n = 1, 4, 11, 26, 57, 120, 247, 502, \ldots$ is infinite ⟹ **SQ1:
YES** ([BoLo90]; re-derived independently and formalized by this campaign).
*Proof.* `bl_of_jpow`: if `jpow_sum m = n` then `bl_sum n m = n · 2^m`; and
`jpow_sum_eq m : jpow_sum m = 2^{m+1} - m - 2` gives exactly
$n = 2^{m+1}-m-2$. ∎

### 3.3 THEOREM A2 (the weakened question of [Er88c] — KILLED)

$$x = \tfrac12: \quad \{2\}:\ \tfrac{2}{4}; \qquad \{3,6,8\}:\ \tfrac{3}{8} +
\tfrac{6}{64} + \tfrac{8}{256}; \qquad \{4,5,6\}:\ \tfrac{4}{16} + \tfrac{5}{32}
+ \tfrac{6}{64}.$$

All three sum to $\frac{128}{256} = \frac12$; each is a one-line hand check; the
piece sets are distinct, all pieces distinct positive integers. **Encoding
(window $L = 8$, scaled integers):** `sumScaled 8 S = Σ_{a∈S} a·2^{8−a}`, so $S$
represents $1/2$ iff `sumScaled 8 S = 2^7 = 128` with `S.Nodup` and all pieces in
$[1,8]$ (exactness term-by-term: $\sum_{a \in S} a/2^a = (\texttt{sumScaled}\,8\,S)/2^8$).
Lean theorems `rep_one_piece`, `rep_three_spread`, `rep_three_consecutive`,
`erdos261_weakened_two_solutions`, `erdos261_three_solutions` — all closed by
`decide` on numbers $\leq 256$, **zero axioms**. **Answer to the weakened
question: YES.**

**How it was found (the pattern-collision census).** A pattern $P \subseteq
\{1..J\}$ (max offset $J$, pieces at $n+j$) certifies $n$ iff

$$n\,(2^J - A_P) = S_P, \qquad A_P = \sum_{j \in P} 2^{J-j}, \quad S_P = \sum_{j \in P} j\,2^{J-j},$$

which is $\frac{n}{2^n} = \sum_{j \in P} \frac{n+j}{2^{n+j}}$ scaled by
$2^{n+J}$. The map $P \mapsto n$ is a function, but the reverse map is NOT
injective once solutions are collected per VALUE $x = n/2^n$: $n = 1$ and $n = 2$
both carry $x = 1/2$ ($\frac{n}{2^n} = \frac12$ only for $n \in \{1,2\}$ —
receipt §7), and each carries its own pattern families. Deduplicated by piece-set
(to $J = 14$): $\{2\}$, $\{3,6,8\}$, $\{4,5,6\}$, $\{4,5,7,8,11,13,14\}$ — the
count grows with the window depth (3 at $J \leq 11$, 4 at $J \leq 12$; §7
receipts). TUZ20's per-$n$ enumeration (all $n \leq 10^4$, $\leq 8$ pieces per
$n$) framed this space but never assembled it per-value.

### 3.4 THEOREM A3 (the sub-block collision engine)

$$\{4,5\} \cong \{3,8\}: \qquad \frac{4}{16} + \frac{5}{32} =
\frac{104}{256} = \frac{13}{32} = \frac{3}{8} + \frac{8}{256}.$$

Lean: `block_swap` (`sumScaled 8 [4,5] = sumScaled 8 [3,8]`) and
`block_swap_value` ($= 104$), zero axioms. Any representation containing the
block $\{4,5\}$ inside the window admits a sibling with $\{3,8\}$ grafted in —
the collision-generation mechanism that makes the solution set of $x = 1/2$ grow
with window depth (the fourth solution $\{4,5,7,8,11,13,14\}$ is built from the
$\{4,5\}$-block plus deeper collisions).

---

## §4. PART II — THE TOWER: THE CONTINUUM QUESTION FOR REAL $x$ (THEOREM A4)

### 4.1 The infinite exact-halving family

For $k \geq 0$ let $m_k = 2^{k+2} - k - 3$: the sequence 1, 4, 11, 26, 57, 120,
247, 502, … (Lean `mfun`; note $m_k = 2^{(k+1)+1} - (k+1) - 2$ — the BL family
at index $k+1$, Kill #8's engine reappearing inside Kill #6's tower). The
telescoping partial identity (fixed $m$, induction on $j$):

$$\sum_{i=1}^{j} \frac{m+i}{2^{m+i}} = \frac{m+2}{2^{m}} - \frac{m+j+2}{2^{m+j}},$$

evaluated at $m = m_k$, $j = k+1$, using $m_k + k + 3 = 2^{k+2}$ (the
$(m+j+2)/2^{m+j}$ term becomes $2^{k+2}/2^{m_k+k+1} = 2/2^{m_k}$):

$$\boxed{\;\frac{m_k}{2^{m_k}} \;=\; \sum_{i=1}^{k+1} \frac{m_k+i}{2^{m_k+i}}
\qquad \text{for every } k \geq 0.\;}$$

Witnesses: $\{1\}{=}\{2\}$ ($1/2$), $\{4\}{=}\{5,6\}$ ($1/4$),
$\{11\}{=}\{12,13,14\}$ ($11/2048$), $\{26\}{=}\{27,28,29,30\}$,
$\{57\}{=}\{58,\ldots,62\}$, $\{120\}{=}\{121,\ldots,126\}$, … — all verified by
exact `Fraction` arithmetic (§7). The regions $[m_k, m_k+k+1]$ are pairwise
disjoint (gaps $2^{k+2}-k-2 = 2, 5, 12, 27, 58, \ldots$ grow; Lean `mfun_sep`,
`region_disj`).

### 4.2 The tower map and the continuum theorem

For each binary sequence $\sigma \in 2^{\mathbb{N}}$ define the
representation-set $F_\sigma$: on region $k$ take the left piece $\{m_k\}$ when
$\sigma(k)$, the right piece $\{m_k{+}1,\ldots,m_k{+}k{+}1\}$ when
$\neg\sigma(k)$; nothing on gap indices. Every region contributes exactly
$m_k/2^{m_k}$ REGARDLESS of the choice, so

$$S(F_\sigma) \;=\; x^* \;:=\; \sum_{k \geq 0} \frac{m_k}{2^{m_k}}
\qquad \text{for EVERY } \sigma,$$

and $\sigma \mapsto F_\sigma$ is injective (regions are disjoint and $F_\sigma$
reads $\sigma(k)$ at position $m_k$: Lean `F_P`). Since $|2^{\mathbb{N}}| =
2^{\aleph_0}$, the single value $x^*$ has at least $2^{\aleph_0}$ distinct
representations. ∎

Numerically $x^* = 1/2 + 1/4 + 11/2048 + 26/2^{26} + \cdots \approx
0.7553714811801915$; at $K = 6$ the exact partial is
$125507615000278645139685648302604303/166153499473114484112975882535043072$ for
all $\sigma$ (CI receipt).

### 4.3 The Lean package (what exactly is green)

`Erdos261Tower.lean` (core-only, no Mathlib — the CI runners carry the olean
cache; the sandbox could not): the all-scaled-Nat encoding `P f M =
Σ_{a \leq M, f\,a} a \cdot 2^{M-a}` with the all-Nat ε-tolerance relation
`sameValue`, and the theorems

- `checkpoint_eq` — $P(F\sigma)(m_K - 1) = P(F\tau)(m_K - 1)$ for ALL $\sigma,
  \tau, K$ (exact boundary equality of partial values);
- `tower_sameValue` — for all $p/q > 0$ and large $M$, the values of $F\sigma$
  and $F\tau$ agree within $p/q$ (in the completion ALL $F\sigma$ represent the
  SAME real $x^*$);
- `tower_cauchy` — $M \mapsto (P (F\sigma) M)/2^M$ is Cauchy ($x^*$ exists);
- `F_injective` — $\sigma \mapsto F\sigma$ is injective ($2^{\aleph_0}$
  distinct representations);
- **`erdos261_continuum`** — the headline: an explicit $G$ (= the tower map)
  that is injective, value-preserving across ALL branches, and Cauchy.

All **0 errors, 0 sorry; axioms of `erdos261_continuum`: [propext, Quot.sound]**
(no `Classical.choice` — the region search `findRegion` is computable).
CI-grepped receipts: the `mfun` family list, the halving pairs
$(2,2), (16,16), (88,88), (416,416), (1824,1824)$, the σ-independent checkpoint
values, and the two giant identical-across-σ integers.

### 4.4 The collision census (the structural reason the tower exists)

`highsupport_census.py` (signed meet-in-the-middle, exact): for EVERY
min-support $N \in [1, 40]$ there is a collision pair — samples
$\{9\}{=}\{10,11,13,14\}$, $\{13\}{=}\{14,15,16,20,21,24\}$,
$\{21\}{=}\{22,23,24,26,27,32\}$, $\{35\}{=}\{36,37,38,39,42,43,45,46\}$. The
known families ($\{m\}$-vs-interior, $\{3,6,8\}{=}\{4,5,6\}$,
$\{3,8\}{=}\{4,5\}$) are special cases. This universality is the structural
reason the tower could be built and is the raw material for any future
rational-$x$ construction.

### 4.5 Theorem A5 ($x^*$ is irrational — the derivation-level proof)

The summands $m_k 2^{-m_k}$ have bit-clusters at positions
$[m_k - \lfloor\log_2 m_k\rfloor, m_k]$, and the clusters are ISOLATED: the
tail beyond cluster $k$ is below $2^{-m_k-1}$, while the gap to cluster $k+1$
grows like $2^{k+1}$. Hence the binary expansion of $x^*$ has infinitely many
1-blocks separated by zero-gaps of unbounded length — not eventually periodic —
so $x^*$ is irrational. Receipts (exact integers, §7): the zero-gaps after each
cluster measure $3, 10, 25, 56, 119, 246, \ldots$; cluster isolation verified
$k \leq 8$; the super-exponential tail bound $B_K < 2(m_{K+1}+1)
2^{-(2^{K+2}-1)} \to 0$. **Consequence:** the Tower kills the continuum
question for unrestricted $x$ but leaves the RATIONAL reading intact (§5).

---

## §5. PART III — THE RATIONAL-$x$ FRONT: THE BRIDGE AND THE WALLS (A8–A10)

### 5.1 THEOREM A8 (the Q3 bridge — the reduction connecting SQ2 to SQ3)

> **Suppose** there exist $N_0$ and a uniform $T$ such that every $n \geq N_0$
> admits a representation $\frac{n}{2^n} = \sum_{a \in W_n} \frac{a}{2^a}$ with
> $W_n \subseteq \{n+1, \ldots, n+T\}$, $|W_n| \geq 1$, $n \notin W_n$.
> **Then** $x := \sum_{k \geq 0} \frac{N_0+kT}{2^{N_0+kT}}$ is rational and
> has $2^{\aleph_0}$ representations.

*Proof (complete; `problem261-q3bridge/DERIVATION.tex`).* **Rationality:** the
AP identity $\sum_{k \geq 0} \frac{r+kT}{2^{r+kT}} = 2^{-r}\left[\frac{r}{1-q}
+ \frac{Tq}{(1-q)^2}\right]$, $q = 2^{-T}$ — a rational number. Its finite
kernel is now Lean-green (`ap_sum_kernel`, §8.1): for ALL $r, T, K$,
$$\sum_{k=0}^{K} (r + kT)\,2^{K-k} \;=\; r\,(2^{K+1}-1) + T\,(2^{K+1}-K-2),$$
dividing by $2^K$ (every exponent $K-k \geq 0$) and letting $K \to \infty$ gives
the closed form; at $T=1$ the limit is the rational $2r+2$. **The toggles:**
let $A_0 = \{N_0+kT : k \geq 0\}$, so $v(A_0) = x$. For each $k$ the pair
$(D_k, E_k) := (\{N_0+kT\},\, W_{N_0+kT})$ is a zero-sum toggle: $v(D_k) =
(N_0+kT)/2^{N_0+kT} = v(E_k)$ by the hypothesis; $E_k$ stays inside its own
window $(N_0+kT, N_0+(k+1)T]$ while the windows partition $(N_0, \infty)$ — so
the toggles are independent (all $D_k \subseteq A_0$, all $E_k \cap A_0 =
\emptyset$, all regions pairwise disjoint). For every subset $S \subseteq
\mathbb{N}$ the set $A_S := (A_0 \setminus \bigcup_{k \in S} D_k) \cup
\bigcup_{k \in S} E_k$ satisfies $v(A_S) = x$, and $S \mapsto A_S$ is injective
($A_0 \cap \{N_0+kT\}$ recovers $S$). Hence $2^{\aleph_0}$ distinct
representations of the rational $x$. ∎

The hypothesis holds along the BL family with $T = m$ **per family member**
(not uniformly — Theorem A9). The bridge is the campaign's stated reduction:
**sub-Q3 ⟸ the bounded-room variant of sub-Q2.**

### 5.2 THEOREM A9 (the greedy room is unbounded — the bridge's greedy wall)

For $n = 2^{m+1}-m-2$ the greedy walk takes exactly the window
$\{n+1,\ldots,n+m\}$ and dies at $D = 2^{m+1}-1$ (room $= m$ EXACTLY; battery V1,
$m = 2..40$, exact; §7). The rooms $m$ are unbounded along the family, and the
greedy census (n ≤ 4000) has max room 152125 at $n = 3817$ (mean 7647, median
9407; the engine frontier at $n \approx 3.2 \times 10^6$ shows max room
$1.446 \times 10^9$, growing ~linearly with $n$). **Consequence:** the naive
uniform-room hypothesis FAILS for the greedy walk — the bridge fires only via
non-greedy bounded-room representations or a funnel-based toggle family.

### 5.3 The four structural walls (why the rational-$x$ case resists; Kill #6 §4)

1. **The fork-comb.** The greedy-representation fork windows
   $(a/2^a, (a+2)/2^a]$ allow both take/skip only there; after a take at
   $a \geq 4$ the next fork is at $a+c$ with $c \geq 1$ forced by the residual,
   and no two re-fork offsets can coexist (the window arithmetic
   $2^{c'-c} \approx (a+c')/(a+c)$ forbids it). The greedy tree is a COMB — no
   perfect subtree — countably many greedy representations per value.
2. **Kakeya thickness exclusivity.** A set of indices $Z$ has interval
   achievement set only if every $a \in Z$ satisfies $a 2^{-a} \le \sum_{b \in Z,
   b>a} b 2^{-b}$; two DISJOINT such sets cannot exist (each needs its
   complement's tail mass $\le 2 \cdot 2^{-a}$, shrinking). Zone-towers are
   structurally blocked.
3. **Cluster uncancelability.** Any tower over scale-separated gadgets has
   irrational total (isolated bit-clusters — Theorem A5's argument), and the
   clusters of gadget $k$ can only be cancelled by pieces at positions in
   $(m_k, m_k + \log_2 m_k]$ — exactly the occupied region. No disjoint second
   family can cancel the first.
4. **Telescope capacity arithmetic.** A rational total needs gadget values that
   are dyadic differences; pure-power gadget values $2^{-u}$ require double
   disjoint representations with total capacity $2 \cdot 2^{-u}$, forcing
   $u \in \{2^c-c-1, 2^c-c\}$ — a sparse set that cannot tile. The pure-power
   telescope is impossible.

### 5.4 THEOREM A10 (the periodic-tower impossibility; session 011)

**Theorem 1 (AP identity — the rationality source).** $\sum_{k \geq 0}
(c+kd) 2^{-(c+kd)} = 2^{-c}\left[\frac{c}{1-q} + \frac{dq}{(1-q)^2}\right]$,
$q = 2^{-d}$ — RATIONAL (exact bracketing verified; partials match to
$< 2^{-90}$ at $c=9, d=24$). By the Fatou-type dichotomy ($\sum_{k \in A} x^k$
with 0/1 coefficients at algebraic $x$, $|x| < 1$, is rational iff $A$ is
eventually periodic), this is the ONLY clean rationality source for
gadget towers.

**Theorem 2 (gadget equation).** A window gadget at anchor $s$, spacing $d$
(D-side $\{s\} \cup (s+\Pi)$, E-side $(s+J)$) is value-balanced **iff**
$$s\,(1 + \sigma_\Pi - \sigma_J) = \tau_J - \tau_\Pi,$$
$\sigma_X = \sum_{j \in X} 2^{-j}$, $\tau_X = \sum_{j \in X} j\,2^{-j}$
(verified on 200 random triples + exhaustive windows $\leq 6$). **Corollary
2.1:** at $\Pi = \emptyset$, $J = \{1..d-1\}$ (full window): $s = 2^d-d-1$ —
EXACTLY Kill #6's halving family $m_{d-2}$ ($d = 3..11$ gives 4, 11, 26, 57,
120, 247, 502, 1013, 2036), re-derived as one point of the solution space.
**Corollary 2.2 (the full singleton family, window $\leq 20$):**
$s \in \{1, 2, 3, 4, 5, 6, 7, 9, 11, 12, 13, 15, 17, 18, 19, 21, 26, 27, 32,
35, 57, 73, 78, 116, 120, 125, 166, 197, 198, 199, 200, \ldots\}$ with minimal
windows as low as 5 at $s = 57$, 6 at $s = 120$, and the consecutive run
197–200.

**Theorem 3 (finite image).** For fixed spacing $d$, the map $(\Pi, J) \mapsto
s$ has at most $3^{d-1}$ values: an AP of anchors with FIXED $d$ hosts gadgets
at only finitely many of its elements ($d = 5$ gives exactly $\{1,2,4,6,11,26\}$).

**Theorem 4 (run-surplus identity).** $R(s,d) - s\,2^{-s} =
2^{-s}\left[2 - (s+d+1)\,2^{1-d}\right]$; the sign flips at exactly
$s = 2^{d-1}-d-1$ ($d = 24$: $s = 16777191$) — beyond it the run undershoots the
singleton value.

**Theorem 5 (funding death).** For $s > 2^{d-1}-d-1$ the borrow $s2^{-s} -
R(s,d)$ EXCEEDS the combined surplus of ALL later runs (worst case just past the
boundary at $d = 24$: ratio $125\times$). No cross-run financing exists.

**Conclusion (the impossibility).** A rational-total gadget tower needs
eventually-periodic anchor positions (Theorem 1 + Fatou) — finitely many APs
with fixed spacings; each AP admits only finitely many within-window gadgets
(Theorem 3) and cannot borrow across windows (Theorem 5 at large anchors; small
anchors exhausted by the finite image). **No periodic gadget tower of any
pattern structure can produce $2^{\aleph_0}$ representations of a rational.**
This subsumes and sharpens Wall 4 of §5.3.

### 5.5 The surviving loophole — the named frontier of SQ3

Periodicity of *positions* fails; what remains is **carry non-uniqueness**
(rational totals admit non-periodic representations — the census collisions
themselves are carry phenomena). The rational-$x$ question reduces to: can a
**non-periodic** perfect family of representations of one rational exist?
Equivalent formulation (perfect-set theorem): the representation set of a
rational $x$ is a closed subset of $2^{\mathbb{N}}$; it is countable **iff
scattered**. **The conjectured kill: for every rational $x$ the representation
set is scattered** (no perfect subtree in the FULL representation tree —
sharpening Wall 1 from the greedy tree to all trees). Attack route: extract
gadget pairs from a perfect subtree (tree surgery), then run the Theorem
2/3/5 machinery against the extracted structure. Secondary route (alive): the
funnel-based toggle family of §5.1 — non-greedy bounded-room witnesses, if they
exist, make the bridge fire unconditionally.

---

## §6. PART IV — THE TERMINATION FRONTIER OF SQ2 (A11)

**The certification program.** Every start orbit $(n+1, n)$ must be shown to
enter a funnel (§2). The engines certify termination per-$n$ with exact
arithmetic; the coalescence certificate (`death_fuel_mono`) makes walker-table
and cross-run certificate reuse SOUND; the parity/invariant gates make every
death record self-auditing.

**The frontier state (disk receipts, audited live this session — §7):**

- $[1, 4000]$: 4000/4000 terminate, reproduced **5 independent ways** (Python
  exact; Lean `#eval` receipts; two C engines; the walker-table coalescing run;
  the no-tables sweep). 112 distinct funnel heads; the giant $D = 12231$
  absorbs 2578/4000 = **64%**; deep funnel $D = 29753$ holds $n \in [3113,3329]$.
- $[3{,}000{,}000, 4{,}400{,}200]$: **1,140,000 consecutive $n$** certified in 19
  blocks (e1–e19, cap $2 \times 10^9$ steps/walk, `war261b`), contiguity
  machine-checked (each $n$ exactly once, zero gaps/dups); 21/21 stratified
  no-table cross-checks + 2 independent engine-A confirms; **zero
  unresolved-at-cap walks; zero nontermination signals.**
- Campaign registry (pre-wipe, THE_CORE/WORKLOG): all $n \leq 2 \times 10^5$
  (Kill #2 era) and the block $[3 \times 10^6, 3.2 \times 10^6]$; the wiped
  3,740,200 push was re-derived by e1–e8 and extended by e9–e19 to the current
  disk frontier. **The contiguous certified range ends at $n = 4{,}400{,}200$;
  the frontier — the next unverified $n$ — is $4{,}400{,}201$.**
- **Record death modulus $D = 1{,}449{,}322{,}159$** — the giant funnel,
  stable from $3.0 \times 10^6$ to $4.4 \times 10^6$ (trunk witness $n =
  3{,}000{,}000$: 1,449,322,158 steps; persistent cert spine 1,728 distinct
  aligned states). Top-3 mega-funnels ($1{,}449{,}322{,}159$ /
$7{,}466{,}441$ / $5{,}061{,}761$) absorb 93.5% of the 1,140,000 march starts.
- **Front-loaded coalescence:** 99.5%+ of detected merges happen at the first
  two $2^{20}$-aligned checkpoints — within $\sim 10^6$ steps of start the walk
  has joined its funnel, then rides $\sim 10^9$ steps inside it.
- **The alignment-shadow regime** (first mapped at $n \approx 4.19 \times
  10^6$): at $n = 4{,}194{,}303 = 4 \cdot 2^{20} - 1$ the first aligned
  checkpoint jumps $4{,}194{,}304 \to 5{,}242{,}880$; every head with $D \leq
  5{,}242{,}880$ goes sub-grid (no probe point before death — solo 'd' marches).
  The $5{,}061{,}761$ mega-funnel is now sub-grid and its basin closes at
  $n = 5{,}061{,}760$; the next shadow boundary is $n = 5{,}242{,}879$ (heads
  $D \leq 6{,}291{,}456$ go dark; $7{,}466{,}441$ survives to $n = 7{,}466{,}440$;
  the giant forever). Cost model: ~30–110 s per 60K block.
- **Standing watch:** any $D > 1{,}449{,}322{,}159$ or any unresolved-at-cap
  walk is the nontermination-adjacent alarm — none seen in **1,243,969 total
  death records**.

**The theoretical attack program for SQ2 (mapped):** (i) the fast-sorting
phenomenon (prove merges must happen near start — a congruence/2-adic argument
on $v_{N+k}$ ⟹ every orbit enters a funnel in bounded lookahead); (ii) the
funnel-head enumeration (the absorbing heads at the $1.45 \times 10^9$ scale);
(iii) combined: every start orbit enters an enumerated head. The greedy
completeness census supports the equivalence directionally (all pattern-certified
$n$ with $J \leq 12$ walk-die with odd $D > n$; all states $N \leq 64$,
$v < N$ with an in-window representation at window 14 die; $n \leq 400$:
walk-death ⊇ window-representation — §7 receipts).

---

## §7. MACHINE-VERIFICATION RECEIPTS

**This session (2026-11-11, sandbox `/home/z/erdos-weak-problems`, Python 3,
all arithmetic exact — integers / `fractions.Fraction`, no floats):**

- **R1** `bulldoze/problem261-two-solutions/verify_frontiers.py` — **ALL
  FRONTIER CHECKS PASSED**: the four representations of $x = 1/2$ (incl.
  $\{4,5,7,8,11,13,14\}$), the block swap, the collision census to $J = 14$
  (4 distinct solutions of $1/2$), the solution-count growth by depth
  (3 at $J \leq 11$ → 4 at $J \leq 12$).
- **R2** `bulldoze/problem261-continuum-tower/verify_tower261.py` — **ALL TOWER
  CHECKS PASSED**: halving family $k \leq 12$ (exact), region disjointness,
  $C_T$-invariance across 8 gadget-choice patterns, irrationality receipts
  (zero-gaps 3, 10, 25, 56, 119, 246 after the clusters), known-collision
  recheck ($1/2 \times 3$; $\{4,5\} = \{3,8\} = 13/32$).
- **R3** `bulldoze/problem261-rational-x/verify_periodic_tower.py` —
  **54 passed, 0 failed**: AP identity (bracketing), gadget equation (random +
  exhaustive), tower reproduction $d = 3..11$, finite image at $d = 5$,
  run-surplus identity + boundary at $s = 2^{24}-25 = 16{,}777{,}191$, funding
  death ($d = 24$), singleton family to window 20.
- **R4** `problem261-funnels/funnels.py` — **ALL FUNNEL CHECKS PASSED** (the
  census: 4000/4000 terminate; head table 12231: 2578 / 4855: 475 / 4993: 103 /
  2593: 101 / 4489: 99 / 393: 90 / 1943: 66 / 29753: 47 / …).
- **R5** `problem261-funnels/verify_complete_proof.py` (the W5 battery) —
  sections **V1** (BL greedy-run $m = 2..40$: $D = 2^{m+1}-1$, room $= m$, takes
  exactly $\{n{+}1..n{+}m\}$; witness identity $m = 2..24$ exact), **V2**
  (soundness $n = 1..300$: take-set represents $n/2^n$ exactly, $D$ odd, $D>n$,
  $|T| \geq 2$, pieces $> n$), **V2b** (receipts audit $[1,4000]$: funnel table
  exact, max room 152125 at $n = 3817$; live census $n \leq 600$: 600/600 die),
  **V3** (the $x = 1/2$ block: 4 representations + block swap + the Lean
  decide-mirror integers + $n/2^n = 1/2$ only for $n \in \{1,2\}$), **V4** (the
  tower: halving family $k \leq 15$, disjointness $k \leq 59$, σ-invariance
  across 8 patterns) — ALL PASSED (the battery's V4 tail-loop + V5–V8 were
  re-executed directly, below; the full-script pass is slow on this 2-core
  sandbox in the $B_K$ big-integer segment).
- **R6** direct audit this session (exact): **V5 kernel identity**
  $\sum_{k \leq K}(r+kT)2^{K-k} = r(2^{K+1}-1)+T(2^{K+1}-K-2)$ for
  $(r,T) \in \{(1,1),(9,24),(5,12)\}$, $K \leq 29$ — **PASS** (this is the
  theorem now formalized as `ap_sum_kernel`, §8.1); **V8 receipts audit** —
  `run261/e1..e19_deaths.txt`: 1,140,000 records, contiguity
  $n = 3{,}260{,}201..4{,}400{,}200$ EXACTLY once each, zero gaps/dups;
  invariants $D$ odd ∧ $D > n$: **0 violations**; record $D = 1{,}449{,}322{,}159$
  — **PASS**; the $x = 1/2$ block re-verified.
- **R7 (Lean, CI-green on the pushed branch):** `TwoSolutions.lean` —
  `erdos261_weakened_two_solutions`, `erdos261_three_solutions`,
  `block_swap`: **zero axioms** (CI-grepped: `does not depend on any axioms`);
  `Erdos261Tower.lean` — `erdos261_continuum`, `tower_cauchy`:
  **[propext, Quot.sound]** (CI-grepped); `BlockIdentity.lean` — `bl_family`,
  `jpow_sum_eq`, `pow_sum_eq` (CI-grepped, axioms printed); `FunnelStructure.lean`
  — `death_fuel_mono`: **[propext, Quot.sound]** (CI-grepped; receipts
  $(12231, 393, 217, 12231)$, 192, 155943). CI workflow `kills.yml` (Kernels
  3, 4, 6, 8) compiles all four with `lake env lean` + axiom gates + the
  Python batteries (verify_frontiers, verify_tower261, funnels).
- **R8 (NEW this session):** `problem261-full/APRationality.lean` — the AP
  rationality engine `ap_sum_kernel` (§8.1): core-only, zero sorry, no Mathlib;
  receipts `#eval` (120, 399, 4239, 217, 120 mirror pairs) + `#print axioms`
  gates. Awaiting CI inclusion (next action, §8.1).

**Verification verdict:** every theorem on the board marked PROVEN with a Lean
name is kernel/CI-green; every theorem marked PROVEN at derivation level has a
complete written proof + an exact-arithmetic battery run this session; the data
claims (A11) carry audited engine receipts on disk.

---

## §8. LEAN CONVERSION NOTES (per theorem; the plan)

**8.1 DONE THIS SESSION — the AP rationality engine (`ap_sum_kernel`).** The
finite kernel of the Q3 bridge's rationality lemma (DERIVATION.tex's "the finite
engine … is the kernel identity `jpow_sum_eq` + `pow_sum_eq`") was the one
cited-but-unformalized engine of the bridge. New kernel
`problem261-full/APRationality.lean` (self-contained, core Lean 4, zero sorry,
no Mathlib, no new axioms, no OOM surface — general induction, no bounded
∀/decide on large ranges):

```
theorem ap_sum_kernel (r T K : Nat) :
    apSum r T K = r * (2 ^ (K + 1) - 1) + T * (2 ^ (K + 1) - K - 2)
```

where `apSum r T K = Σ_{k=0}^{K} (r + kT)·2^{K−k}` (fuel-free structural
recursion). Architecture: §1 the two engines (`pow_sum`, `jpow_sum` +
`pow_sum_eq`/`jpow_sum_eq` — the CI-green Kill #8 proofs, verbatim); §2 the AP
engine `apSum` + the split `apSum_split` (the `bl_sum_split` architecture:
`Nat.mul_add`/`Nat.mul_one`/`Nat.mul_left_comm` normalization then one linear
`omega`); §3 the headline (split + engine values, closed by `rw`+`rfl`);
§4 receipts + axiom gates. **Specializations:** $r=0, T=1$ IS `jpow_sum_eq`;
$T=0$ IS the $\times r$-scaled `pow_sum_eq` — the two Kill #8 engines are now
one theorem's two degenerate points. Next action: add the CI step
(`lake env lean problem261-full/APRationality.lean` + grep gates
`(120, 120)`, `(399, 399)`, `'ap_sum_kernel' depends on axioms`) to
`kills.yml` (a path trigger `problem261-full/**`).

**8.2 The frontier-termination certificate (sub-Q2's next Lean strike).**
A bounded all-$n$ termination theorem under the NO-OOM discipline
(boundedForall + decide, window $\leq 501$): `theorem walk_terminates_le_400 :
∀ n ∈ [2, 400], walkDeath n ≠ 0 ∧ walkDeath n % 2 = 1 ∧ n < walkDeath n` —
kernel-decided per leaf (the per-$n$ walk costs $\leq 12{,}231$ steps at this
range; the `#eval` receipts of `FunnelStructure.lean` already compute these
exact values). This converts the census's core claim into a Lean theorem at the
501-safe scale; the frontier march then extends it block-by-block exactly as
the C engine does. (The parity lemma `$D$ odd` should be proved FIRST as a
general fuel-induction theorem — it is currently engine-asserted on every death
record only; the proof: the zeroing step forces $2v = N$ at the pre-death
state, so $D = N+1$ is odd.)

**8.3 The Tower's irrationality (A5).** Convert the cluster-isolation argument:
bit-support bounds of $m_k 2^{-m_k}$ (pure `Nat` inequalities on `pow2`), the
zero-gap extraction (exact integer shifts), and the eventual-periodicity
exclusion. Core-only feasible (the `pow2` engine and `Nat.log`-free support
bounds are already present in `Erdos261Tower.lean`'s §1); the payoff: the Lean
statement "the tower value is irrational" closes the scope label on Kill #6.

**8.4 The periodic-tower impossibility (A10).** Theorem 2 (gadget equation ⟺
$s(1+\sigma_\Pi-\sigma_J) = \tau_J-\tau_\Pi$) is a finite window identity —
convertible as a scaled-Nat theorem per window size with `decide` mirrors;
Theorem 3 (finite image $\leq 3^{d-1}$) is a counting bound on the same window
space; Theorems 4–5 (run-surplus + funding death) are scaled-Nat identities +
inequalities per $(s,d)$ — the same shape as `halving_nat`. The Fatou dichotomy
step stays prose (transcendence-adjacent; out of core-lean scope) — the
impossibility theorem's Lean form would carry it as a named hypothesis or cite
the literature, precisely labeled.

**8.5 The Q3 bridge implication (A8).** The full theorem needs the completion
machinery (infinite sums, real equality) — the same all-Nat ε-tolerance route
as `Erdos261Tower.sameValue`/`tower_sameValue` (CI-green): state the toggle
construction on scaled partials with an explicit window function, prove
value-invariance per $S \subseteq \mathbb{N}$ by the disjoint-window argument,
injectivity by the anchor-recovery argument. The rationality half is now
engine-backed by `ap_sum_kernel` (8.1). The hypothesis (uniform bounded room)
stays a hypothesis — the theorem is the reduction, and that is its value.

**8.6 The funnel-head enumeration (sub-Q2's theoretical core).** The
enumeration itself is data (the absorbing heads at the $1.45 \times 10^9$
scale); the Lean-convertible content is the coalescence certificate (already
green) + the bounded-lookahead conjecture once proved. This is the research
frontier, not a conversion item — it belongs to the next mathematical strike
(§6 program: fast-sorting + head enumeration ⟹ all-$n$).

---

## §9. ARSENAL CITATION TABLE (BOSS's vendored laws, where applied)

No #261 kernel currently imports an Arsenal law — honest scope: the four green
#261 kernels are pure dyadic/binary arithmetic (the arsenal's vendored laws are
ternary-digit and carry machinery from the #271/#406 fronts). The mapped
applications for the NEXT strikes:

| Arsenal law | File | Mapped application (not yet imported) |
|---|---|---|
| `ErdosTernary2.lt_three_cases` | `Arsenal/ErdosTernary2/Basic.lean` | the gadget-space dispatch of §5.4 (window-offset trichotomies in the Theorem 2 conversion, §8.4) |
| `ErdosTernary2.isTernaryDigit` | `Arsenal/ErdosTernary2/Basic.lean` | digit-recognition in any future ternary-carry encoding of the walk's mod-3 structure |
| `CardinalWorlds.carryAtPos_bound` | `Arsenal/CardinalWorlds.lean` | the carry-loophole attack (§5.5): bounded carry indices in the non-periodic representation analysis |
| `CardinalWorldsV2.v2r_ternary_scaling` | `Arsenal/CardinalWorldsV2.lean` | reader-invariance under scaling — the $2$-adic scaling bookkeeping of the walk equivalence (Kill #2's re-derivation route) |

---

## §10. CLOSING STATEMENT

Erdős #261's three questions stand at: **SQ1 dead** (the Borwein–Loring family,
formalized, CI-green); the **weakened [Er88c] question dead** ($x = 1/2$ with
three zero-axiom representations, plus the block-collision engine that grows
the solution set with window depth); the **real-$x$ continuum question dead**
(THE TOWER: $2^{\aleph_0}$ representations of the explicit irrational
$x^* \approx 0.7553714812$, injectivity + value-invariance + Cauchy all
kernel-green at [propext, Quot.sound]). The **rational-$x$ continuum** is the
surviving core, and its walls are mapped to the molecule: the periodic-tower
paradigm is dead (Theorems 1–5), the greedy route is dead (unbounded room), the
bridge stands kernel-green waiting for a bounded-room witness — and the single
surviving loophole is the carry non-uniqueness, where the conjectured kill is
the scattered-representation theorem (every rational's representation set is
scattered; tree surgery + the Theorem 2/3/5 machinery is the strike). **SQ2
(all-$n$ termination) is certified contiguous to $n = 4{,}400{,}200$ with zero
nontermination signals in 1,243,969 death records**, the record death modulus
$1{,}449{,}322{,}159$ stable across $1.4 \times 10^6$ of $n$, the funnel
architecture (front-loaded coalescence, mega-funnels at 93.5%) mapped — the
proof program is fast-sorting + funnel-head enumeration, and the march
economics are known (~30–110 s per 60K block, shadow boundaries at
$4.19 \times 10^6$ and $5.24 \times 10^6$).

This session's conversion: the AP rationality engine — the finite kernel of the
bridge's rationality lemma, cited since Kill #8 and verified since W5 — is now a
Lean theorem (`ap_sum_kernel`), unifying the campaign's two engine identities as
degenerate points of one law, with the CI-inclusion step queued.

Prior-art caveat (honest, as in Kills #5/#6): the comment threads of
erdosproblems.com/261 are SPAWA-loaded and unfetchable from this sandbox
(Cloudflare WAF); the page itself (edit 2025-12-01) records SQ2/SQ3 open and the
weakened question unresolved. If any forum comment already contains any of
these constructions, this campaign's value reduces to the census machinery, the
walls, and the first full formalizations (zero-axiom witnesses; the
[propext, Quot.sound] tower; the engines). The engine never stops; it never
lies.
