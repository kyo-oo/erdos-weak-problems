# ERDŐS #1108 — THE SUBSET KERNEL LAW + THE FULL PAIR-CASCADE LAW

**Campaign:** Sessions 018 (structure law) → 023 (the general cascade
law + census-24 + CI registration). **Target:** Erdős Problem #1108
(asked by Erdős at Oberwolfach 1988, tagged `factorials`, open):

> Let $A = \{\sum_{n\in S} n! : S\subset\mathbb{N} \text{ finite}\}$.
> If $k\ge 2$, then does $A$ contain only finitely many $k$th powers?
> Does it contain only finitely many powerful numbers?

Known context: Brindza–Erdős [BrEr91] — for any $r$, if
$n_1!+\cdots+n_r!$ is powerful then $n_1 \ll_r 1$ (bounded terms at
bounded cardinality). So the entire open frontier lives at
$|S| \to \infty$. It is open even whether infinitely many squares of
the form $1 + n!$ exist (Brocard/Brown — the $\{1,u\}$ channel).

**What is delivered** — the structural laws that govern the $p$-adic
valuations of *every* element of $A$: the isolated-minimum law
(Session 018), **THE FULL CASCADE LAW (Session 023, new)** — the
general-$S$ 2-adic valuation formula with no singleton hypothesis —
the square parity invariant it forces on every square in $A$, the
all-prime stack and singleton laws (verified), and the certified
census extended to $\max S \le 24$. All Lean kernels compiled by CI;
all verification batteries green.

---

## 1. THE PAIR LAW (p = 2)

**Pairing.** $P_j = \{2j, 2j+1\}$ for $j \ge 0$ (the element $0$ pairs
with $1$; every law holds for arbitrary nonempty lists — repeats
included).

**Lemma 1 (flatness).** $v_2((2j)!) = v_2((2j+1)!)$ — since
$(2j+1)! = (2j+1)\cdot(2j)!$ and $2j+1$ is odd.

**Lemma 2 (jump).** $v_2((2j)!) < v_2((2j+2)!)$ — since
$(2j+2)! = (2j+2)(2j+1)!$ and $v_2(2j+2) \ge 1$.

By Legendre $v_2(n!) = n - s_2(n)$, the common pair level is
$\Lambda(j) = 2j - s_2(j)$, strictly increasing, with jumps
$1 + (\text{trailing ones of } j)$.

**The stack.** For $S \subseteq \mathbb{N}$ finite and $b \in S$, write
each factorial at its pair: $b! = 2^{\Lambda(b/2)} \cdot u_b$ with
$u_b$ odd. Then

$$\sum_{a \in S} a! \;=\; \sum_j 2^{\Lambda(j)} O_j(S), \qquad
O_j(S) = \sum_{b \in S \cap P_j} u_b \in \mathbb{Z}.$$

**Level occupancy (the parity heart).** With $u_{2j}$ odd and
$u_{2j+1} = (2j+1)u_{2j}$:

| $S \cap P_j$ | $O_j$ | parity |
|---|---|---|
| $\varnothing$ | $0$ | even |
| $\{2j\}$ | $u_{2j}$ | **odd** |
| $\{2j+1\}$ | $(2j+1)u_{2j}$ | **odd** |
| $\{2j, 2j+1\}$ | $u_{2j}(2j+2) = 2(j+1)u_{2j}$ | even |

*The level $\Lambda(j)$ carries an odd coefficient iff $S \cap P_j$ is a
singleton.*

## 2. THE ISOLATED-MINIMUM LAW (Session 018; Lean `isolated_min_v2`)

If the lowest occupied pair $P_{j*}$ of $S$ is a singleton $\{b\}$,
then

$$v_2\Big(\sum_{a\in S} a!\Big) = v_2(b!) = \Lambda(j*) \quad
\text{EXACTLY},$$

since $\Sigma = 2^{\Lambda(j*)}(O_{j*} + 2W)$ with $O_{j*}$ odd and
dominated addition ($\texttt{v2\_lt\_add}$) gives the exact value.

**THE SQUARE COROLLARY (Lean `square_pair_singleton_even`).** If
$\sum_{a\in S} a!$ is a perfect square and the bottom pair is a
singleton, then $\Lambda(j*)$ is even, i.e. $s_2(j*) \equiv 0
\pmod 2$.

## 3. THE FULL CASCADE LAW (Session 023, NEW — Lean `full_cascade_v2`)

The isolated-minimum law is the *degenerate* case. The general law
needs **no singleton hypothesis**. Let $j_0$ be the lowest occupied
pair of $S$ and define the **cascade integer**

$$C(S) \;=\; \Big(\sum_{a\in S} a!\Big) \Big/ 2^{\Lambda(j_0)} \in
\mathbb{Z}_{\ge 1}.$$

(Every $a \in S$ carries $v_2(a!) \ge \Lambda(j_0)$ — equality exactly
on the bottom pair — so the division is exact and $C(S) \ge 1$.)

**THE FULL CASCADE LAW.** For EVERY finite nonempty $S$:

$$\boxed{\;v_2\Big(\sum_{a\in S} a!\Big) \;=\; \Lambda(j_0) \;+\;
v_2\big(C(S)\big) \quad \text{EXACTLY.}\;}$$

*Proof.* Factor $\Sigma = 2^{\Lambda(j_0)} \cdot C(S)$ (exact
division, §pair-level lemmas) and apply multiplicativity
$v_2(2^k C) = k + v_2(C)$. ∎ (Lean: `pow_dvd_sumFacts` +
`pow_two_dvd_of_v2_ge` + `v2_pow_mul`.)

**The machine form (how $v_2(C)$ is read off the occupancy pattern).**
Write the occupied pairs above $j_0$ as a stack
$(d_i, A_i)$, $d_i = \Lambda(j_i) - \Lambda(j_0)$ strictly increasing,
$d_0 = 0$, $A_i = O_{j_i}$. Then $v_2(C) = \nu$ where $\nu$ is the
carry machine: if $v_2(A_0) < d_1$ then $\nu = v_2(A_0)$; else divide
the stack by $2^{d_1}$ (merging $A_0/2^{d_1} + A_1$ into the new
leading coefficient, accumulating $d_1$) and iterate. Each merge
consumes one pair level; termination in $\le$ #pairs steps. (This is
pure factoring — verified: machine = closed form = direct valuation on
all 16383 subsets of $[1..14]$.)

**First-level readings.**
- *Singleton bottom*: $C = u_b + 2W$ is odd ⟹ $v_2(C) = 0$ — the
  isolated-minimum law.
- *Full bottom*: $O_{j_0} = 2(j_0{+}1)u_{2j_0}$ is even ⟹ $v_2(C) \ge
  1$ — the cascade jumps at least one level above $\Lambda(j_0)$.
- *Examples* (receipts in the Lean file): $\{4,5\}$: $\Lambda = 3$,
  $C = 144/8 = 18 = 2\cdot 9$, $v_2 = 3+1 = 4$ ✓. $\{4,5,7\}$:
  $C = 5184/8 = 648 = 2^3 \cdot 81$, $v_2 = 3+3 = 6$ ✓. $\{2,3,8\}$:
  $\Lambda(1) = 1$, $C = 40328/2 = 20164 = 2^2 \cdot 5041$,
  $v_2 = 1+2 = 3$ ✓.

## 4. THE SQUARE PARITY INVARIANT (Lean `square_cascade_even`)

Every square $r^2 = \sum_{a\in S} a!$ must satisfy

$$\big(\Lambda(j_0) + v_2(C(S))\big) \equiv 0 \pmod 2
\qquad\Longleftrightarrow\qquad
s_2(j_0) \equiv v_2(C(S)) \pmod 2,$$

using Legendre $\Lambda(j) = 2j - s_2(j)$. **No hypothesis on $S$**
beyond nonemptiness. This is the complete mod-2 obstruction: the
bottom-pair binary digit-sum parity must match the cascade parity.
All 15 census squares obey it (the nontrivial checks: $\{4,5\}$:
$s_2(2)=1$, $\nu=1$; $\{4,5,7\}$: $s_2(2)=1$, $\nu=3$).

## 5. THE GENERAL $p$-BLOCK LAW (all primes; verified)

Fix a prime $p$. **$p$-blocks:** $B^p_j = \{pj, \dots, pj+p-1\}$ for
$j \ge 1$, $B^p_0 = \{1, \dots, p-1\}$. Levels $\mu_p(j) = v_p((pj)!)$
are constant on blocks and strictly increase across blocks.

**THE STACK LAW.** With $j*_p$ the lowest occupied block and
$V_p(S) = \sum_j p^{\mu_p(j)-\mu_p(j*_p)} U_j(S)$:

$$v_p\Big(\sum_{a\in S} a!\Big) \;=\; \mu_p(j*_p) + v_p\big(V_p(S)\big).$$

**THE ALL-PRIME ISOLATED-MINIMUM LAW.** If the bottom $p$-block is a
singleton $\{b\}$ then $V_p(S) \equiv b!/p^{\mu_p(j*)} \not\equiv 0
\pmod p$, so $v_p(\Sigma) = \mu_p(j*_p)$ EXACTLY.

*Verified exactly on all subsets of $[1..12]$ at $p \in
\{2,3,5,7,11\}$: stack law 20475/20475, singleton law 7399/7399
(`verify_cascade.py`, Battery B).*

## 6. THE OBSTRUCTION WEB (the #1108 engine)

$$\sum_{a \in S} a! \text{ is a square} \iff
\forall p:\ v_p(\Sigma_S) \text{ even} \wedge \text{cofactor square},$$

with the necessary conditions:
* **(p = 2)** the FULL CASCADE parity of §4 (bottom pair + cascade);
* **(Bertrand window)** for $p \in (\max S/2, \max S]$: $\Sigma_S
  \equiv T_p := \sum_{a \in S,\ a < p} a! \pmod p$;
* **(all primes)** the block cascades of §5.

The sparse-dodge is real ($S \cap [1,p) = \{1\}$ makes $T_p = 1$ for
every window prime) — the web does not close by Bertrand alone; the
composite cascade beyond the window primes is the remaining wall.

## 7. THE CERTIFIED CENSUS (exact integer arithmetic)

**Squares (Sessions 018 + 023).** Exhaustive Gray-code census with
square-residue prefilters (mod $2^6\cdot3^2\cdot5\cdot7\cdot11\cdot13$)
over ALL subsets of $[1..N]$: $N = 22$ (Session 018), $N = 24$
(Session 023, `deep_census24.py`). **Exactly 15 squares** (the trivial
$\{1\} = 1^2$ plus 14):

| $S$ | $\Sigma$ | root |
|---|---|---|
| $\{1,2,3\}$ | $9$ | $3$ |
| $\{1,4\}$ | $25$ | $5$ |
| $\{1,5\}$ | $121$ | $11$ |
| $\{1,7\}$ | $5041$ | $71$ |
| $\{4,5\}$ | $144$ | $12$ |
| $\{1,5,6\}$ | $841$ | $29$ |
| $\{4,5,7\}$ | $5184$ | $72$ |
| $\{1,2,3,6\}$ | $729$ | $27$ |
| $\{1,2,3,7,8\}$ | $45369$ | $213$ |
| $\{1,4,8,9\}$ | $403225$ | $635$ |
| $\{1,2,3,6,9\}$ | $363609$ | $603$ |
| $\{1,4,5,6,7,8\}$ | $46225$ | $215$ |
| $\{1,2,3,6,7,8,10\}$ | $3674889$ | $1917$ |
| $\{1,2,3,7,8,\dots,15\}$ | $1401602635449$ | $1183893$ |

**Zero squares for $\max S \in \{16,\dots,24\}$** — the frontier at
depth 24. Every hit re-verified through the full cascade law + parity
invariant.

**Powerful sums (Session 18).** Census over $[1..16]$: 22 powerful
sums, 7 non-square (e.g. $\{2,3\}=8$, $\{1,2,4\}=27$,
$\{2,3,8\} = 2^3\cdot71^2$).

## 8. STRUCTURAL DECOMPOSITION (why the hits exist)

**(a) Brocard/Brown channel.** $\{1,u\}$ square $\iff u!+1$ square —
$u \in \{4,5,7\}$ (known complete below $10^9$), no others to
$\max S \le 24$.

**(b) Gadget identities.** $[u,u+1]$ sums to $u!(u+2)$ (square only at
$u=4$: 144); $[u,u+2]$ sums to $u!(u+2)^2$ — never square for
$u \ge 2$.

**(c) Composition channels.** $\{1,2,3,7,8\} = 9(7!{+}1) = (3\cdot
71)^2$; $\{1,2,3,6,7,8,10\} = 729 \cdot 5041 = (27\cdot71)^2$;
$\{2,3,8\} = 8(7!{+}1) = 2^3 \cdot 71^2$.

**(d) Difference-of-squares engine.** If $\Sigma_S = r^2$ and
$\Sigma_{S\cup\{m\}} = r'^2$ then $(r'-r)(r'+r) = m!$ — square
extensions are factor pairs of factorials with matching parity (e.g.
$25 \xrightarrow{10 \cdot 8!} 635^2$).

## 9. THE FRONTIER (honest scope)

Delivered and CI-registered: the subset kernel law (isolated minimum),
**the full cascade law (general $S$)**, the square parity invariant,
the all-prime stack + singleton laws (verified), the census to
$\max S \le 24$ (squares) and $\le 16$ (powerful).

Still open within #1108 (labeled, not claimed):
1. **Finiteness of squares/powerfuls.** Brindza–Erdős reduces to
   $|S| \to \infty$; the heuristic count $\sum_j 2^j/(2\sqrt{j!})$
   converges (finiteness expected); the cascade parity invariant now
   constrains the bottom pair of EVERY candidate square — the wall is
   the composite cascade beyond the window primes plus the
   sparse-dodge.
2. **Infiniteness (negative direction)** would need an infinite square
   chain — zero new squares for $\max S \in [16,24]$ is evidence
   against.

Next engines: Legendre parity ($\Lambda(j) = 2j - s_2(j)$) as a Lean
theorem (upgrading the invariant to the explicit $s_2$ form); the
all-prime isolated-minimum law in Lean (the `vpad` toolkit of
TheoremBGeneral transfers); census MitM beyond 24.

## Files

* `SubsetKernelLaw.lean` — the kernel file: §1–§5 (isolated minimum +
  pair-singleton square corollary) + §6 (FULL CASCADE LAW + square
  cascade corollary) + receipts. Core Lean 4, zero sorry, zero custom
  axioms, CI-compiled.
* `verify_cascade.py` — Batteries A–D (triple-method law; all-prime
  stack + singleton; census 18; census-24 frontier re-verification).
* `deep_census24.py` + `deep24.txt` — the depth-24 census + log.
* `deep_squares.py`, `deep22.txt`, `verify_subset_kernel.py`,
  `deep_census.py` — Session-018 artifacts (depth-22 census, batteries).
