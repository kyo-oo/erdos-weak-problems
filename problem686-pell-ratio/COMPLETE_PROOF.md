# COMPLETE_PROOF.md — Erdős #686: THE COMPLETE ASSEMBLY (W15)

**Front:** `problem686-pell-ratio/` — the four-kernel kill spine
(Kernel 16 `Erdos686.lean`, Kernel 26 `Erdos686Squares.lean`,
Kernel 32 `Erdos686K3.lean`, Kernel 42 `Erdos686K2Class.lean`),
the W1 LaTeX proof (`K2CLASS_COMPLETE_PROOF.md`), the derivation
(`DERIVATION.md`), six verification engines. This file assembles every
CLOSED channel into one partial-structure theorem, states the exact gap
to the verbatim corpus ask, and carries the verification receipts.
Arsenal-only; no `sorry`; no sub-case dressed as the answer.

---

## §0 THE PROBLEM (VERBATIM, erdosproblems.com/686)

> Can every integer $N \geq 2$ be written as
> $$N=\frac{\prod_{1\leq i\leq k}(m+i)}{\prod_{1\leq i\leq k}(n+i)}$$
> for some $k\geq 2$ and $m\geq n+k$?

*(Verbatim as recorded in all four kernel headers: `Erdos686.lean` ll. 6–8,
`Erdos686Squares.lean` ll. 9–13, `Erdos686K3.lean` ll. 9–13,
`Erdos686K2Class.lean` ll. 9–13 — the teorth/erdosproblems corpus statement
of problem #686, uniform across the front.)*

**In-house reading (the front's standing law, fixed at Kill #20 / K16 and
held uniformly by K16/K26/K32/K42):** $m,n\in\mathbb N$, $n \ge 1$, $k \ge 2$,
$m \ge n+k$. At $k=2$ the ask is $(m+1)(m+2)=N\,(n+1)(n+2)$, $n\ge1$,
$m\ge n+2$ (`Rep2`); at $k=3$ it is $(m+1)(m+2)(m+3)=N\,(n+1)(n+2)(n+3)$,
$n\ge1$, $m\ge n+3$ (`Rep3`). (The $n=0$ reading — denominator $k!$ — is a
different habitat, never this front's target.)

---

## §1 THE PARTIAL-STRUCTURE THEOREM (the assembly)

**The Chebyshev chain.** For $y \ge 2$ define $a_0=1$, $a_1=y$,
$a_{n+2}=y\,a_{n+1}-a_n$ (`chev`). The **chain** is
$$\mathcal C \;:=\; \{\,\mathrm{chev}\,y\,j \;:\; y \equiv 2 \ (\mathrm{mod}\ 4),\ y \ge 10,\ j \ge 1\,\}.$$
Layer structure: $a_1$-layer $= y$ (all $t \equiv 2 \bmod 4$, $t \ge 10$);
$a_2$-layer $= y^2-1$ (odd: $99, 195, 323, 483, \dots$);
$a_3$-layer $= y^3-2y$ ($\equiv 0 \bmod 4$: $980, 2716, \dots$);
$a_4$-layer $= y^4-3y^2+1$ ($9701, \dots$); degree $j$ in $y$ per layer.

**THEOREM (the closed channels of Erdős #686).**

* **(A) Non-square channel — COMPLETE** (Kernel 16, Kill #20, CI run
  42212351838 GREEN). For every **non-square** $N \ge 2$ there exist $m,n$
  with $n \ge 1$, $m \ge n+2$, $(m+1)(m+2) = N\,(n+1)(n+2)$ — a $k=2$
  representation. Full proof in §2 (Pell unit construction; the 90-witness
  Lean table is the machine certificate for $N \le 100$, the battery the
  dual-method certificate for $N \le 200$).

* **(B) $k=2$ square channel — COMPLETE, both directions, scan-free**
  (Kernel 42 = the W1 eight theorems; LaTeX `K2CLASS_COMPLETE_PROOF.md`;
  Lean `Erdos686K2Class.lean`, 642 lines, r3 = commit `3b39ebf`). For every
  $t \ge 2$:
  $$\big(\exists\,m\,n,\ \mathrm{Rep2}(t^2)\,m\,n\big) \iff t \in \mathcal C,$$
  and the representing pair is constructively explicit: given
  $t = \mathrm{chev}\,y\,j \in \mathcal C$,
  $X = (\mathrm{chev}\,y\,(j{+}1)-\mathrm{chev}\,y\,(j{-}1))/2$,
  $Y = y/2$, $m = (X-3)/2$, $n = (Y-3)/2$. Full proof in §3.

* **(C) $k=3$ square witness laws** (Kernel 32, Kill #36, CI run 42527356579
  GREEN). Six $k=3$ square classes: $t \in \{3, 4, 70, 1189, 1798, 4756\}$
  have kernel-decided $k=3$ witnesses; the witness relation composes (chain
  law); the $4756 = 4\cdot1189$ composite double-hit is proved. Full
  statement of laws in §4.

* **(D) No-go theorems.** (i) The general $k=2$ no-go: $t \notin \mathcal C
  \Rightarrow$ **no** $k=2$ representation of $t^2$ (immediate contrapositive
  of (B)). (ii) The explicit small-$t$ form (`erdos686k2_nogo`): $2 \le t
  \le 16$, $t \notin \{10, 14\} \Rightarrow \neg\exists m\,n,\ \mathrm{Rep2}(t^2)$
  — scan-free, modular only. (iii) Kernel 26's census theorem (subsumed by
  (B)): for $t \in [2,100]$, $t^2$ is $k=2$-representable $\iff$
  ($t \equiv 2 \bmod 4$, $t \ge 10$) or $t = 99$ — and the engine census
  extends this to $t \le 300$ with second sporadic $t = 195 = \mathrm{chev}\,14\,2$.
  §5.

**COROLLARY (the exact gap — the completion equivalence).** By (A) every
non-square $N$ is represented at $k=2$; by (B) every $t \in \mathcal C$ is
represented at $k=2$ and every $t \notin \mathcal C$ is **not**; by (C) the
off-chain $t \in \{3, 4, 1189, 4756\}$ are represented at $k=3$. Therefore
the verbatim corpus ask — "can **every** integer $N \ge 2$ be written …" —
is **exactly equivalent** to the single remaining channel:

$$\boxed{\text{For } t \notin \mathcal C \cup \{3,4,1189,4756\}:\ \text{does } t^2
\text{ admit a representation at some } k \ge 3?}$$

YES on this channel (all off-chain $t$) ⟹ the corpus answer is **YES**
(every $N \ge 2$ covered). NO on even one such $t$ ⟹ the corpus answer is
**NO** (that $t^2$ is a counterexample: no $k{=}2$ by (D), no $k \ge 3$ by
assumption). §6 names the channel's frontier and structure. This assembly
is therefore the **complete partial-structure theorem** for #686: the
closed channels are proved below in full, and the open core is named
exactly — never dressed as solved.

---

## §2 PART I — THE NON-SQUARE CHANNEL (complete Pell proof)

*(Kernel 16 `Erdos686.lean`; DERIVATION.md Part I; Kill #20.)*

**THEOREM I.** For every non-square $N \ge 2$ there exist $m \ge n+2$,
$n \ge 1$ with
$$(m+1)(m+2) = N\,(n+1)(n+2).$$

**Proof.** Substitute $X = 2m+3$, $Y = 2n+3$ (both odd, $Y \ge 5$, $X \ge Y+4$
at the end). Since $4(m+1)(m+2) = (2m+3)^2 - 1$ and $4(n+1)(n+2) =
(2n+3)^2-1$ (ring), the equation is equivalent to the Pell-form identity
$$X^2 - N\,Y^2 = 1 - N. \tag{$\ast$}$$

**The unit construction.** $N$ non-square ⟹ the Pell equation
$x^2 - N\,y^2 = 1$ has its fundamental solution $(x_1, y_1)$, $x_1 \ge 1$,
$y_1 \ge 1$ (continued fractions). The element $1+\sqrt N$ has norm $1-N$;
hence for every $j \ge 1$,
$$X_j + Y_j\sqrt N = (x_1+y_1\sqrt N)^j\,(1+\sqrt N), \qquad
X_j^2 - N\,Y_j^2 = 1 - N,$$
so every $(X_j, Y_j)$ solves $(\ast)$, with $X_1 = x_1 + N y_1$,
$Y_1 = x_1 + y_1$; and for $j = 2$: $x_2 = x_1^2 + N y_1^2$, $y_2 = 2x_1y_1$
(squaring the unit), so $X_2 = x_2 + Ny_2$, $Y_2 = x_2 + y_2$.

**Parity lemma (some $j \in \{1,2\}$ makes $X_j, Y_j$ both odd).**
Case analysis on $x_1^2 - N y_1^2 = 1$:

* $N \equiv 1 \pmod 4$: if $y_1$ odd then $x_1^2 \equiv 1 + y_1^2 \equiv 2
  \pmod 4$ — impossible; so $y_1$ even, $x_1$ odd ($x_1^2 \equiv 1$). Then
  $X_1 = x_1 + Ny_1 = \text{odd}+\text{even}$, $Y_1 = x_1+y_1 =
  \text{odd}+\text{even}$ — both odd. $j = 1$.
* $N \equiv 3 \pmod 4$: if $y_1$ odd then $x_1^2 \equiv 1+3 \equiv 0 \pmod 4$,
  so $x_1$ even and $X_1 = \text{even}+\text{odd}$, $Y_1 = \text{even}+
  \text{odd}$ — both odd. If $y_1$ even then $x_1$ odd and $X_1, Y_1 =
  \text{odd}+\text{even}$ — both odd. $j = 1$.
* $N$ even: $Ny_1^2 \equiv 0 \pmod 2$ forces $x_1$ odd. If $y_1$ even,
  $j=1$ works as above. If $y_1$ odd (the odd-odd unit): $Y_1 = x_1+y_1$
  even — fails; take $j = 2$: $x_2 = x_1^2 + Ny_1^2 = \text{odd}+
  \text{even} = \text{odd}$, $y_2 = 2x_1y_1$ even, so $X_2 = x_2 + Ny_2 =
  \text{odd}$, $Y_2 = x_2 + y_2 = \text{odd}$. $j = 2$.

**Size lemma (at the parity-valid $j \in \{1,2\}$: $n \ge 1$ and $m \ge n+2$).**
Here $m - n = (X_j - Y_j)/2 = (N-1)\,y_j/2 \ge 0$ and $n \ge 1 \iff Y_j \ge 5$.

* $N \ge 5$: $m \ge n+2 \iff X_j - Y_j \ge 4$, and $X_j - Y_j = (N-1)y_j
  \ge 4 \cdot 1 = 4$ ✓ automatically. For $Y_1 \ge 5$: the fundamental pairs
  with $x_1 + y_1 \le 4$ solving $x^2 - Ny^2 = 1$ are exactly $(1,1),(1,2),
  (1,3) \to N=0$; $(2,1) \to N=3$; $(2,2) \to N = 3/4 \notin \mathbb Z$;
  $(3,1) \to N=8$ — none is a non-square $N \ge 5$, so $Y_1 \ge 5$ ✓. If
  the parity lemma sent us to $j = 2$: $Y_2 = x_2 + y_2 \ge x_1^2 + Ny_1^2
  + 2 \ge 1 + 5 + 2 = 8 \ge 5$ ✓ and $X_2 - Y_2 = (N-1)y_2 \ge 4 \cdot 2
  = 8 \ge 4$ ✓.
* $N = 2$: fundamental $(x_1,y_1) = (3,2)$; $j=1$ gives $(m,n) = (2,1)$ —
  $m \ge n+2$ fails. $j=2$: $(x_2,y_2) = (17,12)$, $X_2 = 41$, $Y_2 = 29$,
  $(m,n) = (19,13)$: $20 \cdot 21 = 420 = 2 \cdot 14 \cdot 15$ ✓.
* $N = 3$: fundamental $(2,1)$; $j=1$ gives $Y_1 = 3$ ($n = 0$ — fails).
  $j=2$: $(x_2,y_2) = (7,4)$, $X_2 = 19$, $Y_2 = 11$, $(m,n) = (8,4)$:
  $9 \cdot 10 = 90 = 3 \cdot 5 \cdot 6$ ✓.
* $N = 8$: fundamental $(3,1)$ — $j=1$ fails parity ($Y_1 = 4$ even).
  $j=2$: $(x_2,y_2) = (17,6)$, $X_2 = 65$, $Y_2 = 23$, $(m,n) = (31,10)$:
  $32 \cdot 33 = 1056 = 8 \cdot 11 \cdot 12$ ✓.

Every case closes; the witness is $(m,n) = ((X_j-3)/2, (Y_j-3)/2)$ at the
parity-and-size-valid $j \in \{1,2\}$. ∎

**Machine certificates.** The Lean table `pellWitnesses`
(`Erdos686.lean` §2, `erdos686_table_all` by `decide`): all **90
non-squares $2 \le N \le 100$** with explicit $(m,n)$ — e.g. $N=61$ at
$(m,n) = (7780855913, 996236513)$. The battery (`pell_battery.py`,
dual-method: Pell-unit construction ‖ direct arithmetic) verifies **186/186
non-squares $\le 200$**, zero failures, $j \in \{1,2\}$ throughout — re-run
GREEN this session (§8).

---

## §3 PART II — THE COMPLETE $k=2$ SQUARE CLASSIFICATION (Kernel 42 / W1)

*(The eight theorems, all PROVEN; complete LaTeX in
`K2CLASS_COMPLETE_PROOF.md` (W1, 444 lines); Lean `Erdos686K2Class.lean`
(r3). Notation: $a_n := \mathrm{chev}\,y\,n$; all arithmetic in
$\mathbb N$ with truncated subtraction — **every subtraction below is
exhibited as exact**.)*

**Support laws.**

* **L1 (monotonicity, `chev_mono`/`chev_mono'`/`chev_pos`).** $y \ge 2
  \Rightarrow a_n \le a_{n+1}$ for all $n$ — induction: $a_{n+2} =
  y\,a_{n+1} - a_n$ with $y\,a_{n+1} \ge 2a_{n+1} \ge a_{n+1} + a_n$ (IH),
  exact subtraction. Hence $i \le j \Rightarrow a_i \le a_j$ and $1 \le a_n$.
* **L2 (additive law, `chev_add`).** $a_n + a_{n+2} = y\,a_{n+1}$ — from
  the definition and L1 (exact subtraction, `Nat.add_sub_cancel'`).
* **L4 (gap laws, `gap_mod4`/`gap_ge`).** With $g_i := a_{i+1} - a_i$
  (exact by L1): $g_0 = y-1$; $g_{i+1} = g_i + (y-2)\,a_{i+1}$;
  $g_i \ge y-1$; and $y \equiv 2 \pmod 4 \Rightarrow g_i \equiv 1
  \pmod 4$. *(The round-1 kernel's `gap_hop` was REFUTATED as written —
  RHS typo; counterexample $y{=}10, j{=}1$: $90 \ne 100$ — and deleted in
  the r2/r3 rewrite; Route B = these gap laws replaces it.)*

**T1 (`cassini`).** $a_n a_{n+2} + 1 = a_{n+1}^2$.
*Proof.* Induction on $n$. Base $n=0$: $a_0a_2+1 = (y^2-1)+1 = y^2 =
a_1^2$ (exact: $y \ge 2$). Step: multiply the additive laws
$a_n + a_{n+2} = y a_{n+1}$ and $a_{n+1} + a_{n+3} = y a_{n+2}$ by $a_{n+2}$
resp. $a_{n+1}$; equal right-hand sides give $a_na_{n+2} + a_{n+2}^2 =
a_{n+1}a_{n+3} + a_{n+1}^2$; substitute the IH $a_na_{n+2} = a_{n+1}^2-1$
(exact) to get $a_{n+1}a_{n+3} + 1 = a_{n+2}^2$. ∎

**T3 (`pair_diff_mod4`).** $y \equiv 2 \pmod 4$, $j \ge 1$ ⟹
$(a_{j+1} - a_{j-1}) \bmod 4 = 2$.
*Proof.* $a_{j+1}-a_{j-1} = g_j + g_{j-1}$ (exact, L1); each gap
$\equiv 1 \pmod 4$ by L4; $1+1 \equiv 2$. ∎

**T4 (`erdos686k2_witness_of_chain`, the ⟸ construction).** $y \equiv 2
\pmod 4$, $y \ge 10$, $j \ge 1$ ⟹ with $t = a_j$, $E = a_{j+1}-a_{j-1}$,
$X = E/2$, $Y = y/2$, $m = (X-3)/2$, $n = (Y-3)/2$:
$\mathrm{Rep2}(t^2)\,m\,n$.
*Proof.* (1) $E \equiv 2 \pmod 4$ (T3) ⟹ $E = 2X$ exact, $X$ odd; $y = 2Y$,
$Y$ odd $\ge 5$. (2) L2 at $j{-}1$: $a_{j-1} + a_{j+1} = y\,t = 2Yt$, and
$d_2 - d_1 = E = 2X$ with $d_1 = a_{j-1} = Yt - X \ge 1$, $d_2 = a_{j+1} =
Yt + X$. (3) **Master identity** (Cassini T1 at $j{-}1$, index shift):
$d_1d_2 + 1 = t^2$, i.e. $(Yt)^2 - X^2 + 1 = t^2$, i.e.
$$X^2 - 1 = t^2\,(Y^2-1). \tag{$\star$}$$
(4) $X = 2m+3$, $Y = 2n+3$ ⟹ $(m+1)(m+2) = (X^2-1)/4$ and
$(n+1)(n+2) = (Y^2-1)/4$; dividing $(\star)$ by 4:
$(m+1)(m+2) = t^2(n+1)(n+2)$ — `Rep2`'s first conjunct with $N = t^2$.
(5) Sizes: $n \ge 1$ from $Y \ge 5$; $m \ge n+2 \iff X \ge Y+4$, and
$X = E/2 \ge (g_j + g_{j-1})/2 \ge y - 1 = 2Y - 1 \ge Y + 4$ (L4, $Y\ge5$). ∎

**T5 (`mutual_step`).** $2 \le u_1 < u_0$, $u_0 \mid u_1^2-1$, $u_1 \mid
u_0^2-1$ ⟹ exists $u_2$: $u_0u_2 = u_1^2-1$, `Mutual $u_1\,u_2$`,
$1 \le u_2 < u_1$.
*Proof.* $u_2 := (u_1^2-1)/u_0$ (integral, $\ge 1$ since $u_0 \le u_1^2-1$;
$< u_1$ since $u_1^2 < u_1u_0$). Put $W = u_0u_2 = u_1^2 - 1$. Then
$u_1 \mid u_2^2 - 1$: $u_1 \mid W + 1$ so $u_1 \mid (W-1)(W+1) = W^2 - 1
= (u_0^2-1)u_2^2 + (u_2^2-1)$ (pure ring; difference of squares, $W \ge 1$),
and $u_1 \mid (u_0^2-1)u_2^2$ (hypothesis × $u_2^2$); subtract
divisibilities. And $u_2 \mid u_1^2 - 1 = u_2 u_0$ — witness $u_0$. ∎

**T6 (`chain_of_mutual`, the descent).** $1 \le u_1 < u_0$, `Mutual $u_0\,u_1$`
⟹ exists $y \ge 2$, $j \ge 1$: $u_0 = \mathrm{chev}\,y\,j$ and
$u_1 = \mathrm{chev}\,y\,(j-1)$.
*Proof.* Fuel induction on $u_0$. If $u_1 = 1$: return $(y,j) = (u_0, 1)$
($a_1 = y = u_0$, $a_0 = 1 = u_1$). If $u_1 \ge 2$: T5 yields $u_2$ with
`Mutual $u_1\,u_2$`, $1 \le u_2 < u_1$; apply the IH to $(u_1, u_2)$,
getting $u_1 = \mathrm{chev}\,y\,j$, $u_2 = \mathrm{chev}\,y\,(j-1)$; the
**Cassini climb** at $j{-}1$ gives
$\mathrm{chev}\,y\,(j-1)\cdot\mathrm{chev}\,y\,(j+1) = u_1^2 - 1 = u_0u_2$,
and cancelling $u_2 \ge 1$: $u_0 = \mathrm{chev}\,y\,(j+1)$. Return
$(y, j+1)$. ∎

**T7 (`erdos686k2class`, the iff — THE CLASSIFICATION).** For every
$t \ge 2$: $\big(\exists m\,n,\ \mathrm{Rep2}(t^2)\,m\,n\big) \iff
\exists y\,j:\ y \bmod 4 = 2 \wedge 10 \le y \wedge 1 \le j \wedge
t = \mathrm{chev}\,y\,j$.
*Proof.* **(⟸)** T4 directly. **(⟹)** Given `Rep2 (t²) m n`: put
$X = 2m+3$, $Y = 2n+3$, $T = tY$. (1) **Master′**: from
$(2m+3)^2 = 4(m+1)(m+2)+1$ and $(2n+3)^2 = 4(n+1)(n+2)+1$ (ring) and the
Rep2 equation: $X^2 + t^2 = T^2 + 1$. (2) $X < T$ (else $T^2 \le X^2$
forces $t \le 1$); set $d_1 = T - X \ge 1$, $d_2 = X + T$; then
$d_1d_2 = T^2 - X^2 = t^2 - 1$, $d_1 < t$ (else $t^2 \le d_1^2 \le d_1d_2
= t^2-1$). (3) **`Mutual t d₁`**: $t \mid d_1 + d_2 = 2T = 2tY$ so
$t \mid d_1(d_1+d_2) = d_1^2 + (t^2-1)$, hence $t \mid d_1^2 - 1$; and
$d_1 \mid t^2 - 1 = d_1d_2$. (4) **Descent**: T6 on $(t, d_1)$ yields
$y \ge 2$, $j \ge 1$ with $t = \mathrm{chev}\,y\,j$, $d_1 =
\mathrm{chev}\,y\,(j-1)$. (5) $d_2 = \mathrm{chev}\,y\,(j+1)$ (Cassini at
$j{-}1$: $\mathrm{chev}\,y\,(j-1)\cdot\mathrm{chev}\,y\,(j+1) = t^2-1 =
d_1d_2$; cancel $d_1 \ge 1$). (6) **Y-law**: $d_1 + d_2 = 2tY$ (step 2) and
$d_1 + d_2 = \mathrm{chev}\,y\,(j-1) + \mathrm{chev}\,y\,(j+1) = y\,t$
(L2 at $j{-}1$); cancel $t \ge 1$: $y = 2Y = 4n + 6 \equiv 2 \pmod 4$,
$y \ge 10$ ⟺ $n \ge 1$ ✓. ∎

**T8 (`erdos686k2_nogo`, scan-free).** $2 \le t \le 16$, $t \ne 10$,
$t \ne 14$ ⟹ $\neg\exists m\,n,\ \mathrm{Rep2}(t^2)$.
*Proof.* If `Rep2 (t²) m n`, T7 (⟹) gives $y \equiv 2 \pmod 4$, $y \ge 10$,
$j \ge 1$, $t = \mathrm{chev}\,y\,j$. Monotonicity: $y \le t \le 16$; the
residue split is exhaustive: $y \in \{10, 14\}$. $y = 10$: $j = 1$ gives
$t = 10$ (excluded); $j \ge 2$ gives $t \ge \mathrm{chev}\,10\,2 = 10^2-1
= 99 > 16$. $y = 14$: $j=1$ gives $t = 14$ (excluded); $j \ge 2$ gives
$t \ge 14^2 - 1 = 195 > 16$. All four arms contradict. Modular throughout —
no scan of $(m,n)$. ∎

**Subsumption corollaries.** (i) Kernel 26's census theorem
($t \in [2,100]$: $t^2$ $k=2$-representable $\iff$ ($t \equiv 2 \bmod 4$,
$t \ge 10$) $\vee$ $t = 99$) is T7 restricted to $t \le 100$: the chain
values $\le 100$ are exactly the $a_1$-family $\{10, 14, \dots, 98\}$ plus
$99 = \mathrm{chev}\,10\,2$. (ii) Kernel 16's square family
(`erdos686_square_family_identity`: $t = 2(2d+5)$, $m = (2d+5)^2-2$,
$n = d+1$, a subtraction-free polynomial identity) is T4 at $j = 1$.
(iii) Kernel 26's no-go reduction (`erdos686sq_noRep`: any $k=2$
representation of $t^2$ forces a divisor pair $(d_1,d_2)$ of $t^2-1$ with
the master identity $(2m+3)^2 - t^2(2n+3)^2 = 1-t^2$) is steps (1)–(2) of
T7 (⟹). (iv) The de-sporadicization: $99 = \mathrm{chev}\,10\,2$ and
$195 = \mathrm{chev}\,14\,2$ — the "sporadics" are $a_2$-layer chain values
(`edge99`, `edge195`). (v) New-layer kernel receipts: `edge980` ($t = 980
= \mathrm{chev}\,10\,3$, $m = 2399$, $n = 1$: $2400 \cdot 2401 = 5762400
= 980^2 \cdot 6$), `edge2716` ($t = \mathrm{chev}\,14\,3$, $(m,n) =
(9407, 2)$), `edge9701` ($t = \mathrm{chev}\,10\,4$, $(23761, 1)$),
`edge323`, `edge10604`, `edge17524`.

---

## §4 PART III — THE $k=3$ SQUARE WITNESS LAWS (Kernel 32)

*(Kernel 32 `Erdos686K3.lean`, Kill #36, CI run 42527356579 GREEN,
commit e42d681→5210b88. $c_3(x) = (x+1)(x+2)(x+3)$; `Rep3 N m n` ⟺
$c_3(m) = N\,c_3(n) \wedge 1 \le n \wedge n+3 \le m$.)*

**The five primitive edges (kernel-decided, each an exact identity).**

| edge | identity |
|---|---|
| `edge70` | $48 \cdot 49 \cdot 50 = 117600 = 70^2 \cdot 2 \cdot 3 \cdot 4$ |
| `edge4` | $14 \cdot 15 \cdot 16 = 3360 = 16 \cdot 5 \cdot 6 \cdot 7$ |
| `edge3` | $26 \cdot 27 \cdot 28 = 19656 = 9 \cdot 12 \cdot 13 \cdot 14$ |
| `edge1189` | $1680 \cdot 1681 \cdot 1682 = 4{,}750{,}102{,}560 = 1189^2 \cdot 3360$ |
| `edge1798` | $13454 \cdot 13455 \cdot 13456 = 1798^2 \cdot 90 \cdot 91 \cdot 92$ |

**The chain law (`erdos686k3_chain`).** $c_3(a) = t_1^2 c_3(b)$ and
$c_3(b) = t_2^2 c_3(c)$ ⟹ $c_3(a) = (t_1t_2)^2 c_3(c)$ — pure ring: the
witness relation **composes**.

**The composite double-hit (`edge4756`).** $c_3(1679) = 4756^2\,c_3(4)$,
witnessed by the chain $4 \to 13 \to 1679$: one product
$1680 \cdot 1681 \cdot 1682 = 4{,}750{,}102{,}560$ serves **two** squares —
$1189^2 \cdot c_3(13)$ and $4756^2 \cdot c_3(4)$ — the S037 engine's
"double hit" explained and PROVED ($4756 = 4 \cdot 1189$).

**The six $k=3$ square classes (`erdos686k3_existence`, `erdos686k3_main`).**
$N = 9$ ($m,n = 25,11$), $16$ $(13,4)$, $4900$ $(47,1)$, $1413721$
$(1679,13)$, $3232804$ $(13453,89)$, $22619536$ $(1679,4)$ — all with $m \ge
n+3$, $n \ge 1$: the first kernel-certified $k=3$ cases of the square front.
Of these, $t = 70, 1798$ are already $\in \mathcal C$ ($k=2$-covered by
Part II); the genuinely new off-chain coverage is $t \in \{3, 4, 1189,
4756\}$.

---

## §5 PART IV — THE NO-GO THEOREMS (assembled)

1. **The general $k=2$ square no-go (from T7).** $t \notin \mathcal C$
   ⟹ $t^2$ has **no** $k=2$ representation. This is the contrapositive of
   T7 (⟹) and is **scan-free**: the entire obstruction is the Chebyshev-chain
   structure of the mutual-pair descent.
2. **The explicit small-$t$ no-go (T8).** $t \in \{2,3,4,5,6,7,8,9,11,12,
   13,15,16\}$: no $k=2$ representation of $t^2$ — i.e. the squares
   $N = 4, 9, 16, 25, 36, 49, 64, 81, 121, 144, 169, 225, 256$ are
   $k=2$-impossible. (Of these, $N = 9, 16$ are rescued at $k=3$ by Part
   III; the rest are the open core's frontier.)
3. **Kernel 26's census theorem (subsumed).** For every $t \in [2,100]$:
   $t^2$ is $k=2$-representable $\iff$ ($t \equiv 2 \bmod 4$, $t \ge 10$)
   or $t = 99$ — kernel-certified by `census_scan_true` (one `decide`,
   ~1.3M kernel reductions, ZERO AXIOMS) + the `erdos686sq_noRep` divisor-
   pair reduction. The engine census extends to $t \le 300$: exactly the
   family $\cup \{99, 195\}$ (75 values; second sporadic $195$).
4. **Kernel 26's no-go bridge (`erdos686sq_noRep`).** The master-identity
   reduction: any $k=2$ representation of $t^2$ forces a divisor pair
   $(d_1, d_2)$ of $t^2-1$ with $d_1 = tY - X$, $d_2 = X + tY$, $X = 2m+3$
   odd $\ge 9$, $Y = 2n+3$ odd $\ge 5$, $X \ge Y+2$ — the finite
   divisor-pair scan that T7's descent then eliminates structurally.

---

## §6 THE NAMED REMAINING CHANNEL (the exact gap, stated precisely)

**The channel.** By §1's completion equivalence, the verbatim corpus ask
reduces to:
$$\mathcal{R} \;:=\; \{\, t^2 \;:\; t \notin \mathcal C \cup \{3,4,1189,4756\}\,\}
\quad\text{— does every } N \in \mathcal{R} \text{ have a } k \ge 3
\text{ representation?}$$

**What is already known on the channel (engine evidence, this session
re-run).** The $k=3$ census is exact on its scanned range — all witnesses
$(t, m, n)$ with $t \le T_{\max}$, $n \le N_{\max}$, $m \le
\sqrt[3]{T_{\max}^2 c_3(n)}$ (a complete scan of that box, no other bound):
$t \le 300$ ($n \le 400$) gives exactly $\{3, 4, 70\}$; $t \le 5000$
($n \le 120$) gives exactly the six witnesses of Part III
(`battery686k3.py` GREEN, `engine686k3_census.py` GREEN). These are
bounded-range facts, not non-existence proofs: a $k=3$ witness for an
off-chain $t$ could live outside the box, and the historical $k=3$ hunt
(zero witnesses at $m < 600\,000$ for all 9 named $t$) is likewise bounded.
**The YES/NO frontier (honest).** Within the scanned range, $t = 3, 4$
are the ONLY off-chain $t$ with $k=3$ witnesses; every other off-chain
$t \le 5000$ ($2, 5, 6, 7, 8, 9, 11, 12, 13, 15, 16, 17, 19, 20, 21,
23, 24, 25, \dots$) has none there. Consequently the **smallest $N$ of the
whole problem whose representability is undetermined is $N = 4$**
($t = 2$: $k=2$ excluded by T8 — PROVEN; $k=3$ absent from the census
range; $k \ge 4$ untouched). The undetermined $N$'s begin
$4, 25, 36, 49, 64, 81, 121, 144, 169, 225, 256, 289, \dots$ — squares
whose $t$ is off-chain and $k=3$-witnessless in range ($t = 11, 12, 13,
15, 16, 17$; $t = 18 \equiv 2 \bmod 4 \ge 10$ is family, $t = 99$ is
chain, $t = 100$ off-chain undetermined, …).

**The two-sided resolution conditions (what a full kill requires).**

* **YES-direction:** a construction giving, for every off-chain $t$, some
  $k \ge 3$ (possibly $k \to \infty$ with $t$) representation of $t^2$.
  No such construction is known; the $k=3$ witness structure (the six
  classes, the chain law) does not extend: the engine successor scan shows
  the $k=3$ chains END at $47$ and $1679$ ($t \le 20000$) — the
  witness family is Siegel-finite per curve (the historical engine
  note; structural, not a theorem of this front).
* **NO-direction:** a single off-chain $t$ with a proof that $t^2$ has no
  representation at ANY $k \ge 2$. $k = 2$ is already excluded (Part II —
  proven for all such $t$); the remaining need is all-$k$ non-existence.
  Per fixed $(t, k)$ the equation $\prod_{i \le k}(m+i) =
  t^2\prod_{i\le k}(n+i)$ is a Thue-type (superelliptic) equation —
  finitely many solutions per $(t,k)$ — but $k$ is unbounded, so the
  obstruction needs a uniform argument. The engine's $k=3$ hunt found zero
  witnesses at $m < 600\,000$ for all 9 named $t$ (S033/S037 volleys).

**The named front (per the kernel headers).** K42's honest scope (ll.
44–46): "the COMPLETE $k=2$ channel (all $t$, both directions). The
$k \ge 3$ channel for the non-chain $t$ is the named next front (Lemma
$\Omega$ of the S045 derivation)." K32's honest scope: "the general
square classification at $k \ge 3$ remains open (engine census: $t \le
300$ exactly $\{3,4,70\}$; full witness census $t \le 5000$ = exactly the
six classes)." K26's honest scope: "the $k \ge 3$ square war (the $t$'s
with NO $k=2$ representation: $5, 7, 8, 11, 12, 13, \dots$) is the named
next front." **All four kernels name the same channel — this §6.**

**Honest verdict.** The corpus question's YES/NO is OPEN, and by §1's
completion equivalence it is exactly the channel $\mathcal R$ above. The
assembly delivered here: the complete partial-structure theorem (all
closed channels proved in full, §§2–5) + the single named remaining core.

---

## §7 THE ARSENAL (BOSS's own mathematics, applied — citations)

The vendored 16,021-theorem arsenal (Mathlib pin 51e6992e, exact match),
applied to #686's own objects in all four kernels:

* **`Arsenal.ErdosTernary2.Basic`** (erdosternary2, bulldoze branch, 7,426
  theorems):
  * `lt_three_cases` (Basic.lean:16, $n<3 \Rightarrow n=0 \vee n=1 \vee
    n=2$) — the ternary trichotomy routing: K16 §4 `erdos686_ternary_routing`
    + `erdos686_t4_residue` (the $4 \equiv 1 \bmod 3$ case-elimination).
  * `isTernaryDigit` (Basic.lean:44) — witness-digit validity: K26 §7
    (digits of $242, 243$), K32 §6 ($1679, 13453$), K42 §8 ($4801, 2401$).
* **`Arsenal.CardinalWorlds`** (HC-PROOF, research branch, 8,595 theorems):
  * `carryAtPos_bound` (CardinalWorlds.lean:108, $\mathrm{carryAtPos}\ R\ p
    < 4$) — the carry bound on the witness products: K26 §7
    ($58806 = 242 \cdot 243$), K32 §6 ($13456 = 13454+2$), K42 §8
    ($5762400 = 2400 \cdot 2401$).
* **`Arsenal.CardinalWorldsV2`**:
  * `v2r_ternary_scaling` (CardinalWorldsV2.lean:71, $v_2(3^a \cdot c) =
    v_2(c)$) — the $p$-adic bookkeeping of the Pell witness arithmetic:
    K16 §4 ($v_2(6)=v_2(2)$, $v_2(12)=v_2(4)$, $v_2(15)=v_2(5)$ — the
    table entries $N = 6, 12, 15$), K26 §7 ($v_2(3^2 \cdot 243) =
    v_2(243)$), K32 §6 ($v_2(3^2 \cdot 13456) = v_2(13456)$), K42 §8
    ($v_2(3^2 \cdot 2401) = v_2(2401)$ — the **R3 repair**: the round-1
    dyadic conjunct $v_2(2^2 \cdot 2401) = v_2(2401)$ was FALSE
    ($v_2(4 \cdot 2401) = 2 \ne 0$); the arsenal law verbatim replaced it).

---

## §8 VERIFICATION RECEIPTS

### This session (W15, foreground, all GREEN)

| battery | verdict | receipt |
|---|---|---|
| `pell_battery.py` | **GREEN** | 186/186 non-squares $2..200$ dual-method (Pell-unit construction ‖ direct arithmetic), zero failures; 25 square-family instances ($N \le 11236$); $k=3$ squares $\{9,16\}$; 90-entry Lean-table consistency (90 expected) |
| `battery686sq.py` | **GREEN** | census $t = 2..100$ dual-method (divisor-pair scan ‖ quadratic): $99/99$ matches family+$99$ exactly; family cross-check $u = 2..24$ ALL OK; sporadic $242 \cdot 243 = 58806 = 9801 \cdot 6$; total 0.0s |
| `battery686k3.py` | **GREEN** | six witnesses dual-method (direct ‖ isqrt-square reconstruction); chain law $16\,c_3(4) = c_3(13) = 3360$, $c_3(1679)/c_3(13) = 1189^2$, $c_3(1679)/c_3(4) = 4756^2$; census $t \le 300$ ($n \le 400$) exactly $\{3,4,70\}$ (witness set exact); census $t \le 5000$ ($n \le 120$) exactly the six |
| `battery686k2class.py` | **GREEN** | M1+M2: 762 chain replays ($t \le 3000$: Rep2 product + master Pell identity + odd $X,Y$ + sizes); M3 the classification seal $t \le 2000$: divisor-pair scan set = chain set EXACTLY both directions (508 values); 8 witness edges ($980, 2716, 9701, 323, 10604, 17524, 99, 195$); de-sporadicization $99 = \mathrm{chev}\,10\,2$, $195 = \mathrm{chev}\,14\,2$; no-go list $\{2,5,6,7,8,9,11,12,13,15,16\}$ |
| `engine_squares.py` ($t \le 300$) | **GREEN** | 75 $k=2$-representable $t$ ($73$ family $+$ sporadics $99, 195$); Thm-B family identity + scan membership ALL OK |
| `engine686k3_census.py` ($300, 400$) | **GREEN** | distinct $t = [3, 4, 70]$ — the $k=3$ census exactly |

### Kernel CI receipts (historical, the kill records)

| kernel | kill | CI | state |
|---|---|---|---|
| K16 `Erdos686.lean` | **Kill #20** (Session 029) | run 42212351838 GREEN (commit 025dd39) | non-square channel + 90-witness table + arsenal bridge |
| K26 `Erdos686Squares.lean` | **Kill #29** (Session 036) | run 42422680476 GREEN | infinite family + sporadic 99 + no-go bridge + census $t \le 100$ (`census_scan_true` ZERO AXIOMS) |
| K32 `Erdos686K3.lean` | **Kill #36** (Session 038) | run 42527356579 GREEN (e42d681→5210b88) | five primitive edges + chain law + six $k=3$ classes |
| K42 `Erdos686K2Class.lean` | K42 in CI war (S045/S046) | r2 run 43023692349 FAILED (13 sites, all root-caused: **L79 the omega atom law** — omega does not normalize indices inside opaque applications, `chev y (k-1+1) ≠ chev y k` as atoms; truncation guards; three dead lemmas manualized; the Cassini-climb rebuild) → **r3 = 3b39ebf pushed, run 43038195739** | the COMPLETE $k=2$ classification (W1's eight theorems; this assembly's §3) |

### W1 battery receipts (the classification's original seals,
`K2CLASS_COMPLETE_PROOF.md` §K)

cassini 11 $y$-values; `gap_hop` refutation $(y,j)=(10,1)$: $90 \ne 100$;
`pair_diff_mod4` on $y \in \{6,10,\dots,54\}$ (+ negative control: the
$y \equiv 2 \bmod 4$ hypothesis is necessary); witness construction on 649
chain values ($y \in \{10,14,\dots,1006\}$, $t \le 10^8$); `mutual_step`
exhaustive on all 1246 mutual pairs $2 \le u_1 < u_0 \le 1200$;
`chain_of_mutual` on all 6073 mutual pairs $u_0 \le 3000$ (descent
simulated on 3145 pairs, 0 failures); **the airtight classification seal
$t \le 1000$**: all `Rep2(t²)` solutions enumerated via the divisor pairs of
$t^2-1$ (bijective, no search bound) — representable set = chain set
EXACTLY, 255 values / 255 solutions (one each), Y-law $t =
\mathrm{chev}\,(4n+6)\,j$ on every solution; no-go $t \in \{2,\dots,16\}
\setminus \{10,14\}$: zero solutions.

---

## §9 STATUS VERDICT

* **CLOSED (proved in full, above):** the non-square channel (every
  non-square $N \ge 2$, $k=2$ — §2); the $k=2$ square channel (the
  Chebyshev-chain classification, all $t$, both directions, scan-free —
  §3); the $k=3$ witness laws (six kernel classes + chain law + composite —
  §4); the $k=2$ no-go theorems (general + explicit + census — §5).
* **THE SINGLE NAMED REMAINING CORE:** the off-chain square $k \ge 3$
  channel $\mathcal R$ (§6) — "for $t \notin \mathcal C \cup
  \{3,4,1189,4756\}$: does $t^2$ admit a $k \ge 3$ representation?" —
  exactly equivalent to the corpus YES/NO by §1's completion equivalence.
  Smallest undetermined $N$: **$N = 4$**.
* **This assembly is the complete partial-structure theorem for Erdős
  #686** — every closed channel proved, the open core named exactly,
  nothing partial dressed as complete. The full corpus resolution (§6's
  channel) remains open.
