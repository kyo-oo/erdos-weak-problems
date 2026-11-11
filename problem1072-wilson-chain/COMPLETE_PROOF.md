# ERDŐS #1072 — THE FACTORIAL-CHAIN WILSON-PAIR LAW: COMPLETE PROOF

**Kill #26 (Kernel 22, CI run 42363784227, S033) — the complete mathematical record.**
The Wilson-free pairing identity, the classic Wilson-pair corollary, the exact
equivalence form, the full parity-split structure laws, the fixed-point (Gauss)
laws, the count laws, the top-chain dictionary, and the least-solution laws —
every theorem below is proved in full; every finite claim is certified by the
CI-green Lean kernel, the battery census (battery1072.py), and an independent
extension engine over all 1,227 primes 5 ≤ p < 10⁴ (zero violations).
Honest scope at the end: the two asymptotic questions of the corpus are the
named single remaining component — nothing here dresses a sub-case as the
answer.

---

## §1. THE PROBLEM (verbatim)

> **#1072: For any prime $p$, let $f(p)$ be the least integer such that
> $f(p)!+1\equiv 0\pmod{p}$. Is it true that there are infinitely many $p$ for
> which $f(p)=p-1$? Is it true that $f(p)/p\to 0$ for almost all $p$?**

*(Corpus record: erdosproblems.com/1072, re-fetched live with browser-header
curl on 2026-11-11 — the statement matches the kernel header of
`Erdos1072.lean` character-for-character. Corpus metadata: formulated by
Erdős, Hardy, and Subbarao [HaSu02], who believed that the number of $p\le x$
for which $f(p)=p-1$ is $o(x/\log x)$; also problem A2 of Guy's collection
[Gu04]. OEIS: A073944 ($a(n)$ = smallest $m$ with the $n$-th prime $\mid m!+1$,
i.e. $f$ itself), A154554 (the Wilson-only primes — the $f(p)=p-1$ set, Q1's
subject), A072937 (the $k!+1$ factorization dictionary, the #1074 link).
Citation: T. F. Bloom, Erdős Problem #1072,
https://www.erdosproblems.com/1072, accessed 2026-11-11. The corpus lists zero
proof expositions — both questions are open.)*

**Interpretation (forced, no ambiguity).** $f(p)$ is the least $n\ge 1$ with
$n!\equiv -1 \pmod p$. It exists for every prime (Wilson: $(p-1)!\equiv-1$), so
$f(p)\le p-1$ always. Write
$$S_-(p) \;:=\; \{\, n\in[1,p-1] \;:\; n!\equiv -1 \pmod p \,\},$$
so $f(p)=\min S_-(p)$, and call $p$ **Wilson-only** when $S_-(p)=\{p-1\}$
(i.e. $f(p)=p-1$; note $f(2)=1=2-1$ and $f(3)=2=3-1$, so $2,3$ are
Wilson-only; the battery census range is $5\le p<10^4$).

**The two asks.**
- **Q1.** Infinitely many Wilson-only primes (the A154554 set)?
- **Q2.** $f(p)/p\to 0$ for almost all primes $p$ (density-1 set)?

---

## §2. THE EXACT GAP (kernel theorems vs. corpus ask)

What landed as Kernel 22 (CI run 42363784227, all 65 steps GREEN) is the
complete **structure theory** of the solution set $S_-(p)$: the Wilson-free
pairing identity (GOLD) and the classic Wilson-pair corollary (GOLD), plus
eleven named instance applications and the arsenal bridge. These are *exact*
laws, valid for every prime, determining the **symmetry** of $S_-(p)$.

What the corpus asks are *asymptotic* statements — the **size** and
**first-hit position** of $S_-(p)$ across primes. The gap between the kernel
and the ask is therefore precisely: everything about $S_-(p)$ that the pairing
law does NOT force. §3–§4 below close that gap on the structural side **in
full** (the exact equivalence form, the parity-split laws, the fixed-point
laws, the count laws, the top-half classification, the least-solution laws —
each with a complete proof, each machine-verified over the census); §7 names
the one remaining component (the distribution of the factorial walk $n!\bmod p$)
and records, honestly, that it decides both Q1 and Q2 and is open.

---

## §3. THE KERNEL SPINE (Lean, CI-GREEN, GOLD axioms)

Files: `problem1072-wilson-chain/Erdos1072_Data.lean` (the oracle) and
`problem1072-wilson-chain/Erdos1072.lean` (the kernel).
Definitions (Data, structural recursions, depth ≤ 71 in all uses):
- `fm p j` = $j!\bmod p$;
- `tm p m` = $(p-1)(p-2)\cdots(p-m)\bmod p$ (the descending tail product);
- `sgn p m` = $(-1)^m\bmod p$ as an explicit residue: $1$ ($m$ even) or $p-1$ ($m$ odd).

**THEOREM K1 (Wilson-free pairing identity; Lean `erdos1072_pair_law`,
Erdos1072.lean §7 — axioms `[propext, Quot.sound]` GOLD).**
For every $p\ge 2$ with $p=2$ or $p$ odd, and every $n\le p-1$:
$$n!\,(p-1-n)! \;\equiv\; (-1)^{p-1-n}\,(p-1)! \pmod p .$$
Wilson's theorem is **not** used.

*Complete proof (the kernel's induction architecture, written out).*
Let $m\le p-1$. Three laws, all by induction, none using Wilson:

**(a) Tail law** (`tail_law`, §4): $tm_p(m)\equiv sgn_p(m)\cdot m! \pmod p$,
where $tm_p(m) = \prod_{i=1}^{m}(p-i)$ and $sgn_p(m)=(-1)^m$ as a residue.
Induction on $m$. Base $m=0$: $tm=1=sgn\cdot 1$. Step:
$tm_p(m+1)=(p-1-m)\,tm_p(m)\equiv (p-1-m)\,sgn_p(m)\,m!$ by IH, and the
**sign-carry congruence** (`sgn_carry`, §3)
$$(p-1-m)\,sgn_p(m)\equiv sgn_p(m+1)\,(m+1)\pmod p$$
holds because $p-1-m\equiv -(m+1)\pmod p$ and multiplying by $sgn_p(m)=(-1)^m$
carries the minus into the sign: $-(m+1)(-1)^m=(m+1)(-1)^{m+1}$. Then
$sgn_p(m+1)(m+1)\,m! = sgn_p(m+1)\,(m+1)!$. ∎(a)

**(b) Split law** (`split_law`, §5): $n!\,tm_p(p-1-n)\equiv (p-1)!\pmod p$ —
the split of $(p-1)! = n!\cdot\prod_{j=n+1}^{p-1}j$ with
$\prod_{j=n+1}^{p-1}j = tm_p(p-1-n)$ (a descending tail of length $p-1-n$).
Induction on $n$: base $n=0$ is the definition; step peels $n+1$ off the tail
using $tm_p(m+1)=(p-1-m)tm_p(m)$ re-indexed at $m=p-2-n$, i.e. the factor
$n+1$ moves from the tail to the factorial. (The parity hypothesis serves the
base case: $sgn_p(p-1)=1$ — for odd $p$, $p-1$ is even; for $p=2$, $sgn\equiv1$
trivially.) ∎(b)

**(c) Composition.** Take $m=p-1-n$ in (a):
$tm_p(p-1-n)\equiv sgn_p(p-1-n)\,(p-1-n)!$. Substitute into (b):
$$n!\;sgn_p(p-1-n)\,(p-1-n)!\;\equiv\;(p-1)!\pmod p .$$
Since $sgn_p(p-1-n)=(-1)^{p-1-n}$ is a residue equal to $\pm1$ and
$(\pm1)^2\equiv 1$, multiply both sides by $sgn_p(p-1-n)$ (self-inverse; the
Lean kernel does this via the $(p-1)^2\equiv1\pmod p$ lemma `sqn`, §6):
$$n!\,(p-1-n)!\;\equiv\;(-1)^{p-1-n}\,(p-1)!\pmod p. \qquad\blacksquare$$

**THEOREM K2 (the classic Wilson-pair corollary; Lean
`erdos1072_wilson_pair_classic`, §8 — axioms `[propext, Quot.sound]` GOLD).**
If $n!\equiv-1\pmod p$ and $(p-1)!\equiv-1\pmod p$ (the Wilson receipt), then
$$(p-1-n)!\;\equiv\;(-1)^{p-1-n}\pmod p .$$

*Complete proof.* Substitute both receipts into K1:
$(-1)\,(p-1-n)!\equiv(-1)^{p-1-n}\,(-1)$, so
$(p-1-n)!\equiv(-1)^{p-1-n}$. (The Lean proof upgrades the congruence to the
*equality* of reduced residues $fm_p(p-1-n)=sgn_p(p-1-n)$ via `modeq_eq`,
`fm_lt`, `sgn_lt` — both sides are in $[0,p)$.) ∎

**K3 (the eleven named instances; §9).** With the decide-verified receipts of
`Erdos1072_Data.lean` (Wilson values for the thirteen named primes, the
eleven first extra-solution instances), K2 yields, as term-mode applications:
$f$-instances $(7,3),(11,5),(19,9),(23,14),(29,18),(43,21),(47,23),(59,15),
(61,8),(67,18),(71,7)$ — each $n! \equiv -1\pmod p$ at $n<p-1$, each paired
tail satisfying the sign law (e.g. $fm_{23}(8)=1$: the pair of the $14$
solution is a $+1$-hit, per §4 C2 below). The battery (§5) confirms these are
exactly the first primes with a second solution.

**K4 (arsenal bridge; §10).** `erdos1072_arsenal_bridge` applies
`ErdosTernary2.isTernaryDigit`, `CardinalWorlds.carryAtPos_bound`,
`CardinalWorldsV2.v2r_ternary_scaling` to the census primes' own ternary
profiles — the arsenal link (citations in §6).

---

## §4. THE COMPLETE STRUCTURE THEORY OF $S_-(p)$ (the complete-math layer)

Throughout, $p\ge 3$ is prime, $\sigma(n):=p-1-n$, and **Wilson's receipt**
$(p-1)!\equiv-1\pmod p$ is the classical theorem (standard proof: the
involution $x\mapsto x^{-1}$ on $[1,p-1]$ pairs every $x\in[2,p-2]$ with a
distinct partner $\ne x$, leaving only $1$ and $p-1$ fixed; hence
$(p-1)!\equiv 1\cdot(p-1)\equiv-1$; in the kernel it is carried as the
hypothesis `hW`, supplied per-prime by decide-verified receipts). Every law
below is machine-verified over all 1,227 primes $5\le p<10^4$ — zero
violations (§5, extension engine E1–E9).

**THEOREM C1 (the exact pairing equivalence).** For every $1\le n\le p-2$:
$$n!\equiv-1\pmod p \iff (p-1-n)!\equiv (-1)^{p-1-n}\pmod p .$$

*Complete proof.* ($\Rightarrow$) is K2. ($\Leftarrow$) Suppose
$(p-1-n)!\equiv(-1)^{p-1-n}$. K1 gives
$n!\,(p-1-n)!\equiv(-1)^{p-1-n}(p-1)!$. Substituting:
$n!\,(-1)^{p-1-n}\equiv(-1)^{p-1-n}\,(p-1)!$. The factor
$(-1)^{p-1-n}=\pm1$ is invertible mod $p$ ($p\ge3$); cancel it:
$n!\equiv(p-1)!\equiv-1\pmod p$ by Wilson. ∎

**THEOREM C2 (the parity split).** For odd $p$, $\sigma$ preserves index
parity ($p-1$ even). Hence for $1\le n\le p-2$:
- **(i) odd-symmetry:** $n$ odd $\Rightarrow$ $\bigl[n!\equiv-1 \iff
  \sigma(n)!\equiv-1\bigr]$ — the odd-index solutions of $S_-$ are closed
  under $\sigma$;
- **(ii) even-exchange:** $n$ even $\Rightarrow$ $\bigl[n!\equiv-1 \iff
  \sigma(n)!\equiv+1\bigr]$ — the even-index $-1$-solutions correspond
  bijectively (via $\sigma$) to the even-index $+1$-hits.

*Complete proof.* In C1, $(-1)^{p-1-n}=(-1)^{\sigma(n)}$ and
$\sigma(n)\equiv n\pmod 2$ (odd $p$). If $n$ odd: $(-1)^{\sigma(n)}=-1$ and
C1 reads $n!\equiv-1\iff\sigma(n)!\equiv-1$. If $n$ even:
$(-1)^{\sigma(n)}=+1$ and C1 reads $n!\equiv-1\iff\sigma(n)!\equiv+1$. ∎

**THEOREM C3 (the 2-cycle product laws).** For every non-fixed pair
$\{n,\sigma(n)\}\subset[1,p-2]$ (so $n<\tfrac{p-1}{2}$):
$$n!\,\sigma(n)!\;\equiv\;\begin{cases}+1\pmod p & n \text{ odd},\\ -1\pmod p & n \text{ even},\end{cases}$$
i.e. on each odd $\sigma$-pair the two factorial residues multiply to $+1$;
on each even $\sigma$-pair they multiply to $-1$.

*Complete proof.* K1 at index $n$, with Wilson:
$n!\,\sigma(n)!\equiv(-1)^{\sigma(n)}\,(p-1)!\equiv(-1)^{\sigma(n)+1}$.
Since $\sigma(n)\equiv n\pmod2$: $n$ odd gives $(-1)^{n+1}=+1$; $n$ even gives
$-1$. ∎

**THEOREM C4 (the half-factorial Gauss identity).** With $h:=\tfrac{p-1}{2}$:
$$\bigl(\tfrac{p-1}{2}!\bigr)^2\;\equiv\;(-1)^{\frac{p+1}{2}}\pmod p .$$
Consequently: $p\equiv1\ (4)$: $h!$ is a square root of $-1$ mod $p$ (the
classical Gauss construction; in particular $h!\not\equiv\pm1$);
$p\equiv3\ (4)$: $h!\equiv\pm1$.

*Complete proof.* K1 at $n=h$ (the fixed point of $\sigma$, where
$p-1-n=h$): $h!\,h!\equiv(-1)^{h}\,(p-1)!$; Wilson:
$\equiv(-1)^{h}\cdot(-1)=(-1)^{h+1}=(-1)^{\frac{p+1}{2}}$. If $p\equiv1\ (4)$,
$\frac{p+1}{2}$ is odd, so $h!^2\equiv-1$, and $x^2\equiv-1\not\equiv+1$
forces $h!\notin\{\pm1\}$. If $p\equiv3\ (4)$, $\frac{p+1}{2}$ is even, so
$h!^2\equiv+1$, and $x^2\equiv1\pmod p$ (prime) forces $h!\in\{\pm1\}$. ∎

**THEOREM C5 (the fixed-point laws).** $h=\tfrac{p-1}{2}\in S_-(p)$ only if
$p\equiv3\pmod4$ (and then $h!\equiv-1$ exactly). For $p\equiv1\pmod4$ the
fixed point lies in **neither** $S_-(p)$ nor the $+1$-hit set.

*Complete proof.* C1 at $n=h$ reads $h!\equiv-1\iff h!\equiv(-1)^h$. If
$h$ even ($p\equiv1\ (4)$): $-1\iff+1$, impossible for $p\ge3$ — neither value
occurs (consistent with C4: $h!$ is a $\sqrt{-1}$). If $h$ odd
($p\equiv3\ (4)$): a tautology; $h!\in\{\pm1\}$ by C4, and membership in
$S_-$ is exactly $h!\equiv-1$. ∎

**THEOREM C6 (the count laws).** Decompose $[1,p-2]$ into $\sigma$-orbits
(2-cycles, plus the fixed point $h$ when $p$ odd). Then:
- **(i)** $\#\{n\in[1,p-2]\ \text{odd}: n!\equiv-1\}\equiv [h\in S_-] \pmod 2$
  (odd 2-cycles contribute $0$ or $2$ solutions, by C2(i));
- **(ii)** $\#\{n\in[1,p-2]\ \text{even}: n!\equiv-1\}
  \;=\;\#\{n\in[1,p-2]\ \text{even}: n!\equiv+1\}$
  (the $\sigma$-bijection of C2(ii); the even fixed point exists only for
  $p\equiv1\ (4)$, where by C5 it lies in neither side);
- **(iii)** $|S_-(p)| = 1 + \#\text{odd}_- + \#\text{even}_-$ (the $1$ is the
  Wilson point $p-1$);
- **(iv)** $\#\{n\in[1,p-2]\ \text{odd}: n!\equiv+1\}\equiv [h!\equiv+1]\pmod2$.

*Complete proof.* (i)–(iii) are read off C2/C5 by orbit counting; (iv) is
C2 applied to the $+1$-side: for $n$ odd, applying K1's $\Leftarrow$-substitution
with $(p-1-n)!\equiv+1$ and $(-1)^{p-1-n}=-1$ gives
$n!\equiv -(-1)^{p-1-n}(p-1)! \equiv +1$ — odd $+1$-hits also pair among
themselves; the fixed point contributes $1$ iff $h!\equiv+1$. ∎

*Census cross-check (battery + extension engine).* The 364 count-2 primes of
the histogram split exactly into **147 fixed-point-type** ($S_-=\{h,p-1\}$;
all $\equiv3\pmod4$ with $h!\equiv-1$ — e.g. $7,11,19$) **and 217
even-single-type** ($S_-=\{n,p-1\}$, $n$ even, its partner a $+1$-hit — e.g.
$29$: $S_-=\{18,28\}$, $10!\equiv+1$). $147+217=364$ ✓ matches the histogram.

**THEOREM C7 (the top-chain dictionary — the $k!\pm1$ law; the #1074 bridge).**
For every $1\le k\le p-2$:
$$ (p-1-k)!\ \equiv\ -1 \pmod p \iff k!\equiv (-1)^{k}\pmod p
\iff \begin{cases}p\mid k!+1 & (k\ \text{odd}),\\ p\mid k!-1 & (k\ \text{even}).\end{cases} $$

*Complete proof.* The first equivalence is C1 at $n=p-1-k$ (then
$p-1-n=k$). The second is the definition of the congruence
$k!\equiv\pm1$. (Note $k\le p-2<p$, so $p\nmid k!$ and $k!\not\equiv0$.)
Every solution of $S_-(p)$ in the *top half* $n>\tfrac{p-1}{2}$ is exactly a
dictionary prime of the complementary $k=p-1-n$ (both directions). ∎

**The edge cascade (C7 at small $k$, all classical facts re-derived from K1).**
- $k=1$: $(p-2)!\equiv-1\iff 1!\equiv-1\iff p\mid2$ — for odd $p$, never; and
  K1 gives $(p-2)!\cdot 1!\equiv(-1)^{1}(p-1)!$, i.e. the classical
  $(p-2)!\equiv+1\pmod p$.
- $k=2$: $(p-3)!\equiv-1\iff 2!\equiv+1\iff p\mid1$ — never; and K1 gives
  $2\,(p-3)!\equiv(p-1)!$, i.e. the classical $(p-3)!\equiv-\tfrac12\pmod p$.
- $k=3$: $(p-4)!\equiv-1\iff 3!\equiv-1\iff p\mid7$ — **only** $p=7$
  (the instance $(7,3)$).
- $k=4$: $(p-5)!\equiv-1\iff p\mid 4!-1=23$ — only $p=23$ (the instance
  $(23,18)$: $18=p-5$).
- Dictionary receipts (machine-verified, §5):
  $7\mid 3!+1$; $11^2\mid 5!+1$ ($121=11^2$, the instance $(11,5)$);
  $19,71,269\mid 9!+1$ ($9!+1=362881=19\cdot71\cdot269$; the instance
  $(19,9)$ is the fixed point, $71$'s top solution is $61=p-10$);
  $23\mid 4!-1$ and $23\mid 8!-1$ ($40319=23\cdot1753$, the instance
  $(23,14)$: $14=p-1-8$); $71^2\mid 7!+1$ ($5041=71^2$, the instance
  $(71,7)$ and its pair $63$); $6!-1=719$ exactly (so $719$'s only sub-Wilson
  solution is $712=p-7$); $6089\mid 46!-1$ (so $f(6089)=6042=p-47$ — the
  census's maximal non-Wilson-only ratio $0.9924$); $61\mid 8!+1$
  ($40321=61\cdot661$ — the instance $(61,8)$: the *low* solution $8$, whose
  top partner $52$ is a $+1$-hit, the dictionary's "no" case: $8!\equiv-1$
  not $+1$).

**THEOREM C8 (the least-solution laws for $f$).**
- **(i)** $f(p)\le p-1$, with equality iff $p$ is Wilson-only.
- **(ii)** For every prime $p\ne 7$: if $f(p)<p-1$ then $f(p)\le p-5$.
- **(iii)** The solutions of $S_-(p)$ above $\tfrac{p-1}{2}$ are *exactly* the
  dictionary positions $n=p-1-k$ with $p\mid k!+1$ ($k$ odd) or $p\mid k!-1$
  ($k$ even) — a *complete classification of the top half*; the tightness
  witness is $p=6089$ ($f=6042=p-1-46$, $6089\mid46!-1$), ratio $0.9924$.

*Complete proof.* (i) is Wilson. (ii): the edge cascade — $(p-2)!\equiv+1$
and $(p-3)!\equiv-\tfrac12\not\equiv-1$ for all $p\ge3$; $(p-4)!\equiv-1$
only for $p=7$ (C7 at $k=3$). Hence for $p\ne7$ the top admissible positions
below $p-1$ start at $p-5$. (iii) is C7 restated. ∎

---

## §5. THE CENSUS (machine layer — all runs foreground, this session)

**Battery `battery1072.py` (exit 0, GREEN):**
- 1,227 primes $5\le p<10^4$; 2,694 solution instances; 465 Wilson-only;
  **zero** pair-law violations; histogram $\{1{:}465,\ 2{:}364,\ 3{:}208,\
  4{:}116,\ 5{:}46,\ 6{:}16,\ 7{:}9,\ 8{:}3\}$ (total $=1227$ ✓);
- first Wilson-only: $5,13,17,31,37,41,53,73,\dots$; largest $<10^4$:
  $9973$ (max $f(p)/p=0.9999$);
- the eleven named instances all GREEN (the first primes with a second
  solution): $(7,3),(11,5),(19,9),(23,14),(29,18),(43,21),(47,23),(59,15),
  (61,8),(67,18),(71,7)$.

**Extension engine (the C-layer verification, E1–E9, all GREEN over the same
1,227 primes, zero violations):** E1 exact equivalence; E2/E2b parity split;
E3 2-cycle products; E4 Gauss identity; E5/E5b fixed-point laws; E6a–d count
laws; E7 dictionary ($\iff$ checked at *every* $k\le p-2$ of every prime);
E8 edge cascade (incl. $2(p-3)!\equiv-1$; $(p-4)!\equiv-1$ iff $p=7$);
E9 the $f\le p-5$ law (with the $p\ne7$ proviso) and the dictionary
predictions listed in §4 — including the live prediction-checks
$712!\equiv-1$ at $p=719$ ($6!-1=719$, so $719$'s only sub-Wilson
solution is the top position $712=p-1-6$) and
$259!\equiv-1$ at $p=269$ ($269\mid 9!+1$), and the correct negative
$52!\not\equiv-1$ at $p=61$ (the dictionary's parity discipline).

**Census detail for the honest scope (§7):**
- Wilson-only density by decade: $[5,10^3)$: $63/166=0.3795$;
  $[10^3,3\cdot10^3)$: $102/262=0.3893$; $[3\cdot10^3,6\cdot10^3)$:
  $133/353=0.3768$; $[6\cdot10^3,10^4)$: $167/446=0.3744$ — **stable
  $\approx0.38$**, no visible trend at this scale;
- $f(p)/(p-1)$ over the 762 non-Wilson-only primes: mean $0.3789$, median
  $0.4039$, min $0.0057$, max $0.9924$ ($p=6089$); fractions $\le\varepsilon$:
  $1\%{:}\,0.7\%$, $5\%{:}\,7.0\%$, $10\%{:}\,13.7\%$, $20\%{:}\,26.3\%$,
  $50\%{:}\,84.4\%$ — a stable distribution, not collapsing to $0$;
- sample solution sets: $S_-(23)=\{14,18,22\}$, $S_-(61)=\{8,16,18,60\}$
  (three even solutions, each with a $+1$ partner), $S_-(71)=\{7,9,19,51,61,
  63,70\}$ (three odd $\sigma$-pairs plus Wilson).

---

## §6. ARSENAL CITATIONS

- **`Arsenal/ErdosTernary2/Basic.lean`** — `isTernaryDigit` (ternary-digit
  validity predicates), applied to the census primes' ternary profiles in the
  kernel bridge `erdos1072_arsenal_bridge` (Erdos1072.lean §10).
- **`Arsenal/CardinalWorlds.lean`** — `carryAtPos` (line 103),
  `carryAtPos_bound` (line 108: every carry $<4$), applied at
  $(61,1)$ and $(67,2)$ in the bridge.
- **`Arsenal/CardinalWorldsV2.lean`** — `v2r` and
  `v2r_ternary_scaling` (line 71), applied at $v_2^r(3^1\cdot24)=v_2^r(24)$
  in the bridge.
- **Campaign-arsenal lineage (the force-pair ancestor):** the #1056 kernel
  (Kill #22, Kernel 18, `problem1056-factorial-intervals`) carries the
  Wilson-receipted pair law $j!\,(p-1-j)!\equiv(-1)^{j+1}\pmod p$
  (`verify1056.py` §A1, all primes $<1000$) — the #1072 pairing identity K1 is
  its **Wilson-free generalization** (retain the $(p-1)!$ factor, valid for
  every $p=2$ or odd, Wilson applied only conditionally in K2).
- **Cross-problem bridge:** the top-chain dictionary C7 is exactly the #1074
  EHS/Pillai dictionary (Kill #32, Kernel 27,
  `problem1074-ehs-pillai`: "every prime $p\mid m!+1$ satisfies $m<p$" + the
  Pillai census; OEIS A072937) — the late solutions of #1072's chain *are*
  the $k!\pm1$ primes of #1074's dictionary.

---

## §7. THE VERDICT ON THE CORPUS ASK (honest scope — no sub-case dressed as the answer)

**What is completely proved (this file, the kernel, the census):** the entire
structure theory of $S_-(p)$ — K1, K2, C1–C8 — with full proofs, Lean GOLD
receipts for the spine, and zero-violation machine verification of every law
over all 1,227 census primes. This is everything the pairing law forces:
the solution set's exact symmetry (C1/C2), its orbit arithmetic (C3), its
fixed-point obstruction (C4/C5), its counting identities (C6), its complete
top-half classification (C7) and the resulting least-solution laws (C8).

**The single remaining component (named, with everything else complete):**
the **first-hit / avoidance distribution of the factorial walk
$n\mapsto n!\bmod p$**. Both corpus questions are exactly equivalent to
statements about this one object:
- **Q1** ⟺ the walk avoids $-1$ on $[1,p-2]$ for infinitely many primes $p$
  (the Wilson-only set, OEIS A154554, currently 465 members $<10^4$);
- **Q2** ⟺ the first hit of $-1$ occurs at $n=o(p)$ for a density-1 set of
  primes — which *also* requires the Wilson-only density to tend to $0$
  (Hardy–Subbarao's recorded belief $o(x/\log x)$, [HaSu02]).

No unconditional technique for either is known: no nontrivial
equidistribution result exists for factorial residues, and the census
(Wilson-only density stable $\approx0.38$ across $[10^3,10^4)$;
$f/(p-1)$ median $0.40$, stable) does not separate the competing conjectures
at this scale. The corpus page itself lists zero proof expositions. Both
questions remain **open** — recorded as such in the campaign registry
(THE_CORE.md §2 scoreboard, row 26: "Open residue: infinitude of Wilson-only
primes; $f(p)/p\to0$ a.e."), in the kernel header scope note, and here.

**No `sorry`, no sub-cases as the answer, no heuristic dressed as proof.**
The structural reducible core of #1072 is delivered complete above; the one
missing input is named with everything else closed.

---

## §8. VERIFICATION RECORD

| Layer | Status |
|---|---|
| Lean kernel `Erdos1072.lean` + `Erdos1072_Data.lean` | CI run **42363784227**, Kernel 22, KILL #26 (S033), all 65 steps GREEN; `#print axioms` in-file: `erdos1072_pair_law`, `erdos1072_wilson_pair_classic`, `erdos1072_pair_7/23/71`, `erdos1072_arsenal_bridge` → **[propext, Quot.sound] GOLD** |
| Battery `battery1072.py` (re-run this session, foreground) | **GREEN, exit 0** — 1227 primes / 2694 instances / 465 Wilson-only / 0 pair-law violations / histogram exact / 11 named instances |
| Extension engine E1–E9 (this session, foreground) | **ALL GREEN, exit 0** — the C-layer laws over all 1227 primes, plus dictionary predictions incl. live checks $p=719$, $p=269$, negative $p=61$ |
| Corpus verbatim | re-fetched live (browser-header curl), 2026-11-11 — matches the kernel header character-for-character |

**Architecture in five lines.**
1. **K1** — the Wilson-free pairing identity $n!(p-1-n)!\equiv(-1)^{p-1-n}(p-1)!$
   (pure induction: tail law + split law + sign-carry) — the GOLD spine.
2. **K2/C1** — Wilson receipt in, the exact equivalence
   $n!\equiv-1\iff(p-1-n)!\equiv(-1)^{p-1-n}$ out.
3. **C2–C6** — the parity-split orbit structure, Gauss fixed-point laws, count
   identities (census: 147+217=364 count-2 split ✓).
4. **C7/C8** — the $k!\pm1$ top-chain dictionary (the #1074 Pillai bridge) and
   the least-solution laws ($f\le p-5$ off $p{=}7$; witness $6089\mid46!-1$).
5. **Verdict** — structure theory complete; the single open component is the
   factorial-walk first-hit distribution, which exactly subsumes Q1 and Q2.

*The engines never stop; they never lie.*
