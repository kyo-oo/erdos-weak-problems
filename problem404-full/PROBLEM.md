# ERDŐS #404 — THE FULL PROBLEM: p-ADIC FACTORIAL-SUM CLASSIFICATION

## THE UNSOLVED PROBLEM (verbatim, erdosproblems.com/404, accessed 2026-11-02)

> For which integers $a \geq 1$ and primes $p$ is there a finite upper bound on
> those $k$ such that there are $a = a_1 < \cdots < a_n$ with
> $p^k \mid (a_1! + \cdots + a_n!)$?
> If $f(a,p)$ is the greatest such $k$, how does this function behave?
> Is there a prime $p$ and an infinite sequence $a_1 < a_2 < \cdots$ such that
> if $p^{m_k}$ is the highest power of $p$ dividing $\sum_{i \leq k} a_i!$
> then $m_k \to \infty$?

Status: OPEN (site page, last edited 2025-12-01; tags: number theory, factorials).

## WHAT THIS PACKAGE DELIVERS (this round)

1. **THEOREM A — the p-adic reduction** (Lean kernel-green): every sum factors as
   $a! + \sum_{i \in B} i! = a! \cdot (1 + \sum_{i \in B} P_i)$ with $P_i = (a+1)(a+2)\cdots i$,
   so $f(a,p) = v_p(a!) + g(a,p)$ where $g$ is the max depth at which $-1$ is a
   subset sum of the $P$-staircase mod $p^k$; bounded-ness is decided by the first
   obstruction level; $g = \infty \iff$ an exact $\mathbb{Z}_p$ zero-sum
   $\sum_{i \in Z} i! = 0$ exists, and then the infinite chain of sub-question 3
   EXISTS (its elements are $Z$'s sorted elements; the partial-sum valuations
   tend to infinity automatically). [Full proof in DERIVATION.tex; the finite
   split theorem + the chain's finite witnesses in the Lean kernel.]

2. **THEOREM B — the $p \mid (a{+}1)$ class completely solved** (Lean kernel-green):
   if $p \mid a+1$ then $f(a,p) = v_p(a!)$ exactly. Every sum
   $a! + \sum_B i! \equiv a! \pmod{p^{v_p(a!)+1}}$'s unit part is fixed.

3. **THEOREM C — $f(4,2) = 6$ exactly** (Lean kernel-green): the witness
   $4! + 5! + 7! = 5184 = 2^6 \cdot 81$, and the mod-16 obstruction
   (all eight sub-sums of $\{P_5, P_6, P_7\} = \{5, 30, 210\}$ miss $-1$:
   reachable residues $\{1, 3, 4, 6, 8, 15\} \pmod {16}$, none $\equiv 0$;
   all later $P_i \equiv 0 \bmod 16$).

4. **THE BLOCK-IDENTITY STRUCTURE THEORY** (Lean kernel-green): the consecutive
   factorial blocks factor exactly:
   $[u, u{+}1] = u!\,(u{+}2)$, $\;[u, u{+}2] = u!\,(u{+}2)^2$,
   $\;[u, u{+}3] = u!\,(u{+}2)(u^2 + 5u + 5)$.
   (The pair law $v_2[u,u+1] = v_2(u!) + v_2(u+2)$ IS the Kill-#4 kernel law.)

5. **THE COMPUTATIONAL CLASSIFICATION** (exact integer engines, this package):
   the full $g$-table for $a \leq 40$, primes $p \leq 61$; all bounded entries
   certified by complete DP obstruction; the unbounded candidates
   $(2,2), (6,2)$ verified obstruction-free to depth $2^{28}$ (28 consecutive
   p-adic levels); the nested explicit chain for $(2,2)$ to level 22 (every
   level's witness list recorded and verified by exact big-integer arithmetic).

6. **CONJECTURE D** (labeled as conjecture, with the evidence): $g(2,2) = \infty$
   and $g(6,2) = \infty$; if true, sub-question 3 is answered **YES** (the
   infinite chain exists, e.g. starting $2, 3, 5, 6, 7, 8, 9, 11, \ldots$).
   The proof frontier: the gadget-lift lemma (each p-adic level needs an
   exact-valuation-$k$ subset of fresh terms; the gap levels $k \in \{5, 6, 9,
   12, 13, 14, \ldots\}$ require non-block subsets — the zoo data in
   `zoo.py`/`gadget_plan.json` maps the supply).

## Files
- `PadicReduction.lean` — the Lean 4 kernel (core-only, zero sorry, zero custom axioms).
- `DERIVATION.tex` — the complete human mathematics (Theorems A/B/C, the
  classification, the structure theory, the conjecture and its frontier).
- `classifier.py` — the subset-sum DP classifier (`scan`, `deep`, `witness`, `verify-bounded`).
- `nested.py` — the nested witness extractor (the König chain).
- `zoo.py` + `gadget_plan.json` — the gadget-supply census.
- `coverage.py` — the block-valuation coverage analysis.
- `verify_404.py` — the verification battery (all receipts re-checked, exact integers only).

## Prior art
The problem is stated in Erdős–Graham 1980 (see site refs). The p=2 tail law
(Kill #4 of this campaign, `problem404-padic-kernel/KernelLaw.lean`) is the
special case of the full-tail subset; the present package supersedes it toward
the complete classification.
