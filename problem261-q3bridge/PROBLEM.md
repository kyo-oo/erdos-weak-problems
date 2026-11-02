# ERDŐS #261 — THE RATIONAL-x BRIDGE (sub-question 3 reduction)

## THE UNSOLVED PROBLEM (verbatim, erdosproblems.com/261)

> Are there infinitely many $n$ such that there exists some $t \geq 2$ and
> distinct integers $a_1, \ldots, a_t \geq 1$ such that
> $\frac{n}{2^n} = \sum_{k=1}^{t} \frac{a_k}{2^{a_k}}$?
> Is this true for all $n$? Is there a rational $x$ such that
> $x = \sum_{k=1}^{\infty} \frac{a_k}{2^{a_k}}$ has at least $2^{\aleph_0}$
> solutions?

Status: OPEN. Sub-question 1 is known (Borwein–Loring [BoLo90]: every
$n = 2^{m+1} - m - 2$ has the witness $\{n+1, \ldots, n+m\}$). Sub-questions
2 (all $n$) and 3 (rational $x$ with $2^{\aleph_0}$ solutions) are open.
This campaign's Kills #2 (walk equivalence), #5 (three representations of
1/2), #6 (irrational $x^*$ with $2^{\aleph_0}$) cover the neighboring ground.

## WHAT THIS PACKAGE DELIVERS

1. **THE Q3 BRIDGE (new theorem — full proof in DERIVATION.tex):**
   if every sufficiently large $n$ has a representation of $n/2^n$ whose
   pieces all lie in $(n, n+T]$ for a UNIFORM bound $T$, then the rational
   $x = \sum_{k \geq 0} (N_0 + kT)/2^{N_0+kT}$ has $2^{\aleph_0}$
   representations.  (The rationality is the arithmetic-progression sum
   identity; the $2^{\aleph_0}$ is the independent toggle family
   $\{N_0+kT\} \leftrightarrow$ its witness, in disjoint windows.)
   **This reduces the rational-$x$ question to the bounded-room variant of
   the all-$n$ question — a new connection between sub-questions 2 and 3.**

2. **The representation-family identity, formalized** (`BlockIdentity.lean`,
   kernel-green): the integer identity behind the Borwein–Loring family
   (independently re-derived by this campaign):
   $\sum_{j=1}^{m}(n+j) \cdot 2^{m-j} = n \cdot 2^m$ for
   $n = 2^{m+1}-m-2$, plus the two engines
   ($\sum j\,2^{m-j} = 2^{m+1}-m-2$, $\sum 2^{m-j} = 2^m-1$) and the
   toggle receipts.

3. **The computational frontier**: the walk termination frontier extended
   $10^5 \to 3\cdot10^6$ (64-bit C engine, this package; all terminate).
   The walk is $v_{N+1} = (2v_N) \bmod N$ from $(n+1, n)$
   (Kill #2's equivalence theorem).

## Files
- `BlockIdentity.lean` — the Lean kernel (core-only, zero sorry).
- `DERIVATION.tex` — the Q3 bridge theorem + the family identity, complete proofs.
- `walk.py`, `walk_engine.c` — the engines.
