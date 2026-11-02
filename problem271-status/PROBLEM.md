# ERDŐS #271 — THE STANLEY SEQUENCE FRONTIER (honest status)

## THE UNSOLVED PROBLEM (verbatim, erdosproblems.com/271)

> Let $A(n) = \{a_0 < a_1 < \cdots\}$ be the sequence defined by $a_0 = 0$
> and $a_1 = n$, and for $k \geq 1$ define $a_{k+1}$ as the least positive
> integer such that there is no three-term arithmetic progression in
> $\{a_0, \ldots, a_{k+1}\}$.  Can the $a_k$ be explicitly determined?
> How fast do they grow?

Status: OPEN (last edit 2026-01-20).  Tags: additive combinatorics,
arithmetic progressions.  OEIS A005487.

## THE HONEST FRONTIER MAP

Known (per the problem page and the literature):
- $A(1)$ = the Cantor set (no ternary digit 2) — classical.
- Odlyzko–Stanley [OdSt78]: $A(3^k)$ and $A(2 \cdot 3^k)$ characterized
  for all $k \ge 0$.
- The dichotomy conjecture: every $A(n)$ eventually grows like
  $a_k \asymp k^{\log_2 3}$ or $a_k \asymp k^2/\log k$; no sequence of the
  second type is known; Lindhurst's data suggests $A(4)$ (OEIS A005487)
  is of the second type.
- Moy [Mo11]: $a_k \le (\frac12 + \epsilon)k^2$ eventually; van Doorn–
  Sothanaphan (comments): the explicit $a_k \le \frac{(k-1)(k+2)}{2} + n$.

**The complete problem — an explicit determination for every seed $n$ —
includes $A(4)$, which is a 45-year-old open case (no closed form known,
OEIS A005487).  A one-shot of the complete #271 therefore requires new
mathematics that cracks the general Stanley-sequence structure problem,
including the Type-2 growth existence question.**

## WHAT THIS CAMPAIGN HAS VERIFIED (Kill #3, CI-green)

`bulldoze/problem271-stanley-a2/StanleyA2.lean`:
the greedy 3-AP-free sequence seeded $\{0, 2\}$ — which is $A(2)$, the
$k=0$ member of the Odlyzko–Stanley family $A(2 \cdot 3^k)$ — admits the
exact closed form $A(2) = \{3m + d : m \in C,\ d \in \{0,2\}\}$ with $C$
the Cantor set, by the Cantor top-witness induction
(`stanley_a2_greedy`, axioms [propext, Classical.choice, Quot.sound]).
This is a full formal verification of one known-family member — correct,
kernel-green, but a **particular case, not the complete problem** (BOSS's
assessment, confirmed by this round's statement retrieval: the problem
asks for all $n$).

## THE ATTACK ORDER (per the arsenal map)

1. The engine: `bulldoze/scripts/discover_sorted.py` (Erdős-convention
   greedy Stanley hunts; session-007 strike found the recursive block laws
   for $A(3), A(6), A(9)$ and certified that the clean census-doubling
   two-seed families below $t = 19$ are exactly $\{3^k, 2\cdot3^k\} \cup
   \{1\}$ — consistent with Odlyzko–Stanley being the complete list of
   "Cantor-like" two-seed families).
2. The frontier: $A(4)$'s structure (block decomposition, growth data)
   — the entry point for any Type-2 progress.
3. The GST transfer: the ternary digit engines (Kill #1 pattern lift,
   LTE towers) apply to the digit-structure questions inside Stanley
   theory; no direct one-shot identified.
