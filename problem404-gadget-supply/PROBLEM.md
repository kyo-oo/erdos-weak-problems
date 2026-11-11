# ERDŐS #404 — SUB-QUESTION 3: THE GADGET-SUPPLY PROGRAM (Conjecture D)

## THE UNSOLVED PROBLEM (verbatim, erdosproblems.com/404)

> For which integers $a \geq 1$ and primes $p$ is there a finite upper bound on
> those $k$ such that there are $a = a_1 < \cdots < a_n$ with
> $p^k \mid (a_1! + \cdots + a_n!)$?
> If $f(a,p)$ is the greatest such $k$, how does this function behave?
> Is there a prime $p$ and an infinite sequence $a_1 < a_2 < \cdots$ such that
> if $p^{m_k}$ is the highest power of $p$ dividing $\sum_{i \leq k} a_i!$
> then $m_k \to \infty$?

Status: OPEN. The third sub-question (the infinite chain) is the target of
this package.

## THE REDUCTION (Theorem A, kernel-green in problem404-full)

For seed $a$ and prime $p = 2$: write $P_i = 3 \cdot 4 \cdots i = i!/2$
($i \geq 3$). Then $2! + \sum_{i \in B} i! = 2 \cdot (1 + \sum_{i \in B} P_i)$,
and the infinite chain for $(2,2)$ exists iff for every $k$ there is a finite
$B \subseteq \{3, 4, \ldots\}$ with $v_2(1 + \sum_{i \in B} P_i) \geq k$
(König compactness: the finite witnesses cohere into an exact
$\mathbb{Z}_2$ zero-sum $\sum_{i \in Z} i! = 0$).

## WHAT THIS PACKAGE DELIVERS (the complete gadget-supply theory, kernel-green)

1. **THE LIFT LAW** (`lift_law`, Lean): if $v_2(x) = v_2(y) = V$ ($x, y \geq 1$)
   then $v_2(x+y) \geq V+1$. This is the engine of the level-by-level
   construction: to raise a chain sitting at valuation $V$, add a gadget of
   EXACT valuation $V$. (Companion facts, both immediate: a gadget of
   valuation $j < V$ poisons the sum down to $j$; one of valuation $j > V$
   leaves the valuation at $V$.)

2. **THE PAIR LAW** (`pair_law`, Lean, all $u \geq 3$):
   $P_u + P_{u+1} = P_u \cdot (u+2)$, hence
   $$v_2(P_u + P_{u+1}) = v_2(P_u) + v_2(u+2).$$
   The supply of pair-gadgets at level $k$ is $\{u : v_2(P_u) + v_2(u+2) = k\}$
   — the $v_2(u+2)$ factor contributes every $j \geq 0$, so pairs supply
   every level of the form $v_2(P_u) + j$.

3. **THE TRIPLE LAW** (`triple_law`, Lean, all $u \geq 3$):
   $P_u + P_{u+1} + P_{u+2} = P_u \cdot (u+2)^2$ (perfect square), hence
   $$v_2 = v_2(P_u) + 2 \cdot v_2(u+2).$$
   The square exponent doubles the congruence freedom: the pairs' gap levels
   are the triples' supply.

4. **THE CONSTRUCTIVE CHAIN (certified depth 23)**: the 10-gadget chain
   $\{3\}, \{3,5\}, \{3,5,6,7\}, +\{11\}, +\{12\}, +\{15\}, +\{16\}, +\{19\},
   +\{20\}, +\{23\}$ with valuations $3, 7, 8, 10, 11, 15, 16, 18, 19, 23$ —
   each step an application of the LIFT LAW at the current valuation.
   Together with the reachable-set DP ($-1 \in R_k$ for all $k \leq 24$,
   `verify_gadgets.py`) and the prior obstruction-free certification to
   depth $2^{28}$: **$g(2,2) \geq 23$, certified.**

5. **THE DEAD-END LAW (the choice structure)**: the greedy chain
   $\{3\} \to \{3,4\}$ TRAPS at $V = 4$: modulo 32 the staircase residues
   beyond index 4 are $\{28, 8, 24, 0\}$, whose subset sums never hit
   $16 \bmod 32$ — NO gadget of valuation 4 exists disjoint from $\{3,4\}$.
   The construction must choose $\{5\}$ at $V = 2$ (jumping to $V = 6$).
   Choice matters; the DFS decision tree is mapped in `verify_gadgets.py`.

## OPEN FRONT (honest label)

The full proof of $g(2,2) = \infty$ (hence sub-Q3 = YES for $(2,2)$) needs
the gadget supply at EVERY level $V$ with the disjointness scheduling — the
pair/triple laws reduce the supply to the arithmetic of
$v_2(P_u) + j \cdot v_2(u+2)$ ($j \in \{1, 2\}$), and the remaining gap is
the coverage theorem (every sufficiently large $k$ is
$v_2(P_u) + j\,v_2(u+2)$ with the gadget indices disjoint from the chain's
used set — the windows grow, so disjointness is schedulable in principle).
This package lands the laws, the certified chains, and the decision-tree
structure; the coverage theorem is the live frontier.

## Files
- `GadgetSupply.lean` — the Lean kernel (core-only, zero sorry):
  lift_law, pair_law, triple_law + chain/coverage receipts.
- `DERIVATION.tex` — the complete mathematical derivation.
- `verify_gadgets.py` — the reachable-set DP + DFS battery (exact integers).
