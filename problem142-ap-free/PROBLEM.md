# Erdős Problem #142 — THE $10,000 AP-FRONTIER (verbatim, erdosproblems.com/142)

> Let $r_k(N)$ be the largest possible size of a subset of $\{1,\ldots,N\}$
> that does not contain any non-trivial $k$-term arithmetic progression.
> Prove an asymptotic formula for $r_k(N)$.

Tags: additive combinatorics, arithmetic progressions. Prize: $10000.
Sources: [Er80,p.92] [Er81,p.4] [Er97c] [Va99,1.27]. OEIS: A003002, A003003, A003004, A003005.

Corpus context (verbatim comments):
- Erdős: "probably unattackable at present"; in [Er81] "probably enormously difficult".
- He offered $5000 just for (essentially) showing $r_k(N)=o_k(N/\log N)$.
- Best upper bounds: Kelley–Meka [KeMe23] k=3, Green–Tao [GrTa17] k=4, Leng–Sah–Sawhney [LSS24] k>=5.
- [Er80]: asks for the ORDER OF MAGNITUDE of $r_k(N)$; "we do not even know whether
  $r_k(n)/r_{k+1}(n)\to 0$ for any $k\geq 3$".

DeepMind comparator (google-deepmind/formal-conjectures, ErdosProblems/142.lean):
- erdos_142 (research open): (fun N => r k N) ~[atTop] erdos_142.answer  [asymptotic formula]
- erdos_142.variants.lower (research open, k>1): r k N =o[atTop] (N / log N)
- erdos_142.variants.isTheta (research open): order of magnitude
- erdos_142.variants.three (research open): r 3 N asymptotic

Where r := Set.IsAPOfLengthFree.maxCard (Mathlib), N in [N] = {1..N}, non-trivial k-AP:
a, a+d, ..., a+(k-1)d in A with d >= 1.
