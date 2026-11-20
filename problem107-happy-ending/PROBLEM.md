# Erdős Problem #107 — THE HAPPY ENDING PROBLEM (verbatim, erdosproblems.com/107)

> Let $f(n)$ be minimal such that any $f(n)$ points in $\mathbb{R}^2$, no three
> on a line, contain $n$ points which form the vertices of a convex $n$-gon.
> Prove that $f(n)=2^{n-2}+1$.

Tags: geometry, convex. Prize: $500 ($100 for disproof). Sources: [Er61,p.245] [Er75f,p.106]
[Er81] [Er82e] [Er83c] [Er95,p.184] [Er97c] [Er97e] [Va99,4.66]. OEIS: A000051.

Corpus context (verbatim comments):
- The Erdős–Klein–Szekeres 'Happy Ending' problem. Originated 1931: Klein observed f(4)=5.
- Turán and Makai showed f(5)=9.
- Erdős and Szekeres proved: 2^{n-2}+1 <= f(n) <= binom(2n-4, n-2)+1 ([ErSz60], [ErSz35]).
- Suk [Su17]: f(n) <= 2^{(1+o(1))n}. Holmsen–Mojarrad–Pach–Tardos [HMPT20]:
  f(n) <= 2^{n+O(sqrt(n log n))}.

DeepMind comparator (google-deepmind/formal-conjectures, ErdosProblems/107.lean):
- cardSet n = {N | forall pts : Finset R^2, pts.card = N -> NonTrilinear pts -> HasConvexNGon n pts}
- f n = sInf (cardSet n)
- erdos_107 (research open): forall n >= 3, f n = 2^(n-2) + 1
- nonempty_cardSet (solved; Lean proof exists: linrock/math-proofs)
- f_zero_eq (test, PROVED in file), f_three_eq (test, PROVED in file)
- variants.ersz_bounds (solved): 2^(n-2)+1 <= f n <= Nat.choose (2n-4) (n-2) + 1
- variants.su_bound, variants.hmpt_bound (solved research)
