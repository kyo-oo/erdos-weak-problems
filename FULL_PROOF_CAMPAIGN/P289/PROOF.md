# P289 — Erdős #289: k-Interval Egyptian Families — FULL PROOF (W2-P289)

## §0 VERBATIM TARGET (corpus-erdos/data/problems.yaml #289)

> Is it true that, for all sufficiently large $k$, there exist finite intervals
> $I_1,\ldots,I_k\subset\mathbb{N}$, distinct, not overlapping or adjacent, with
> $|I_i|\ge 2$ for $1\le i\le k$, such that
> $$1=\sum_{i=1}^k \sum_{n\in I_i}\frac{1}{n}\ ?$$

(Addendum: ErGr80 posed it without the restrictions; Kovac showed unrestricted
is easy. HM example for total 2: [2,7],[9,10],[17,18],[34,35],[84,85].)
Externally solved (LEAP arXiv:2606.03303). BOSS: OUR proof, OUR engine.

## §1 STATUS LOG
- t0: verbatim extracted (corpus_statements_full.json["289"]). problem289-intervals/
  read (engine289_round1.py: exact-rational DFS, k=2 negative at M=240).
- PLAN: base family + refinement (splitting) engine ⇒ all k ≥ k₀. Boost engines:
  #306 (BEG induction + CRT prime-pair splitting), #1056 factorial-interval
  structure, bl_family block machinery (bulldoze/problem261).

## §2 THE ENGINE (plan)
Interval sum σ([a,b]) = H_b − H_{a−1}. Need: ∀k ≥ k₀ a family of k disjoint
non-adjacent length-≥2 intervals with total σ = 1.
- K1 (Base): explicit family for some k₀.
- K2 (Splitting): exact identity replacing one interval by two (placed beyond
  all used denominators), preserving total, lengths ≥ 2, non-adjacent.
- K3 (Assembly): induction k → k+1 ⇒ all k ≥ k₀. ⇒ THEOREM (full #289, YES).

## §3 PROOF
(in construction — see §4 experiments for witness data)
