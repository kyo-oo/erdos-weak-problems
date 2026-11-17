# GST all-codimension blowup Picard source saturation: exact non-tautological birth discriminator

- **Date:** 2026-10-20
- **Kind:** all-codimension geometric construction / complete source-sector classification
- **Target:** original-X rational Hodge conjecture, arbitrary X and p, or a genuine counterexample.
- **Route selected:** proof via actual non-tautological perfect-complex source birth on an ambient rational blowup, not counterexample creation by iterative split blowups.
- **Research base:** `eaac8f34169ac86b0837f56bdd089d6b54e6d212`
- **Current code:** `GSTGraphV2SelfExpandingCosmology.lean` commits `18e13252545d559c081feaaca98eb8edb39cfe74` and corrected `be0195acae35aa4a68389154b5db6367e4f62128`.
- **Verification:** GitHub Graph V2 #39412428432 and Pinned Hodge #39412428019 started at corrected commit (result not yet confirmed when this record was written); earlier draft #39412019252 failed with a tactics proof goal, the arithmetic premise was not falsified.
- **Review:** direct geometric derivation and exact symbolic Wolfram check; formal scheme-level projective-bundle/GRR correspondence remains outside the scalar Lean theorem.

## 1. The one geometric construction being tested

Let X be arbitrary smooth projective complex, choose a projective embedding X↪P^N with normal codimension c>=2, form Y=Bl_X(P^N). Write exceptional divisor j:E=P(N_{X/P^N})→Y, q:E→X, ξ=c₁(O_E(1)), and let H be pullback of ambient hyperplane, h=H|X. The genuine original-X Chow return is

\[
R_p(W)=-q_*(\xi^{c-2}j^!W),\qquad W\in CH^{p+1}(Y)_{\mathbb Q}.
\]

The critical question is whether *already available algebraic K₀ geometry on the born rational world* can detect a prescribed original-X primitive residual. The present experiment completely characterizes what happens if all born perfect-complex classes are assembled from Picard line bundles O_Y(uH+vE).

## 2. Uniform all-p Chern–Segre source formula (proof, not finite evidence)

Set n=p+1≥1. Write s_k(N)=q_*(ξ^{c-1+k}), with s₀=1 and S(t)=1/c(N;t) under the project's Segre convention. For every integer u,v (the resulting polynomial extends over Q),

\[
\boxed{
R_p\bigl(\operatorname{ch}_{n}(\mathcal O_Y(uH+vE))\bigr)
=\sum_{b=1}^{n}\frac{u^{n-b}v^b}{b!(n-b)!}\,
A_b
}
\]
with **actual original-X algebraic characteristic classes**
\[
A_b=(-1)^{b+1}h^{n-b}s_{b-1}(N)\in CH^p(X)_{\mathbb Q}.
\]

Derivation: ch_n(O(uH+vE))=(uH+vE)^n/n!, and j^*H=q^*h, j^*E=-ξ. Thus each monomial H^{n-b}E^b (b≥1) returns (-1)^{b+1} h^{n-b}q_*(ξ^{c-2+b})=(-1)^{b+1}h^{n-b}s_{b-1}(N); b=0 returns 0 since q_*(ξ^{c-2})=0. All terms have codimension n-1=p. This is an exact identity in actual rational Chow groups, using the standard geometric exceptional identities as the semantic bridge.

## 3. Unconditional complete Picard-sector source-span theorem

Let F(t)=R_p(ch_n(O_Y(H+tE))) for t∈Z. Then
\[
F(t)=\sum_{b=1}^n \frac{t^b}{b!(n-b)!}A_b.
\]
For t=1,...,n, define the exact rational coefficient matrix M by
\[
M_{tb}=\frac{t^b}{b!(n-b)!}.
\]
It factors as a Vandermonde times invertible diagonal:
\[
\det M
=\left(\prod_{t=1}^n t\right)
\prod_{1\le i<j\le n}(j-i)
\prod_{b=1}^n\frac1{b!(n-b)!}
=\boxed{\frac1{\prod_{j=1}^{n-1}j!}}\ne0.
\]

Thus the actual Chow-span of *all* Picard Chern source returns (all u,v∈Z, all rational virtual sums) is **exactly** the span of n independently indexed normal-characteristic words, modulo any geometric linear relations on X:

\[
\boxed{
\operatorname{span}_{\mathbb Q}\left\{R_p(ch_n(L)):L\in\operatorname{Pic}(Y)\right\}
=\operatorname{span}_{\mathbb Q}\{A_1,\ldots,A_n\}.
}
\]

**Important:** the A_b need not be independent in CH^p(X). The nonzero determinant guarantees that the n integer-twist sources span precisely their geometric span even if its actual dimension is much smaller than n.

It follows, for ANY linear original-X Hodge/Chow period detector ℓ, that

\[
\boxed{
\forall L\in\operatorname{Pic}(Y),\ \ell(cl_X R_p(ch_n L))=0
\iff \ell(cl_X F(t))=0\ \forall t=1,\ldots,n
\iff \ell(cl_X A_b)=0\ \forall b.
}
\]

This gives an exact **finite exhaustion algorithm for an infinite family of genuine algebraic blowup source candidates**. For K₀-classes filtered by such line bundles, the rational Chern character is additive, so the same source image applies regardless of how nonsplit the extensions look as sheaves. This does **not** exclude independent perfect complexes with genuinely non-Picard K₀ class.

## 4. All-codimension explicit inverse, suitable for a later fully graded Lean implementation

By interpolation, for t variable define the Lagrange basis using 0 as an additional root:
\[
L_i(t)=\frac{t}{i}\prod_{\substack{1\le j\le n\\j\ne i}}\frac{t-j}{i-j},\quad i=1,\ldots,n.
\]
Since F(0)=0, F(t)=\sum_{i=1}^n F(i)L_i(t) as a polynomial with coefficients in CH^p(X)_Q. Then
\[
\boxed{
A_b=b!(n-b)!\,[t^b]\sum_{i=1}^n F(i)L_i(t).
}
\]
This constructs every characteristic source A_b using n actual line-bundle born source cycles, with rational coefficients explicitly determined by integer differences. It does not require selecting an abstract Chow preimage of a Hodge target.

At p=2 (n=3), the scalar return is f(u,v)=u²v A/2 + uv² B/2 + v³ C/6. Writing F_i=f(1,i), exact recovery is
\[
A=6F_1-3F_2+\tfrac23F_3,\quad
B=-5F_1+4F_2-F_3,\quad
C=3F_1-3F_2+F_3.
\]
These identities are implemented in existing Lean module as `picardCh3_three_twists_recover_characteristic_periods`, plus the infinite-twist exhaustiveness theorem `picardCh3_three_twists_exhaust_all_sources`. The n-variable determinant proof above is mathematical; **only n=3 source-sector scalar laws** were coded in this commit.

## 5. Independent exact Wolfram computation

Stateless Wolfram evaluator:
```wolfram
m[n_Integer?Positive] := Table[
  Binomial[n,j]*i^j/Factorial[n],
  {i,1,n},{j,1,n}
];
Table[{k,Factor[Det[m[k]]],MatrixRank[m[k]]},{k,1,7}]
```

Output: for n=2..8 determinants 1, 1/2, 1/12, 1/288, 1/34560, 1/24883200, 1/125411328000, all full rank. A separate n=6 exact Lagrange inverse check yielded IdentityMatrix[6]=True. This computational range confirms the hand-derived matrix factorization; it is not the proof of uniform geometry.

## 6. Falsification decision and proof route

The ordinary blowup decomposition of canonical rational Chow/Hodge maps yields defect direct sums. Hence a sequence of blowups starting exclusively with varieties satisfying rational Hodge cannot generate a genuine counterexample: any missing rational Hodge class on a born world must already come from a missing original/base/center component. Conversely a counterexample on X would lift to its rational ambient blowup Y, but that assumes a genuine counterexample downstairs and does not produce one.

Therefore the viable active route remains a proof-side **non-Picard perfect-complex birth**, not recursively multiplying exceptional divisor words. A source object F_alpha on Y with a nonzero true original-X residual period must arise from genuinely non-tautological support/graph/moduli geometry. On K3×K3 the diagonal sheaf explicitly demonstrates such a source, whereas the entire Picard sector has zero diagonal period. For arbitrary X, constructing a non-tautological sheaf *with certified nonzero coupling to the specified r_alpha* is the named first unresolved implication.

**Outcome:** exact mathematically complete all-p Picard-sector classification and universal rational determinant formula; first nontrivial p=2 three-test law submitted to GitHub Lean CI. Not a counterexample or unconditional all-X primitive representative.
