# Mathbox — geometric GST branches from signed finite graphs: construction and all-X stress test

**2026-10-18. Base:** fd951ea2d6e5fed8371611e8a812798e9286dc21.
**Original target unchanged:** construct a canonical Betti representative Z in CH^p(X)_Q of every rational (p,p) Hodge class on every original smooth projective complex variety X. **Not proved here.**

## Actual algebraic construction for all dimensions and codimensions of Q_n

Let Q_n=(P^1_C)^n, with h_i the genuine divisor classes from its factors. For every p, H^(2p)(Q_n,Q) has the genuine algebraic basis h_S=product_{i in S}h_i, over the p-element subsets S of {1,...,n}. The square of each h_i vanishes.

For each coordinate i construct the ACTUAL finite surjective algebraic endomorphism F_i:Q_n->Q_n that squares the i-th P^1 homogeneous coordinates and fixes the other coordinates. The closed graph Gamma_i in Q_n x Q_n is finite over BOTH projections and has its genuine canonical rational Betti class. Its genuine graph pushforward T_i acts by

  T_i(h_S) = h_S if i in S, and 2 h_S if i is not in S.

This follows from the ordinary projection formula and deg(F_i)=2.

Set Delta to the true diagonal correspondence. Form the genuine signed Chow-correspondence cycle
\[
 \Pi_S=\prod_{i\in S}(2\Delta-\Gamma_i)\circ
 \prod_{j\notin S}(\Gamma_j-\Delta).
\]
Correspondence composition and rational subtraction stay inside the algebraic Chow correspondence ring. All factors commute. For each p-element subset T, the eigenvalues above give \(\Pi_S(h_T)=\delta_{S,T}h_T\). A permutation sigma of the factors with sigma(S)=T gives an algebraic graph Gamma_sigma, and
\[
 E_{T,S}=\Gamma_\sigma\circ\Pi_S,\qquad
 E_{T,S}(h_R)=\delta_{S,R}h_T.
\]
These are EXACT rational matrix units built from **genuine signed algebraic cycles on the original Q_n**, not from a freely stipulated operator on Hodge space. This is valid for every n,p on this explicit family; it does not prove the all-X target.

Wolfram exact verification for n=4,p=2 returned six actual rational basis positions, exact projectors, their sum equal to I_6, pairwise orthogonal projector traces, and determinants 8 of the degree-two finite graph actions. The independent n=2,p=1 calculation yielded all four 2x2 matrix units from signed compositions of the finite graph F_1, the factor-swap graph, and the diagonal.

## Single effective correspondence is too restrictive

On Q_2=P^1 x P^1, an effective middle-dimensional correspondence C finite and dominant over both factors sends an ample rational divisor a h_1+b h_2, a,b>0, to another ample class. Indeed the left pullback of an ample class along a finite surjective map is ample, and its right finite pushforward intersects each of the two rulings positively. Lower-dimensional components have no middle-dimensional correspondence action. Therefore no single effective bi-finite correspondence can act on h_1+h_2 as the rank-one map E_11, which yields the nonample boundary class h_1. However the **signed difference** of the graph of the map that squares the *second* factor and the diagonal acts exactly as E_11. Thus a geometry requirement of one effective K for each arbitrary GST matrix-unit event is unnecessarily restrictive, even when Hodge classes already are algebraic.

The current repository already supports rational signed combinations of genuine finite correspondences in GSTClassicalHodgeFiniteClosedCorrespondenceOperator.RationalClosedCorrespondenceCycle. We must USE it, not duplicate it and mislabel that duplication as a new source theorem.

The bare supplied MiddleBettiCorrespondenceKernel kernelClass is not independently certified to be the true fundamental class of its K. The positivity argument above applies to *actual* scheme correspondences and their canonical Betti classes, NOT to unconstrained externally supplied kernels.

## Serious attempted generalization to arbitrary X, and exact obstruction

For any smooth projective complex n-fold X, a sufficiently generic projective projection gives a finite surjective map f:X->P^n. Lifting finite power-map graph correspondences of P^n by the fiber products over f produces actual signed finite correspondences on original X, no target Chow witness chosen. Their action on the rational Betti H^(2p)(X) factors through H^(2p)(P^n,Q), as f^* g_* f_* (up to standard graph convention).

For ANY primitive degree-2p rational Hodge class alpha on X, with 1<=p and 2p<=n, primitive means alpha h^(n-2p+1)=0, where h=f^*H. Consequently
\[
 \int_{P^n}f_*\alpha\,H^{n-p}
 =\int_X\alpha\,h^{n-p}
 =\int_X(\alpha\,h^{n-2p+1})h^{p-1}=0.
\]
As H^(2p)(P^n,Q) is one-dimensional, f_*alpha=0. Every signed combination of these UNIVERSALLY EXISTENT finite projection correspondences therefore annihilates the needed primitive alpha. No sequence of those actions on an algebraic seed creates a missing primitive direction.

**Verdict:** Constructed all-rank signed geometric branch operators on explicit Q_n. The tempting universal pullback of their finite maps does NOT deliver arbitrary primitive algebraic sources: its primitive action vanishes. This is a decisive route-specific failure, not a proof or refutation of the Hodge conjecture. The user-requested all-original-X construction remains unproved. A new X-intrinsic algebraic source not factoring through P^n is required. No new Lean claims or arbitrary Hodge-surjectivity hypotheses have been introduced.
