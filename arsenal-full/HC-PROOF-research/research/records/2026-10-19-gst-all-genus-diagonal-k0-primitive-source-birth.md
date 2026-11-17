# Mathbox GST: actual algebraic diagonal primitive perfect-complex birth on products of curves of arbitrary genus

**Date:** 2026-10-19. **Initial source checkpoint:** 6cad83c857237713000b05df8a44a1c1bbdbefbb. **Main target unchanged:** a genuine Chow cycle on each arbitrary original smooth projective X representing any rational (p,p) alpha via the canonical Betti class. **This route:** construct additional native sources on the entire geometric family X=product of pairs of smooth projective curves of arbitrary positive genera. Existing GSTPrimitiveProductTowerStabilization.lean upgraded in place; actual schemes' Chern/Betti comparisons remain to be formally instantiated.

## A. The diagonal source needs NO elliptic or CM symmetry

Let C be any smooth projective complex curve of genus g≥1, equipped with a closed point o. On S=C×C define true integral divisors x1=[{o}×C], x2=[C×{o}], delta=[diagonal]. The diagonal's normal bundle is the algebraic tangent bundle T_C and hence
\[
\delta^2 = \deg c_1(T_C)=2-2g
\]
as a top intersection number; x1²=x2²=0 and x1x2=xj delta=1. The actual algebraic ample class h=x1+x2 has two primitive divisors
\[
P=x1-x2,\qquad D=\delta-x1-x2.
\]
Their product with h is zero in rational CH²: the two intersections of delta with the coordinate fibers are the identity point (o,o), matching the two coordinate-factor products. Their signed primitive intersection matrix, Q_S(u,v)=−deg(u·v), is
\[
\boxed{G_{P,D}=\begin{pmatrix}2&0\\0&2g\end{pmatrix}.}
\]
The diagonal source D is cohomologically nonzero precisely for g>0; when g=0, on P¹×P¹ the diagonal is x1+x2 and the graph-primitive source vanishes, as the formula predicts. This is an exact geometric genus boundary rather than a formal positivity assumption.

## B. Pure-ch original-C perfect complexes

Let L1,L2 denote the factor line bundles associated with o. Set M=O_{C×C}(delta-x1-x2). The rational algebraic K₀ classes
\[
A=[L1]-[L2],\qquad B=\tfrac12([M]-[M^{-1}])
\]
are real perfect-complex virtual bundles made from algebraic line bundles. As dimension(S)=2, the exponential series for ch is finite, and the antisymmetric inverse operation cancels all degree-two terms:
\[
\operatorname{ch}(A)=P,\qquad \operatorname{ch}(B)=D
\]
with exactly degree-one Chow character and no degree-zero or degree-two terms. Unlike tangent-Chern sources on abelian varieties, B applies to EVERY smooth projective curve, including all g>1.

## C. The arbitrary-genus all-rank native GST world birth

Let C_j be any smooth projective complex curves with genera g_j>0 and points o_j. The ORIGINAL smooth projective 2m-fold
\[
X=\prod_{j=1}^m(C_j\times C_j)
\]
has a polarization H=sum_j(x_{2j-1}+x_{2j}). For each word eps∈{P,D}^m let E_eps be the exterior tensor product of the independently defined perfect complexes A_j or B_j. Their rational Chern characters are PURE of degree m and equal the genuine Chow cycles
\[
Z_\epsilon=\prod_j(P_j\text{ or }D_j)\in CH^m(X)_{\mathbb Q}.
\]
The true Chow product satisfies H Z_eps=0. Their signed polarized primitive Gram, using actual cohomological Künneth/top integration, is
\[
\boxed{Q_X(Z_\epsilon,Z_\eta)
=\delta_{\epsilon\eta}\prod_{j=1}^m
 \begin{cases}2,&\epsilon_j=P,\\2g_j,&\epsilon_j=D.\end{cases}}
\]
All diagonal weights are positive integers, so **2^m mutually orthogonal independent genuine algebraic primitive classes** exist on each such X. This is a nontrivial family with independently varying curve genera, not an elliptic-only hypothesis.

The native graph-containing tensor words have at least one cross \(H^1(C_j)\otimes H^1(C_j)\) Künneth factor and are orthogonal to every pure coordinate-divisor word. The existing GST Catalan noncrossing Koszul primitive sources, whose construction only needs square-zero degree-one divisors on the individual curves, give C_m classes in that pure coordinate sector. Exactly the all-P tensor source overlaps it. Thus the combined **true algebraic primitive rank is at least \(C_m+2^m-1\)** on the original product X for arbitrary positive genera.

## D. Prescribed-alpha exact positive-period native K₀ compiler

For any rational middle primitive Hodge alpha on this SAME original X, measure actual rational periods \(a_\epsilon=Q_X(\alpha,Z_\epsilon)\), and write
\[
w_\epsilon=\prod_j(2\text{ if }P,\;2g_j\text{ if }D),\qquad
\mathcal E_\alpha=\sum_\epsilon \frac{a_\epsilon}{w_\epsilon}\mathcal E_\epsilon.
\]
This rational algebraic K₀ perfect-complex class needs no Chow preimage of alpha. Its genuine ch_m Chow class
\[
Z_\alpha=\sum_\epsilon \frac{a_\epsilon}{w_\epsilon}Z_\epsilon
\]
satisfies exact period reconstruction
\[
Q_X(Z_\alpha,Z_\eta)=a_\eta,\qquad
Q_X(\alpha,Z_\alpha)=\sum_\epsilon \frac{a_\epsilon^2}{w_\epsilon}\ge0,
\]
with strict positivity if any measured period is nonzero. It represents alpha exactly if alpha lies in the constructed graph/Koszul sector. The new Lean theorems in GSTPrimitiveProductTowerStabilization.lean implement the all-rank rational primitive weighted-Gram identity, positivity, exact readout and target-coupling law. Check the revision-matched [external-product GST GitHub CI](https://github.com/kyo-oo/HC-PROOF/actions/workflows/gst-primitive-external-product-birth.yml) before promoting the newest target lemmas to kernel-verified.

**Full finite-flat K₀ projector fixed-point theorem, including the nontrivial Todd class:** Choose a sufficiently positive multiple kH to give an honest finite flat projection f:X→P^(2m). The sources have pure ch_m=Z_eps and H*Z_eps=0 in Chow. For a curve C_j of genus g_j, the degree-one Todd class on C_j×C_j is (1-g_j)(x_(2j-1)+x_(2j)) in rational Betti cohomology. Both factor source types P_j and D_j are H_j-primitive, so their cohomological product with this Todd term vanishes; higher Todd factors vanish against the degree-one source on that complex surface by degree. Therefore **ch(E_eps)·Td(T_X)=ch(E_eps)=Z_eps in rational Betti cohomology** on the product, even though Td(T_X) is not itself 1. GRR gives ch(f_*E_eps)·Td(T_P)=f_*(ch(E_eps)Td(T_X)). Its Betti class is zero since f_*Z_eps is zero by H*Z_eps=0 and the projection formula. The cycle class map for CH*(P^(2m))_Q is an isomorphism, so the GRR right side is actually ZERO IN RATIONAL CHOW on projective space. As Td(T_P) is invertible and the rational Chern character K₀(P)_Q→CH*(P)_Q is injective, **f_*E_eps=0 in actual algebraic rational K₀**. Thus GST's normalized projector fixes EVERY such native perfect-complex source: P_f^K(E_eps)=E_eps. The argument respects the nontrivial canonical/Todd terms and uses no imaginary simplification Td=1 outside the abelian case.

The exact local numerical Todd cancellation for arbitrary genus was added and kernel-checked in the existing GSTPrimitiveProductTowerStabilization.lean as curvePairToddFirst_primitive_cancellation. The full actual-scheme GRR/cycle-class implementation remains an instantiation task separate from this mathematical argument.

**Route result:** new independently constructed algebraic source family of arbitrary positive-genus product varieties, plus arbitrary-rank target-dependent native perfect-complex extraction. Full all-varieties Hodge surjectivity requires a further geometric source-generation mechanism beyond product-curve correspondences. Formalizing a true universal original-X algebraic K₀/Chow source selector without assuming the target preimage remains the fixed goal.

## E. Evidence audit

- Mathematical proof: genuine curve diagonal normal-bundle degree 2-2g, intersection arithmetic, exact pure Chern characters of rational line-bundle virtual differences, external-product Chow primitivity, signed pairing factorization, and positive Gram independence.
- Exact calculation: g=1 agrees with earlier elliptic diag(2,2); g=0 degenerates, as geometrically required. No approximate numerics.
- Lean: existing GSTPrimitiveProductTowerStabilization.lean edited in-place at 2972b8f067aecaaa2f07a6b3dbab81806bffd4ec (all-genus positive Gram) and eeb80d8c2b137302d794a4a53f56198a6819dc75 (target-period selection).
- Caveat: rational intersection coordinate formalization and actual Chow/GRR/canonical Betti instantiation are distinct layers; do not promote a green ring computation into a universal Hodge proof.
