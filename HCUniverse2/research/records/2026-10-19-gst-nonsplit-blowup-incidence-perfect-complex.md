# Mathbox GST — nonsplit original-X exceptional-incidence perfect-complex source

- **Date:** 2026-10-19
- **Kind:** concrete geometric source construction, target-coupling derivation, exact rational computation
- **Program:** the unchanged all-X Hodge conjecture, Gate 3; this is a new non-product geometric testbed for the general arbitrary-arity original-X native K0 source machinery, NOT an all-X proof
- **Base revision:** 8f0a8d0d8e7cc15717b7d1f237d840d2aaf14a24
- **Lean:** updated existing \`GSTUniversalResolvedSupportHodge.lean\` with \`chowManyGeometricFactors_zero_below_grade\`, \`chowManyGeometricFactors_leading\`, \`chowManyGeometricFactors_finiteFlatTodd_firstChow\`; revision-matched GitHub Actions [#39223363764](https://github.com/kyo-oo/HC-PROOF/actions/runs/39223363764) and [#39223363815](https://github.com/kyo-oo/HC-PROOF/actions/runs/39223363815) both successful
- **Mathematical status:** real geometric blowup calculation derived from intersection, exceptional-projective-bundle and standard blowup cohomology laws; Wolfram exact polynomial confirmation; NOT a fully Lean-certified instance of Chow groups of the blowup because the repository has no such supplied scheme-level Chow ring model
- **Original ultimate goal:** for arbitrary smooth projective complex original X,p,alpha, construct an actual Chow cycle on same X with canonical Betti class alpha

## 1. NEW actual nonsplit original-X geometric source, not a formal chosen class

Let B=P^4_C and let i:Y=Q^2=P^1×P^1→P^4 be a **smooth quadric surface contained in a hyperplane P^3**. Set X=Bl_Y(B). X is a smooth projective complex FOURFOLD, not the product Y×P^2 and not a generic abstract Hodge-vector model. Let pi:X→B be the blowup, j:E→X its exceptional Cartier divisor, and q:E=P(N_{Y/B})→Y its P^1-bundle. Its normal bundle is
\[
 N_{Y/B}\simeq O_Y(1)\oplus O_Y(2),\quad
 c_1(N_{Y/B})=3(a+b),
\]
with a,b the genuine two ruling divisor classes of Y, a²=b²=0 and ∫_Y ab=1.

Take two **actual ruling curves** A (class a) and B' (class b) of Y, and their inverse-image surfaces
\[
 S_A=q^{-1}(A), \qquad S_{B'}=q^{-1}(B')\subset E\subset X.
\]
These are codimension TWO honest algebraic surfaces in the ORIGINAL X. Their K0 difference is the actual perfect-complex class
\[
 F=[O_{S_A}]-[O_{S_{B'}}]\in K_0(X).
\]
Every coherent sheaf on the smooth X has a bounded perfect resolution, so these are integral K0 classes; **no input cycle representing an unknown target** was selected. Because each sheaf is supported in codimension 2,
\[
 ch_0(F)=ch_1(F)=0,\qquad
 ch_2(F)=[S_A]-[S_{B'}]=Z=j_*q^*(a-b).
\]
It is a genuinely geometric Hilbert/incidence source constructed from the blowup's closed subscheme, not a formal K0 map or cohomological projector.

## 2. Primitive and nonzero through genuine intersection geometry

Write δ=a-b. Then
\[
 (a+b)\delta=0,\qquad c_1(N_{Y/B})\delta=0,\qquad \delta^2=-2[pt]_Y.
\]
Moreover i_*δ=0 in CH³(P4)_Q: CH³(P4) is one-dimensional and its degree measured against the hyperplane is ∫_Y(a+b)δ=0.

Let ξ=c1(O_E(1)). The blowup excess formula
\[
 \pi^* i_*\delta = j_*\bigl((\xi+q^*c_1(N_{Y/B}))q^*\delta\bigr)
\]
and the above three vanishings yield j_*(ξ q*δ)=0, therefore E·Z=0. By projection formula H·Z=j_*q^*((a+b)δ)=0 for H=pi^*O_P4(1). Consequently
\[
 (mH-E)\cdot Z=0
\]
for every integer m, and in particular for m large enough that L=mH-E is very ample. This is the **genuine Lefschetz-primitive** condition, not only trace-zero.

For normal O_E(-1), j^*j_*γ=-ξ γ and q_*ξ=1:
\[
 \int_X Z^2=-\int_E \xi q^*(\delta^2)=-\int_Y\delta^2=2.
\]
Thus Z is a nonzero rational algebraic codimension-two primitive source on this actual nonsplit original X with **positive** middle primitive norm.

Self-audit: if a different convention for P(N) is used, its O_E(1) and ξ sign must agree with N_{E/X}=O_E(-1). The final norm=+2 is fixed by the self-intersection and ∫δ²=-2.

## 3. Exact original-X target reconstruction, not merely nonzero source

The standard Chow/Betti blowup decomposition is
\[
 H^4(X,Q)=H^4(P4,Q)\oplus H^2(Y,Q)(-1)
\]
and
\[
 H^6(X,Q)=H^6(P4,Q)\oplus H^4(Y,Q)(-1).
\]
Ranks are 3 and 2. For an ample L, hard Lefschetz makes L:H4(X)→H6(X) surjective; hence ker L has dimension 1. Since Z is nonzero and L·Z=0, cl_X^canonical(Z) SPANS the entire rational primitive Hodge sector.

For **every prescribed** rational primitive Hodge class α on this X, without assuming an alpha-Chow representative,
\[
 \boxed{Z_\alpha=\frac{Q(\alpha,\operatorname{cl}Z)}{2}\,Z}
\]
is an actual original-X rational Chow cycle with canonical Betti class α, because Q(Z,Z)=2 and dim_Q ker L=1. The target rational perfect complex can be written
\[
 F_\alpha=\frac{Q(\alpha,\operatorname{cl}Z)}{2}
       ([O_{S_A}]-[O_{S_{B'}}])\in K_0(X)_Q.
\]
This is the exact one-dimensional **non-split original-X** source-to-target source birth and rational coupling construction. Full H^4(X,Q) is algebraic as well by the blowup decomposition and algebraicity of the divisor classes on Y. This positive example verifies the mechanism, NOT the unrestricted all-X target.

## 4. Finite-flat normalized GST projector and Todd comparison

Pick m so L=mH-E is very ample. The embedding |L| followed by a generic linear projection gives an actual finite flat morphism f:X→P4 of degree d>0 and f*O(1)=L.

Since LZ=0, projection formula gives f_*Z=0 in CH²(P4)_Q; indeed CH²(P4)=Q·h² and the coefficient is measured by ∫ f_*Z h²=∫Z L²=0. The corrected K0 class
\[
 \mathcal P_f^K(F_\alpha)=F_\alpha-f^*((f_*O_X)^{-1} f_*F_\alpha)
\]
has lower ch_0,ch_1 zero, and its leading ch_2 is precisely (Q(alpha,Z)/2)Z because the ambient push term vanishes in degree 2. The relative Todd factor has degree-zero term 1, so the degree-two Todd-normalized Chern class is unchanged. This explicitly connects the geometric source to the existing exact arbitrary-arity K0/GRR construction.

## 5. Exact symbolic check (WolframLanguageEvaluator)

In Q[a,b]/(a²,b²) with ∫ab=1, for δ=t(a-b) and normal c1=3(a+b), Wolfram returned

\[
 (a+b)\delta=0,\quad
 3(a+b)\delta=0,\quad
 \delta^2=-2t^2 ab,\quad
 -\delta^2=2t^2 ab.
\]

For t=1 the exceptional signed norm is exactly 2. An independent first-Chern/Todd finite-flat experiment for three mixed source factors with r=(2,1,0), Todd=(1+3z+7z²), inverse=1/5+11z, and push=z³(pushlead+pushnext z) returned:
- degree 2 coefficient=0
- degree 3 coefficient=aa*bb*cc - pushlead/5
- exact difference from expected=0
- higher degree contains the nontrivial Todd/inverse terms.

These computations are exact symbolic checks of the algebraic identities, **not** a replacement for scheme-level blowup, GRR or uniform all-X existence.

## 6. Remaining genuine all-X extrapolation question

The source has two independently built **exceptional ruling sheaf** factors that cannot be obtained from the ambient hyperplane powers alone. The construction enlarges primitive algebraic geometry through an actual codimension-two incidence locus; it does not assume an algebraic representative for its test target.

The general unsolved extrapolation is this: given a nonzero primitive rational Hodge residual r on an arbitrary original smooth projective X, construct an analogous intrinsic Hilbert/closed-incidence sheaf F on **that same X** with Q(r,ch_p(P^K_f F)Td(T_f))≠0, rather than requiring X to be such a blowup. Nothing in the above proves that every X admits the necessary exceptional geometry.

**Disposition:** positive nonsplit source-generation test; continue actual all-X Hilbert/incidence perfect-complex birth, avoid returning to abstract matrix-unit saturation.
