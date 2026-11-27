# GST original-X Chern-corrected algebraic cycle birth, dual Hodge spaces, and the real graded CM curvature

Date: 12 November 2026. Branch: research/gpt6-native-point-primitive-span-20261017.
Target remains the user-specified arbitrary original smooth projective X,p,prescribed rational Hodge alpha -> ACTUAL CH^p(X)_Q with canonical cycle class alpha. The construction below is a **positive genuine original-X theorem for every projective bundle over a smooth projective SURFACE**, including genuinely twisted nontrivial bundles; no target-bearing cycles on other fibers are given. It is NOT a proof for all arbitrary original X.

## 1. Genuine twisted geometric GST worlds

Let B be ANY smooth projective complex surface and let E be ANY algebraic vector bundle of rank m+1 with m>=2. Let X=P_B(E) be the smooth projective quotient-line projective bundle, pi:X->B, and let xi=c1^CH(O_X(1)). Its complex dimension is d=m+2.

The projective-bundle Chow formula gives the TRUE Gysin identities (in CH^*(B), not only after taking degrees):

\[
\pi_*(\xi^m)=1,\qquad
\pi_*(\xi^{m+1})=c_1(E),\qquad
\pi_*(\xi^{m+2})=c_1(E)^2-c_2(E).
\]

Set c1=c1(E), c2=c2(E). Choose a rational NS divisor basis D_1,...,D_rho on B and ACTUAL divisor Chow duals D_i^vee satisfying deg_B(D_i D_j^vee)=delta_ij. Their existence follows from the nonsingular rational Neron--Severi intersection form (Hodge index theorem), and they are genuine Chow divisors, not an assumed higher-codimension Hodge lift. Choose any actual point cycle o in CH^2(B)_Q with deg(o)=1.

The FULL codimension-two rational Hodge fiber of original X has dimension rho+2, and ACTUAL independent original-X Chow sources are

\[
A_0=\pi^*o,\qquad A_i=\pi^*D_i\cdot\xi\ (1\le i\le\rho),\qquad
A_\infty=\xi^2.
\]

They are actual cycles born from independently algebraic divisors and projective bundle geometry, for ANY prescribed Hodge alpha. The basis and its Betti dimensions are the classical projective-bundle formula, not a hypothesis that alpha already comes from Chow.

## 2. NEW EXPLICIT curvature-corrected actual Chow dual construction

The naive complementary candidates xi^m, D_i^vee xi^(m-1), o xi^(m-2) do NOT form a dual Chow frame when c1(E) or c2(E) is nonzero; their  (rho+2)-square pairing matrix has actual Chern-mixing entries.

The corrected ACTUAL complementary codimension-m Chow cycles are

\[
\boxed{
B_0=\xi^m-c_1\xi^{m-1}+c_2\xi^{m-2},\quad
B_i=D_i^\vee\xi^{m-1}-(c_1 D_i^\vee)\xi^{m-2},\quad
B_\infty=o\xi^{m-2}.
}
\]

All c1,c2,D_i^vee and intersection products are ACTUAL algebraic Chow cycles on the ORIGINAL X (pullbacks from B suppressed).

**THEOREM, valid for every B,E,m as typed:**

\[
\boxed{\deg_X(A_\mu B_\nu)=\delta_{\mu\nu}
\quad(\mu,\nu=0,1,\ldots,\rho,\infty).}
\]

Proof: use the above THREE actual Chow Gysin identities. For A_i and B_0, the c1 terms cancel. For A_infty and B_0 the cancellation is the exact CH^2(B) equation
(c1^2-c2)-c1^2+c2=0.
For A_infty and B_i, the actual CH^2(B) equation
c1 D_i^vee-c1 D_i^vee=0.
All remaining cross terms vanish by Chow degree considerations; A_i B_j reduces to the ACTUAL surface intersection deg(D_i D_j^vee)=delta_ij, and A_0 B_0 and A_infty B_infty each give one.

This is MUCH STRONGER than treating a nonzero native curvature Gram matrix as a hypothetical source. It gives every source and every dual as an actual scheme-theoretic algebraic cycle.

For any PRESCRIBED rational Hodge alpha of codimension two, set
a_mu=int_X alpha cup cl(B_mu).
The ACTUAL ORIGINAL-X cycle

\[
\boxed{
Z_\alpha=a_0 A_0+
\sum_{i=1}^\rho a_i A_i+a_\infty A_\infty
\in CH^2(X)_Q,\qquad cl_X^{can}(Z_\alpha)=\alpha
}
\]

returns the target with NO preexisting alpha cycle. The codim-two theorem holds for any B,E; using projective-bundle decomposition and the classical full Hodge theorem in complex dimension two for B proves the same source existence for ALL codimensions of X.

## 3. Literal original-X algebraic curvature and nontrivial twisted Chern example

Let B=Bl_12(EllipticCurve x P1), NS rank14, and choose the true rank8 algebraic split bundle
\[
\mathcal E=
\mathcal O_B\oplus\mathcal O_B(f)\oplus\mathcal O_B(g)
\oplus\mathcal O_B(e_1)\oplus\mathcal O_B(e_2)
\oplus\mathcal O_B(e_3)\oplus\mathcal O_B(f+g)
\oplus\mathcal O_B(2f+e_4).
\]
The actual divisor intersection form on B is f^2=g^2=0, fg=1, e_i e_j=-delta_ij, all f/g versus e_i products zero. The Chern classes are NONTRIVIAL:
c1(E)=4f+2g+e1+e2+e3+e4,
deg_B c1(E)^2=12, deg_B c2(E)=7,
and deg_B(c1^2-c2)=5.

The actual original X=P_B(E) has complex dimension9, h10=1, and a TRUE algebraic G_m action scaling each of the eight line summands with a distinct weight. Its fixed components are exactly EIGHT copies of the actual surface B. It is NOT the trivial product X=B x P7, and its source pairing REALLY has Chern corrections.

Order original sixteen source cycles as (o, D_i xi, xi^2), and initial complementary candidates as (xi^7,D_i^vee xi^6,o xi^5).
Their ACTUAL intersection matrix is the lower-unitriangular block matrix

\[
G=\begin{pmatrix}1&0&0\\
w&I_{14}&0\\
t&v^{\top}&1
\end{pmatrix},
\quad
w_i=\deg_B(D_i c_1),\
v_i=\deg_B(D_i^\vee c_1),\
t=\deg_B(c_1^2-c_2).
\]
Its EXACT rational inverse is
\[
G^{-1}=\begin{pmatrix}1&0&0\\
-w&I_{14}&0\\
v^\top w-t&-v^\top&1
\end{pmatrix},
\qquad v^\top w=\deg_B c_1^2.
\]
Thus the last coefficient of its first column is
v^Tw-t=deg_B c2(E)=7.

For the real twisted example, exact Wolfram returned
deg c1^2=12, deg c2=7, t=5,
det G=1, G G^-1=I_16, and all corrected duals integral.
This is an explicit stable, all-rank algebraic correction theorem;
not a numerical Hodge selector. The actual c2(E) remains a CH^2(B)
class in the general theorem, not falsely identified with seven
times a chosen point in CH^2(B): those may differ by degree-zero
Chow classes on an elliptic surface.

## 4. ORIGINAL GST all-degree N-cohomology duality as GENUINE algebraic correspondences

On this original X of dimension d=m+2 with p=2 and its genuine
16-dimensional source/dual Chow frames V_2=span_Q{A_i},
V_m=span_Q{B_i}, construct ACTUAL algebraic correspondences

\[
\Gamma_{2\to m}=\sum_i pr_1^*B_i\cdot pr_2^*B_i
\in CH^{2m}(X\times X)_Q,
\]
\[
\Gamma_{m\to2}=\sum_i pr_1^*A_i\cdot pr_2^*A_i
\in CH^4(X\times X)_Q.
\]

The Chow push--pull formula and the EXACT delta pairing show
\(\Gamma_{2\to m*}(A_i)=B_i\) and
\(\Gamma_{m\to2*}(B_i)=A_i\),
and their composites are identity operators on the paired born
Chow source sectors. They are genuinely degree-SHIFTING
correspondences of different codimensions, not mislabelled
degree-zero self-correspondences.

On the graded original-X N-cohomology source
V_2 direct-sum V_m, define the ACTUAL correspondence actions

\[
\mathscr S(x,y)=(\Gamma_{m\to2}y,\Gamma_{2\to m}x),
\quad
\mathscr J(x,y)=(\Gamma_{m\to2}y,-\Gamma_{2\to m}x),
\quad
\mathscr M(x,y)=(0,2y).
\]

By genuine Chow matrix-unit calculus, not by an artificial
cycle-class map,

\[
\boxed{
\mathscr S^2=I,\qquad
\mathscr J^2=-I,\qquad
[\mathscr J,\mathscr M]=2\mathscr S
}
\]

on the ACTUAL original-X algebraic source and its complementary
cohomological degree. The same exact identities hold after
CANONICAL rational Betti cycle class.

This **realizes the algebraic analogue of the owner's GST
J/M/curvature and Hodge-Star-style duality** on a nontrivially
twisted original projective variety, using exact Chern-corrected
Chow cycles. It is NOT an automatic identification with the
metric-dependent HARMONIC Hodge star for an arbitrary choice
of Kahler metric.

If a rational ample Kahler metric h is chosen, the true harmonic
Hodge star is a rational linear isomorphism on the rational
(p,p) Hodge fibers. Because BOTH complementary Hodge fibers
here are spanned by ACTUAL born Chow cycles, its rational
matrix in their bases can also be compiled into a
genuine algebraic degree-shifting correspondence.
The resulting operator agrees with the true harmonic star
on the stated Hodge fibers by construction and canonical
cycle-class naturality; this last observation applies
ONLY to the displayed fully algebraic source class.

## 5. True owner physical U/J/M 12-cell and finite single-seed return

Any twelve of the independently constructed original-X
codimension-two source cycles, in particular the twelve
exceptional e_i xi, together with their now CHERN-CORRECTED
true Chow duals, give actual rational Chow matrix units.
Use these to compile the owner's EXACT unchanged
Fin4 x Fin3 original physical U/J/M/[J,M] operators
into a codimension-d Chow correspondence \Gamma_b.
The true mixed seed e1 xi+e2 xi has exactly the
original two nonzero physical Navigation Krylov
determinants already proved/exact-computed in the
companion original-product case.
The Chern corrections do not alter the matrix-unit
action because the actual pairings are once again delta_ij.
Adjoin the four actual scalar correspondence channels
10,20,30,40 for the four remaining sources:
the complete 16-dimensional single-seed polynomial
CRT return works verbatim for this nonproduct X.

Everything is literal Chow on the stated original
algebraic variety. The claim does not apply automatically
to arbitrary smooth projective X absent the required
bundle or other source-birth geometry.
