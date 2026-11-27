# Mathbox — GST exact incidence compactification, infinity-charge test, and original-X Chow reconstruction

**Date:** 2026-10-18. **Base:** 314743264fde36e87c1603f1c29ec6100fc53f02. **Exact fixed goal:** for every smooth projective complex original X, codimension p and rational (p,p) Hodge alpha, explicitly produce an algebraic rational Z on that original X, with the canonical Betti class alpha. **Not achieved.** This record gives a genuine original-X reconstruction formula, an exact nonalgebraic same-Hodge-class counterexample to automatic source-growth arguments, and a geometric obstruction to a holomorphic shortcut. It does NOT assume that an arbitrary alpha has an algebraic source.

## 1. The exact incidence geometry, not just an abstract affine torsor

Fix X closed in P^M over C, with its true hyperplane bundle L=O_X(1), h=c1(L). Let P*=(P^M)^vee with dual hyperplane H, and let
\[
\bar J=X\times P^*,\qquad
J=\{(x,\ell):\ell(x)\ne0\}\subset\bar J,\qquad
\pi=pr_X|_J .
\]
The universal evaluation pairing is a **nowhere-vanishing algebraic** section of pr_X^*L tensor pr_{P*}^*O(1) on J. Consequently
\[
\boxed{j^* H=-\pi^*h \quad\text{in }CH^1(J)}
\]
where the equality is a true line-bundle trivialization, not merely a Betti cohomology relation. The map pi is a torsor with affine-space fibers A^M, and both algebraic Chow and rational Betti are homotopy invariant under pi.

**No holomorphic section can replace the cycle descent.** If dim_C X>0, there is NO holomorphic section s:X^an->J^an of pi. Indeed J^an admits a closed holomorphic embedding into C^K (because J is algebraic affine); X is compact connected so every component of that embedding composed with s is a constant holomorphic function. Thus s is constant, contradicting pi∘s=id_X. In particular no analytic cycle can be returned to X by simply restricting to a holomorphic “zero section.”

Moreover a compact positive-dimensional complex analytic subvariety of the Stein affine J cannot exist. If an analytic positive-dimensional cycle D on J were proper over compact X, D would be compact and hence zero-dimensional, a contradiction. **Boundary escape is geometrically unavoidable.**

## 2. Exact original-X algebraic reconstruction from a compactifiable source

Let an analytic codimension-p source D on J have the intended true canonical Betti class
\[
\operatorname{cl}_J(D)=N\pi^*\alpha,\qquad N>0.
\]
Suppose, and DO NOT assume automatically, that the closure \(\bar D\) in compact projective \(\bar J\) is an ACTUAL algebraic codimension-p cycle extending D. (A sharp analytic volume/finite projective mass criterion would be a sufficient analytic route, subject to authentication of the precise extension theorem.) The projective bundle formula decomposes \(\bar D\) uniquely:
\[
\bar D=\sum_{j=0}^{p} pr_X^*B_{p-j}\cdot H^j,\qquad
B_{p-j}=(pr_X)_*(\bar D\cdot H^{M-j})\in CH^{p-j}(X)_{\mathbb Q}.
\]
Here p<=dim X<=M. Intersecting with H^(M-j) and applying pr_{X*} isolates the coefficient B_(p-j); this uses the true projective pushforward, not a prescribed Hodge operator.

Using the ACTUAL incidence trivialization H|J=-pi^*h gives
\[
\boxed{
Z_\alpha=\frac1N\sum_{j=0}^{p}(-h)^j\cdot
(pr_X)_*(\bar D\cdot H^{M-j})\in CH^p(X)_{\mathbb Q}.
}
\]
Its pullback pi^*Z_alpha equals the algebraic restriction j^*\bar D/N in CH^p(J). By the actual canonical cycle-class compatibility and injectivity of pi^* in rational cohomology,
\[
\boxed{\operatorname{cl}^{canonical}_X(Z_\alpha)=\alpha}.
\]
This is a completely explicit, finite, original-X cycle assembly **provided the stated projective algebraic source has actually been made**. The existence of some different algebraic representative of alpha would not force this particular analytic D to extend. Merely having Oka holomorphic D does NOT supply \(\bar D\), so this does NOT close Gate 3.

**Exact coefficient test:** Mathematica calculated the extraction identity
\[
\sum_{j=0}^p(-h)^j[H^M]\bigl(P(H)H^{M-j}\bigr)=P(-h)
\]
for all 25 pairs M=2,...,6 and p=0,...,M, with P(H)=sum_{i=0}^p a_i H^i. Every exact polynomial test returned True. Uniform validity follows by the projective pushforward basis, not by finite testing alone.

## 3. Same rational Hodge class, same algebraic holomorphic bundle, but infinite infinity mass

This is an explicit new adversarial construction for the proposed GST infinity worldtrace, not an attack on the Hodge conjecture.

Take X=P¹, M=1 and J=P¹×(P¹)^vee minus the incidence diagonal. An ordered pair of complementary lines determines the rank-one projection
\[
P=\begin{pmatrix}a&b\\c&1-a\end{pmatrix},\qquad a(1-a)=bc.
\]
Under u=2a-1, v=2b, w=2c, the **actual affine Jouanolou carrier** identifies algebraically with
\[
Q=\{(u,v,w)\in\mathbb A^3:u^2+vw=1\}.
\]
Wolfram checked exactly that u²+vw-1=4(a²-a+bc), which vanishes by the projector law. Projection to the image line gives pi:Q->P¹ with affine-line fibers.

Let alpha=c1(O_P¹(1)) and let D_0=pi^*([point]), an ACTUAL algebraic divisor on Q representing pi^*alpha. There is an actual algebraic holomorphic line bundle F=pi^*O_P¹(1) with a regular section s_0 whose zero divisor is D_0.

Now construct the new entire holomorphic function g=e^u-1 on Q^an and new holomorphic section
\[
s=s_0\cdot g\quad\text{OF THE SAME algebraic holomorphic line bundle }F.
\]
Its exact effective analytic zero divisor is
\[
D' = D_0+\sum_{k\in\mathbb Z}Q_k,\qquad
Q_k=\{u=2\pi i k,\;vw=1+4\pi^2k^2\}.
\]
Every Q_k is a distinct irreducible nonempty algebraic C* curve. On every compact subset of Q only finitely many k appear, so this is a bona fide locally finite CLOSED HOLOMORPHIC ANALYTIC divisor. The added divisor is principal, so
\[
\operatorname{cl}_J(D')=\operatorname{cl}_J(D_0)=\pi^*\alpha\ne0.
\]
But the effective sum has infinitely many irreducible components; it is **not** an algebraic cycle of finite type.

Even more sharply, compactify Q in P³ by U²+VW=T². Each Q_k has projective closure a smooth degree-2 conic in the hyperplane U=(2 pi i k)T (since 1+4pi²k²!=0). Each carries the SAME positive Fubini–Study area, 2 in the normalized class \(\int_{\mathbb P^1}\omega_{FS}=1\). Their union therefore has INFINITE total projective volume, though D_0 alone has finite volume. All the Q_k meet the same two projective boundary points at T=0, exhibiting actual infinite boundary-charge accumulation.

**This defeats a stronger false inference than the prior K3 non-Hodge test:** even when alpha IS a genuine algebraic rational (1,1) Hodge class, and even when the Oka holomorphic line bundle itself is the pullback of a TRUE ALGEBRAIC line bundle, arbitrary holomorphic sections need not have bounded infinity mass. Rational Hodge periods and bundle Chern coordinates alone cannot determine the infinity-volume growth of the chosen analytic representative. The source SELECTION law must have genuinely algebraic-growth control.

## 4. Precise geometric mass discriminator, corroborated by exact integrals

For a holomorphic graph w=f(z), its product-projective Fubini–Study area on C has a vertical term
\[
\int_{\mathbb C}\frac{|f'(z)|^2}{(1+|f(z)|^2)^2}\,dx\,dy.
\]
For the algebraic graph f(z)=z^m (m positive integer), polar coordinates give exactly \(\pi m\) in the unnormalized area convention. Mathematica calculated \(\pi,2\pi,3\pi,4\pi,5\pi,6\pi\) for m=1,...,6; by substitution t=r^(2m), the universal result is \(\pi m\). For the transcendental graph f(z)=e^z, the x integral is exactly 1/2 but the integrand is independent of y, so the y integral diverges. This is a natural **COMPACTIFIED projective mass**, not the earlier Euclidean sharp R^(2d) criterion. It detects the same escaping analytic infinity even though the current cohomology class is unchanged.

## 5. Audited status and actual next all-X operation

The existing GST topological K-source plus Oka holomorphic determinantal construction is genuine analytic source birth (subject to authenticating its analytic theorems). The **new** projective-incidence identity gives a *specific finite native algebraic cycle formula on the original X* whenever a source can be extended algebraically. The explicit Q example proves the finite-projective-mass issue is REAL even for Hodge classes with known algebraic representatives and the same bundle/connection. No universal finite-mass choice was constructed, and **the Hodge conjecture remains unproved**.

The remaining mathematical objective, with no goalposts moved, is to **construct** for every Hodge alpha a specific holomorphic determinantal source whose projective closure has finite calibrated mass, not merely a source of the correct topological class. Without that exact geometry, the original-X formula above is conditional and must never be promoted to an unconditional Hodge theorem. No new Lean source was added or claimed green in this record.
