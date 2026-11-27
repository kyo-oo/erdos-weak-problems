# Mathbox — universal exact holomorphic determinantal source, and sharp algebraicity-growth gate

**Date** 2026-10-18. **Base** 7adcba816cd2d9e7c8c3549ef8044818fba013d4. **Original goal remains:** for EVERY smooth projective complex original X, p and rational (p,p) Hodge alpha, construct a native algebraic Chow cycle Z on X with canonical Betti class alpha. **This record does not prove it.**

## 1. Construct a genuine topological bundle without an unstable rank-p postulate

For finite-CW X, the rational *topological* Chern character K^0_top(X) tensor Q -> H^even(X,Q) is an isomorphism. Prescribe a virtual K class whose only positive character below degree 2p is zero, and whose pth character is (-1)^(p-1) alpha/(p-1)!. Clear denominators to get a genuine integral virtual class; add a stable complement and enough trivial summands to realize it as [E]-[O^s] for an ACTUAL smooth rank-r complex bundle E, r>=p. Newton identities give

\[
c_j(E)_Q=0\ (1\le j<p),\qquad c_p(E)_Q=N\alpha
\]

with integer N>0. No algebraic cycle witness was assumed. Arbitrary lower AMBIENT Chern charges m_j h^j may also be inserted rationally via the ch/Chern dictionary, then integralized. These do NOT imply a holomorphic realization on the projective original X.

## 2. Construct an EXACT holomorphic analytic codimension-p cycle on every associated affine carrier

Let pi:J(X)->X be the genuine Jouanolou affine-space torsor, built as the nonincidence open in X times the dual projective space. J(X) is smooth algebraic affine and Stein analytically; pi is a homotopy equivalence. Pull back E. Oka-Grauert supplies an ACTUAL holomorphic vector bundle F on J(X)^an with the same topological class. This is *exact* integrability (not approximately holomorphic). For s=r-p+1, choose a sufficiently generic s-tuple of global holomorphic sections using Cartan's theorem A and holomorphic transversality, yielding the actual closed analytic determinantal rank-drop locus

\[
D_\alpha=\{u\in J(X):\operatorname{rank}(s_1(u),\ldots,s_s(u))\le s-1\}.
\]

Its expected complex codimension is r-s+1=p. Analytic Thom-Porteous and the correct noncompact Poincare duality identify

\[
\boxed{\operatorname{PD}_{BM}[D_\alpha]=c_p(F)=N\,\pi^*\alpha \in H^{2p}(J(X),\mathbb Q).}
\]

The Poincare dual is via **Borel-Moore** homology; compact homology would be the wrong target. These standard external analytic inputs (especially global section transversality in the relevant Stein scope) need exact primary-source authentication before promotion. This is a REAL complex-analytic representative for ANY rational cohomology alpha on the canonical affine carrier. It is NOT necessarily an ALGEBRAIC representative, and pi is nonproper: one cannot push forward D_alpha as a Chow cycle to X.

## 3. Algebraic multicharge identity now kernel green

For any rank r, the correct Chern twist formula is

\[
c_p(E\otimes L^k)=\sum_{j=0}^{p}\binom{r-j}{p-j}(kh)^{p-j}c_j(E).
\]

When c_j(E)=m_jh^j (0<=j<p, m_0=1) and c_p(E)=N alpha, this is

\[
\boxed{c_p(E\otimes L^k)=N\alpha+
\left(\sum_{j=0}^{p-1}\binom{r-j}{p-j}m_j k^{p-j}\right)h^p.}
\]

Thus arbitrary lower independent source charges do not spoil primitive target recovery; their entire contribution can be subtracted by genuine algebraic hyperplane cycles. Exact Wolfram tests: (r,p)=(4,2),(5,3),(6,4),(7,5) give ambient terms respectively 6k²+m, 10k³+3mk, 15k⁴+6mk², 21k⁵+10mk³. The existing GSTPrimitiveTransverseCycleExtraction.lean was upgraded **in place** and the two named all-codimension formal polynomial proofs passed **focused CI #39108995274** and **full pinned integration #39108995310**, at commit 7adcba816cd2d9e7c8c3549ef8044818fba013d4. The earlier failing proof script had a multiplication association mistake; the repair is now green. This is characteristic algebra, NOT holomorphic bundle existence.

## 4. A sharp GST infinity-mass criterion (not proved for Hodge input)

Fix a closed affine embedding J(X) into C^M. Write d=dim_C J(X)-p. To upgrade the ACTUAL holomorphic D_alpha into an algebraic cycle, a concrete sufficient test is

\[
\operatorname{Vol}_{\mathbb C^M}(D_\alpha\cap B_R)=O(R^{2d})\qquad(R\to\infty).
\]

This is the *sharp real-dimension exponent*, NOT an unspecified arbitrary polynomial bound. The classical Bishop-Stoll algebraicity criterion is expected to imply that a pure d-dimensional closed complex-analytic subset with this growth is algebraic (verify its exact original source and assumptions before relying on it). If we actually construct an Oka determinant satisfying this estimate, Chow's affine bundle homotopy invariance would descend an algebraic cycle to ORIGINAL X with the required canonical class alpha/N. **No Hodge-specific uniform sharp growth bound has been proved.**

**Sharp-exponent adversarial computation, independent of Hodge:** the transcendental closed analytic graph w=e^z in C² has complex dimension d=1. For R large enough, the strip log(R/4)<=Re z<=log(R/2), |Im z|<=R/2 lies in its intersection with the Euclidean ball B_R. The graph has induced area form (1+|e^z|²)dxdy. Its area on that strip alone is at least
\[
 R\int_{\log(R/4)}^{\log(R/2)}e^{2x}\,dx
   =\frac{3}{32}R^3.
\]
Wolfram evaluated this integral EXACTLY as 3R³/32. Therefore an analytic nonalgebraic graph may have polynomial area growth while still violating the algebraicity-required **sharp exponent R^(2d)=R²**. This is a genuinely discriminating mass/growth test, not numerical sampling. For the proposed infinity mass construction, an arbitrary O(R^M) bound with M>2d DOES NOT suffice.

**Decisive adversarial K3:** On a projective K3 of Picard rank one, choose integral beta outside H^(1,1). An Oka holomorphic line on J(X) with c1=pi^*beta admits an analytic divisor with that cohomology class. If that divisor were algebraic, Picard/Chow affine-bundle invariance would descend an algebraic divisor to X, contradicting Lefschetz (1,1). So this analytic divisor is necessarily NONALGEBRAIC. Under the Bishop-Stoll criterion it necessarily violates sharp O(R^(2d)) minimal growth. This proves that Oka exact holomorphicity alone CANNOT force the needed infinity mass bound; rational Hodge type must be used in the new bound.

**Cohomological boundary residue is too weak:** pi^*beta and pi^*alpha extend in rational cohomology across the smooth projective compactification X times dual projective space, regardless of Hodge type. Hence their *linear* cohomological infinity residue already vanishes. The K3 counterexample shows such vanishing does not force algebraic closure or the growth estimate. A new nonlinear growth-control construction, not another residue reduction, is needed.

## 4b. GST infinite-volume worldtrace: exact degree at infinity, not finite-stage closeness

For an analytic pure d-dimensional complex cycle D in C^M, define the normalized boundary mass observable
\[
\Theta_D(R)=\frac{d!}{\pi^d R^{2d}}\operatorname{Vol}(D\cap B_R).
\]
The monotonicity formula for positive complex analytic cycles says this observable is nondecreasing with R. On an algebraic cycle, its limit at infinity equals the integer algebraic projective degree (with multiplicities). In conjunction with the sharp Bishop-Stoll criterion (external exact-source verification outstanding), uniform boundedness of Theta_D is the precise algebraicity test. A finite-R approximate value does NOT certify that the infinity limit is finite.

**Original exact polynomial-graph derivation.** For the genuinely algebraic holomorphic curve D_m={(z,w):w=z^m} in C², m>=1, let q=q(R)>0 solve q²+q^(2m)=R². Its induced Euclidean area is
\[
A_m(R)=\pi(q^2+m q^{2m}),\qquad
\Theta_{D_m}(R)=\frac{q^2+m q^{2m}}{q^2+q^{2m}}.
\]
Then
\[
\frac{d\Theta_{D_m}}{dq}=
\frac{2(m-1)^2q^{2m+1}}{(q^2+q^{2m})^2}\ge0,\qquad
\lim_{R\to\infty}\Theta_{D_m}(R)=m.
\]
Wolfram EXACTLY verified the derivative identity (difference 0), positivity for m=2,...,5, and limits 1,2,3,4,5,6 for m=1,...,6. The general proof is one rational derivative and dominance of q^(2m) for m>1; the limit for m=1 is 1. This gives a genuine integer WORLDTRACE at infinite affine radius, not merely a cohomological label.

By contrast, the transcendental graph w=e^z has an explicit ball-contained strip of analytic area at least 3R³/32 for large R; since d=1, its normalized density is at least 3R/(32*pi) and diverges. This proves why the growth exponent 2d is sharp.

**Mathematical interpretation:** the Euclidean Kähler form is exact on affine C^M; by Stokes, the analytic volume of D∩B_R is determined by geometric boundary flux rather than by the ordinary Betti class of D. Thus the projective-origin Hodge class alone does not supply a bound for Theta_D without an independently constructed nonlinear infinity-growth control. This observation blocks another unsupported shortcut: zero cohomological infinity residue cannot be conflated with bounded normalized geometric mass.

**Integration with actual GST mass laws:** GSTResearchGeometricMassSemanticAudit.lean already proves that raw signed coefficient mass is NOT a homology/cycle-class invariant. The new normalized analytic boundary-volume Theta_D deliberately is NOT such an invariant either; instead its finite/infinite limiting behavior detects growth of an independently constructed holomorphic carrier. GSTPolarizedHodgeResidualEnergy.lean supplies a different, *cohomology-defined* positive Hodge residual norm. Those two readouts are logically independent: the residual polarization concerns the fixed original-X cohomology class, while infinity mass concerns the chosen analytic representative's growth on J(X). Any proposed law forcing finite infinity mass from positive/zero residual energy needs an independent nonlinear analytic proof and is NOT present in either existing Lean module.

**The unsolved target-specific implication** is to build some Oka holomorphic determinantal D_alpha from the prescribed Hodge alpha with sup_R Theta_D_alpha(R)<infinity. No such bound is proved, and it is not inferred from the algebraic graph examples.

## 5. A geometric stability barrier and how source charges actually change it

For nonzero primitive codimension-two alpha, the pure rank-two source c1=0,c2=N alpha has c2.h^(n-2)=0. Any **slope-polystable** projective holomorphic realization would have a Hermitian-Einstein connection; equality in Bogomolov-Lubke forces projectively flat curvature, and c1=0 forces flatness, contradicting nonzero rational c2. For p>=3, the pure source has c1=c2=0 but nonzero c_p, yielding the same contradiction. Tensoring by an ample line bundle does not alter the discriminant. ADDING an independent positive ambient c2 charge raises its discriminant degree and removes this *particular* obstruction, but by itself does NOT force a holomorphic bundle or an algebraic Chow source on X.

## Exact research status

Genuine stable topological source on every X: constructive, standard K-theory. Genuine holomorphic analytic determinantal cycle on J(X): constructive using named Stein analytic existence theorems, with primary-source check outstanding. Universal all-rank multicharge identity: **Lean GREEN** (two workflow receipts). Rational Hodge-to-sharp algebraic infinity mass estimate: **UNPROVED**. Construction of a Chow cycle on arbitrary ORIGINAL X: **UNPROVED**. Neither a green Lean formula nor an analytic cycle is the full Hodge theorem.

Next mathematical operation: derive a Hodge-sensitive exact minimal growth estimate for a SELECTED Oka holomorphic determinantal source, without assuming a holomorphic bundle on original X, without importing the target Chow cycle, and without mistaking cohomological residue zero for geometric regularity.
