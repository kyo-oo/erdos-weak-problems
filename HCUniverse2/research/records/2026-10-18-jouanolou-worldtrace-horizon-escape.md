# Mathbox: exact worldtrace horizon escape — why local analytic convergence cannot imply global algebraicity

**2026-10-18.** Correctly extends the earlier [original-X incidence and boundary-charge record](2026-10-18-incidence-compactification-gst-boundary-charge.md). It is a falsification of a specific tempting proof step, NOT a counterexample to the Hodge conjecture, which remains open for arbitrary X and primitive (p,p) classes.

## Actual original-X associated Jouanolou model, no abstraction

Let X=P¹ and J=P¹×(P¹)^vee minus incidence. Using the rank-one idempotent model of ordered complementary lines,
\[
J \cong Q=\{(u,v,w)\in\mathbb C^3: u^2+vw=1\}.
\]
Let pi:Q->P¹ denote image-line projection. Fix an actual algebraic line bundle F=pi^*O_P¹(1), its algebraic global section s_0 cutting out a fiber divisor D_0=pi^{-1}(point), and the genuine rational (1,1) class alpha=c1(O_P¹(1)). Thus cl_Q(D_0)=pi^*alpha!=0. Projective compactification \bar Q is the smooth quadric U²+VW=T² in P³, boundary T=0.

## A cohomologically invisible analytic infinity ghost with a calculable escape horizon

For any real 0<epsilon<1, construct the **exact holomorphic** section of the SAME algebraic F:
\[
s_\epsilon=s_0\,(1+\epsilon e^u).
\]
Its analytic divisor is
\[
D_\epsilon=D_0+G_\epsilon,\qquad
G_\epsilon=\bigcup_{k\in\mathbb Z}
   \{u=c_{\epsilon,k},\;vw=1-c_{\epsilon,k}^2\},\qquad
c_{\epsilon,k}=\log(1/\epsilon)+(2k+1)\pi i.
\]
All c_(epsilon,k) differ from +/-1 because the imaginary part is an odd multiple of pi. Thus every added component is a smooth irreducible algebraic affine C* conic, all distinct, and the countable divisor is locally finite and genuine complex-analytic. As G_epsilon is the divisor of the global holomorphic function 1+epsilon exp(u), it has zero Betti class. Therefore
\[
\operatorname{cl}_Q(D_\epsilon)=\operatorname{cl}_Q(D_0)=\pi^*\alpha
\]
for EVERY epsilon, with the SAME X, Hodge alpha and holomorphic algebraic line F.

For any fixed compact K subset Q let R_K=max_{q in K} Re u(q). If epsilon exp(R_K)<1, then |epsilon exp(u)|<1 on K; hence the new factor has NO zeros anywhere on K, so
\[
(D_\epsilon)|_K=(D_0)|_K
\]
for all sufficiently small epsilon. In the affine coordinate ball |u|<=R, a sufficient completely explicit condition is
\[
0<\epsilon<e^{-R}.
\]
Thus the "novel" ghost pieces escape beyond the logarithmic observability horizon log(1/epsilon), and D_epsilon converges *locally identically as analytic cycles* to the algebraic D_0 on every fixed compact.

Yet for each epsilon>0, the projective closure of every separate added component is a conic in \bar Q cut by U=c_(epsilon,k) T. Its normalized Fubini–Study area is exactly 2 (projective degree 2). There are infinitely many k, hence
\[
\int_{D_\epsilon}\omega_{FS}=+\infty
\]
for every epsilon>0, while D_0 has finite projective mass and is algebraic.

**This is a rigorous local/global discontinuity:** not merely "small nonzero defect" but EXACT agreement with an algebraic source on every prescribed compact after epsilon is chosen small, at the cost of unbounded worldtrace charge at infinity. No finite-radius verification, local geometric convergence, or pointwise approximation of holomorphic sections can imply finite global boundary mass. A proof would need a *uniform projective mass estimate* valid up to the boundary.

## Two analytic gauges show why section growth is the wrong invariant

There are TWO mathematically distinct holomorphic operations:
- Multiply s_0 by the nowhere-vanishing entire unit exp(u). Its zero divisor stays EXACTLY D_0 and its algebraic Hodge class stays fixed, despite exponentially growing section coefficients. Therefore "polynomial growth of a chosen holomorphic section" is NOT gauge-invariant and is generally an unnecessarily strong requirement for algebraicity of its ZERO CYCLE.
- Multiply s_0 by 1+epsilon exp(u). Its zero divisor adds G_epsilon, changing its complex-analytic geometry and giving infinite projective volume; nevertheless c1(F) and the rational Hodge class stay fixed.

The gauge-invariant object is the **divisor/current**, not the arbitrary norm of a section in a chosen frame. Poincare–Lelong records the distinction as an exact global current:
\[
[D_\epsilon]-[D_0]=dd^c\log|1+\epsilon e^u|
\]
with the conventional normalization of dd^c. The right side is cohomologically exact but not negligible at noncompact infinity. This is an explicit *cohomologically invisible yet geometrically enormous* GST boundary ghost; the original projective Hodge class cannot detect it.

## Exact analytic finite-fiber test: a different GST geometry signal

Consider the closed analytic graph A_f={(z,w):w=f(z)} in C², where f is an entire function. For an arbitrary nonzero complex slope lambda, let
\[
P_\lambda(z,w)=z+\lambda w .
\]
Its restriction to the analytic source A_f is the entire function \(g_\lambda(z)=z+\lambda f(z)\).

**Exact theorem on this source family:** if \(P_\lambda|_{A_f}\) is a proper holomorphic map for even ONE nonzero lambda, then g_lambda is a proper entire function, hence a polynomial (a proper entire map C->C has at most a pole at infinity, not an essential singularity). Therefore \(f(z)=(g_\lambda(z)-z)/\lambda\) is a polynomial and A_f is ACTUALLY ALGEBRAIC. This is a *constructive finite-projection algebraicity certificate for every entire graph*, not merely a ring formalization.

For polynomial f(z)=z^m and lambda!=0, the tilted map g_lambda(z)=z+lambda z^m is a degree-m polynomial and therefore proper, generically finite of degree m.

For the transcendental f(z)=e^z, the UNTILTED projection lambda=0 onto z is still an honest proper 1-to-1 map from the graph to C; THAT IS NOT AN ALGEBRAICITY CERTIFICATE. Every TILTED map with lambda!=0 becomes transcendental and nonproper. In fact
\[
z+\lambda e^z=t
\quad\Longleftrightarrow\quad
z=t-W_k(\lambda e^t),\qquad k\in\mathbb Z,
\]
giving infinitely many distinct inverse branches for generic t. Wolfram numerically confirmed seven distinct branches k=-3,...,3 at lambda=1,t=0, with residual z+e^z zero at high working precision. Infinite-sheet nonproper geometry is intrinsic to the transcendental source and is invisible to ordinary Hodge/Betti data.

**Application to GST:** this puts an explicit properness requirement on actual analytic geometry BEFORE the native scheme-finite correspondence machinery can act. For arbitrary higher-dimensional analytic determinantal cycles on a fixed affine embedding of J(X), the suggested condition is proper generic finite linear projections with controlled sheet count, but a full higher-dimensional algebraicity theorem with its exact hypotheses has not been authenticated in this no-web session, and such projections have NOT been constructed from arbitrary Hodge alpha. The exact graph theorem is proved; no all-X Hodge construction is asserted. The test is an alternative to infinity mass, not a disguised assertion that all Hodge cycles exist.

## Research status and exact remaining construction

The genuine all-X problem is NOT to prove that *every* Oka representative of a Hodge alpha has bounded mass: the counterexample disproves that stronger false statement even for alpha=c1(O_P¹(1)). The Hodge target requires actively SELECTING at least one holomorphic determinantal D_alpha of finite projective mass for every Hodge alpha. The prior [incidence compactification construction](2026-10-18-incidence-compactification-gst-boundary-charge.md) gives an explicit finite proper-pushforward formula on the ORIGINAL X if and when such a D_alpha algebraizes.

**New rule for GST analytic source engineering:** any Chern–Weil, Oka, calibrated surgery or weighted dbar selection mechanism must constrain the ACTUAL source's boundary current/projective mass, not merely its rational Hodge class, finite-radius approximation, selected section norm, or cohomological residue. No such universal source-selection theorem is supplied here and the full Hodge conjecture has NOT been proved.
