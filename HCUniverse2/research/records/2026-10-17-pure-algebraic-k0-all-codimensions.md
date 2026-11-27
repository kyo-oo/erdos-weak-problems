# Mathbox: genuine pure algebraic K₀ primitive classes in every codimension

- **Date:** 2026-10-17
- **Parent goal:** Exact rational Hodge conjecture for every original smooth projective complex X, all p, every rational Hodge \(\alpha\), with genuine canonical Betti cycle-class equality.
- **Active research obligation:** Produce actual nonambient algebraic K₀ sources in arbitrary Hodge codimensions, not merely universal rank-one ambient line bundles or trivial tangent-projector idempotents.
- **Construction for arbitrary p≥1,d≥2:** Define the smooth Fermat hypersurface of complex dimension \(2p\),
  \[
  X_{p,d}=\bigl\{\sum_{i=0}^{p}(y_i^d-x_i^d)=0\bigr\}\subset\mathbb P^{2p+1}_{\mathbb C}.
  \]
  Its partial derivatives are \(\pm d x_i^{d-1}\) and \(\pm d y_i^{d-1}\), which have no common projective zero. The linear \(p\)-plane \(P=\{y_i=x_i\}\) is a genuine smooth algebraic subvariety of codimension \(p\). Let \(T=X\cap H_1\cap\cdots\cap H_p\) be a transverse complete intersection of \(p\) genuine hyperplanes, so \([T]=h^p\) in cohomology.

- **Explicit source, not a chosen Hodge preimage:** On original \(X\) form
  \[
  \xi_{p,d}=d[\mathcal O_P]-[\mathcal O_T]\in K_0^{alg}(X)_{\mathbb Q}.
  \]
  These are authentic coherent algebraic sheaves with finite locally free resolutions since \(X\) is smooth. The basic GRR/support filtration gives \(\operatorname{ch}_i(\mathcal O_P)=\operatorname{ch}_i(\mathcal O_T)=0\) for \(i<p\), while \(\operatorname{ch}_p(\mathcal O_P)=[P]\), \(\operatorname{ch}_p(\mathcal O_T)=h^p\). Therefore \(\operatorname{ch}_p(\xi_{p,d})=d[P]-h^p\).

- **All-p pure Adams operation:** For \(\dim_{\mathbb C}X=2p\), use the polynomial
  \[
  L_{p,2p}(t)=\prod_{\substack{0\le j\le 2p\\j\neq p}}
     \frac{t-2^j}{2^p-2^j}\in\mathbb Q[t],\qquad
  \xi^{pure}_{p,d}=L_{p,2p}(\psi^2)\xi_{p,d}.
  \]
  Algebraic Adams operations \(\psi^2\) act on the rational \(i\)-th Chern character by \(2^i\). Hence
  \[
  \operatorname{ch}(\xi^{pure}_{p,d})=d[P]-h^p
  \]
  **in exactly codimension p**, with all other Chern character components zero. This is an independently constructed rational algebraic K₀ class in every codimension p.

- **Genuine primitive norm:** The normal sequence \(0\to N_{P/X}\to\mathcal O_P(1)^{p+1}\to\mathcal O_P(d)\to0\) gives
  \[
   q_{p,d}=[t^p]\frac{(1+t)^{p+1}}{1+d t}
     =\sum_{k=0}^{p}\binom{p+1}{k}(-d)^{p-k}.
  \]
  By the binomial theorem \(d q_{p,d}-1=-(1-d)^{p+1}\). The actual geometric intersection numbers are
  \[
  (h^p)^2=d,\quad [P]\cdot h^p=1,\quad[P]^2=q_{p,d}.
  \]
  Consequently \(Z_{p,d}=d[P]-h^p\) has zero ample pairing, is middle primitive by Hard Lefschetz, and
  \[
  \boxed{\langle Z_{p,d},Z_{p,d}\rangle=d^2q_{p,d}-d
          =(-1)^p d(d-1)^{p+1}\neq0.}
  \]
  Its canonical Betti class is therefore nonzero, genuinely nonambient and rational \((p,p)\).

- **Transport to every affine replacement of these source varieties:** Pullback to the explicitly affine Jouanolou torsor \(J(X_{p,d})\to X_{p,d}\) preserves K₀, Chow and rational Betti cohomology, including this nonzero square. On the affine coordinate ring the class has finite projective-module (idempotent) representatives by regularity. Thus the source survives algebraic affine replacement and is not merely an analytic vector bundle.

- **Exact finite machine audit:** \`research/computations/pure_algebraic_k0_all_codimensions.py\` evaluates the integral binomial coefficient \(q_{p,d}\), the primitive cycle ample degree and exact nonzero norm, and the rational Adams selector at all eigenvalues \(2^i\) for \(1\le p\le12\), \(2\le d\le30\): **348** cases. Its assertions use only Python exact integers and \`fractions.Fraction\` with no floating-point arithmetic or stochastic checks. The symbolic proofs above are all-p,d and independent of the finite sweep. CI: [#39052449104](https://github.com/kyo-oo/HC-PROOF/actions/runs/39052449104), to reconcile before claiming green.

- **Nearest previous source:** [Algebraic Adams selector and explicit degree-d cubic-fourfold-plane pure K₀ source](2026-10-17-universal-adams-k0-pure-chern-realization.md). This derivation removes the dimension-four restriction: every p has a complete original-X pure algebraic source and exact nonzero primitive measurement.

- **Mathematical boundary:** This constructs \(\xi_{p,d}\) on **explicitly chosen** smooth hypersurfaces, not a source for every prescribed \((X,p,\alpha)\). The Adams selector transforms existing algebraic sources but does not supply a source for a rational Hodge class that is not already in the algebraic K₀ image. The true remaining Gate-3 theorem is a geometric manufacturing operation for each original \(\alpha\), with exact canonical Chern comparison. That still must be proved for arbitrary X. No source-surjectivity premise has been introduced.

- **Next decisive test:** On an arbitrary original \(X\), extract incidence/degeneracy equations **from the prescribed rational primitive \(\alpha\)** that produce a genuinely nonambient finite projective module on \(J(X)\) and certify \(\operatorname{ch}_p(\xi)=\pi^*\alpha\). In particular, a mechanism using only the fixed tautological class or stably free Jacobian tangent module cannot pass this test; all remaining work must address the target-dependent nonambient source production.
