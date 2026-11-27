# Mathbox Gate 3 — algebraic Adams purification of Chern sources in every codimension

- **Date:** 2026-10-17.
- **Base:** source branch research/gpt6-native-point-primitive-span-20261017, previously verified at commit d1003315265cadf6fadeed10bc8e4a75ec7d2213, Actions #39050631654, 247-module gate with no sorryAx.
- **Exact final theorem:** For every smooth projective complex X, every p, every rational Hodge class α∈H^(2p)(X,Q)∩H^(p,p), produce an actual rational algebraic codimension-p cycle Z on the ORIGINAL X with canonical cl_X(Z)=α.
- **Route task:** Manufacture from a **genuine algebraic** K0 class a rational K0 class with *only* the chosen ch_p, and realize that mechanism on the affine Jouanolou replacement of any original X. This is unconditional for every existing algebraic K0 source. Generating an appropriate source for every α is a distinct unresolved claim.

## Exact universal algebraic extraction: an Adams polynomial

For every smooth quasi-projective complex n-fold V, the rational algebraic K-group K0(V)_Q has Adams operations ψ². Under the canonical rational Chern character,
\[
 \operatorname{ch}_i(\psi^2\xi)=2^i\operatorname{ch}_i(\xi).
\]
For any integer 0≤p≤n define the **explicit rational polynomial**
\[
  L_{p,n}(t)=\prod_{\substack{0\le j\le n\\j\ne p}}
        \frac{t-2^j}{2^p-2^j}\in\mathbb Q[t].
\]
It has \(L_{p,n}(2^i)=\delta_{p,i}\) for every 0≤i≤n by direct factorization and distinctness of the powers of two. Define a **genuine rational algebraic K0 class** by finite algebraic operations:
\[
 \boxed{\xi^{\langle p\rangle}=L_{p,n}(\psi^2)\xi.}
\]
Since ch is compatible with addition and Adams operations,
\[
 \boxed{\operatorname{ch}_i(\xi^{\langle p\rangle})=
 \begin{cases}\operatorname{ch}_p(\xi),&i=p,\\0,&i\neq p.\end{cases}}
\]
This requires no choice of topological/holomorphic bundle and no source-surjectivity hypothesis. It is an explicit construction for **all n,p** on ANY smooth quasi-projective V, and commutes with algebraic pullback (hence with the affine Jouanolou projection). Its proof is the stated finite polynomial identity plus standard algebraic λ-ring Adams/Chern character naturality. Over the rationals, the pth Chern character of any algebraic K0 class is a rational Chow class, so the operation isolates the native codimension-p cycle without higher Chern-component contamination.

For n=4, p=2, Wolfram obtained the exact universal projector
\[
 L_{2,4}(t)=\frac{(t-1)(t-2)(t-8)(t-16)}{288},
\]
with values \((0,0,1,0,0)\) at \(t=1,2,4,8,16\). The proof for all n,p follows from the same factorization, rather than extrapolation.

## A nonambient nonzero pure-Chern source, every degree d

Take **any smooth degree-d hypersurface fourfold** \(X_d\subset\mathbb P^5\), d≥2, containing a projective plane \(P\). Let \(T=X_d\cap H_1\cap H_2\) be a general smooth codimension-two hyperplane section, \(C=X_d\cap H_1\cap H_2\cap H_3\) a general smooth codimension-three hyperplane section, and \(q\) a point. All are actual algebraic closed subschemes of the original \(X_d\). Their structure sheaves are perfect since X_d is smooth, and determine genuine algebraic K0 classes. Put
\[
 \boxed{\xi_d =
  d[\mathcal O_P]-[\mathcal O_T]
  -\frac{d-1}{2}[\mathcal O_C]
  -\frac{d(d^2-1)}{12}[\mathcal O_q]
  \in K_0(X_d)_{\mathbb Q}.}
\]

**Exact geometric Grothendieck–Riemann–Roch derivation:**
- The normal exact sequence for the plane is
  \(0\to N_{P/X_d}\to\mathcal O_P(1)^3\to\mathcal O_P(d)\to0\). Hence
  \(c_1(N)=(3-d)h_P\), \(c_2(N)=(d^2-3d+3)h_P^2\).
- The inverse Todd class is
  \[
    \operatorname{td}(N)^{-1}
    =1-\frac{3-d}{2}h_P+
      \frac{d^2-9d+15}{12}h_P^2.
  \]
  Thus the degree-four Chern-character component of [O_P] is [P], the degree-six component is \(\frac{d-3}{2}i_*h_P=\frac{d-3}{2d}h_X^3\), and degree-eight component is \(\frac{d^2-9d+15}{12}[q]\).
- For a complete intersection of two hyperplanes \(T\), the inverse Todd factor is \(((1-e^{-h})/h)^2=1-h+(7/12)h^2+\dots\). Thus \(\mathrm{ch}_2(\mathcal O_T)=h_X^2\), \(\mathrm{ch}_3(\mathcal O_T)=-h_X^3\), \(\mathrm{ch}_4(\mathcal O_T)=\frac7{12}h_X^4\).
- For \(C\), \(((1-e^{-h})/h)^3=1-\frac32h+\dots\), hence \(\mathrm{ch}_3(\mathcal O_C)=h_X^3\) and \(\mathrm{ch}_4(\mathcal O_C)=-\frac32h_X^4\).
- Finally \(\mathrm{ch}_4(\mathcal O_q)=[q]\). Since \(h_X^4=d[q]\), direct collection gives
  \[
  \boxed{\mathrm{ch}_0(\xi_d)=\mathrm{ch}_1(\xi_d)=
         \mathrm{ch}_3(\xi_d)=\mathrm{ch}_4(\xi_d)=0,\qquad
         \mathrm{ch}_2(\xi_d)=d[P]-h_X^2.}
  \]
  Both higher cancellations are identically zero as rational polynomials in d; Wolfram checked them symbolically.

The class \(Z_d=d[P]-h_X^2\) is a nonzero primitive algebraic Hodge (2,2) class: \(\int Z_d h_X^2=d\cdot1-d=0\), and its exact self-intersection, using \(P^2=d^2-3d+3\), is
\[
 \boxed{\langle Z_d,Z_d\rangle=d(d-1)^3>0\quad(d\ge2).}
\]
This is a concrete, pure Chern-character source manufactured **directly from algebraic structure-sheaf equations**, with no arbitrary lifted Hodge preimage.

## Passage to the universal affine replacement

For any smooth projective \(X\subset\mathbb P^N\), the affine Jouanolou bundle \(\pi:J(X)\to X\) is an affine-space torsor. Pullback induces integral Chow and K0 isomorphisms and a rational Betti homotopy equivalence. If a nonambient source (such as ξ_d above) is constructed by explicit original-X subvarieties, its pullback class on J(X) is a genuine algebraic K0 class. By smooth affine regularity, a class of perfect coherent sheaves is represented by a rational signed combination of **actual finite projective modules**, each the image of a polynomial idempotent matrix over the coordinate ring A=Γ(J(X),O). Thus the source admits algebraic projector representatives over A, not merely abstract holomorphic vector bundles. The corresponding Chern character remains \(\pi^*Z_d\).

## What remains to manufacture for arbitrary α

The Adams operation **purifies** any existing algebraic K0 class, but never conjures a new primitive Hodge direction from an ambient-only source. The explicit structure-sheaf example uses P, a genuine plane whose existence is independently checked from the equation of X_d. On arbitrary X, the problem is to synthesize an algebraic K0 element ξ(α) using only **geometric equations of X and the prescribed rational Hodge class α**, with
\[
 \mathrm{ch}_p(\xi(\alpha))=\pi^*\alpha
\]
on J(X), with no hidden Chow preimage or Hodge-surjectivity premise. This remains equivalent to the original conjecture, but the route now provides a fully algebraic **target normal form** and a complete universally valid algebraic purification operation.

**Decisive next experiment:** Construct genuinely nonambient projective modules from X-intrinsic incidence/degeneracy conditions, not just the universal tautological line or the (stably free) Jacobian tangent summand, and compare their Chern character with the primitive Hodge direction. The degree-d pure K0 formula above is the checked benchmark.
- **Proof status:** Complete classical mathematical proof of algebraic Adams purification (all X,n,p) and of the explicit degree-d pure K0 source on hypersurfaces containing a plane; exact Wolfram arithmetic confirms coefficients, no inference of universal Hodge-surjectivity from a successful benchmark.
