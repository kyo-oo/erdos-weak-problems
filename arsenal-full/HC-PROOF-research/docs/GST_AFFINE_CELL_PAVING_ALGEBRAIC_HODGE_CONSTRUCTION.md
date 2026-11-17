# GST primitive-cycle construction from affine cell pavings

**Target:** actual rational algebraic representatives of every Hodge class on broad families of smooth projective complex varieties, with NO assumption that every Hodge class has a preimage.

**Status:** complete classical mathematical argument for varieties with an independently given **algebraic affine paving**. The geometric statements about Borel–Moore homology and localization are not currently Lean-formalized in HC-PROOF. New exact Lean kernels for two complementary cases are:
- \`GSTQuadricPrimitiveRulingGeometry.lean\` — primitive middle cycles on ALL even quadrics; [focused CI 38721017545 — SUCCESS](https://github.com/kyo-oo/HC-PROOF/actions/runs/38721017545).
- \`GSTDivisorWordRealization.lean\` — native cycles from finite polynomial words in genuine algebraic divisor classes; inspect focused CI before claiming success.

## Geometric theorem (every dimension, all codimensions)

Let \(X\) be any smooth projective complex variety with a finite sequence of **closed algebraic subvarieties**

\[
\varnothing=X_{-1}\subset X_0\subset\dots\subset X_N=X
\]
such that each successive difference \(U_i=X_i\setminus X_{i-1}\) is isomorphic over \(\mathbb C\) to an affine space \(\mathbb A^{k_i}\). No Chow-to-Hodge surjectivity hypothesis appears in this definition; a paving is a concrete geometric stratification.

For an affine space \(\mathbb A^k\), complex Borel–Moore homology has exactly one nonzero rational group: \(H_{2k}^{BM}(\mathbb A^k,\mathbb Q)\cong\mathbb Q\). Use the actual localization long exact sequence for the closed–open pair \((X_{i-1},U_i)\):

\[
\cdots\to H^{BM}_r(X_{i-1})\to H^{BM}_r(X_i)
\to H^{BM}_r(U_i)\xrightarrow{\partial}
H^{BM}_{r-1}(X_{i-1})\to\cdots.
\]

Inductively, \(H^{BM}_{\text{odd}}(X_{i-1},\mathbb Q)=0\) and the previous cell closures are a rational basis in even homology. Since the unique nonzero homology of \(U_i\) occurs in even degree \(2k_i\), the connecting arrow \(\partial\) targets an odd group and vanishes. Thus one new independent rational generator is added at degree \(2k_i\). The fundamental class of the **actual algebraic closure** \(\overline{U_i}\subset X_i\) maps to this open-cell generator. Consequently the fundamental classes of all cell closures provide a rational Borel–Moore homology basis of \(X\).

Because \(X\) is smooth projective of dimension \(d\), it is compact and Poincaré duality identifies the homology class of the cell closure \(\overline{U_i}\) of complex dimension \(k_i\) with the **cohomological cycle class** of the actual codimension-\((d-k_i)\) algebraic subvariety:

\[
\operatorname{cl}_{d-k_i}([\overline{U_i}])
\in H^{2(d-k_i)}(X,\mathbb Q).
\]

These cycle classes span \(H^{2p}(X,\mathbb Q)\) for each \(p\), and odd Betti cohomology vanishes. In particular every rational Hodge \((p,p)\) class \(\alpha\) has a unique expansion (after a chosen cellular basis)

\[
\alpha=\sum_{i:\,k_i=d-p}q_i\,
\operatorname{cl}_p([\overline{U_i}]),\quad q_i\in\mathbb Q.
\]

**Constructed cycle:**

\[
\boxed{Z_\alpha=\sum_{i:\,k_i=d-p}
q_i[\overline{U_i}]\in \mathrm{CH}^p(X)_\mathbb Q,
\qquad \operatorname{cl}_p(Z_\alpha)=\alpha.}
\]

The \(\overline{U_i}\) are actual algebraic subvarieties fixed by the paving, NOT reverse-engineered from \(\alpha\). The coefficients come from ordinary rational coordinates in a separately certified geometric homology basis. This constructs **every primitive and nonprimitive rational Hodge class in every codimension**, for every smooth projective complex variety carrying such an affine paving.

## Important concrete classes

Smooth complex projective quadrics, generalized flag varieties and Grassmannians have classical finite Schubert cell pavings. Smooth projective toric varieties admit appropriate algebraic affine pavings from torus actions. Each family exists in arbitrarily high complex dimension. All of their rational Hodge classes have actual algebraic representatives from the cellular closures (Schubert varieties or torus-invariant strata).

A generic smooth projective variety **does not** come with an affine paving. The claim that every smooth projective complex variety admits a finite affine paving is false: for example, many varieties have nonzero odd-degree Betti cohomology or non-\((p,p)\) Hodge components, whereas an affine-paved smooth projective variety has only even, Tate-type cohomology. Thus one must not use this to claim the full Hodge conjecture for arbitrary \(X\).

## Remaining primitive Hodge obstruction for arbitrary X

The universal target remains: build native algebraic cycles for **primitive rational Hodge classes not accounted for by any verified cellular, divisor-generated or CM family**.

The full GST CM–NM graph operations preserve existing algebraic cycle images. Without a new independently constructed geometric correspondence, incidence cycle, rational period comparison or target-specific algebraic subvariety, their internal transformations cannot prove a previously unknown Hodge class is algebraic. In particular:
- arbitrary primitive classes need not lie in the algebra generated by divisors;
- arbitrary smooth projective varieties are not CM abelian powers, cellular varieties or finite images of a fixed CM elliptic power;
- a Lean theorem whose hypothesis is Hodge-fiber cyclicity, realization of an arbitrary primitive, or surjectivity of the cycle-class map does not discharge this missing step.

**Scope verdict:** every Hodge class on affine-paved smooth projective varieties is explicitly algebraic; original universal Hodge conjecture for *all* smooth projective complex varieties remains open.

**Contributor attribution:** intentionally anonymous.
