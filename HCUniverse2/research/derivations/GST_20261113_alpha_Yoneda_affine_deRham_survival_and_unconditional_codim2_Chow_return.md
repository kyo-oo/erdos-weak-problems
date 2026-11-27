# GST algebraic Yoneda-to-affine survival, and an unconditional codimension-two original-X Chow RETURN

**Date:** 13 November 2026. **Starting checkpoint:** 71743c392d03ce214f079055819066e3e08793e0.  
**Permanent owner target:** for arbitrary smooth projective complex original \(X\), codimension \(p\), and prescribed rational \((p,p)\)-Hodge \(\alpha\), construct \(Z_\alpha\in CH^p(X)_{\mathbb Q}\) with canonical rational Betti class \(\alpha\). This paper derives a new exact boundary return and the next truly missing input; it DOES NOT claim unconditional universal alpha-to-cycle existence.

## 1. Actual original-X algebraic Yoneda source and its affine death

As proved in the companion algebraic Yoneda research file, a rational Hodge class \(\alpha\) gives an actual coherent derived morphism
\[
e_\alpha:\mathcal O_X\longrightarrow\Omega_X^p[p],
\qquad
[e_\alpha]\in \operatorname{Ext}^p_X(\mathcal O_X,\Omega_X^p)
\cong H^p(X,\Omega_X^p).
\tag{1}
\]

Fix a smooth very ample divisor \(i:D\hookrightarrow X\), and put \(j:U=X\setminus D\hookrightarrow X\). The complement \(U\) is a smooth affine algebraic variety.

**Theorem A (coherent-channel death on every affine complement).** For EVERY \(p\ge1\), the Yoneda extension restricts to zero in
\[
\boxed{
j^*e_\alpha=0\in
\operatorname{Ext}^p_U(\mathcal O_U,\Omega_U^p)
=H^p(U,\Omega_U^p)=0.
}
\tag{2}
\]
This holds for EVERY complex \((p,p)\)-coherent class, not merely rational Hodge classes.

**Proof.** Affine coherent/quasi-coherent sheaves have no higher Zariski cohomology. The sheaf \(\Omega_U^p\) is locally free and \(\operatorname{Ext}^p_U(\mathcal O_U,\Omega_U^p)=H^p(U,\Omega_U^p)\). The restriction map therefore vanishes. QED.

This does NOT imply that the rational Betti class \(j^*\alpha\in H^{2p}(U,\mathbb Q)\) vanishes; the Hodge-to-Dolbeault identification for projective \(X\) does not identify a single coherent Ext group with the entire algebraic de Rham cohomology of NONPROPER \(U\).

## 2. Real survival: primitive middle classes remain Betti-nonzero

**Theorem B (genuine cohomological survival with algebraic-Ext death).** Let \(d=\dim_\mathbb C X=2p\), \(p\ge1\), and let \(0\ne\alpha\in H^{2p}(X,\mathbb Q)\cap H^{p,p}(X)\) be primitive for an ample \(h=[D]\), so \(h\alpha=0\). For a smooth very ample \(D\) representing a positive multiple of \(h\),
\[
\boxed{
j^*\alpha\ne0\in H^{2p}(U,\mathbb Q)
\quad\text{but}\quad
j^*e_\alpha=0\in\operatorname{Ext}^p_U(\mathcal O_U,\Omega_U^p).
}
\tag{3}
\]
**Proof.** Localization gives
\(\ker(j^*:H^{d}(X)\to H^{d}(U))
=\operatorname{im}(i_*:H^{d-2}(D)(-1)\to H^{d}(X))\).
Weak Lefschetz gives \(H^{d-2}(X)\overset{\sim}{\to}H^{d-2}(D)\), and the projection formula identifies this image as \(hH^{d-2}(X)\). The primitive decomposition \(H^d(X)=P^d(X)\oplus hH^{d-2}(X)\) is direct. Since \(\alpha\) is nonzero primitive, it cannot lie in the kernel, so its Betti restriction is nonzero. The coherent restriction is zero by Theorem A. QED.

In particular the first genuinely open central dimension, \(d=4,p=2\), exhibits exact algebraic-coherent death AND nonzero algebraic-de-Rham/BETTI survival on the SAME original projective variety. This is an explicit structural warning against extracting a Chow cycle by restricting only the coherent Ext class to an affine world.

## 3. Full algebraic-de Rham carry of the surviving class

Because \(U\) is smooth affine, algebraic de Rham cohomology is the cohomology of GLOBAL algebraic forms:
\[
H^{2p}_{dR}(U)=
H^{2p}(\Gamma(U,\Omega_U^\bullet),d).
\tag{4}
\]
The canonical algebraic de Rham comparison maps \(j^*\alpha\) to a degree-\(2p\) class represented by an ACTUAL closed global algebraic \(2p\)-form \(\eta_{\alpha,U}\in\Gamma(U,\Omega_U^{2p})\).

**Theorem C (actual N-channel degree transfer, not Chow birth).** In the situation of Theorem B, the nonzero rational Betti class \(j^*\alpha\) has a nonzero algebraic de Rham representative \([\eta_{\alpha,U}]\) despite \(j^*e_\alpha=0\). The class has transferred from the projective Dolbeault bidegree-\((p,p)\) coherent channel to the total degree-\(2p\) global algebraic de Rham channel. Algebraic de Rham comparison and affineness prove this for all even-dimensional original \(X\), without an algebraic cycle. This is a typed geometric candidate for the owner's causal death/survival and independent N-hole readout.

## 4. ORIGINAL-X unconditional boundary return in codimension TWO

**Theorem D (sharp codimension-two return, arbitrary smooth projective X).** Let \(X\) be ANY smooth projective complex variety of dimension \(d\ge2\), let \(D\subset X\) be a smooth ample divisor, and \(U=X\setminus D\) with inclusion \(j\). For ANY prescribed rational \((2,2)\)-Hodge class \(\alpha\in H^4(X,\mathbb Q)\), 
\[
\boxed{
\alpha\in\operatorname{im}\bigl(CH^2(X)_\mathbb Q\xrightarrow{\operatorname{cl}^{\mathrm{can}}_X}H^4(X,\mathbb Q)\bigr)
\Longleftrightarrow
j^*\alpha\in\operatorname{im}\bigl(CH^2(U)_\mathbb Q\xrightarrow{\operatorname{cl}^{\mathrm{can}}_U}H^4(U,\mathbb Q)\bigr).
}
\tag{5}
\]
In particular, any independently constructed algebraic codimension-two cycle on the AFFINE \(U\) representing \(j^*\alpha\) produces a genuine codimension-two Chow cycle on the SAME original \(X\) with exact canonical rational Betti class \(\alpha\), with NO higher Hodge hypothesis and no guessed primitive inverse.

**Proof (actual cycle construction).** The forward direction follows by restriction. Conversely, take a genuine algebraic \(Z_U\in CH^2(U)_\mathbb Q\) with \(\operatorname{cl}_U(Z_U)=j^*\alpha\). Take the codimension-two scheme-theoretic closures of its finitely many irreducible components in \(X\) to obtain \(\bar Z\in CH^2(X)_\mathbb Q\). Then
\[
\delta=\alpha-\operatorname{cl}_X(\bar Z)
\in H^4(X,\mathbb Q)
\]
is rational Hodge of type \((2,2)\) and satisfies \(j^*\delta=0\). By the Betti localization/Gysin exact sequence of the smooth divisor \(i:D\to X\),
\[
\delta=i_*\gamma,\qquad \gamma\in H^2(D,\mathbb Q)(-1).
\]
The Gysin map is a morphism of pure polarizable rational Hodge structures (with the Tate twist). Its image is a rational Hodge substructure. Since the category of polarizable rational Hodge structures is semisimple, the Hodge morphism \(i_*\) admits a rational Hodge splitting on its image, so the rational Hodge vector \(\delta\) admits a rational **(1,1)** preimage \(\gamma_{\mathrm{Hdg}}\in H^2(D,\mathbb Q)\) with \(i_*\gamma_{\mathrm{Hdg}}=\delta\).
By the actual Lefschetz \((1,1)\) theorem for the smooth projective \(D\), choose an ACTUAL rational algebraic divisor \(T\in CH^1(D)_\mathbb Q\) with class \(\gamma_{\mathrm{Hdg}}\). Define
\[
\boxed{
Z_\alpha=\bar Z+i_*T\in CH^2(X)_\mathbb Q.
}
\tag{6}
\]
True Gysin/cycle-class naturality gives
\(\operatorname{cl}_X^{\mathrm{can}}(Z_\alpha)=
\operatorname{cl}_X(\bar Z)+i_*\gamma_{\mathrm{Hdg}}=\alpha\).
No algebraicity of \(\alpha\) on \(X\) was assumed. QED.

**Elementary injectivity alternative for the central \(d\ge4\) case.** Weak Lefschetz identifies \(H^2(D)\cong H^2(X)\), and Hard Lefschetz makes multiplication \(h:H^2(X)\to H^4(X)\) injective for \(d\ge4\). Therefore \(i_*:H^2(D)\to H^4(X)\) is injective. Hodge type of \(\delta=i_*\gamma\) then forces \(\gamma\) to be type \((1,1)\) by injectivity, without invoking semisimplicity. The resulting cycle (6) is the same exact construction.

## 5. Higher p boundary reduction and the precise remaining algebraization equation

The same proof works for codimension \(p\) provided the rational Hodge conjecture in codimension \(p-1\) holds on the smooth ample divisor \(D\). The only difference is that a boundary correction \(\gamma\in H^{2p-2}(D,\mathbb Q)\cap H^{p-1,p-1}\) must be represented by an actual \(CH^{p-1}(D)_\mathbb Q\) cycle before pushforward. This is an induction interface, not an automatic higher-codimension source.

For \(d=4,p=2\) and \(0\ne\alpha\) primitive, Theorems B–D specialize to:
\[
e_\alpha|_U=0,\quad
0\ne\beta=j^*\alpha\in H^4(U,\mathbb Q),\quad
\beta=[\eta_{\alpha,U}]_{dR},\quad
\boxed{
\beta\ \text{algebraic on }U\ \Longrightarrow\
\alpha\ \text{algebraic on original }X .
}
\tag{7}
\]
The prior original GST affine-middle Clifford/Bott research constructs, from the integral multiple of \(\beta\), a holomorphic rank-stable bundle on the Stein \(U\) whose rational \(\operatorname{ch}_2\) is \(\beta\). If a genuine ALGEBRAIC vector bundle or algebraic virtual \(K_0\)-class with that same \(\operatorname{ch}_2\) is independently constructed on \(U\), the canonical Chow Chern character supplies \(Z_U\), and (6) explicitly completes the original-X return. Thus the remaining first-central-case task is **projective-origin analytic-to-algebraic Clifford \(K_0\) realization on the affine complement**; the boundary return is now actually constructed, not deferred. The existence of the algebraic Clifford lift has NOT been proved.

## 6. Direct stress test of the earlier Yoneda projector strategy

The Yoneda extension \(e_\alpha\) and its rank-one matrix-unit projector in the companion file are genuine original-X algebraic coherent morphisms. However Theorem B shows even a NONZERO primitive original-X rational Hodge class can have its coherent Ext restriction die on affine \(U\) while its Betti class survives there. Therefore an argument that first restricts \(e_\alpha\) to affine \(U\), applies only coherent Ext and \(K_0\) operations there, and attempts to recover \(\beta\) is mathematically invalid: it starts from zero in the proposed coherent degree. A valid GST proof must retain the full de Rham/hypercohomological carry \(\eta_{\alpha,U}\) and construct an actual algebraic \(K_0\) class with its canonical period, not merely rebuild a zero Ext class.

**Evidence status:** Theorem A is affine coherent vanishing; B follows from genuine middle Lefschetz/Gysin; C is algebraic de Rham comparison; D is an unconditional explicit *return operation* from a supplied affine algebraic source to the original X, using semisimple polarizable Hodge structures and Lefschetz \((1,1)\). These are standard-mathematical hand proofs, self-reviewed, not Lean kernel formalizations. In the first central codimension-two case the ONLY unresolved arrow in this route is existence of the affine algebraic \(K_0\) representative for the prescribed projective-origin \(\beta\). This is not a proof of the unrestricted rational Hodge conjecture.

**Repository source interfaces:** earlier original-X projective primitive thimble survival, 2026-11-13 affine Clifford Oka birth, 2026-10-21 boundary Deligne construction, GSTUniversalChowRetractToTarget.lean, GSTHodgeSingleHypothesisConditional.lean, and the companion algebraic Yoneda file. No unrelated finite test varieties were substituted.


## 7. Stronger exact result: conservation of the ENTIRE codimension-two Hodge defect under the affine fold

Write
\[
W_X=Hdg^2(X)_{\mathbb Q}
=H^4(X,\mathbb Q)\cap H^{2,2}(X),\quad
A_X=\operatorname{im}(\operatorname{cl}_X^{\rm can}:CH^2(X)_{\mathbb Q}\to W_X),
\]
and let \(r=j^*:W_X\to H^4(U,\mathbb Q)\). Put \(A_U=\operatorname{im}(\operatorname{cl}_U^{\rm can}:CH^2(U)_{\mathbb Q}\to H^4(U,\mathbb Q))\).

**Theorem E (exact affine-defect conservation for arbitrary original X).** Theorem D implies both
\[
\boxed{\ker(r)\subseteq A_X,\qquad r(W_X)\cap A_U=r(A_X).}
\tag{8}
\]
Consequently restriction induces an ACTUAL isomorphism of rational vector spaces
\[
\boxed{
\frac{W_X}{A_X}\ \xrightarrow{\ \sim\ }\
\frac{r(W_X)}{r(W_X)\cap A_U}.
}
\tag{9}
\]
The same statement holds in codimension \(p\) whenever the Hodge conjecture is established in codimension \(p-1\) for the smooth boundary \(D\).

**Proof.** Since zero is an algebraic class on \(U\), Theorem D applied to any \(w\in\ker r\) proves \(w\in A_X\). Since the restriction of an original-X algebraic cycle is algebraic on \(U\), \(r(A_X)\subseteq r(W_X)\cap A_U\). Conversely if \(r(w)\in A_U\) for \(w\in W_X\), Theorem D constructs an ACTUAL original-X cycle representing \(w\), whence \(w\in A_X\) and \(r(w)\in r(A_X)\). These establish (8). The induced quotient map is surjective by definition, and injective because \(r(w)\in r(A_X)\) means \(r(w-a)=0\) for some \(a\in A_X\); then \(w-a\in\ker r\subseteq A_X\), hence \(w\in A_X\). QED.

**Exact research consequence.** The earlier original-X algebraic Yoneda extension \(e_\alpha\) dies on affine \(U\) for EVERY positive codimension, whereas the whole *nonalgebraic rational Hodge defect* in codimension two is preserved by the affine fold exactly. Thus the correct projective-origin GST affine world must retain the rational Betti/algebraic de Rham \(\beta=j^*\alpha\) as the nonzero source marker and force its ACTUAL affine algebraic \(K_0\) realization. No arithmetic scalar mass, flat Ext-cone, or unrestricted holomorphic Oka map is a substitute for this exact motivic charge.

Theorem E is a general localization-and-Hodge-theory deduction, **not** the missing proof that the quotient in (9) vanishes. It provides a direct equivalence between the original projective defect and the precise affine source-existence defect, with the boundary reconstruction already proved in Theorem D.
