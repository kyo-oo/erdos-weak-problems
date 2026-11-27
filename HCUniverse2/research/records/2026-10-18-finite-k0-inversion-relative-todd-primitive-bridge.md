# Mathbox — finite algebraic K₀ inverse, relative Todd-defect source, and original-X Chow comparison

**Date:** 2026-10-18. **Target:** for every original smooth projective complex X, p, and rational (p,p) alpha, construct a rational algebraic codimension-p cycle Z on X with the genuine canonical Betti class alpha. The following constructs universal *algebraic source operations*, not a representative chosen for an unknown alpha.

**Start checkpoint:** 5494f5550682f2117542df19b05e0481ff5c9062 on research/gpt6-native-point-primitive-span-20261017. **Source modules edited in place:** GSTUniversalResolvedSupportHodge.lean and GSTMaximalLinearHypersurfacePrimitive.lean. **New proof receipts:** dedicated GST Native K0 Original X Extraction and pinned full integration workflows on latest branch (record final run IDs and conclusions after verification). K3 Todd primitive dedicated proof passed [#39150216705](https://github.com/kyo-oo/HC-PROOF/actions/runs/39150216705). Earlier K0 source [#39147402899](https://github.com/kyo-oo/HC-PROOF/actions/runs/39147402899) green. No local Lean installation or external public web search.

## 1. Construct — do not postulate — the finite-flat K₀ inverse

Fix finite flat surjective f:X→P^n, d=deg f≥1. In actual rational algebraic K₀(P^n), let u=[f_*O_X], an algebraic rank-d vector bundle. Write u=d+η where η has rank zero. Let t=1-[O(-1)]∈K₀(P^n); the ring is Q[t]/t^{n+1}, so η^{n+1}=0. Set dinv=1/d∈Q. The inverse is a FINITE algebraic polynomial,

\[
\boxed{u^{-1}=d^{-1}\sum_{j=0}^n(-\eta/d)^j.}
\]

Check by multiplying u=d(1+\eta/d) and the geometric sum; the product is 1-(-\eta/d)^{n+1}=1. This needs no analytic completion, no supplied uInverse witness, and no representative for a desired Hodge class.

The new Lean namespace GSTNativeFiniteFlatK0Extraction contains:
- finiteGeometricSeries_identity, a general commutative-ring truncated geometric-series proof;
- finiteNilpotentBaseInverse and finiteNilpotentBaseInverse_correct, explicit polynomial and exact multiplication;
- finiteNilpotentVirtualPrimitive, native E↦E-f^*(u^{-1}f_*E);
- finiteNilpotentVirtualPrimitive_push_zero and finiteNilpotentVirtualPrimitive_image_iff_kernel, exact trace kernel characterization.

The abstract kernel identity applies after the official scheme-level algebraic K₀, projection formula and rank-zero nilpotency are instantiated. This is an actual computational formula on that geometric ring, rather than an existence assumption for u^{-1}. Lean debugging: generic CommRing does not have a predefined Inv typeclass; d^{-1} is therefore passed as the explicit *scalar* dinv satisfying d*dinv=1, while u^{-1} itself is constructed. Use the finite scalar inverse provided by rational K₀(P^n).

## 2. A genuine source invisible to the normalized K₀ projector: relative Todd defect

The normalized K₀ virtual source P_K(E) is an algebraic K-class on original X. Rational algebraic GRR constructs its Chow realization

\[
\Theta_X(E)=\operatorname{ch}(E)\operatorname{td}(T_f),
\qquad T_f=T_X-f^*T_{P^n}.
\]

GRR says \(f_*\Theta_X(E)=\operatorname{ch}(f_*E)\) and \(f_* \operatorname{td}(T_f)=\operatorname{ch}(u)\). Denote pulled-back Chow ring classes

\[
t=\operatorname{td}(T_f),\quad
U=f^*\operatorname{ch}(u),\quad
U^{-1}=f^*\operatorname{ch}(u^{-1}),\quad
S=f^*\operatorname{ch}(f_*E),\quad q=\Theta_X(E).
\]

The true Chow projector is \(P_{\rm CH}(q)=q-\frac1dS\), and the GRR realization of the normalized K₀ projector is \(\Theta_X(P_K E)=q-(U^{-1}S)t\). Their difference factors EXACTLY as

\[
\boxed{
P_{\rm CH}(q)=\Theta_X(P_KE)+U^{-1}S\;\Delta_f,\qquad
\Delta_f=t-\frac1d U.
}
\]

This is a literal polynomial identity using only U*U^-1=1. In GSTUniversalResolvedSupportHodge.lean it is checked by chow_projector_eq_K0_projector_plus_Todd_defect; the code proves it in EVERY commutative coefficient ring and tracks the exact condition under which the two projector formulas agree.

The *intrinsic* relative Todd defect is the actual algebraic original-X Chow class

\[
\boxed{\Delta_f=
  \operatorname{td}(T_X-f^*T_{P^n})
  -\frac1d\,f^*\operatorname{ch}([f_*O_X]).
}
\]

It has zero actual Chow pushforward by GRR and the finite-flat degree identity. It is defined independently of any Hodge target or target-specific E. It can be nonzero in primitive cohomology, unlike P_K(O_X)=0: since f_*O_X=u, P_K(O_X)=O_X-f^*(u^-1 u)=0. **The two algebraic source machines therefore have the same trace-zero image but different complements; one cannot identify their output expressions term by term.**

The factorization gives an ALL-X, ALL-p constructive source dictionary: a Chow-projected GRR class from any algebraic perfect E is an exact sum of a normalized algebraic K₀ source and an explicitly pulled-back algebraic class times the intrinsic Todd defect. Since both terms are genuine rational Chow classes on the ORIGINAL X, no cohomological contraction with alpha or nonalgebraic selector was inserted.

## 3. New exact Todd primitive on original equal-degree K3×K3

For X=S₁×S₂ with polarized K3 surfaces h_i²=2d, d>0, set H=h1+h2. We have c1(T_X)=0, so Todd_2(T_X)=c2(T_X)/12; the inverse Todd of f^*T_P contributes only ambient powers H, annihilated by P_CH. Consequently

\[
[\Delta_f]_2=\frac1{12}P_{\rm CH}(c_2(T_X)).
\]

The previous GST genuine algebraic Chern source Z=P_CH(c₂) satisfies HZ=0 and \(Z^2=768\). Therefore

\[
\boxed{H\,[\Delta_f]_2=0,\qquad [\Delta_f]_2^2=\frac{768}{12^2}=\frac{16}{3}>0.}
\]

This is a true original-X algebraic codimension-two primitive source on an infinite family, with no chosen Hodge target representative and no special plane or background codimension-two sheaf as data. GSTMaximalLinearHypersurfacePrimitive.lean was edited in place to add gstK3ProductRelativeToddPrimitive, gstK3_relativeToddDefect_is_primitive, gstK3_relativeToddDefect_norm and gstK3_relativeToddDefect_nonzero. Their all-d rational intersection identities passed the dedicated [Lean CI #39150216705](https://github.com/kyo-oo/HC-PROOF/actions/runs/39150216705). The genuine Chow/Todd construction and Chern–Betti comparison are mathematical geometric facts to be instantiated by the final actual-X Stage2G connector rather than simply inferred from a formal arithmetic identity.

## 4. Precise limit test: which geometric source is required next?

For a degree-d smooth hypersurface X⊂P^{n+1}, \(c(T_X)=(1+h)^{n+2}/(1+dh)\). Every intrinsic tangent/normal Chern, Todd and characteristic class built functorially from these bundles lies in the ambient subring Q[h], and P_CH kills that subring. Consequently the universal intrinsic Todd defect is ZERO on hypersurfaces, even when their primitive Hodge part is nontrivial. On an abelian variety the tangent bundle is trivial, and the same mechanism yields only pullbacks from P^n; thus it cannot create the exceptional Weil source solely from the intrinsic trivial bundle. Both examples show how to sharpen the actual source choice, **not** a failure of the algebraic projection theorem.

The next nonambient source therefore must be an actual *non-tautological* coherent/perfect complex E with nonzero primitive Chern character. In the repository's QM abelian fourfold case, an algebraic graph of an independently realized isogeny gives such a perfect complex \(E=[O_{\Gamma}]\). Its degree-two Chern character is the genuine codimension-two graph Chow class by GRR and rank/codimension support; the normalized finite-flat K₀ construction extracts its primitive part on the ORIGINAL abelian fourfold. This is a concrete bridge from the existing GST CM native geometry to the universal K₀/Chow source operators. The generic Weil source on arbitrary abelian fourfolds is not produced by the intrinsic Todd defect, so genuine graph/sheaf geometry remains the targeted next operation.

For the requested all-X Hodge theorem one ultimately needs, for *each* primitive rational Hodge alpha, a geometrically constructed algebraic E whose projected Chern/Todd class has nonzero suitable alpha pairing or completes its sector. The expression of a projector on an arbitrary input E does not supply that E. A completed verification must also replace the supplied H.cycleClass field by the real canonical Betti cycle-class construction.

**Mathbox evidence classification:** finite-polynomial inverse and Todd factorization proved at the rational ring level with Lean receipts subject to the latest focused CI; K3 primitive nonvanishing proved via actual intersection arithmetic; original-X actual algebraic Chern/Todd constructions grounded in standard Chow/GRR formulas; unconditional all-Hodge source selection remains under active investigation.
