# Mathbox Gate 3 — affine-to-original Chow cycle reconstruction in codimension two

- **Checkpoint:** 2026-10-17, branch research/gpt6-native-point-primitive-span-20261017.
- **Pinned original target:** Every rational \((p,p)\) Hodge class on every smooth projective complex \(X\), all codimensions \(p\), has an actual native rational algebraic representative under the canonical geometric Betti map.
- **Route:** Construct the affine cycle on \(U=X\setminus Y\), then algebraize the boundary discrepancy on \(Y\) and return a cycle on the **original \(X\)**.
- **Fixed domain:** Any smooth projective complex variety \(X\) and any smooth ample divisor \(i:Y\hookrightarrow X\); codimension \(p=2\). Let \(j:U\hookrightarrow X\) be the affine open complement, and let \(\alpha\in H^4(X,\mathbb Q)\cap H^{2,2}(X)\).
- **Independent geometric inputs:** The ordinary Chow closure operation \(\mathrm{clo}:CH^2(U)_\mathbb Q\to CH^2(X)_\mathbb Q\), the native cycle-class maps on \(U\) and \(X\), the analytic restriction \(j^*\), the localization exact sequence
  \[
    H^2(Y,\mathbb Q)(-1)\xrightarrow{i_*}H^4(X,\mathbb Q)
       \xrightarrow{j^*}H^4(U,\mathbb Q),
  \]
  rational strictness of the Gysin map on pure Hodge structures, and the classical Lefschetz \((1,1)\) theorem on \(Y\). The closure is defined by taking the irreducible subvariety closure of each codimension-two subvariety of \(U\); proper codimension remains two.
- **Exact source construction:** Suppose a genuine algebraic codimension-two cycle \(Z_U\in CH^2(U)_\mathbb Q\) has \(\operatorname{cl}_U(Z_U)=j^*\alpha\). Set \(C=\overline{Z_U}\) (a genuine codimension-two rational algebraic cycle on \(X\)), and \(\delta=\alpha-\operatorname{cl}_X(C)\). Betti/chow naturality gives \(j^*\delta=0\). Localization then places \(\delta\) in the image of \(i_*\). Because \(\delta\) is rational of Hodge type \((2,2)\), strictness of the Hodge morphism provides a rational \((1,1)\) lift \(\beta\) on \(Y\). Lefschetz \((1,1)\) yields a genuine algebraic divisor \(D_Y\) with \(\operatorname{cl}_Y(D_Y)=\beta\). Finally,
  \[
  \boxed{\ Z_X=C+i_*D_Y\in CH^2(X)_\mathbb Q,\qquad
          \operatorname{cl}_X(Z_X)=\operatorname{cl}_X(C)+\delta=\alpha\ . }
  \]
  The boundary divisor is independently constructed; only the affine cycle is an input.
- **All-X strength:** Holds for *every* smooth projective complex \(X\), not merely even-dimensional \(X\), because it only uses the degree-two Gysin source for \(p=2\). In contrast with direct hyperplane restriction (which annihilates primitive middle classes), the affine restriction \(j^*\alpha\) can retain nontrivial primitive information and is the quantity that must be algebraized.
- **Exact Wolfram audit:** Rational toy localization \(\mathbb Q^3\xrightarrow{R}\mathbb Q^2\) with \(R=\begin{pmatrix}1&0&0\\0&1&0\end{pmatrix}\) and support Gysin \(G=(0,0,1)^T\). Exactness \(\ker R=\operatorname{im}G\). Given \(\alpha=(2,-3,7)\), source affine class \((2,-3)\), and native closure class \((2,-3,4)\), the difference is \(G(3)\), and the corrected class is exactly \((2,-3,7)\). This finite-dimensional test checks degree, variance, sign and exactness; it is not a proof of affine source existence.
- **Lean implementation:** Existing \`GSTUniversalResolvedSupportHodge.lean\` now contains \`AffineCodimensionTwoLocalization\` with a genuine open-scheme morphism, a closure map on the actual native algebraic cycles of \(U\), true rational Betti restriction and the geometric localization kernel. The theorem \`affine_cycle_plus_divisor_boundary_represents_hodge_two\` returns a native original-\(X\) codimension-two cycle; \`all_hodge_two_of_affine_open_cycle_sources\` supplies an all-\(X\) codimension-two reduction when the independent affine source generator is provided.
- **Kernel status:** First integrated run [#39043756944](https://github.com/kyo-oo/HC-PROOF/actions/runs/39043756944) exposed a missing namespace for \`GeometricCycleClassSpine\`, causing Lean placeholders and a failed axiom audit. Repaired in commit \`12c5da64eee488d07fb8f91b03a05b94b69c8220\`; new run [#39043970122](https://github.com/kyo-oo/HC-PROOF/actions/runs/39043970122) pending/active at record creation. Do not claim Lean green before source-specific verification.
- **Independent analytic source route:** Since \(U\) is smooth affine complex it is Stein. Rational topological K theory provides, for any \(j^*\alpha\), a rational virtual topological vector-bundle class \(\xi\in K^0_{\mathrm{top}}(U)\otimes\mathbb Q\) with \(\operatorname{ch}(\xi)=j^*\alpha\) in degree four and zero in other degrees (rational Chern-character isomorphism for finite CW complexes). An actual topological bundle can be made holomorphic over Stein \(U\) via Oka–Grauert. The **decisive missing operation** is a genuine algebraic vector-bundle/K-theory representative of that rational topological class. The existence of a holomorphic bundle is not algebraic representability and the analytic-to-algebraic comparison on affine \(U\) must be proved, not presumed.
- **Exact Chern arithmetic:** For any rational topological K class with only \(\operatorname{ch}_p=\gamma\) nonzero,
  \[
  c(t)=\exp\!\big((-1)^{p-1}(p-1)!\gamma t^p\big),\quad
  c_p=(-1)^{p-1}(p-1)!\gamma.
  \]
  Wolfram checked \(p=1,\ldots,6\): multipliers \(1,-1,2,-6,24,-120\). In codimension two \(c_2=-\gamma\). If the topological K class algebraizes as an algebraic virtual bundle, the algebraic \(ch_2\) supplies the affine cycle needed above. Rational algebraic K0→Chow via the Chern character for smooth affine varieties gives the native cycle.
- **Next exact implication:** For every prescribed rational primitive \((2,2)\) class \(\alpha\), produce a rational algebraic K0 class on \(U\) with topological Chern character \(j^*\alpha\). This is a genuine new source problem on **the actual affine geometry of \(X\)**, not a declaration that an unknown cycle on X exists.
- **Adversarial equivalence check:** Under localization, affine-source representability of \(j^*\alpha\) for every rational Hodge \(\alpha\) is equivalent to projective codimension-two Hodge representability for that class: one direction uses the explicit closure-plus-boundary theorem; the converse restricts any existing native projective cycle to U. Therefore the current reconstruction is a substantive *explicit reduction and algorithm*, not itself a universal Hodge proof. Any universal statement that assumes the affine generator is tautological until that generator is actually constructed.
- **Scope verdict:** Mathematically proved affine-to-original correction from independently standard geometry; Lean interface compilation pending. Topological/Stein bundle lift is standard geometric input not yet formally instantiated; algebraic bundle realization is the isolated unproved source-birth step.
- **Stop rule:** No new symbolic finite-rank cases or abstract correspondence-equivalence lemmas unless they create the affine algebraic source, prove a geometric algebraization step, or identify a counterexample to the proposed algebraization mechanism.

## Adversarial source-selection: holomorphic does not imply algebraic on Stein affine varieties

The rational topological K-class \(\xi\) of the restricted Hodge target \(j^*\alpha\) can be represented on a smooth affine \(U\) by a holomorphic virtual bundle (rational Chern-character isomorphism, Oka–Grauert). However, **there is no unconditional holomorphic-to-algebraic vector bundle upgrade on arbitrary affine \(U\)**.

Concrete independent test: let \(U=(\mathbb C^*)^2=\operatorname{Spec}\mathbb C[x^{\pm1},y^{\pm1}]\). Its coordinate ring is a localization of the polynomial UFD \(\mathbb C[x,y]\), hence remains a regular UFD and has algebraic \(\operatorname{Pic}(U)=0\). On the other hand \(U^{an}\simeq(S^1)^2\) is Stein and has \(H^2(U^{an},\mathbb Z)\simeq\mathbb Z\); the analytic exponential sequence plus Cartan theorem B gives \(\operatorname{Pic}_{hol}(U^{an})\simeq H^2(U^{an},\mathbb Z)\simeq\mathbb Z\). Thus nontrivial holomorphic line bundles on \(U\) have no algebraic representatives, **even after rationalizing \(c_1\)**. Wolfram checked \(P_U(t)=(1+t)^2\), \(b_2(U)=1\), and \(E_c(U)=(uv-1)^2\), agreeing with the exact ranks.

The actual Gate 3 target is *more specific* than algebraizing an arbitrary topological bundle: \(\xi\) must be the pure-Chern-character lift of \(j^*\alpha\) for a **projective rational \((p,p)\) Hodge class**. On this torus, \(H^2(U,\mathbb Q)=\mathbb Q(-2)\) is pure weight four, whereas projective \(H^2(X)\) has pure weight two. Therefore this Picard counterexample does not disprove algebraization for those projective-origin Hodge restrictions; it only refutes the **blanket Oka \(\Rightarrow\) algebraic** step. A valid general argument needs an independent algebraic comparison for that restricted pure-weight summand, or another source-generation mechanism.

**Status:** route filter passed (an incorrect strengthening was eliminated). The primary source requirement remains constructing the *affine algebraic* codimension-\(p\) representative in the precise projective-origin Hodge subspace, which is equivalent to the remaining conjectural source assertion.

## Sharp affine weight target and all-codim algebraic induction

For a smooth projective \(X\) and a smooth boundary divisor \(Y\), the mixed Hodge structure on \(U=X\setminus Y\) satisfies the lowest-weight image identity
\[
\operatorname{im}\bigl(H^{2p}(X,\mathbb Q)\xrightarrow{j^*}H^{2p}(U,\mathbb Q)\bigr)
= W_{2p}H^{2p}(U,\mathbb Q).
\]
Here the equality follows from the Deligne mixed-Hodge localization sequence and strictness of its weight filtration: the first term is pure weight \(2p\), whereas the connecting image enters weight at least \(2p+1\). The subspace relevant to the Hodge conjecture is the rational \((p,p)\) part of this **lowest weight**, not the arbitrary holomorphic K-theory of \(U\). The holomorphic nonalgebraic torus example above lies in \(H^2(U)\) of weight four and is excluded automatically when \(p=1\).

The new theorem \`affine_boundary_induction_constructs_original_hodge_cycle\` in \`GSTUniversalResolvedSupportHodge.lean\` proves the all-\(p\) successor formula from exact Chow/Betti localization:
\[
Z_X=\overline{Z_U}+i_*D_Y,\quad D_Y\in CH^{p-1}(Y)_{\mathbb Q}.
\]
It needs the **strictly lower weight** rational Hodge theorem in codimension \(p-1\) on \(Y\), together with a genuine algebraic cycle \(Z_U\in CH^p(U)_{\mathbb Q}\) realizing \(j^*\alpha\). Its generated cycle lives on original X. [GitHub Actions #39044347980](https://github.com/kyo-oo/HC-PROOF/actions/runs/39044347980) compiled the 247-module gate at SHA \`037e7644c69459c242717b7c3b9998952caf880a\`, with the sorryAx audit passing. Evidence artifact 12105028521, SHA256 \`6ed9913f3ba7879bbf5f6568a6208b93ca52a9c6bb04b31a040e9c714b908cda\`.

**Focused next construction:** Build genuine algebraic K-theory/Chow generators for the lowest-weight \((p,p)\) classes \(W_{2p}H^{2p}(U)\) that arise by restriction from the prescribed original X; avoid the false blanket claim that Oka makes all holomorphic bundles algebraic. This is an exact source-birth problem on the affine open, with a completely verified cycle-level return to original X once solved.
