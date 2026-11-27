# Mathbox: actual projective-GST fold source, finite central descent, and surviving causal nerve cohomology

**Date:** 2026-10-23 (Asia/Kolkata). **Branch:** `research/gpt6-native-point-primitive-span-20261017`. **Base:** `2f93e744504b850b8f107c5e8f29e7ec47cd142a`.

## Exact original-X target and scope

Input ANY smooth projective complex original X of dimension d, any 2≤p≤d, any prescribed rational (p,p) Hodge class alpha. Target a genuine original-X rational Chow cycle Z with canonical Betti class alpha. Work only with the actual arbitrary-N GST affine incidence scheme J_N(X), not with an elliptic/CM fixture. Input alpha is NEVER postulated to have an algebraic preimage.

**Full mathematics:** [projective higher-causal descent manuscript](../derivations/GST_higher_causal_projective_descent_torsion_gerbe_2026-10-23.tex), created `4ff5a4d904ae9fde43738081c22425f8e261861d` and upgraded through `274f400186ef225dfa1fcdf946437ee2891b931f`.

## New direct theorem: source from projective geometry, with NO GL lifting assumption

The GST Oka fold constructs an honest holomorphic rank-r bundle H_alpha on J with FULL `ch(H_alpha)=r+m q^*alpha` and c1=0 rationally, for arbitrary original X and any p≥2.

**Crucial geometry-first breakthrough in proof format:** Suppose the genuine PGL_r projective-space bundle P(H_alpha) on J carries an ACTUAL coherent holomorphic higher-causal translation transport, so it descends to an actual holomorphic projective-space bundle `rho:Y_alpha→X`. Because X is projective, holomorphic PGL bundles algebraize (projective GAGA). This projective bundle need NOT be lifted to a rank-r vector bundle to build the genuine Chow source. Define the tautologically intrinsic rational Chow class `zeta=(1/r)c1^CH(T_(Y/X))` from the ACTUAL relative tangent bundle and the full projective Segre pushforward

`S_Y(t)=Σ_(k=0)^d rho_*(zeta^(r−1+k)) t^k in CH^*(X)_Q[t]/(t^(d+1))`.

Here S_Y(0)=1 from the actual fiber integral. The new exact direct source:

`Z_alpha = 1/(m(p−1)!) [t^p] log S_Y(t)∈ CH^p(X)_Q`.

**Proof of canonical Betti equality:** Locally for P(E), Euler sequence gives zeta=xi−c1(E)/r; formal Chern roots centered y_i=x_i−(Σx_j)/r; true projective-bundle Gysin yields `S_Y(t)=∏_i(1−y_i t)^−1`. Thus

`[t^p]log S_Y(t)= (p−1)!/p! Σ_i y_i^p`.

Because the Oka H has all positive ch except pth zero and p≥2, its rational mean root is zero, and this equals `m(p−1)!q^*alpha`. The affine fold q^* injects in rational cohomology. Proper Gysin pushforward and Chern comparison guarantee actual `cl_X^can(Z_alpha)=alpha`. Crucially this is an intrinsic PGL geometrical cycle construction **even if no actual vector-bundle GL lift of Y is chosen**. Odd higher p are retained (unlike adjoint End H invariants). A change of local lift E→E⊗L shifts all roots by a common c1(L), leaving their centered powers invariant exactly.

This is a meaningful lower-input geometric source theorem: older route required an actual GL lift and determinant compatibility; the new construction requires only the nonabelian PGL projective spatial fold and its actual coherence.

## Independently proved central descent, no additional source assumption

A second theorem handles projective descent plus determinant to a true GL bundle: the exact finite-central group extension `1→μ_r→GL_r→PGL_r×G_m→1` and the affine q homotopy equivalence show the finite μ_r-lifting obstruction for a pair (Q,L) vanishes on original X when it vanishes after pullback to actual J. Any residual torsion line M on Stein J with M^r=O pulls back from an original-X holomorphic line since q^*:H²(X,Z)→H²(J,Z) is an isomorphism and torsion has zero exponential obstruction. This constructs the genuine E on original X. For a rational Hodge class the original determinant L always exists (Lefschetz (1,1) and holomorphic exponential sequence), so one projective causal coherent fold is sufficient to produce the entire bundle or directly the projective Chow formula above.

## Genuine all-dimensional higher-causal nerve theorem

The actual higher-causal nerve is J_n=J×_X...×_XJ (n+1 factors), and every J_n is AFFINE because X is separated and J affine. Its alternating face cochain `δ = Σ_i(-1)^i d_i^*` has δ²=0 from actual cosimplicial identities. Faithfully flat affine Cech-Amitsur descent shows

`H^k(Γ(J_•,O),δ)≅H^k(X,O_X)≅H^(0,k)(X,C)` for EVERY k, every original X and every affine dimension N.

Thus for any original X with h^(0,2)>0, all individual J_n are Stein and have H^q(J_n,O)=0 for q>0, while the actual full two-cell nerve cohomology H²(Γ(J_•,O),δ) is NONZERO. This is an exact mathematical spatial-higher-causal result and directly exposes why stagewise Cartan-B vanishing is insufficient to force projective two-cell coherence. The nonabelian PGL obstruction is harder than this additive O case; its vanishing is not asserted.

## Wolfram independently executed exact projective geometry

[Actual committed Wolfram source](../computations/gst_intrinsic_pgl_projective_chow_segre_2026_10_23.wl), source blob `d4a3c388848c3dfc2399877829d9dcdd2deeba34`, executed via WolframLanguageEvaluator without errors:

- **35/35** independent exact rational projective Gysin residue sums match the centered-root projective Segre coefficients, ranks r=2..6, k=0..6.
- **25/25** exact centered-root log power calculations, r=2..6, p=1..5.
- **5/5** exact common line-twist invariance comparisons for all ranks 2..6.

These are finite checks supporting the splitting-principle all-rank symbolic proof, NOT assumptions of arbitrary-X projective descent.

## Existing native Lean kernel formalization

The REAL `GSTGraphV2UnboundedHigherCausality.lean` file was edited IN PLACE at commit `c3df713edc9ba72ef496b496d30db7a9f5265912`. `CausalProjectiveChern.centeredRoot_shift_invariant` and `centeredPower_shift_invariant` are meant to kernel-check the genuine projective characteristic's invariance under arbitrary line twist for every finite positive rank and every p. Initial GitHub Actions `39922996872` FAILED because the finite-sum body required explicit parentheses and the kernel did not accept the unexpanded `change` goal. Repaired the actual existing Lean file at exact commit `05a3c311c35c753f327698d51cfef5537697b5ad`. [GitHub Actions run **39923468726**](https://github.com/kyo-oo/HC-PROOF/actions/runs/39923468726) **COMPLETED SUCCESS** on that exact matching source SHA, with no Lean errors and the mandatory no-sorryAx gate passed; full run logs were read. This certifies both `centeredRoot_shift_invariant` and `centeredPower_shift_invariant` as kernel compiled. No local Lean installed or run. Scheme-level Gysin/GAGA theorem is proven mathematically in source, not kernel formalized as a Chow construction.

## Logical outcome, precise next independent claim

The source formula above is PROVED as a genuine conditional geometric theorem with strictly fewer hypotheses than previous GL-lift approaches. The spatial-fold existence, entire pure Chern character, determinant descent, scalar obstruction, and all-degree Hodge preservation are unconditional for every original X. The one currently independent Hodge-sensitive assertion is: **for each rational (p,p) alpha, construct some Oka projective PGL fold with an ACTUAL globally coherent two-cell transport along J→X**. This nonabelian coherence is not imposed by ordinary cohomological translation invariance. A full universal proof needs this implication with no Chow witness in the input; no statement here assumes its existence.

**Mathbox evidence label:** exact original-X projective Chow return theorem proved under typed PGL coherence; entire higher-causal nerve cohomology proven; universal PGL coherence construction incomplete. Audit is self-review, not independent external verification.

## New theorem after projective Gysin audit: entire rational PGL source invariant algebra

The intrinsic centered characteristic classes pch_p for 2≤p≤r freely generate the symmetric invariant polynomial ring in the centered Chern roots y_i=x_i−(∑x)/r. Proof is the fundamental theorem of symmetric polynomials with e1(y)=0 and invertible triangular Newton identities over Q. This means the **ENTIRE rational intrinsic characteristic spectrum** of an arbitrary rank-r projective PGL bundle, including odd p, is recovered by the projective Segre logarithm. The first explicit forms:
- `pch2=ch2−c1²/(2r)`
- `pch3=ch3−(c1/r)ch2+c1³/(3r²)`.
The direct original-X source formula is genuinely native to projective geometry and does not require a hidden choice of O(1) or a Brauer lift.

**Terminal evidence checkpoint:** Wolfram 35+25+5 exact rational tests passed; mathematical splitting-principle proof global and all ranks; native centered-root and centered-power line-twist invariance kernel compiled green at `05a3c311c35c753f327698d51cfef5537697b5ad`, CI #39923468726. The actual source-birth predicate is flat PGL projective translation coherence. No code or previous CI run on the branch is represented as proving global algebraic PGL coherence.
