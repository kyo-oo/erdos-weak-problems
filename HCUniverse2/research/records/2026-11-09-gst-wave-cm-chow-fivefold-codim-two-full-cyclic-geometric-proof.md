# New GST single-fold geometric construction: wave plus CM phase on a smooth projective complex fivefold

**Date:** 2026-11-09. **Branch:** `research/gpt6-native-point-primitive-span-20261017`. **Focus:** the actual GST hypothesis; constructive original-X geometry rather than another abstract graph law. This record extends `2026-11-09-gst-entire-wave-cm-curvature-ncohomology-hypothesis-attack.md`.

## 1. The exact original-X target

Let

\[
X=(\mathbb P^1_{\mathbb C})^5,\qquad
h_i=\operatorname{pr}_i^*c_1(\mathcal O_{\mathbb P^1}(1)).
\]

Künneth/cohomology and the intersection ring give

\[
H^*(X,\mathbb Q)=\mathbb Q[h_1,\ldots,h_5]/(h_1^2,\ldots,h_5^2),
\qquad \deg h_i=2.
\]

Every class in H^4 is (2,2). The rational Hodge fiber

\[
W=H^4(X,\mathbb Q)\cap H^{2,2}(X)
\]

has dimension \(\binom52=10\). For each two-subset \(I\subseteq\{1,2,3,4,5\}\), let

\[
D_I=\prod_{i\in I}h_i\in\mathrm{CH}^2(X)_{\mathbb Q}.
\]

These are ten ACTUAL original-X algebraic codimension-two cycles. Their algebraic duals are the complementary degree-three classes \(D_{I^c}\in \mathrm{CH}^3(X)\) and satisfy the exact *geometric* intersection law

\[
\boxed{\int_XD_K D_{I^c}=\delta_{KI}}.
\]

Thus for each ordered pair of two-subsets I,J, define a **genuine algebraic Chow correspondence** of codimension five on the original product \(X\times X\):

\[
\boxed{\Gamma_{JI}=\pi_1^*D_{I^c}\cdot \pi_2^*D_J
\in\mathrm{CH}^{5}(X\times X)_{\mathbb Q}}.
\]

Via true proper pushforward and intersection product,

\[
(\Gamma_{JI})_*(D_K)
=(\pi_2)_*\big(\pi_1^*D_K\cdot
  \pi_1^*D_{I^c}\cdot\pi_2^*D_J\big)
=\delta_{IK}D_J.
\]

So \(\Gamma_{JI}\) realizes the entire ten-by-ten rational matrix-unit algebra on the true rational (2,2) sector. This is actual algebraic geometry, not a free cohomology operator. These correspondences are not asserted to be finite over the projections; the current `FiniteClosedCorrespondence` Lean interface alone does not cover them. Full-Chow canonical push-pull is standard mathematics; its formal Lean adapter is an additional implementation task.

## 2. Actual GST wave + Gaussian CM-like correspondence law

Order the ten algebraic cycles as

\[
D_{12},D_{13},D_{14},D_{15},D_{23},D_{24},D_{25},D_{34},D_{35},D_{45}.
\]

Let C be the four-by-four rational companion matrix of \(\Phi_5(t)=t^4+t^3+t^2+t+1\), and set

\[
S_8=\operatorname{diag}(C,C),\quad
J_8=\begin{pmatrix}0&-I_4\\I_4&0\end{pmatrix},\quad
J_2=\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
\]

Extend to the ten-dimensional ACTUAL rational Hodge sector:

\[
S=\operatorname{diag}(S_8,I_2),\quad
J=\operatorname{diag}(J_8,J_2),\quad
\boxed{T=S+J}.
\]

The equations

\[
\boxed{S^5=I_{10},\quad J^2=-I_{10},\quad SJ=JS}
\]

hold exactly, and the matrices S,J,T are each **realized by true algebraic Chow correspondences** on X×X: for any M put \(\Gamma_M=\sum_{I,J}M_{JI}\Gamma_{JI}\). Thus \(T\) is the genuine Betti action on W of the codimension-five algebraic correspondence \(\Gamma_T=\Gamma_S+\Gamma_J\). On the entire Betti cohomology, these particular correspondences act zero on degrees other than four; the displayed order-five and CM laws are assertions about W, NOT the whole Betti ring.

The label "Gaussian CM-like" here refers to the **actual rational correspondence algebra action J²=-I on W**. It does NOT assert that the product of projective lines is a classical CM abelian variety, nor that J comes from a CM self-isogeny; the algebraic action is still genuine and exact.

## 3. One original-X algebraic seed, full orbit, explicit determinant

Let

\[
\boxed{Z=D_{12}+D_{35}\in\mathrm{CH}^2(X)_{\mathbb Q}}.
\]

In the ordered basis, its rational Hodge class is \(v=e_1+e_9\). The exact ten-by-ten Krylov matrix

\[
\mathcal K=
\big[v,\ Tv,\ T^2v,\ldots,T^9v\big]
\]

has determinant

\[
\boxed{\det\mathcal K=10,292,525\ne0.}
\]

This was calculated with Wolfram using **exact integer/rational arithmetic**, not floating tolerances. The companion+CM block has irreducible degree-eight polynomial

\[
P_8(x)=x^8+2x^7+7x^6+10x^5+16x^4
 +10x^3-2x^2-4x+1.
\]

The other block has \(P_2(x)=x^2-2x+2\), and \(\gcd(P_8,P_2)=1\), furnishing an independent Chinese-remainder explanation of why the single seed cycles through all ten directions.

**Therefore** the actual native Chow orbit

\[
Z,\ \Gamma_{T*}Z,\ \Gamma_{T*}^2Z,\ldots,
\Gamma_{T*}^9Z
\]

is a rational basis of every rational (2,2) Hodge class on this **specified smooth projective complex fivefold**. For each target \(\alpha\in W\), solve \(c=\mathcal K^{-1} [\alpha]\), and the explicit cycle \(Z_\alpha=\sum_{r=0}^9 c_r(\Gamma_T)_*^r Z\) satisfies \(cl_X(Z_\alpha)=\alpha\).

This is a **genuine geometric instantiation of the one-fold cyclicity condition in codimension two** with GST order-five information dynamics and a rational CM-like phase operator. It is a proof for this particular X and p, not a universal construction on arbitrary X.

## 4. Why this cannot simply be repeated for arbitrary X

The geometry of X=(P¹)^5 is special: all ten Hodge basis cycles and their algebraic intersection duals are explicitly available. They give the full matrix-unit Chow correspondence algebra *before* selecting a fold.

For arbitrary X and primitive rational Hodge class alpha not already represented by known cycles, using this matrix-unit construction would require a complete algebraic Hodge basis and its duals. Supplying those is already the deep algebraic-source problem.

Hence the valuable generalizable piece is the **cyclotomic plus rational complex structure one-seed cyclicity mechanism**, while the missing general construction is a GST-derived source/return correspondence and primitive detector on X **without** pre-supplying basis cycles for missing Hodge classes.

Another precise distinction: `GSTGraphV2InformationRecovery.shuffle_five` is a local information-cell identity; the S action above is *modeled after* its \(\Phi_5\) cyclotomic sector. It is not proved to be the image of the **entire** seven-axis causal event graph under a geometry-preserving functor. That comparison is a further theorem to develop.

## 5. Reproducibility

The exact script `research/computations/gst_cm_wave_chow_fivefold_codim2_20261109.wl` was committed, fetched from GitHub, and executed verbatim using connected Wolfram Language. Outputs:
- 10 explicitly enumerated two-subsets, independent intersection table = \(I_{10}\): True;
- \(S^5=I\), \(J^2=-I\), \(SJ=JS\): all True;
- \(\gcd(P_8,P_2)=1\): True;
- Krylov determinant \(10,292,525\) and exact rank 10.

New Lean `GSTGraphV2IntegratedWaveCMGate.lean` (separate abstract native adapter) proves every arbitrary finite wave/CM/curvature word and every power of a mixed sum of **supplied genuine native cycle operators** commutes with the cycle-class map, plus the rank-one CM impossibility boundary. Its kernel verification is tracked at `https://github.com/kyo-oo/HC-PROOF/actions/workflows/gst-integrated-wave-cm-gate.yml`. This does **not** yet instantiate the full Chow correspondences \(\Gamma_M\) as a Lean data type.

## 6. The source-birth experiment that can now discriminate the hypothesis

On an original fourfold X, codimension two, isolate the primitive rational Hodge sector \(P^{2,2}(X)\). Build a GST/CM wave family of genuine Chow correspondences **without** an unknown basis-vector cycle as input. Compute canonical whole-Betti actions and test whether the spectral primitive projection of its real native seed orbit is cyclic. Use actual Hodge classes/periods and algebraic incidence/kernels; mere coordinate rephasing, CM period equalities, infinite formal wave rank, and abstract matrix-unit actions are not substitutes.

If that nontrivial original-X primitive test can be solved geometrically, it would establish a real new instance of the birth principle beyond explicit Tate/divisor-product sectors. That is the precise next point where new GST mathematics is required.


## 7. Stronger conclusion: the complete one-fold orbit law for ALL weights of this X

The same intersection-dual formula works for every codimension \(p\), not just p=2. For \(0\le p\le5\), the actual Hodge basis is \(D_I\) for all p-subsets \(I\subseteq\{1,\ldots,5\}\), with rank

\[
\boxed{\big(h^{0,0},h^{1,1},h^{2,2},h^{3,3},h^{4,4},h^{5,5}\big)
=(1,5,10,10,5,1).}
\]

The canonical algebraic dual is \(D_{I^c}\in\mathrm{CH}^{5-p}(X)\), with the same intersection pairing. Every matrix unit \(E_{J I}\) is realized by the codimension-five cycle \(\pi_1^*D_{I^c}\cdot\pi_2^*D_J\). Thus we can choose one single correspondence and one seed *at each weight*:

- **p=0 or p=5:** one-dimensional rational Hodge space; choose the identity correspondence on the Hodge class and the point/fundamental seed. All powers equal the initial class.
- **p=1 or p=4:** five-dimensional rational Hodge space; take the 5-cycle permutation matrix S₅ and seed first basis cycle. The exact Wolfram Krylov determinant is **1**, and \(S_5^5=I_5\). These odd-rank fibers use the pure GST information-wave cycle and **do not impose J²=-I on an odd-dimensional rational space**.
- **p=2 or p=3:** ten-dimensional rational Hodge space; use the exact wave+CM \(T_{10}=S_{10}+J_{10}\) above and seed the sum of basis cycles 1 and 9. Its exact Krylov determinant is **10,292,525**, and the whole 10-dimensional Hodge space is generated.
- **p>5:** H^{2p}(X,Q)=0 and CH^p(X)_Q=0; choose zero seed, and the zero Hodge fiber is cyclic vacuously.

Therefore, by a **fully concrete scheme of actual original-X Chow correspondences at every codimension**, the single-fold orbit hypothesis is established for this specified fivefold `X=(P1_C)^5`. No unknown Hodge class is used to choose the seed or operator. This is stronger than proving just the p=2 part: it provides a complete all-p instance of the exact GST law in a nontrivial five-dimensional smooth projective complex model.

This result does not assume a complex CM endomorphism on odd-dimensional rational Hodge fibers and does not require making the same correspondence act with the same matrix on all different weights.

Note that the toric product X already has its Chow and Hodge classes completely understood; this construction is a real GST-family mechanism/benchmark and a proof of the target law for this family, not evidence that arbitrary primitive X has such a geometric generator.

**Extra Wolfram verification:** exact 5×5 cyclic shift satisfies S₅^5=I₅; its seed orbit determinant is 1; the binomial ranks were computed as {1,5,10,10,5,1}.


## 8. Even stronger: ONE AND THE SAME actual GST correspondence works in EVERY weight on X

The six weight-specific operators above may be assembled into **one single algebraic correspondence on X×X** rather than six independent operators. This works because the product-of-projective-lines Chow ring contains actual **degree-selective** Künneth matrix units.

For each p=0,..,5, use the actual rational matrix \(M_p\) from Section 7:
\(M_0=M_5=[1]\),
\(M_1=M_4=S_5\),
\(M_2=M_3=T_{10}=S_{10}+J_{10}\).

Define the single codimension-five original-X algebraic correspondence

\[
\boxed{
\Gamma_{\mathrm{GST}}=
\sum_{p=0}^{5}\;
\sum_{|I|=|J|=p}
(M_p)_{J,I}\;
\pi_1^*D_{I^c}\cdot\pi_2^*D_J
\ \in \mathrm{CH}^{5}(X\times X)_{\mathbb Q}.
}
\]

Because \(D_{I^c}\) has cohomological degree \(2(5-p)\), its push-pull integral against a class of degree \(2q\) is zero unless \(q=p\). Therefore \(\Gamma_{\mathrm{GST}}\) acts on all rational Betti cohomology by the exact BLOCK-DIAGONAL linear operator

\[
\boxed{
T_{\mathrm{GST}}=
\operatorname{diag}(1,S_5,T_{10},T_{10},S_5,1)
}
\]

in the canonical even-degree Chow/Hodge monomial basis. Here all odd Betti degrees vanish. Every Hodge weight has the explicit native seed from Section 7, and powers of the SAME correspondence generate the ENTIRE rational (p,p) fiber at that weight.

**This is exactly a concrete all-weight instance of the one-correspondence GST fold-orbit law on X=(P1)^5.** It is stronger than the law's requirement \(\forall p\,\exists\Gamma_p\): we exhibit one \(\Gamma_{\mathrm{GST}}\) that works simultaneously across all weights, with one seed chosen separately per weight.

Wolfram exact block-matrix verification:

\[
\boxed{
\dim H^{\mathrm{even}}(X,Q)=32,\quad
\operatorname{rank}T_{\mathrm{GST}}=32,\quad
\det T_{\mathrm{GST}}=4\ne0.
}
\]

So the global GST correspondence is **rationally invertible on the full Betti cohomology**. In fact the inverse operator is also realized by a rational algebraic correspondence on this X using the same matrix units (take \(M_p^{-1}\) for each block). This is true algebraic-source information preservation at the whole-Betti correspondence level, not just the original local twelve-cell permutation. It is NOT asserted to be an isomorphism of schemes or to preserve cup product: an invertible Chow correspondence on cohomology is more general than a geometric automorphism.

This complete one-correspondence construction uses actual known Chow bases of the special toric product. It does not infer their existence from a dimensionless graph on arbitrary X.


### Complete all-weight verification packet

The committed exact Wolfram packet `research/computations/gst_single_global_chow_operator_fivefold_allweights_20261109.wl` was fetched from GitHub and executed verbatim. It reports the full sequence of Hodge ranks `{1,5,10,10,5,1}`, all six complementary Chow intersection pairing matrices exactly identity, **all six** cyclic-seed Krylov ranks `{1,5,10,10,5,1}`, all six Krylov determinants `{1,1,10292525,10292525,1,1}`, and the single full Betti correspondence matrix of dimension 32 with determinant **4** and rank **32**. Every check is exact rational/integer, with no floating tolerance.

The companion `GSTGraphV2IntegratedWaveCMGate.lean` has a completed kernel-green run [42663099970](https://github.com/kyo-oo/HC-PROOF/actions/runs/42663099970) at commit `9095fd43a772042faca6b01a34ecb5e0ec2d86ec`; it covers arbitrary mixed native wave/CM/curvature words, single-fold sum and iterates, exact cycle-class naturality, and rank-one CM incompatibility. The **particular 32-dimensional toric Chow action** is proved in the mathematical derivation via Künneth and intersection products, and its finite matrix algebra is exact Wolfram-verified; it has not been encoded as a full Chow-correspondence instance in Lean.
