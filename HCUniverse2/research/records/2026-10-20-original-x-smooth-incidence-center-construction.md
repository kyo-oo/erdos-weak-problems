# Original-X smooth incidence centers and prescribed primitive residuals

**Work package:** `GST-ORIGINAL-X-SMOOTH-CENTERS-20261020`.  
**Base:** `dbde8210a1b13a36aefafbd22c8fa06cc067a080`.  
**Requested target:** for every original smooth projective complex X and every prescribed nonzero rational primitive Hodge residual r, construct a genuine algebraic center whose native output on X has nonzero polarized period against r.  
**Outcome:** the universal **bundle-to-smooth-center constructor** and its exact original-X return are established below. Universal existence of a bundle/center with nonzero prescribed residual period is **not proved**. The intrinsic tangent/diagonal-normal candidate is tested and fails on the nonzero Weil plane. Do not report the conditional source compiler as the requested universal existence theorem.

This continues the [interacting blowup construction](2026-10-20-gst-interacting-blowups-connected-arbitrary-rank.md) on the same research branch. No public web search, subagent, local Lean installation, or manuscript integration was used.

## 1. Precise primitive period and route tests

Let dim X=n, 1<=p<=n/2, h a genuine ample divisor, and

\[
 r\in H^{2p}(X,\mathbb Q)\cap H^{p,p}(X),\qquad
 h^{n-2p+1}r=0.
\]

Define ell_r(u)=(-1)^p integral_X r u h^(n-2p), for codimension-p algebraic classes u. For every codimension-(p-1) class v,

\[
 \ell_r(hv)=0.
\]

This is the exact cancellation used below. It does not assert h r=0 outside middle dimension. A residual in the current Lean projection packet is not automatically Lefschetz primitive solely because its function is named `primitiveResidual`; the geometric caller must verify this primitive condition.

| Executed route | First discriminator | Outcome |
|---|---|---|
| Universal primitive diagonal and exceptional slicing | Does the operation give a one-sided native class, rather than a pairing using r on both factors? | Existing diagonal detector already gives the two-sided pairing; not relabelled as a new center constructor |
| Bundle sections, rank compression, smooth incidence and exceptional return | Compute the whole projective push and primitive twist terms | Positive construction in every X and p for every independently algebraic bundle |
| Intrinsic tangent/normal-bundle supply for that constructor | Does a nonzero primitive Weil residual pair with its actual returned center? | Zero, by an exact eight-generator exterior calculation; only this supply family is ruled out |

## 2. Universal rank-n smooth incidence construction

Start with an **actual algebraic vector bundle** E on X. Twist E by O(mh) until it is globally generated, then adjoin trivial summands to make its rank R>=n. Choose R-n general algebraic sections. Their rank-drop locus has expected codimension n+1>n, hence is empty. They define an algebraic subbundle O^(R-n), with globally generated locally free quotient V of rank n and

\[
 c(V)=c(E\otimes O(mh))
\]

The trivial summands are adjoined **after** twisting, so they do not alter this Chern identity. There is no target class or topological-to-algebraic bundle assumption in this operation.

Choose n-p+1 general sections s_i of V. In the fixed projective ambient world

\[
 W=X\times\mathbb P^{n-p},
\]

form the actual closed incidence zero scheme

\[
 \boxed{S=\{(x,[\lambda]):\textstyle\sum_i\lambda_i s_i(x)=0\}.}
\]

It is the zero scheme of a section of the globally generated rank-n bundle pr_X^*V tensor O(1). Generic smoothness/Bertini gives S smooth of dimension n-p, or empty. This follows directly from the universal evaluation map: at each (x,[lambda]), variations of the section tuple surject onto V_x since some lambda_i is nonzero and V is globally generated.

With xi the projective hyperplane, the actual top Chern class is

\[
 [S]=c_n(\mathrm{pr}_X^*V\otimes O(1))
     =\sum_{i=0}^n\mathrm{pr}_X^*c_i(V)\xi^{n-i}.
\]

Projective integration extracts the coefficient of xi^(n-p). Therefore

\[
 \boxed{(\mathrm{pr}_X)_*[S]=c_p(V)\quad\text{in }CH^p(X).}
\]

S has codimension n in W. Let rho:Bl_S(W)->W with exceptional divisor F. The same genuine proper blowup sign as in the previous work gives

\[
 \boxed{(\mathrm{pr}_X\rho)_*(F^n)=(-1)^{n-1}c_p(V).}
\]

This returns a genuine native class on the prescribed original X; the center is not another unrelated base variety. The ambient dimension 2n-p is fixed by X,p, independently of the rank and number of bundle summands. For n>=2 the blowup is an ordinary higher-codimension smooth-center blowup. The codimension-one case has the corresponding Cartier-divisor identity without a new birational world.

## 3. Direct smooth centers INSIDE the original X in middle dimension

The determinantal locus D of the n-p+1 sections has first rank drop of codimension p. Its next rank stratum has expected codimension 2(p+1). Thus if

\[
 n\le 2p+1,
\]

the next stratum is absent for general sections. D is smooth and the incidence map S->D is an isomorphism: the kernel line is unique at each point. In particular for **every middle-dimensional primitive problem n=2p**, this constructs a smooth center D **inside the original X**, with [D]=c_p(V). For the blowup rho:Bl_D(X)->X,

\[
 \rho_*F^p=(-1)^{p-1}[D],\qquad
 (-1)^{p-1}\ell_r(\rho_*F^p)=\ell_r(c_p(V)).
\]

The direct smooth-subvariety statement is not asserted outside this dimension range. The smooth incidence center with proper native pushback remains available in every dimension.

## 4. Twisting preserves the complete prescribed primitive period

For an algebraic rank-R bundle,

\[
 c_p(E(mh))=\sum_{i=0}^p
 \binom{R-i}{p-i}(mh)^{p-i}c_i(E).
\]

Every term except i=p has a positive factor h. Hence

\[
 \boxed{\ell_r(c_p(V))=\ell_r(c_p(E)).}
\]

The globally generated twist is thus a genuine smooth-center replacement with exactly preserved residual period. Rank compression preserves the entire Chern class. This removes global generation, arbitrary high rank, singular determinantal geometry in middle dimension, and twist contamination from the center-construction step. It supplies no reason that the final period must be nonzero for an arbitrary r.

## 5. A finite positive-copy center packet for every Chern character

For p>=1, let f(t)=[z^p]c_z(E)^t. It is a polynomial of degree at most p and f(0)=0. Differentiating at zero gives

\[
 f'(0)=[z^p]\log c_z(E)=(-1)^{p-1}(p-1)!\operatorname{ch}_p(E).
\]

Lagrange interpolation at the integer nodes 0,1,...,p gives

\[
 f'(0)=\sum_{j=1}^p\frac{(-1)^{j-1}}j\binom pj f(j).
\]

Indeed the j-th Lagrange basis polynomial with j>0 has derivative at zero (-1)^(j-1) binom(p,j)/j; the value at zero contributes nothing because f(0)=0. Since f(j)=c_p(E^\oplus j),

\[
 \boxed{\operatorname{ch}_p(E)=\frac1{(p-1)!}
 \sum_{j=1}^p\frac{(-1)^{p+j-2}}j\binom pj\,c_p(E^{\oplus j}).}
\]

Every j is positive: the smooth-center constructor uses ordinary bundles, not a purported geometric negative-rank bundle. Apply the construction separately to these p bundles. Their actual native center returns C_j obey the same identity after applying ell_r. A nonzero ch_p(E) period therefore selects one center with nonzero period by testing a finite list. No supplied target-cycle preimage is used.

For p=2, set a=ell_r(C_1), b=ell_r(C_2). Then

\[
 q=\ell_r(\operatorname{ch}_2(E))=b/2-2a.
\]

Select C_1 when a!=0, otherwise C_2. This selected center detects whenever q!=0. The actual rational native cycle a C_1+b C_2 has period a^2+b^2, and the exact sharp identity is

\[
 17(a^2+b^2)-4q^2=(a+4b)^2\ge0.
\]

Thus its period is at least 4q^2/17. This is a uniform algebraic estimate, not a determinant or positivity premise.

For general p, Cauchy gives center energy sum_j a_j^2 >= q^2/sum_j w_j^2 for the displayed explicit weights. Also sum_j w_j^2 <= (binom(2p,p)-1)/((p-1)!)^2, giving a positive coarse bound in every p. These unrestricted interpolation/Cauchy conclusions have the displayed mathematical proofs; Lean currently checks the complete all-p push/twist laws and the sharp p=2 estimate, not the whole all-p interpolation argument.

**Native period completeness.** Every actual codimension-p cycle has its class as the leading ch_p of its perfect structure sheaf; on smooth projective X this sheaf admits a finite resolution by algebraic vector bundles. Applying the preceding finite packet to those bundles expresses its primitive period as a rational combination of constructed smooth-center periods. Conversely each center return is itself algebraic. Thus the catalogue of these centers tests precisely the same primitive periods as the entire native Chow image. This is not completeness for the whole Hodge space. In particular, enumerating sections of a fixed bundle or increasing its twist does not prove a new nonzero period exists.

## 6. Positive equation-driven benchmark with an explicit twist

Use the repository's [existing plane syzygy bundle](2026-10-17-plane-syzygy-bundle-native-chern-source.md) on a smooth degree-d hypersurface fourfold X_d containing a plane P, d>=2. If F=sum ell_i q_i, its syzygy bundle E has c1=-3h, c2=3h^2-[P]. Its graded syzygies are generated by the three degree-two Koszul relations and the degree-d relation (q_i): any lifted relation differs from a multiple of (q_i) by a Koszul relation. Therefore

\[
 O_X(-2)^3\oplus O_X(-d)\twoheadrightarrow E,
\]

so **E(d) is globally generated**, with a concrete twist. A general section produces a smooth surface S_d in the original X_d, with

\[
 [S_d]=(d^2-3d+3)h^2-[P].
\]

The equation-relation section is nonzero on P, since otherwise X_d would be singular there. Nonvanishing on the proper P is an open condition on sections, compatible with generic smoothness; S_d can be chosen disjoint from P.

For Z_d=d[P]-h^2, the known plane normal bundle gives P^2=d^2-3d+3, h^2P=1 and h^4=d. Thus

\[
 Z_d\cdot[S_d]=-(d-1)^3,\quad h^2[S_d]=(d-1)^3>0,
 \quad\deg\rho_*(\rho^*Z_d F^2)=(d-1)^3>0.
\]

For E+E the second center period is -2(d-1)^3, so q=(d-1)^3 and the target-selected center energy is 5(d-1)^6. These are all-d identities, not a claim of a fresh native direction beyond the already known plane sector. This benchmark verifies the new center construction; it is not a replacement objective.

## 7. The unseeded intrinsic candidate fails the original hard test

On an abelian n-fold the tangent and cotangent bundles are trivial. Their tensor/Schur bundles, followed by twists in a single polarization, have Chern classes in Q[h]. Their returned center periods vanish against primitive r.

The code independently implements the actual eight-generator rational exterior algebra of the Weil-type fourfold chart, with theta=sum_j epsilon_j u_j v_j, epsilon=(1,1,-1,-1). The real and imaginary parts of product_j(u_j+i v_j) have primitive Gram diag(8,8) and wedge to zero with theta. For all such tangent-derived twisted bundles, c2=binom(R,2)m^2 theta^2, whose two exact Weil periods are zero. This is an actual nonzero primitive target test, not a zero vector or a definition of its period as zero.

**Scope:** this rules out the tested intrinsic tangent/normal-bundle supply, all its trivial-bundle Schur copies and single-polarization twists. It does not rule out other algebraic bundles, other Hilbert components or other interacting GST centers. It supplies no rational Hodge counterexample.

## 8. Exact universal obligation and evidence

The missing selection is now explicit: on the prescribed original X and nonzero primitive residual r, find an **algebraic** E with ell_r(ch_p(E))!=0. Once such E is constructed, the finite packet above constructs and selects a smooth detecting center, in original X itself in middle dimension. Replacing E by a topological or holomorphic bundle, assuming the required period is nonzero, or assuming a target-directed correspondence would not establish this selection. The general claim remains open at this checkpoint.

The untried continuation is a component-changing original-X sheaf/incidence construction supplying such a bundle class beyond the intrinsic Chern/polarization catalogue. Changing sections, twist, rank, or the number of copies inside the failed intrinsic family is not that change. The next acceptance test is its computed nonzero r-period, followed by the now explicit smooth-center conversion; a two-sided diagonal pairing alone does not pass it.

Artifacts:

- [Existing universal support module](../../GSTUniversalResolvedSupportHodge.lean), `GSTNativeSmoothIncidenceCenter`: unrestricted projective-push coefficient, primitive full-twist invariance, actual Chern sum identity and sharp center energy.
- [Existing original-X native module](../../GSTActualXHodgeResidualProjection.lean): actual `codimensionCycles X.X p` output and explicit one-center selection, without inserting a universal source-existence field.
- [Existing hypersurface primitive module](../../GSTMaximalLinearHypersurfacePrimitive.lean): all-d equation-driven smooth-center period and positive mixed feedback.
- [Reproducible exact program](../computations/gst_original_x_smooth_incidence_centers.py), [output](../computations/gst_original_x_smooth_incidence_centers.output.json), [v2 manifest](../computations/gst_original_x_smooth_incidence_centers.manifest.json): full formal Chern/Newton identity p=1..12, 300 dimension cases, exact 625-point rational energy benchmark, d=2..20 source benchmark, and genuine Weil exterior null test.
- [Independent Wolfram program](../computations/gst_original_x_incidence_wolfram.wl), [returned output](../computations/gst_original_x_incidence_wolfram.output.txt): exact symbolic Chern interpolation p=1..8 and unrestricted sharp energy/source-period polynomial identities.
- Generic support laws at `61dacf38fff56ac0b2f5020426dfb7dd8da0aedc`: native K0 [39388679194](https://github.com/kyo-oo/HC-PROOF/actions/runs/39388679194) **success**, full pinned integration [39388679169](https://github.com/kyo-oo/HC-PROOF/actions/runs/39388679169) **success**.
- Actual-X native compiler at `95e30fe1c6593d375d222be0bcefc42eac596154`: full pinned integration [39389051548](https://github.com/kyo-oo/HC-PROOF/actions/runs/39389051548) **success**.
- Selected-center and all-d benchmark code at `1ecc8fd83d9e2c087656c74f11452ac54c8147f7`: full pinned integration [39389490154](https://github.com/kyo-oo/HC-PROOF/actions/runs/39389490154) **success**, **8967 jobs**; focused hypersurface [39389490070](https://github.com/kyo-oo/HC-PROOF/actions/runs/39389490070) **success**. All six selected new axiom receipts use only `propext`, `Classical.choice`, `Quot.sound`. Complete integration log contains no `sorryAx`; full CI computation JSON equals the recorded local output. [Exact receipts and artifact provenance](../computations/gst_original_x_incidence_lean.receipt.txt). The v2 computation manifest validates against current input/output hashes.
- Final exact-computation source at `ae647d8b46d55256f0320255df0d2fbb6ac786ad`: full pinned integration [39390054109](https://github.com/kyo-oo/HC-PROOF/actions/runs/39390054109) **success**. The Lean source is unchanged from the preceding audited pin; the final exact script, independent Wolfram source/output and validated manifest are preserved. The separately triggered focused original-X run [39389490121](https://github.com/kyo-oo/HC-PROOF/actions/runs/39389490121) was last observed still compiling at checkpoint assessment; its source already passed the full pinned integration.

**Review provenance:** adversarial self-review of ranks, Chern degrees, kernel incidence, dimension restriction, exceptional signs, rank compression, primitive exponents and the source-selection quantifier. Python/Newton and Wolfram/log implementations are independent checks of the stated polynomial assertions. Lean verifies the displayed algebra and native-cycle formulas relative to the supplied Stage-2G map; generic geometric existence, Bertini, resolution and the canonical fundamental-class comparison are separate mathematical leaves, not newly instantiated Lean scheme constructions.
