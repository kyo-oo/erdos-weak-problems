# GST signed causal purity spectrum — original-X three-branch theorem

- **Date:** 2026-10-22 IST
- **Kind:** Mathbox substantive research attempt, all-depth geometric theorem, adversarial semantic audit, exact Wolfram calculation, existing Lean-module upgrade
- **Program/route:** GST universal Hodge source program / positive-vs-negative causal-dimensional realization
- **Base checkpoint:** `43b16683187b0fbd1a46300766ef0677e6cf0bb7` and later live work on `research/gpt6-native-point-primitive-span-20261017`; prior all-graph finite-holonomy work indexed before this attempt
- **Exact domain:** Every nonempty connected smooth projective complex original `X`; every `p>=0`; every nonzero rational Hodge `alpha in H^(2p)(X,Q) cap H^(p,p)(X)`; cyclic arity `m>=2`; arbitrary signed depth
- **Immutable original target:** Construct `Z_alpha in CH^p(X)_Q` with canonical Betti class `alpha`, without assuming the answer. The causal fold experiment does not silently replace it.
- **Nearest prior route and first distinction:** The prior cyclic and all-graph causal holonomy papers constructed NEGATIVE gap `delta=-h` on projective singular worlds, pure companions, and cohomological recovery. This route introduces a distinct **smooth quasi-projective, free Kummer quotient** with POSITIVE gap `delta=+a`, an explicit geometrically born non-Chow rational class, and an all-arity signed-gap monoid. The finite holonomy smooth companion is reused, not reinvented.
- **Success test:** Positive and negative gap classes must be genuine nonzero rational geometric MHS summands for EVERY original X and prescribed nonzero alpha; no arbitrary Hodge labels. Show exact full Hodge polynomial, sign law and target-sensitive injection. Establish a real algebraicity statement from weight strictness, not an arbitrary source map.
- **Failure test:** If free quotient geometry is ill-defined, Kummer action on H1 is nontrivial, weight coefficients disagree with Kunneth, or the claimed nonalgebraic class has weight equal to its degree, the route fails.

## Precise uniform result

Set `B=X^m`, `G=C_m` cyclically permuting factors, and `K_q=H^q(B,Q)^G`. Use `I_m` for its full graded Hodge polynomial and `A=t²s²uv`. On `B x G_m`, act by `(b,z)->(rho b,zeta_m z)`; this is FREE since z never vanishes. The quotient `U_m=(B x G_m)/C_m` is a real smooth quasi-projective algebraic variety with

```text
H^k(U_m,Q) = K_k + K_(k-1)(-1)   (genuine MHS direct sum)
P_Um = (1+t*s²*u*v) I_m.
```

For `a>=1,b>=0`, define `U_(m,a,b)=U_m x (G_m)^(a-1) x D1^b`, where D1 is the genuine rational nodal projective curve, with `P_D1=1+t+A`. Its exact all-depth polynomial is `I_m(1+t*s²*u*v)^a(1+t+A)^b`, complex dimension `m dim(X)+a+b`, and it contains, functorially and nontrivially for every nonzero alpha, the tensor of its cyclic symmetrization `Theta_m(alpha)` with all a logarithmic H¹ generators and b nodal graph H¹ generators:

```text
cohomological degree = 2p+a+b
Hodge bidegree = (p+a,p+a)
weight = 2p+2a
Hodge charge = 0
purity gap = a-b.
```

The prior projective nodal `Y_m x D1^(b-1)` realizes negative gap `-b`. Every signed integer gap is geometrically realized, not merely assigned to an abstract grading.

### Equal complex dimension triad

For any `ell>=1`, the three algebraic worlds

```text
Y^- = Y_m x D1^(2ell-1)          projective singular
Y^0 = S_m x (P1)^(2ell-1)        smooth projective
Y^+ = U_m x (G_m)^(2ell-1)       smooth quasi-projective
```

all have complex dimension `m dim(X)+2ell`; every original target alpha has nonzero injectively related cohomological output in common degree `2p+2ell`, with bidegrees `(p,p)`, `(p+ell,p+ell)`, `(p+2ell,p+2ell)`, weights `2p`, `2p+2ell`, `2p+4ell`, and gaps `-2ell,0,+2ell`. The smooth projective output is algebraic iff alpha is, by genuine finite-etale quotient Chow transfer, projective pushforward and original-X point restriction.

### Stronger no-go theorem on the positive branch

For alpha nonzero, the `Y^+` output has cohomological degree `2(p+ell)` but pure weight `2p+4ell`, so is NOT the ordinary canonical rational cycle class of any `CH^(p+ell)(Y^+)_Q` class: algebraic codimension-`p+ell` cycle classes on smooth quasi-projective worlds have pure weight `2p+2ell` and type `(p+ell,p+ell)`. MHS weight strictness excludes equality. This is a genuine non-algebraic rational diagonal cohomology class born on a smooth **nonproper** algebraic world for every X and every nonzero alpha; not an HC counterexample.

### New compactification obstruction and exact Kummer residue

The expanded [LaTeX](../derivations/GST_signed_causal_purity_spectrum_2026-10-22.tex) also proves `betaPlus` lies outside the image of **every** smooth-projective compactification restriction `H^(2p+2ell)(Ybar,Q) -> H^(2p+2ell)(YPlus,Q)`: a pure weight-`2p+2ell` source cannot map to the nonzero independent weight-`2p+4ell` output under a degree-preserving MHS morphism. Thus simply compactifying the born class does not convert it into a smooth-projective Hodge class.

A new canonical **topological residue decoder** is explicit: for Kummer base `w=z^m`, the normalized rational generator `lambda1=(1/m)[dlog(w)/(2pi i)]` pulls back to `[dlog(z)/(2pi i)]`; with further torus generators `lambda_i`, the positive folded class is `betaPlus_a(alpha)=alphaU cup lambda1 cup ... cup lambda_a`. Pullback through the finite etale cover followed by projection to top torus Kunneth degree returns `Theta_m(alpha) tensor Q(-a)`. Removing this **explicit Tate twist** and restricting along the original-X point insertion recovers alpha (or m alpha for p=0). This is a genuine whole-alpha cohomological left inverse, **not** a Chow-cycle constructor; the weight-twist firewall is essential.

### Monodromy integration upgraded inside the existing GST law

Beyond the initial green signature fold, the source was strengthened again. The existing `CausalHodgeCell.monodromyLower r` for `r<=min(leftWeight,rightWeight)` and the new `signedCausalFold a b` **commute on the actual current Lean types**, and their combined exact signature is `charge'=charge`, `purityGap'=purityGap+a-b-2r`. Exact symbolic Wolfram returned `commutator={0,0,0}`, charge difference `0`, and gap difference `a-b-2r`. This is a grade-level theorem, not an unverified claim of geometric family monodromy commutation. Added three existing-file declarations and `#print axioms` at source commit `49217682940d6179a71e14a3183d04d0c2e9a8bb`; workflow `39779744770` failed specifically because the original monodromy coordinate bounds were not exposed to the `omega` arithmetic tactic; this was repaired by `change r ≤ p at hl` and `change r ≤ q at hr` without altering the theorem statement. **GitHub Actions [run 39780455617](https://github.com/kyo-oo/HC-PROOF/actions/runs/39780455617) completed SUCCESS** at exact changed Lean source SHA `0604ae95768e63c977bc7d05c5bf5ec7b38589cd`, including the monodromy/signed-fold commute, purity-gap and charge theorems and `#print axioms` check. No local Lean installation.

The earlier kernel compilation for `charge_signedCausalFold`, `purityGap_signedCausalFold`, `signedCausalFold_comp`, pure diagonal and balanced birth passed [GitHub Actions run 39778959643](https://github.com/kyo-oo/HC-PROOF/actions/runs/39778959643) at exact Lean source revision `611418a4ef5267248915b827d09967ab4afd4aa8`. An earlier run failed on an unsolved integer-cast normalization and was explicitly repaired, not misreported as green.

### Full arbitrary-X connectedness audit

The mathematical proof has been strengthened to any **nonempty smooth projective original X, including disconnected X**. For a chosen point x0, let `e=c_x0^*` act on rational H0(X), the idempotent constant-self-map pullback. Cyclic symmetrization satisfies `s^*Theta_m(alpha)=(Id+(m-1)e)alpha`, for all codimensions, and exactly inverts via `J=Id-((m-1)/m)e`; on higher cohomology e vanishes. This corrects the scalar m shortcut when H0 has multiple components. The same J is induced by rational combinations of actual algebraic pullbacks on CH0 so the smooth-projective Chow return remains genuine. Stateless exact Wolfram verified 30/30 small rational idempotent and inverse matrices (component counts 1..5, fold arities 2..7), with no failures.

### Graded GST law in existing Lean module

`CausalHodgeCell.signedCausalFold a b` sends `(k,p,q)->(k+a+b,p+a,q+a)`; its `charge` is unchanged and its `purityGap` changes by `a-b`. Includes compositional associativity, pure diagonal signature, arbitrary-target signed signature and balanced cancellation. The Lean declarations are an exact arithmetic/graded shadow, not a Lean formalization of all scheme/MHS geometry. Full mathematical source type and geometric realization are in the LaTeX artifact.

## Verification and provenance

- **Authoritative LaTeX argument:** [signed purity spectrum](../derivations/GST_signed_causal_purity_spectrum_2026-10-22.tex).
- **Stateless exact Wolfram code:** [reproducible finite audit](../computations/gst_signed_causal_purity_spectrum_2026_10_22.wl), executed verbatim from current committed source. **36/36 cases passed**, for X elliptic/P1, cyclic m=2,3,4, ell=1,2,3, p=0,1; exact coefficient positivity and expected nonzero graded signatures. Elliptic m=2 ell=1 p=1 gives dimensions `(2,10,2)` in selected negative/pure/positive graded cells. P1 gives `(1,4,1)`. Smallest selected sector dimensions over all cases `(1,3,1)`.
- **Existing GST Lean module edited:** [GSTGradedWorldAlgebra.lean](../../GSTGradedWorldAlgebra.lean), commit `ea3dcbbffc209b998a514360d3ee5d643a93fd83`. GitHub Actions targeted workflow `GST Emergent Dimension Causal Fold` run `39778193906`, initially in_progress: UPDATE outcome after fetching revision-matched CI.
- **Review:** Author self-review (Mathbox proof-audit method) checked quotient freeness, Kummer monodromy on H1, graded Koszul invariants, MHS weight shifts, p=0 section rescaling, and nonalgebraicity against actual Chow cycle class. Finite numerical evidence only verifies polynomial identities, not the original-X Hodge conjecture.
- **Disposition:** Scoped signed causal purity-spectrum construction succeeded mathematically under established complex algebraic topology facts; Lean status separate from scheme-level geometry. Universal original-X Chow source input neither assumed nor obtained from this fold.
- **Next discriminating question:** Can a causal operation of a *different algebraic-geometric type* generate a genuinely new original-X Chow class rather than merely transporting nonalgebraic graded cohomology between singular/open worlds? Ordinary weight-preserving degree-zero correspondences cannot erase the ± gap.
