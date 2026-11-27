# Mathbox — canonical secant-sheaf Weil extraction into original-fourfold native Chow assembly

- **Date:** 2026-10-19
- **Program/route:** unconditional original-X rational Hodge construction, Gate 3; retain all-X target unchanged
- **Checkpoint:** branch \`research/gpt6-native-point-primitive-span-20261017\`, base \`8775d34aa265246cf6f5f6f442d1f7d6815052cd\`
- **Source files edited IN PLACE:** \`GSTWeilFourfoldAuxiliaryExtraction.lean\` and \`GSTUniversalCMArithmeticObstruction.lean\`
- **Exact verified Lean revisions:** extraction/coefficient \`c303a36d88b7df86ce7599ca77d1f6eafa9afac7\` **GREEN** [dedicated #39239186561](https://github.com/kyo-oo/HC-PROOF/actions/runs/39239186561) and [pinned #39239186480](https://github.com/kyo-oo/HC-PROOF/actions/runs/39239186480); native Chow assembly \`b4f209d22af3b9909a602853b9e64166d2b48db8\` **GREEN** [pinned #39239626751](https://github.com/kyo-oo/HC-PROOF/actions/runs/39239626751)
- **Reference mathematical derivation:** [all-period sixfold transport, genuine Hilbert and Gysin extraction](2026-10-18-weil-all-period-transport-and-original-fourfold.md), sections 1-7. Pinned primary source \`openai/math\`, git revision \`301488868beec11bfd897168433b0a64f5258559\`, \`paper.tex\` at blob \`d154748feaa7775d2488902ca32f5615e5f4dad6\`, theorem \`p3sw:projective-germ\`.
- **Proof audit:** own review of source comparison, rational normalization, positive d, Hilbert period quantification, proper push-pull/Gysin and canonical cycle map. Neither CI nor Wolfram proves a theorem involving actual analytic sheaf deformation on arbitrary X without the explicit geometric objects.

## 1. One genuine computed sheaf character replaces free nonzero Weil rank

The genus-three secant source's mathematical character computation produces a signed exceptional Weil tensor
\[
  \kappa_3(F_0)_{\rm Weil}=-\alpha(\Omega_+ + \Omega_-),
  \qquad \alpha=\frac{d+1}{4d},\quad d>0.
\]
The balanced tensor \((x,y) =(-\alpha,0)\) is given concretely by the sheaf calculation, not a chosen target class.
The actual elliptic graph difference \(D_0=\Delta-F_1-F_2\) has the checked Gysin intersection contraction \((x,y)\mapsto(-2x,-2y)\). Hence the fixed fourfold Weil coefficient predicted by the honest source is
\[
  z=\left(\frac{d+1}{2d},0\right)\ne(0,0).
\]
The Lean declarations \`secantSeedCanonicalTensor\`, \`secantSeedCanonicalGraphContraction\`, \`secantSeedCanonicalExtractedWeilComponent_nonzero\` certify it for ALL rational d>0, without an independently chosen nonzero Weil vector or generic rank hypothesis.

Let
\[
  r_4=(d+1)^4-6d(d+1)^2+d^2,\qquad
  s_4=4(d+1)((d+1)^2-d)
     =4(d+1)(d^2+d+1)>0.
\]
The genuine K-endomorphism \(d+1+u\), \(u^2=-d\), acts on the original Weil plane by \(T(x,y)=(r_4 x-ds_4 y,s_4 x+r_4y)\).
On the fixed z,
\[
\det(z,Tz)=s_4 z_1^2
 = \boxed{\frac{(d+1)^3(d^2+d+1)}{d^2}}>0.
\]
The new Lean theorem \`secantSeedCanonicalCMOrbitDet_pos\` proves positivity by invoking the independently green uniform fourth-power CM orbit theorem; Wolfram separately simplified the rational expression and checked positivity for all d>0.

## 2. Concrete original-fourfold rational target coefficients

Given any prescribed exceptional rational Weil coordinates \((a,b)\), the explicit rational reconstruction coefficients are
\[
  \mu=\frac{b}{s_4 z_1}
     =\frac{bd}{2(d+1)^2(d^2+d+1)},\qquad
  \lambda=\frac{a}{z_1}-\frac{r_4 b}{s_4 z_1}
     =\frac{d(4(d+1)(d^2+d+1)a-r_4 b)}
            {2(d+1)^2(d^2+d+1)}.
\]
Thus \(\lambda z+\mu Tz=(a,b)\) exactly over Q. Wolfram simplified the coefficients and returned the target \((a,b)\) symbolically under d>0.

If \(\Gamma_{A\times B}\) is the **genuine** Hilbert-spread codimension-three cycle on the padded original A×B from the manuscript's semiregularity/period argument and \(p_A\) is proper projection, define
\[
  Z_0=(p_A)_*(\Gamma_{A\times B}\cdot p_B^*D_0)
    -c_\mathrm{ambient}\,\Theta_A^2\in CH^2(A)_\mathbf Q .
\]
With canonical Betti coefficient z and genuine algebraic CM isogeny pullback \(T_{\mathrm{Chow}}\), every prescribed middle rational Hodge target with Hodge coordinates \((q,(a,b))\) has the **explicit original-A algebraic combination**
\[
  \boxed{Z_\alpha
      =q\,\Theta_A^2+\lambda Z_0+\mu T_{\mathrm{Chow}}Z_0 }.
\]
This formula contains no selected Chow preimage of alpha.

## 3. New Lean assembly and exact residual geometric interface

The new \`auxiliaryWeilEveryMiddleHodgeClass_from_secantCharacter\` in the existing \`GSTUniversalCMArithmeticObstruction.lean\` feeds the concrete mathematical coefficient \(((d+1)/(2d),0)\) into the already kernel-verified Hilbert/CM original-A constructor. The old \`hWeilNonzero\` is NO LONGER an input: it follows from the secant coefficient proof.

Its genuine scheme/analytic inputs are STILL separate data:
- \`Parameter,projection,good,hclosed,hidentity,hlocal\` representing an actual analytic Hilbert/Baire source family with local semiregular sheaf deformation;
- \`fixedSixfoldBetti,cycleAt,hHilbertClass\` representing the fixed true sixfold Betti/Chern/Hilbert cycle class at each chosen period;
- \`extract,hProperGysinNaturality\` representing real cup with the elliptic graph-difference divisor followed by canonical proper Gysin;
- \`hSecantCharacter\` matching that geometric source's actual extracted Betti class to the computed specific coefficient;
- \`G,thetaSquare,coordinates,cmPullback,hCMFunctorial\` representing real canonical original-A cycle class and genuine isogeny action.

These need concrete Lean inhabitants from the manuscript's analytic/categorical/scheme constructions. The compiled theorem gives a native cycle \`Z\` with \`H.cycleClass 2 Z = alpha\` relative to the supplied interfaces; it does not independently instantiate canonical rational Betti cohomology for a real smooth projective complex scheme, and cannot be promoted to the all-X unconditional Hodge theorem on that basis.

The pinned external text \`p3sw:projective-germ\` was read at its exact source statement during this round. It assumes a proper holomorphic submersion with relatively ample line, an ordinary coherent central sheaf F0 with INJECTIVE full raw Ext² trace-Atiyah semiregularity in selected degrees, and flat rational Chern characters lying in the required Hodge filtration; it concludes a local flat coherent deformation. The previous record provides candidate central sheaf, obstruction computation and source comparison. Independent geometric instantiation in Lean remains unfinished.

## 4. Strongest surviving status, no false closure

**GREEN & proved:** rational leading secant source coordinate, nonzero Weil vector, strictly positive CM orbit determinant, and native rational Chow target assembly conditional ONLY on concrete Hilbert/Betti/Gysin/CM geometry, no free nonzero Weil-source premise.

**Manuscript-level source chain:** the cited geometric record argues for semiregularity, actual coherent deformation, Hilbert spread and Gysin on all Weil-type fourfold periods using named outside theorems. This record does not independently certify those sophisticated geometric hypotheses or the full all-X conclusion. The scope is Weil fourfold middle classes under its Hodge-coordinate decomposition, NOT arbitrary smooth projective X.

**Remaining concrete proof interface:** instantiate the actual relative Hilbert family and canonical Betti/Gysin comparison on the original A in Lean (and verify the fixed sixfold source Chern-character normalization). The broader all-varieties Hodge conjecture still requires a universal source construction beyond the Weil family.

**Disposition:** active source route OPEN; stronger actual numeric proof integrated and green; do not return to redundant CM matrix units or suggest a counterexample from failed pushdown.
