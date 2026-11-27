# Mathbox execution after the committed GST research-direction correction

**Date:** 2026-10-23. **Branch:** research/gpt6-native-point-primitive-span-20261017. **Base checkpoint:** 315465462cf552d3cddabd97fe31f00a308ff9fc (the mandated direction-failure audit).

**Research owner's target:** For EVERY original smooth projective complex X, p and rational Hodge alpha, construct an INDEPENDENT genuine original-X Chow class Z_alpha with canonical Betti image alpha. No cycle-class surjectivity postulate or pre-existing alpha algebraic source as input.

**Mathbox workflows applied:** research-program, research-attempt, proof-audit, computation-audit. Self-audit (no independent referee); GitHub connected source edits, Wolfram exact arithmetic. No public web; no local Lean install.

## 1. The FIRST new construction now really DEPENDS on alpha

[Mathematical proof source](../derivations/GST_target_sensitive_original_X_signed_determinantal_calibration_2026_10_23.tex) created in commit cc60426017f5e5aa508663fa6564de801fdeae76 and subsequently mathematically strengthened in commits 5645520b23ce2504c1b0e095c45b571a41fe6f90 and fb9933df022d0956b7e96fbc1f72f4e2352d7266.

**Proved:** For arbitrary original X and prescribed rational alpha∈H^(2p)(X,Q), rational complex topological K-theory builds ACTUAL smooth complex bundles E_+,E_- with ENTIRE ch(E_+)=r_++m(alpha+lambda h^p), ch(E_-)=r_-+m lambda h^p. No given Chow cycle or algebraic span assumption. Generic tuples of smooth sections define actual Whitney-stratified determinantal integral pseudocycles D_+,D_- ON ORIGINAL X, each with integral homology Poincare dual to its pth Chern class. Their explicit rational signed combination T_alpha has PD_X[T_alpha]=alpha EXACTLY, since cp(E_+)-cp(E_-)=(-1)^(p-1)(p-1)!m alpha. Unlike fixed PGL tangent classes or all finite-divisor folds, these genuine geometric spaces are **selected by alpha itself**, not selected independent of the target.

**Nonzero primitive coupling, proved:** for NONZERO h-primitive rational (p,p) r with 2p≤d, the actually constructed original-X T_r obeys (-1)^p⟨T_r,r h^(d-2p)⟩ = (-1)^p∫_X r² h^(d-2p)>0, by the strict Hodge-Riemann bilinear relations. Thus we DID derive a target-dependent source with independently guaranteed nonzero original-X period. Its category is smooth REAL geometric integral pseudocycle, NOT algebraic Chow. This corrects the previous research-direction error without hiding the type boundary.

**Necessary signed geometry, proved:** no single nonzero effective analytic codim-p cycle can have a nonzero primitive target class r: ∫r h^(d-p)=0, whereas an effective nonzero projective cycle has strictly positive ample degree. A rational background lambda h^p chosen with appropriate sign and large absolute value makes each of cp(E_±) have strictly positive Kähler degree; it removes a simple degree-sign impossibility, not the algebraic realization problem.

## 2. First target-sensitive analytic source-return theorem: compact original-X geometry

Let k=d-p, omega represent the integral Kähler h, phi=omega^k/k! be the Wirtinger calibration and defect Δ(T)=Mass(T)-T(phi)≥0.

**Proved:** If genuinely alpha-dependent determinantal integer cycles D_{±,j} on the SAME compact original X represent the constructed E_± Chern homology classes, have uniform masses and Δ(D_{±,j})→0, Federer-Fleming gives integral closed flat limits C±. Lower semicontinuity plus closedness of phi forces both limits to be Kähler calibrated. By the positive closed rectifiable integral current structure theorem they are true holomorphic cycles, algebraic by projective Chow. The constructed *actual ORIGINAL-X* rational Chow cycle is Z_alpha=(-1)^(p-1)/(m(p-1)!)([C+]−[C−]), with the correct CANONICAL Betti image. This is a quantified **geometric compactness proof**, not an abstract Hodge-to-Chow selector. The analytic estimates are a genuinely additional geometric demand, not asserted to follow from Hodge-type preservation alone.

## 3. Hodge-specific new inequality and completed finite mathematical check

For off-diagonal (a,b) forms psi of complementary real degree 2k with a+b=2k,a≠k, the pointwise Kähler-angle estimate on an oriented 2k-real plane xi is |psi(xi)|≤C||psi|| sqrt(1−phi(xi)). Integrating a real rectifiable T and applying Cauchy-Schwarz yields the *quantitative universal inequality* |T(psi)|²≤C²||psi||_∞² Mass(T) Δ(T).

For a NON-Hodge rational class gamma, an off-diagonal closed harmonic complementary psi has a fixed NONZERO pairing with gamma. Therefore a bounded-mass cycle sequence in gamma cannot satisfy Δ→0. For a Hodge class, all these off-diagonal pairings vanish exactly. This is a proven **Hodge-sensitive discriminator for real geometric source approximation**, unlike topological fold invariance which holds for Hodge and non-Hodge alike. Absence of the obstruction is necessary, not claimed sufficient.

[Executed exact Wolfram file](../computations/gst_original_X_alpha_signed_degeneracy_and_angle_2026_10_23.wl), committed SHA 3d8be81a36b705e4ff488bddc0f9fdf78551ee4b, fetched blob 8d16985894671a9425d0e3b2b6b23062b4ea5345. **68/68** exact pure Chern-character coefficient/sign/source reconstruction identities passed (p=1..8,d=p..12), 68/68 higher singular rank codimension checks passed; exact one-complex-line Kähler angle identity passed; no failures. General mathematics follows the cited universal K-theory, Thom-Porteous and Wirtinger theorems, not finite extrapolation.

## 4. Actual geometric dynamic: central middle dimension

For original complex d=2p, a generic rank-deficiency source D_± is a TRUE SMOOTH COMPACT real middle-dimensional submanifold because the next lower matrix-rank stratum would have complex codim 2(p+1)>d and is thus empty under transversality.

Its smooth mean-curvature flow (during smooth existence) has the EXACT Lyapunov identity dΔ/dt=−∫|H|²dμ≤0, since the Kähler calibration integral is fixed in homology while mass decreases by first variation. Thus the first requirement in the return theorem, uniform bounded mass, follows automatically for smooth flow. The second demand, Δ→0, does NOT follow from the differential identity alone: singularities and noncomplex stationary critical points may intervene. A genuine higher-dimensional GST geometric source-growth/regularization law must establish the full defect dissipation for this alpha-dependent signed pair.

## 5. Actual proof status and next noncircular work

- **Completed original-X target-sensitive geometric constructor:** YES, actual real signed stratified pseudocycle with PD exactly alpha and strictly nonzero primitive coupling.
- **Completed original-X genuine rational Chow constructor for all primitive alpha:** NO, because current control does not establish uniform-mass zero-calibration-defect sequences; the compact return theorem proves exactly what such estimates would accomplish without inserting a Chow source as input.
- **Avoided repetition:** no new fixed PGL tangent Chern sources, no elliptic deformation toy target, no more algebraization iff reformulation as the claimed new theorem, no invented Lean 'cycleClass' formalization.
- **Concrete mathematical continuation:** derive and audit an actual GST causal-geometric deformation scheme that drives the alpha-SELECTED signed determinantal cycles to a bounded-mass asymptotically complex-calibrated pair. First investigate middle-dimensional smooth mean-curvature flow, including singularity/positive-defect stationary obstructions, without assuming global defect extinction.

**The current mathematically honest difference:** the entire attempt is now built around the specified alpha and has a rigorous nonzero ORIGINAL-X target coupling from scratch; the source is real geometric, not yet a fabricated Chow class.