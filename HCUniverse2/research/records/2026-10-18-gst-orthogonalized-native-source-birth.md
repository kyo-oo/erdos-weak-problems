# Mathbox — orthogonalized original-X native birth: optimal correction, exact rank-one saturation, and source boundary

- **Date:** 2026-10-18
- **Kind:** new mathematical construction and correction of previous GST route
- **Program:** Hodge for every original smooth projective complex X, all p and all rational (p,p) alpha. Target remains a genuine native rational Chow cycle with canonical Betti class alpha; it is NOT proved here.
- **Base checkpoint:** 75e2dbd18626f5ef6c25762e08113fc93276e907, active branch research/gpt6-native-point-primitive-span-20261017
- **Affected earlier route:** [Target-directed source birth / Gram integer gap](2026-10-18-gst-target-directed-birth-and-gram-integer-gap.md).
- **Actual code:** GSTPolarizedHodgeResidualEnergy.lean and GSTActualXHodgeResidualProjection.lean **edited in place**, no local Lean installation.
- **Attempt outcome:** new explicit OPTIMAL rational-native source correction and one-birth saturation of a rank-one primitive sector, subject to a genuine independently constructed native source; universal independent source existence remains open.

## 1. Correct a flaw in the previous native energy descent

For a fixed original smooth projective X and codimension p, work in its true finite-dimensional rational primitive Hodge fiber V with the signed-positive primitive intersection form Q. Let the genuine old native Chow cycles z_i span the known rational algebraic subspace A⊆V, and let pi_A denote the rational Gram-orthogonal projector built from the true intersection Gram matrix.

For a prescribed alpha, let r=alpha-pi_A(alpha). The old GST energy step in the previous record took an independently constructed true native cycle Z with z=cl_X(Z), then subtracted t*z from r, with
t=Q(r,z)/Q(z,z).

**The weakness:** in general z=a+s with a=pi_A(z)∈A and s=z-pi_A(z)∈A^perp. Although r∈A^perp, the update r-t*z has old component -t*a and is therefore NOT a legitimate residual of the enlarged old source space. Its energy drops, but can drop much less than the attainable optimal value.

**NEW actual native source, not a free Hodge operation:**
\[
 Z_\perp := Z-\operatorname{projNative}_{A}(\operatorname{cl}_X Z)\in CH^p(X)_{\mathbb Q},
 \quad \operatorname{cl}_X Z_\perp=s.
\]
This subtraction takes place in the ACTUAL native rational codimension-p cycle group on the ORIGINAL X and needs no selected native preimage for the prescribed alpha. The corrected target-born native cycle is
\[
\boxed{
 Z_\alpha^{new}
 =\operatorname{projNative}_A(\alpha)
 +t Z_\perp,\qquad
 t=\frac{Q(r,s)}{Q(s,s)}
}
\]
when s!=0. Its **actual Hodge residual** is
\[
\boxed{\alpha-\operatorname{cl}_X Z_\alpha^{new}=r-t s.}
\]
The true optimal energy identity is
\[
Q(r-ts,r-ts)=Q(r,r)-Q(r,s)^2/Q(s,s).
\]
Because Q(r,a)=0, Q(r,z)=Q(r,s), and Q(z,z)=Q(a,a)+Q(s,s), the corrected energy gain is at least the naive gain, strictly larger when both Q(r,s) and a are nonzero and Q positive.

If r=t*s, this explicitly constructed original-X algebraic cycle has EXACT class alpha. This is a genuine source-assembly theorem, not an assumed source-to-Hodge preimage.

## 2. Exact original geometric test that changes the result

Take a smooth cubic fourfold containing a plane P. The genuine intersection matrix on H=h², C=[P] is
\[
G=\begin{pmatrix}3&1\\1&3\end{pmatrix}.
\]
The known old class is H, target alpha=C, and fresh native source is the actual algebraic plane C.

The old residual is r=C-H/3, with Q(r,r)=8/3. The naive correction uses t_old=(r.C)/(C.C)=8/9, and yields nonzero residual (-1/3,1/9) with energy 8/27.

The NEW source correction computes
\[
s=C-\tfrac13 H=r,\qquad
t_{new}=Q(r,s)/Q(s,s)=1,
\]
and outputs the genuine native Chow cycle
\[
Z_{\alpha}^{new}=H/3+1\cdot(C-H/3)=C.
\]
Its residual vanishes EXACTLY, with no limit and no denominator growth. This is not a newly discovered algebraic plane; the plane C is explicitly the independently supplied geometrical source. It demonstrates that the earlier GST energy descent was genuinely suboptimal and that the corrected construction can end at an exact solution as soon as a source generating the residual sector is available.

**Wolfram exact test:** obtained
\`{{-1/3,1},{-1/3,1},8/9,8/27,1,0,{0,1}}\`, in the order residual r, corrected source s, old coefficient, old energy, new coefficient, new energy, reconstructed target class. Entire calculation is exact rational arithmetic; no numeric precision issues.

## 3. A single native source saturates ALL targets in a rank-one quotient

Let K=intersection of kernels of the old true geometric dual detectors; if the genuine residual Hodge subspace K is the rational line Q*s, with s=cl_X(Z_perp), then for EVERY alpha in V, the computed residual r lies in K, so r=t*s for some rational t. The exact corrected native construction therefore produces a Chow cycle representing alpha for EVERY target, **using ONE independently constructed native source Z in addition to the already-available cycles**.

The theorem \`one_native_birth_saturates_rank_one_residual_sector\` formalizes this all-target, one-source saturation. Its hResidualLine premise concerns only a geometric vector-space dimension and the location of the genuine source's nonzero residual; it does not provide alpha-specific cycles or assume target algebraicity. Thus this case is structurally stronger than a theorem requiring a fresh witness for each target.

The existing native CM Weil orbit theorem is the appropriate two-dimensional complement: a single actual nonzero Weil source can generate a rational two-plane by a genuine non-real CM isogeny, after ambient Chow purification. In that setting the CM action supplies the second native direction. Both mechanisms demonstrate that it can suffice to construct ONE genuinely new algebraic source per suitable irreducible/CM-cyclic missing sector, rather than a separate source for each rational target class.

## 4. What the correction CANNOT prove

If the full primitive algebraic cycle-class span A=cl(CH^p(X)_Q) is a proper subspace of V, then there exists a nonzero rational Hodge r∈A^perp (positive nondegenerate Q). For every genuine algebraic native source Z on the SAME X, Q(r,clZ)=0. Therefore neither the new projector, existing CM/Hodge algebraic correspondences, trace-zero surgery, nor a purely native GST world birth obtained entirely from already-algebraic cycles can force nonzero target coupling. The statement that some coupled original-X cycle exists for every nonzero full residual is already equivalent to the still-open Hodge spanning statement under finite positive polarization; it must not be inserted as a new GST postulate.

Equally, the live HodgeBigradedBettiData model supplies an H.cycleClass map. Lean verification of this abstract map must not be misreported as verified official singular-Betti cycle-class semantics until Gate 1's canonical comparison has been instantiated.

**The undecided geometric challenge** remains target-born realization of at least one genuinely new algebraic cycle for every primitive residual *sector* on arbitrary original X. Rank-one and CM-cyclic cases show how one new source would finish that sector, but do NOT construct that source.

## 5. Verification and continuation

- \`GSTPolarizedHodgeResidualEnergy.orthogonalizedNativeBirth_class\`,
  \`correctedTargetNativeBirth_residual\`,
  \`correctedTargetNativeBirth_exact_of_residual_parallel\`,
  \`correctedTargetNativeBirth_strict_energy_descent\` passed official Lean Action [CI #39132618893](https://github.com/kyo-oo/HC-PROOF/actions/runs/39132618893), in commit 131da62615be012296222bd365b00ccc4754ceb1.
- Original-X specialization \`ActualXCycleProjectionData.correctedTargetCycle_class_eq\` written in commit 3d90c70a7bb055b308bb1f9bf17fca9448dee71d and full pinned integration [#39132849888](https://github.com/kyo-oo/HC-PROOF/actions/runs/39132849888) passed.
- One-native rank-one saturation added in commit 95ddd8400f8b7705808b84d7f252ac4e4269cdd4; follow its focused CI for final receipt before treating it as kernel verified.
- **Next genuine construction route:** use original-X geometric secant/determinantal coherent sheaves with actual algebraic projective compactification and canonical Chern classes, or a genuinely nonsplit Weil source, to produce the required NEW cycle from a prescribed positive Hodge residual. Avoid repeating matrix corrections in lieu of that source.
- **Evidence label:** exact native correction and rational rank-one theorem mathematically proved, Lean review current subject to listed CI; source-existence for all X **open**.
- **Review provenance:** self-audit using independent rational Gram computation; no claim of full Hodge resolution.
