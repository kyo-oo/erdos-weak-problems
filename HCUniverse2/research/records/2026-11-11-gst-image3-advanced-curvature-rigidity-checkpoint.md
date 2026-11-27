# 2026-11-11 — GST Image-3 advanced source expansion and original-X geometry type audit

**Owner research target:** universal original-X GST geometric antecedent for the established conditional Hodge theorem. This checkpoint does **not** assert the universal antecedent or unconditional Hodge algebraicity.

**Starting immutable source:** curvature branch SHA `296478b17cd342eef7aa7f2361f764cd29a4f1ad`.

**Isolation:** branch `research/gpt6-image3-advanced-curvature-rigidity-20261111`; no owner working branch or parallel geometry branch was rewritten.

## Executed mathematical routes

**Route A — failed original fixed-cell resonance proof repair (implemented).**
The former `GSTImageThreeCurvatureResonance.lean` had four tactic/elaboration errors at lines 164,252,255,266 on an older SHA. The new source fixes those declarations and proves additional exact structural theorems:
- `fixedPair_curvatureFold`: original null/max two-cell F block;
- `fixedPair_controllability_det`: two-fold exact determinant `2b-1` for ALL rational a,b;
- `fixedPair_independent_off_resonance`: independence iff b≠1/2;
- `resonanceOrbitSpan_le_kernel`, `resonanceOrbitSpan_ne_top`: a proper hyperplane contains the ENTIRE resonant native orbit span for every rational a.

The original native Lean file **compiled successfully** within run `43013771919` (`Build completed successfully (8967 jobs)`). The overall workflow then failed because its repeated generator invocation duplicated a `lean_lib` target. This is a CI script failure AFTER the native Lean build, not a failed native theorem. The workflow was corrected to a single top-level import-chain build at commit `a9ce041f694dbef6bcbd0faa32f9ca822011d9a9`; latest full geometry CI status must be checked independently.

**Route B — factor the complete original native determinant (proved algebraically; exact Wolfram audit).**
The 12-state U,J,M,[J,M] source splits into 2 fixed and 10 rotating invariant cells, and the exact all-parameter Krylov determinant equals the product of the 2-cell determinant, 10-cell determinant, and characteristic-polynomial resultant (positive sign in the original cell ordering). This is derived in
`research/derivations/GST_image3_CM_curvature_two_ten_resultant_exact_2026_11_11.md`
and tested from the owner's original operators in
`research/computations/GST_image3_CM_curvature_two_ten_resultant_factorization_20261111.wl`.
The a=0 factorization is EXACTLY `(2b-1)*P10(b)*(b^4 P16(b))`. It identifies the b=0 spectral collision separately from the b=1/2 two-cell controllability obstruction.

**Route C — eliminate fine-tuning in direct SURVIVE strength (exact symbolic + modular proof).**
For `F_a=U+J+a M+[J,M]`, all rational `a` give full native 12-state rank. Exact determinant factors as integer `Q8(a)*Q12(a)`; both have leading coefficients nonzero mod11 and zero roots in ALL 11 elements of F11. The rational-root theorem proves no rational root. Exact original-operator generation, complete mod11 tables and original balanced determinant check all pass in
`research/computations/GST_image3_all_rational_direct_strength_CM_curvature_mod11_20261111.wl`.
An independent Python matrix construction and finite-field Gaussian-elimination check is saved at
`research/computations/gst_image3_direct_survive_mod11_independent.py`.
The universal **all-rational-a** conclusion is supported by the exact polynomial certificate and rational-root argument; it is not currently a separate Lean theorem.

**Route D — arbitrary finite N-hole spectral consolidation (mathematical proof).**
For any rational a, the original F_a has row-sum norm <= R(a)=4+2|a|. An adaptive rational channel separation S(a)=9+4|a| >2R(a) makes the shifted F_a+iS(a)I blocks spectrally disjoint. Each block is native cyclic by Route C; CRT gives full 12h-dimensional orbit for the original mixed seed in every one of h positive finite independent N-hole channels. This is a uniformly quantified **native** result, not a transfinite Chow sum, and it does not automatically land in canonical Hodge cohomology of arbitrary X. Wolfram exact tests confirmed the bound for a=-10,-1,0,1,13/7,100 and rank24 for a=0,h=2 with spacing9.

**Route E — repair geometric type overclaims and strengthen source-image invariance (Lean edited).**
`GSTImageThreeOriginalXCurvatureLanding.lean` now explicitly says that `CycleClassOperatorPair` is a supplied rational cycle-operator/Betti-operator commuting square, NOT an actual algebraic correspondence on X×X. Two new source-image-stability theorems show F and its commutator preserve the complete existing algebraic cycle-class range.
`GSTImageThreeAdvancedGeometricSource.lean` requires FIVE genuine `RealizedFiniteClosedCorrespondence` witnesses U,J,M,JM,MJ with certified equality of the two ordered composition actions on both native cycles and Betti classes. It constructs the actual five-atom rational closed-correspondence word and proves its action agrees with the previously formulated F pair, conditional on those geometric witnesses. The universal existence of the five witness objects, a refined Chow push-pull realization with intersection multiplicities, and full canonical Hodge landing are NOT manufactured here.

## Verification status, strict evidence gate

- **Green native-source build:** run `43013771919`, native file compiled successfully and printed `#print axioms` without sorryAx. The overall job failed on a duplicated temporary Lean library name, corrected in a later workflow commit.
- **Full updated geometric-compiler Lean check:** workflow `gst-image3-advanced-curvature-rigidity.yml` at commit `a9ce041f...`; inspect its exact run status and job log before reporting success.
- **Exact Wolfram:** both newly committed source-factor scripts independently returned `allPassed -> True`.
- **Independent F11:** a separate Python matrix implementation reproduced all eleven determinant residues `(6,2,1,8,6,4,8,9,3,9,5)`, all nonzero.
- No `sorry` or `admit` string appears as a declaration in the three updated/new Lean files. This textual check is NOT a replacement for successful Lean compilation.
- All-rational source cyclicity and all finite-N native rank have mathematical exact-arithmetic proofs/derivations; they have NOT yet been formalized as global Lean theorems.

## Exact noncircularity frontier

Neither a native 12h-dimensional cyclic module nor a `CycleClassOperatorPair` alone yields canonical Hodge algebraicity. The universal original-X problem is actual algebraic correspondences/source cycles with a canonical comparison, a rank-preserving equivariant landing, and a noncircular proof of coverage of every rational Hodge direction. Preserve the already proved conditional `NativeGSTSingleFoldOrbitLaw => EveryHodgeClassIsRationalAlgebraic` unchanged.
