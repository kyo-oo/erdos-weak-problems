# GST full rational Chow image → whole complex Hodge spectral kernel: exact mathematical and Lean bridge

**Date:** 2026-10-22 IST. **Starting source HEAD:** `54c2746bbacdfcf745d7fae2383702958766f22c`. **Research file:** [GST_hodge_spectral_rational_cycle_reduction_2026-10-22.tex](../derivations/GST_hodge_spectral_rational_cycle_reduction_2026-10-22.tex). **Existing Lean file upgraded in place:** [GSTClassicalHodgeExactClayStatement.lean](../../GSTClassicalHodgeExactClayStatement.lean). **Exact reproducible Wolfram:** [gst_rational_Chow_to_Hodge_spectral_kernel_2026_10_22.wl](../computations/gst_rational_Chow_to_Hodge_spectral_kernel_2026_10_22.wl). **GitHub Actions kernel workflow:** [gst-hodge-spectral-kernel-reduction.yml](../../.github/workflows/gst-hodge-spectral-kernel-reduction.yml) — run [39672107848](https://github.com/kyo-oo/HC-PROOF/actions/runs/39672107848) started for exact Lean + CI workflow commit `1998800c8d69defc68ad15e5703af41d9207f031`. Run status MUST be checked separately before claiming green.

## Exact user's two boxed equations and logical direction

For arbitrary actual smooth projective complex X, degree 2p, canonical rational Betti V_Q=H^(2p)(X,Q), canonical complex V_C=C⊗_Q V_Q, and the genuine full Hodge-circle spectral generator G acting on H^(a,b) by i(a−b):
1. the user's strong equality is `A=im(cl_X^can: CH^p(X)_Q→V_Q) = V_Q ∩ ker_C(G)`, i.e. the rational Hodge conjecture's algebraicity equality;
2. the reduced full-complex spectral identity is `H^(p,p)(X)=ker_C(G|V_C)`.

**The spectral identity is independently derivable from the Hodge BIGRADING**, no rational algebraicity needed. Since a+b=2p, nonzero charges are ±2r; the exact all-p polynomial `P_p(G)=∏_(r=1)^p(Id+G²/(4r²))` annihilates all nonzero-charge components and is 1 on H^(p,p). Then the rational Hodge classes are EXACTLY those alpha∈V_Q for which `P_p(G)(1⊗alpha)=1⊗alpha`. The spectral polynomial does NOT preserve Q-rational cohomology as a separate assumed map: rational points are pulled back through scalar extension.

## True reduction and whole native defect

Define `K=V_Q∩ker_C G`, `A=im cl_X^can⊆K`, `D=K/A`. Then for each original X,p the following are equivalent:
- the user's input Chow-image equality A=K;
- for each rational alpha with P_p(G)(1⊗alpha)=1⊗alpha, there is an ACTUAL rational codim-p Chow cycle Z on original X with canonical Betti class alpha;
- the true GST rational Hodge/native quotient defect D vanishes;
- there exist actual defect-zero native landing states for EVERY multiplicity-indexed rational Hodge basis direction, as in `GSTClassicalHodgeFiberedCycleClassDefect.bigradedBettiHodge_of_defectZero_basisStates`. Existence of those states is NOT supplied by the scalar spectral identity.

Dimension formula: `dim_Q D=dim_Q K−rank_Q cl_X^can`. The complex dimension `h^(p,p)(X)` generally need NOT equal dim_Q K. Do not complexify rational algebraic equality into equality with the full complex (p,p) summand without separately proving rational-density/complex spanning, which may fail in concrete Hodge structures.

## Actual Lean target and formal hypothesis types

In EXISTING `GSTClassicalHodgeExactClayStatement.lean` (no new fake data layer), added:
- `SpectralComplexCohomology H p`: complexification of ACTUAL Stage2G rational singular Betti cohomology.
- `SpectralGenerator H p`: complex-linear full-Hodge-charge endomorphism on that complexification.
- `rationalSpectralKernel H p G`: actual Q-submodule comap of `ker G` along `complexificationMapQ`.
- `rationalSpectralKernel_eq_rationalHodge`: exact typed kernel comparison when `ker G=(H.hodgeBigrading p).ppComponent`. This is a Hodge-geometry spectral-realization hypothesis, NEVER a Chow-surjectivity hypothesis.
- `exactHodge_iff_spectralKernel_in_nativeRange`: equivalence between exact existing Hodge-conjecture target and inclusion of the rational spectral kernel in the Stage2G native cycle-class RANGE.
- `CycleClassHodgeCompatible H`: independently requires Stage2G's externally supplied cycleClass be of genuine (p,p) type. Important because Stage2G does NOT yet prove that an arbitrary supplied H.cycleClass is the actual canonical analytic Betti cycle map.
- `exactHodge_iff_nativeRange_eq_spectralKernel`: under that honest canonical-image compatibility, exact rational Hodge conjecture iff the Q-native source image EQUALS the rational zero-charge kernel.

Lean proofs use actual Mathlib submodules, complexification and native cycle maps, and no sorry/admit/custom axioms. The first lemma is a typed comparison conditional on full complex kernel characterization, *not an algebraicity proof*; the two equivalence theorems have no Chow-surjectivity assumption in their input beyond the statement on their LHS.

## Wolfram exact discriminator and nonclaims

The exact script executed in WolframLanguageEvaluator with all p=0..12 charge spectra; every full spectral projector acted as the zero-charge projector, was idempotent, and had rank one in the MODEL with exactly one vector per charge. Rational 3-dimensional toy with G=[[0,0,0],[0,0,-2],[0,2,0]] has complex eigenvalues 0, ±2i and rational zero-charge kernel rank 1. TWO abstract cycle source maps (nonzero full-rank vs zero) are both charge-zero and have the SAME spectral kernel, but only one image surjects. This refutes the attempted *logical inference from spectral kernel alone to native source surjectivity*. These are algebraic linear MODELS, **not examples of smooth projective counterexample varieties** and do NOT refute the Hodge conjecture.

## GST causal fold implication

For any certified fold with genuine rational Hodge-kernel map T and actual Chow map S satisfying canonical class naturality `T cl_X^can = cl_Y^can S`, there is an induced quotient defect map `D_X→D_Y`. A reversible/native-compatible GST fold has an isomorphism on defects and alone cannot eliminate a nonzero defect. If a fold has an INJECTIVE induced defect map and an INDEPENDENT proof that the target defect vanishes, then the source Hodge conjecture holds; this is a correct conditional theorem, and the spectral identity on Y alone does not certify target defect vanishing.

## Evidence status

- LaTeX derivation committed as user requested BEFORE the Lean edit.
- Exact Lean proofs committed to the actual authoritative original target module.
- Separate GitHub Actions-only compilation launched, no local Lean installation.
- Finite Wolfram test passed; its toy finite spectra do not prove the universal algebraicity statement.
- This route achieves the exact formal REDUCTION from rational Chow-image equality to the complex Hodge kernel equation plus the remaining native quotient. It does NOT construct a novel universal original-X Chow representative merely from the spectral equation.
