# Mathbox proof audit: exact direct GST curvature-to-Fitting source normalization

**Date:** 2026-10-23 IST. **Review:** author self-audit using Mathbox proof-audit and computation-audit skills. **Underlying theorem:** [GST direct prescribed-alpha polynomial source equations](../derivations/GST_direct_alpha_finite_polynomial_curvature_source_equations_2026_10_23.tex), augmented at commit `2c346fc553c754704ec80e7b6af68f34f68e38ed`. The original target is arbitrary smooth projective original X,p,rational (p,p) alpha; an independently constructed actual original-X Chow Z with canonical Betti alpha.

## Discovered exact type discrepancy and repair

A finite REGULAR algebraic GST projector P creates an honest algebraic vector bundle E on the TRUE incidence fold q:J→X. The target-directed algebraic Chern--Weil equation
`Omega_p(P+)-Omega_p(P-)-mu eta_alpha=dB`
controls the degree-p **Chern-character** difference. The previous Plucker/Fitting rank-drop zero schemes directly give degree-j **Chern CLASSES** c_j(E). These are NOT the same: for actual formal rank-two bundles with Chern roots E+={1,1}, E-={0,1}, the exact degree-two Chern-character difference is **1/2**, but the c2 difference is **1**. Therefore an attempted pure c_p signed source formula from the target's ch_p equation without lower Chern matching would be FALSE.

**Mathematical correction, valid for ALL original X and p, without assuming lower Chern coincidence:** For every j=1..p construct the true scheme-theoretic GST Fitting degeneracy locus Sigma_(±,j) using rank(r±−j+1) algebraic constant sections of E±. Under generic transversality, each true Chow class C_(±,j)=[Sigma_(±,j)] equals c_j(E±), including the possibility of an empty locus representing zero. Define universal integer Chow Newton polynomials
`N_1(C)=C_1`,
`N_n(C)=Σ_(j=1)^(n-1)(−1)^(j−1)C_j N_(n−j)(C)+(−1)^(n−1)n C_n`.
The unrestricted splitting-principle identity is
`N_p(C_1,...,C_p)=p! ch_p^CH(E)`.
Hence ANY actual alpha-indexed polynomial curvature solution with positive integer mu gives the following explicit ORIGINAL-X genuine rational Chow class:
[
 Z_\alpha=\frac{1}{\mu p!}(q^*)^{-1}\Big(
 N_p([\Sigma_{+,1}],\ldots,[\Sigma_{+,p}])
 -
 N_p([\Sigma_{-,1}],\ldots,[\Sigma_{-,p}])
 \Big),\qquad \mathrm{cl}_X^{can}(Z_\alpha)=\alpha.
]
All products are ACTUAL rational Chow intersection products in the smooth affine GST world J, then returned to X by Chow homotopy invariance; no image-compiler or Hodge-to-Chow selector inserted. For p=2 this gives
`Z=(1/(2mu))(q*)^-1(([Sigma+1]^2-2[Sigma+2])-([Sigma-1]^2-2[Sigma-2]))` exactly.

## Exact independent symbolic computation

[Wolfram source](../computations/gst_direct_alpha_deRham_curvature_certificate_2026_10_23.wl), final fetched blob `17c949a7ce9629069adf5fb3447d1700a0e114b0` executed verbatim through the connected exact Wolfram kernel:

- **28/28** exact NEW Newton Chern-root tests, all 1≤p≤r≤7, using elementary symmetric polynomials computed from independent root variables versus independent power-sum computations; no failures.
- Exact countercheck c2 difference=1 versus ch2 difference=1/2 for E+ roots {1,1}, E- roots {0,1}; both `NaiveTopChernDifferenceWrong=True` and `FullMinorPolynomialCorrect=True`.
- **54/54** idempotent tangent-conjugacy matrix tests m=1..9,r=0..m; symbolic general proof in source.
- Genuine P1 rank-one algebraic incidence projector idempotent and exact curvature `-du∧dv/(1+uv)^2`; Gr(2,5) nondivisor rational degree-two formula `5ch₂(S)-ch₂(O(1))=5((2/5)h²-s₂)` verified EXACT.

**Evidence:** the all-p Newton theorem is a universal formal splitting-principle proof in true Chow; finite Wolfram cases are independent algebraic regression tests, not universal extrapolation. The corrected source is a genuine finite Fitting-scheme CHOW constructor from any actual solution of the prescribed-alpha algebraic curvature equations. Existence of such a solution for every unsupported rational Hodge primitive class is NOT produced by these transformations; that remains the exact arbitrary-X research target, not a hidden hypothesis.

**Changed files:** mathematical derivation and Wolfram source already updated in place; this audit is the durable correction record. No Lean file was edited or compiled.
