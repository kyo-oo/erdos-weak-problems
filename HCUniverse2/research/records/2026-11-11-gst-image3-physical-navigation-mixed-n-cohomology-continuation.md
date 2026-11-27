# Continued GST Image-3 source phase — exact physical Navigation classification and mixed N-hole global cyclicity

**Parent checkpoint:** `research/records/2026-11-11-gst-image3-advanced-curvature-rigidity-checkpoint.md`.

**Work branch:** `research/gpt6-image3-advanced-curvature-rigidity-20261111`.
**Active original-X target:** construct a noncircular universally valid Chow/Hodge geometric landing from original GST source operators on arbitrary smooth projective complex X.

## Native mathematical results added

1. **Actual Navigation off:** for the author's original twelve-cell seed, the full Krylov determinant of `U+J+a M` is exactly
   `-4*a^2*(1+a)*Q8(a)*Q9(a)`, with original ten-cell Q8 and interblock resultant Q9 defined in the committed computation and Lean F19 certificate.
   - Complete residue tables over F19 have NO roots for Q8 or Q9; leading coefficients 256,640 both invertible mod19. Thus no rational roots of these factors.
   - Full original twelve-cell cyclicity iff rational `a != 0` and `a != -1`.
   - Exact exceptional orbit ranks: 10 at a=0, 11 at a=-1. This is native source algebra, NOT a Hodge-cycle theorem.
2. **Actual Navigation on:** existing original b=1 proof gives full twelve-cell cyclicity for **all rational a** via Q8*Q12 and complete F11 proof.
3. **Physical Navigation joint criterion:** for each arithmetic state R and rational a, native rank12 iff `Navigation R || (a != 0 && a != -1)`. No arbitrary half-strength gate is substituted for the true Boolean Navigation charge.
4. **Heterogeneous original N-hole global source:** for arbitrary finite h and original hole-dependent rational a_i and true arithmetic R_i, if each hole satisfies that same exact cyclicity condition, set `L=max|a_i|`, `S=9+4L`, `T=⊕_i(F_(a_i,b_i)+i S I)`, `v_h=(seed,...,seed)`. All block spectral discs are disjoint because original row-sum norms <= 4+2L and S>2(4+2L); polynomial CRT gives a SINGLE full rank12h Krylov orbit. This is stronger than independent holewise two-step cover, and does not claim target Hodge algebraicity.
5. **Lean fusion upgraded:** `GSTImageThreePhysicalNCohoFusion.lean` composes the actual physical navigation predicates with every original `NShape` source hole and proves independent pair reconstruction without synthetic off-resonance hypotheses, plus exact independent-hole original canonical perfect-power tail transport.
6. **CI fixes:** `GSTImageThreePhysicalNavigationControl.lean` and `GSTImageThreeIndependentNCohoSource.lean` explicitly open the original `GSTGraphV2CMWaveFusion` namespace. This repairs the accidental free-implicit `seed`/`WaveSignal` elaboration seen in failed prior runs. The latest exact-HEAD CI must be inspected; a running build is not a success.

## Exact reproducible evidence

- `research/computations/GST_image3_navigation_off_exact_rational_cyclicity_mod19_20261111.wl`: source rebuilt from owner's original cell formulas; both exact 2+10 resultant and full 12x12 determinant computed independently; complete F19 tables and exception ranks verified; Wolfram returned `allPassed -> True`.
- `GSTImageThreeNavigationOffSourceCertificates.lean`: complete finite-field F19 nonroot and leading-unit declarations. A successful GitHub build is required before calling these kernel-certified.
- `research/computations/GST_image3_mixed_physical_N_holes_global_Krylov_20261111.wl`: exact full 24x24 Krylov ranks verified for three distinct mixed physical hole systems with varying direct strengths; Wolfram returned `allPassed -> True`.
- Detailed derivation sections 12–14: `research/derivations/GST_image3_CM_curvature_two_ten_resultant_exact_2026_11_11.md`.

## Strict boundary and active proof target

Exact native cyclicity and full 12h source dimension are **proven algebraic facts about the native GST model**, with source determinant identities and CRT arguments supported by exact symbolic evidence. The arithmetic finite-field certificates have been submitted as new Lean files, but universal rational-root, all-parameter determinant and all-h CRT consequences are not yet kernel-formalized as Lean theorems.

The remaining universal mathematical issue is NOT the native dimension ceiling. It is the original-X geometric identification: actual closed algebraic correspondences, canonical cycle-class functoriality including the appropriate intersection multiplicity, and a surjective comparison with each rational Hodge fiber without assuming the desired algebraicity. The operator-pair image-stability theorem makes this separation precise.
