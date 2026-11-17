# Verified GST emergent-dimensional causal fold kernel and typed Hodge-charge leakage audit

**Date:** 2026-10-21. **Mathematical authority:** [GST_emergent_dimension_causal_hodge_fold_2026_10_21.tex](../derivations/GST_emergent_dimension_causal_hodge_fold_2026_10_21.tex), especially Sections "Universal all-N Hodge-instability" and "GST causal leakage operator". **Correct source record:** [GST emergent-dimensional fold program](2026-10-21-gst-emergent-dimensional-causal-hodge-fold-program.md). **Kernel-verified GitHub workflow:** [GST Emergent Dimension Causal Fold, successful run 39629966545](https://github.com/kyo-oo/HC-PROOF/actions/runs/39629966545), run HEAD SHA `0b6428fa1790ea022f616cb87619ccb2f48ebf72`. Its single Lean job completed with conclusion SUCCESS, and its explicit "Kernel compile emergent-world causal fold theorems" step completed SUCCESS. Job id `119325259073`. The workflow invokes `lake build GSTEmergentDimensionalCausalFold`, with sole root `GSTGradedWorldAlgebra`, and rejects `sorryAx`. No local Lean installation.

## Exact Lean declarations whose build passed

Updated EXISTING `GSTGradedWorldAlgebra.lean`, not an unrelated wrapper:
- `cosmicTateFold (j) (a,b)=(a+j,b+j)`
- `cosmicTateFold_degree` proving D increases by 2j
- `cosmicTateFold_charge` proving signed Q remains constant
- `cosmicTateFold_comp` proving exact addition of fold depths
- `cosmicTateFold_charge_zero_iff` preserving the diagonal Q=0 sector
- `cosmicTatePath` and `cosmicTatePath_charge` proving all finite sequences of same-type dimension folds conserve signed charge.

**Scope:** the Lean kernel proves the abstract Nat×Nat GST graded-world theorems and their finite causal histories, NOT the canonical Hodge realization of arbitrary smooth projective X, the rational Hodge conjecture, or the geometric all-N projective-bundle theorem. The geometric proof is in the separate LaTeX source and verified exact finite Wolfram calculations.

## New typed Hodge-charge leakage theorem

For ANY given actual fixed-degree Hodge realization `V=⊕_(a+b=m)H^(a,b)`, let `P_q` project onto summed bidegrees of signed charge `q=a−b`. For a specified cohomological fold `F`, define the actual operator
`L_q(F)=Σ_(r≠q) P_r F P_q`.
**Exact identity:** F preserves the Hodge signed charge of EVERY homogeneous source iff `L_q(F)=0` for all q. Every finite composition of Hodge-safe causal operations stays safe. An algebraic Tate/push/pull edge satisfies the condition by true Hodge functoriality, provided its degree and Tate shifts are treated correctly.

For the actual smooth partial-conjugation involution on A=E_i×E_i, the rational algebraic mixed-diagonal class eta is pure charge 0 and its image eta' is pure sum of signed charges +2 and -2. Thus `L_0(F*)(eta)=eta'≠0`. Since `(F*)²=id`, the SECOND non-holomorphic fold returns eta' to the rational Hodge (1,1) sector. This gives BOTH user-proposed directional outcomes as explicit equations: Hodge→nonHodge→Hodge under two causal steps. It does NOT yield a Hodge-conjecture counterexample because the intermediate non-Hodge class is not in the rational (p,p) hypothesis.

For arbitrary nonempty original smooth projective X and any N≥0, stabilization with E_i×E_i×P^N yields actual classes whose signed charges change from 0 to ±2 for all 0≤j≤N. This is universal across ALL X after stabilization; it does NOT assert a non-Hodge image on the untouched original X.

## Fully executed Wolfram script

[Reproducible exact Wolfram source](../computations/gst_emergent_dimension_causal_fold_2026_10_21.wl), file blob SHA `c0e2b0843455e4038358c0d12b66f13e417a3d97`. Stateless evaluation through WolframLanguageEvaluator returned:
- N3SymbolicLeftInverse=True and N3SymbolicRightInverse=True;
- N0Through9ExactReconstruction={{0,True},...,{9,True}};
- InitialAbelianSurfaceHodge02Coefficient=0;
- FoldedAbelianSurfaceHodge02Coefficient=-2 I;
- PartialFoldInvolution=True;
- explicit PASS success message.

## Causal law interpretation boundary

The abstract GST `HigherCausalCosmos.Cell n` is a coherence n-cell, not automatically a geometric n-dimensional manifold; `cosmic_hodge_rank_one` is an abstract rank-one world diagonal, not a bound for actual Hodge numbers. The genuinely typed interface is a Hodge cohomological realization, not an arbitrary assignment of internal graph indices to `H^{p,q}(X)`. Smooth projective algebraic folds conserve signed Hodge charge and have exact Chow/Hodge defect splittings; a nonholomorphic fold violates that interface, and a nodal fold changes the geometric category to mixed Hodge.

**Conclusion:** Exact signed charge theorem NOW Lean kernel green, exact Wolfram calculations passed, all-N geometric fold mathematics recorded, and explicit Hodge-breaking/restoring causal operator obtained. The all-arbitrary-X rational Chow source-birth target remains distinct; neither algebraic dimensional folding nor Hodge-breaking topological folding automatically constructs a new algebraic cycle on the original X.
