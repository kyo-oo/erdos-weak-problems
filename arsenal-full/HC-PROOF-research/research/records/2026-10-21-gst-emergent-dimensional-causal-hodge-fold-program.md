# GST emergent dimensions, causal graph folds and Hodge-type bifurcation — executed mathematics

**Date:** 2026-10-21 IST. **Pin:** `62e5f97b265ad437c0a1c79f449b4aeec5908b44`, active branch `research/gpt6-native-point-primitive-span-20261017`. **User hypothesis:** Temporarily ASSUME the rational Hodge conjecture true on every smooth projective complex variety, then perturb the emergent dimensions and GST higher causal graph laws to distinguish Hodge-preserving from Hodge-breaking folds. **Mathematical artifact:** [GST_emergent_dimension_causal_hodge_fold_2026_10_21.tex](../derivations/GST_emergent_dimension_causal_hodge_fold_2026_10_21.tex); **Lean change:** [GSTGradedWorldAlgebra.lean](../../GSTGradedWorldAlgebra.lean); **exact Wolfram experiment:** [gst_emergent_dimension_causal_fold_2026_10_21.wl](../computations/gst_emergent_dimension_causal_fold_2026_10_21.wl). No public internet research and no local Lean installation.

## Did we read all 701 Lean files?

**NO.** GitHub recursive tree was inspected at pinned original head and reported exactly **701 Lean files**, with no truncation. This is a complete *file census*, not a complete read of every one of the 701 bodies. We newly inspected the actual source text or theorem inventory of the most directly load-bearing modules:

- `GSTGeneralSpace.lean`: GeneralSpace carrier and identity/associative paths have NO metric or dimension field. Charts and grading are optional observations. This grounds the user's dimensional-emergence intuition literally, as an ABSTRACT ontology.
- `GSTGeneralSpaceSchemeDimensionObservation.lean`: Krull dimension as an observation of scheme-local geometry, not a primitive field.
- `GSTGeneralSpaceTopology.lean`: genuine topology and path realization as an optional capability.
- `GSTGeneralSpaceCohomology.lean`: graded cohomology is optional; `algebraicity_iff_reversible_general_space_transport` and `missing_native_direction_persists_recoordination` preserve native-image membership under genuine compatible REVERSIBLE transports. A non-holomorphic topological fold is not automatically such a compatible cycle-class transport.
- `GSTGeneralSpaceFunctorialRealization.lean`: real pullback/transport composition and observation naturality.
- `GSTGradedWorldAlgebra.lean`: `cosmicDegree (a,b)=a+b`, `cosmicCharge (a,b)=a-b` on UNBOUNDED CosmicCell. The pair jointly determines coordinates; finite-window spectral projectors are distinct from arbitrary-X real Hodge decomposition.
- `GSTDimensionFreeHodgeDiagonal.lean`: `cosmicDiagonalClass(p)` and `cosmic_hodge_rank_one` are the **rank-one abstract cosmic diagonal**, not a theorem that actual Hodge `H^{p,p}(X)` has rank one for all X.
- `GSTGraphV2NonEuclidean.lean` and `GSTGraphV2NonEuclideanLaws.lean`: seven-axis combinatorial vertex paths, forward/carry/physical witness laws in the non-Euclidean graph. They are not by themselves holomorphic maps of smooth projective varieties.
- `GSTGraphV2OmniversalCore.lean`: three-sector event graph and closure; typed paths and functorial event morphisms.
- `GSTGraphV2SelfExpandingCosmology.lean`: world birth, internal laws, actual rational `TwoSourceBirth` cycle-source decomposition and `SplitTwoSourceBirth`, including `split_world_birth_hodge_complete_iff_sources` and canonical finite-flat/blowup defect transport. New worlds can BIRTH independent exceptional geometry when it is independently realized; the abstract graph does not assert universal source birth.
- `GSTGraphV2RecursiveStateCausality.lean`: world-dependent packed states, local events vs cross-world transport, closure and `StatePath.preserves` for stable predicates.
- `GSTGraphV2UnboundedHigherCausality.lean`: higher globular cells for every NATURAL level with identities, source/target coherence, and identity tower preservation. Its level N is a *causal coherence dimension*, not proof of a geometric smooth projective n-fold.
- `GSTGraphV2GeneralSpaceRealization.lean`: embeds concrete Graph V2 seven-axes as GeneralSpace and uses genuine forward paths.
- `GSTClassicalHodgeDegreeCertifiedOmniverseCausalCompiler.lean`: degree-certified source compiler assumes an actual target-bearing primitive input; no inferred unconditional Chow source.
- `GSTAllDimensionProjectivePrimitiveCycles.lean`: actual projective product family in every m, not all arbitrary varieties; concrete all-dimensional coefficient theorem.
- `GSTWorldRecoordinationGroupoid.lean` and `GSTGradedNativeCohomologyRealization.lean` listed by tree as related; not all source bodies were independently audited.

Full all-file semantic audit still requires reading the remaining file bodies and reconciling imports/conventions; no claim otherwise.

## EXACT executed mathematics: geometric fold for ALL N

For arbitrary original smooth projective X and actual rank N+1 algebraic vector bundle E, let Y_N=P_X(E). It has complex dimension dim X+N, true projective Chow/Hodge decompositions indexed j=0..N, and the actual TATE fold `(a,b)→(a+j,b+j)` shifts degree by 2j but preserves signed GST cosmic charge a−b. This is proved by actual Hodge functoriality for algebraic pullback, Gysin, cup by Chow cycle and their compositions.

**New exact Chern--Segre causal reconstruction:** for beta=Σ_i ξ^i π*alpha_i, define y_j=π*(ξ^(N-j) beta). Then `y_j=Σ_(i≥j) s_(i-j)(E) alpha_i` and `alpha_j=Σ_(l≥j)(−1)^(l-j)c_(l-j)(E) y_l`, with `Σs_k t^k=1/c_E(−t)`. This holds for every N by formal generating-function inversion, respecting true graded degrees and both Chow and Betti types. In particular the genuine defect D^p(Y_N)=Hdg^p(Y_N)_Q / cl^can CH^p(Y_N)_Q splits exactly as `⊕_(j=0)^N D^(p-j)(X)`: higher dimensions do not erase original-X defects.

**Irreversible world birth by blowup:** for arbitrary smooth center Z⊂X codim c≥2, Y=Bl_Z X has actual Chow/Hodge/Gysin split `D^p(Y)≅D^p(X)⊕Σ_(a=1)^(c-1)D^(p-a)(Z)`. This instantiates the GST SplitTwoSourceBirth idea and proves exact defect conservation. New exceptional Hodge geometry can be added, but base defects remain.

## EXACT executed mathematics: Hodge-breaking actual topological fold

Let A=E_i×E_i, eta=dx1∧dy2−dy1∧dx2 the actual rational algebraic divisor combination `[{0}×E]+[E×{0}]−[diagonal]`. Its rational class is type (1,1). On the SAME underlying smooth real four-manifold the involution F(x1,y1;x2,y2)=(x1,−y1;x2,y2) is a genuine smooth lattice automorphism but not holomorphic. It sends eta to eta'=dx1∧dy2+dy1∧dx2, with exact Hodge decomposition `eta'=(omega1∧omega2−conjugate(omega1)∧conjugate(omega2))/(2i)`. Thus the coefficient of eta∧omega1∧omega2 is ZERO, while that of eta'∧omega1∧omega2 is EXACTLY `−2i`, computed independently by Wolfram exact alternating tensor evaluation. The image has pure (2,0)+(0,2) components and zero (1,1), hence is RATIONAL but NON-HODGE. It lies outside the hypothesis of the rational Hodge conjecture; no contradiction.

**Every-X, every-N stabilization:** for any nonempty smooth projective X and N≥0, Y_(X,N)=X×A×P^N is actual smooth projective. For any 0≤j≤N, `gamma=pr_A^*eta ⋅ pr_P^*h^j` is an actual algebraic rational Hodge (j+1,j+1) class. The actual smooth involution `id_X×F×id_P` produces NONZERO (j+2,j) and (j,j+2) Kunneth pieces, both charges ±2, with zero (j+1,j+1) component. This is valid in arbitrary high emergent dimension but on a STABILIZED X, not proof that every X itself has such a fold.

**Topology-changing singular fold:** identify two points on P1 to form a projective nodal rational curve C. The normalization exact constant-sheaf sequence yields `H^1(C,Q)=Q(0)` (weight 0) despite cohomological degree 1; `H^2(C,Q)=Q(−1)`. Thus topology-changing singularization produces a mixed-Hodge boundary phenomenon because the output is not smooth projective, again no contradiction to HC.

## Formal GST law upgrade

Updated EXISTING `GSTGradedWorldAlgebra.lean` with actual Lean propositions `cosmicTateFold`, `cosmicTateFold_degree`, `cosmicTateFold_charge`, `cosmicTateFold_comp`, `cosmicTateFold_charge_zero_iff`, `cosmicTatePath`, `cosmicTatePath_charge`. These are Nat×Nat algebraic coordinate theorems for arbitrary folds and arbitrary finite causal histories; they do NOT claim to verify complex geometry. Added branch-specific [GitHub Actions Lean kernel workflow](../../.github/workflows/gst-emergent-dimension-causal-fold.yml) to compile exactly that existing Lean file, with no local Lean run. Until a run is actually retrieved as green, the Lean edit is unverified; never claim success from `#check` text alone.

## Exact Wolfram execution and evidence limits

- Wolfram exact 4×4 symbolic fold matrix for N=3: both Chern--Segre inverse products identity, all four free coefficients reconstructed.
- Independent exact integer Chern tests N=0..9: all 10 inverse tests returned TRUE. Finite computation is not the all-N proof.
- On actual E_i×E_i, the original eta Hodge (0,2) wedge test returned 0, partial conjugation returned `−2i`; F^2=identity.
- Nodal rank from normalization exact sheaf calculation, not Wolfram.
- All-N result from projective bundle theorem and generating series; defect identities from actual Chow/Hodge direct sums.
- No universal Hodge source construction, no HC counterexample, and no complete 701-file review claimed.

**Next scientific differentiator within THIS proposed route:** Build a GST causal edge whose original-X geometric realization is genuinely algebraic and whose induced map on Hodge/Chow defects fails to be split native-image-preserving (e.g. independent nonambient center with certified original-X return). If none is found, the dimension-fold operation is a diagnostic transformation of Hodge type rather than a source-birth mechanism.
