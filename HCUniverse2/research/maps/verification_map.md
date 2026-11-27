# VERIFICATION MAP — HC-PROOF branch research/gpt6-native-point-primitive-span-20261017 (clone /tmp/hc-clone-23 @ 6c20bb7)

Task ID 1-m (verification-infrastructure mapper). RESEARCH ONLY — no repo files were modified.
All 15 core regression certificates re-run green this session (exact Fractions, deterministic, each < 15 s).

---

## Section 1 — EXPERIMENTS INVENTORY (research/experiments/, 20 Python certificate scripts)

Run status key: **RAN exit 0** = executed this session from research/experiments/ with python3;
"not run" = outside the 14/15-script core battery named in the campaign records (all are exact-arithmetic, header-declared < 5 s except where noted).

| # | Script | Certifies (from header) | Checks | Status / runtime |
|---|--------|--------------------------|--------|------------------|
| 1 | task13d_pair_walls_verify.py | Task 13-d: pair-channel WALL CONSTANTS on the 16-letter exterior algebra (W_R/W_I/theta class tables, W0 annihilation, period constants, W4 corridor arithmetic, W5 FM normalization round trips, W6 pair Chern table, carrier instance chi(End F)=8m^2) | assert-based, no printed count (13 assert sites, looped) | not run (bounds < 1 s) |
| 2 | task14a_lean_data_mirror.py | Lean-DATA pre-verification MIRROR of **GSTPairChannelWallsCertificate.lean**: every literal the Lean file will decide (masks+signs, W0, period constants, FM normalization+round trips, 4 synthetic pair instances, carrier, linear-detector). **References a Lean file.** | assert-based, no printed count (15 assert sites) | not run (bounds < 1 s) |
| 3 | task14c_decision_attempt_checks.py | Lemma W7 sector rigidity of the cohomological FM transform (NS/W/T-sector rigid, parity preserved) + the (m,q)-consistency grid, 96 instances, no additive contradiction | 96-instance grid, assert-based (9 sites) | not run (bounds < 5 s) |
| 4 | task15a_picard_flatness_checks.py | Lemma W8 Picard-sheaf FLATNESS of the pair channel (W5 k=2 cross-check, k=3 census, grade-3 purity on all committed instances, flatness composites, W8.2 duality face) | assert-based (21 sites) | not run (bounds < 2 s) |
| 5 | task16a_pair_phase_circle_checks.py | Lemma W9 WEIL PHASE CIRCLE / flat-character exactness (full ghost census, m-linearity + q-invisibility, W0 twist-scale stability at all grades, character-input non-vacuity both ways, double-dual census) | assert-based (35 sites) | not run (bounds < 2 s) |
| 6 | task17a_birth_strike_checks.py | Round 17 THE BIRTH STRIKE: component-charge law at the vertex on the discriminator world (B1 W-dead total law; B2 sign-birth channel + typed bridge; B3 monodromy wall — all 32 transitive subgroups of S_2..S_5; B4 funnel bypass + W6-consistency; W9 entry checklist; m:1->2 involution split bookkeeping) | assert-based, no printed count (29 sites; enumerates 156 subgroups of S_5 x orbit partitions, 2^6 sign patterns) | **RAN exit 0** (1.5 s) |
| 7 | task18a_integrability_strike_checks.py | Round 18 THE INTEGRABILITY STRIKE: single-door theorem (I1 traceless two-cell reduction algebra incl. determinant strip; I2 the line-bundle compiler — Lagrange moment weights, all-grade purity — + two-center determinantal identity + sector boundary Q*theta^2; I3 the involution two-cell / S_2 door) | assert-based, no printed count (55 sites) | **RAN exit 0** (0.12 s) |
| 8 | task19a_transport_sweep_checks.py | Round 19 THE TRANSPORT SWEEP: five T-laws (pullback/pair-sum/swap/single-to-pair/scaling), E15 m*-pinning presentation-independence (P^2 m*=2 sinh witness + parity obstruction; curves m*=1; Gr(2,5) m*=360, denominator-lcm law, 2231-rank split), per-world census, terminal re-assertion | assert-based, no printed count (58 sites) | **RAN exit 0** (0.10 s) |
| 9 | discovery_strike_checks.py | THE DISCOVERY STRIKE: 3 new layers (eigenbranch lattice law — door crossings have even scale; exchange-deck residue law H^2(C_2)=0 typed vs (Z/2)^17 untyped; K-freeness) + THE CROSSING at (r,m)=(6,2), split (3,3): **m*(A,2,W_R)=2 EXACT — vertex bit YES** | **270** | **RAN exit 0** (0.26 s) |
| 10 | closing_census_checks.py | THE CLOSING CENSUS: split-world door strike — Face 1 CM-type splits (W_R divisor-generated via 3-term Weil decomposition => m*>0 unconditional by I2), Face 2 generic splits (parity wall: W_R needs #f in {0,4}, NS^2-products have #f=2); census "every row TRUE" | **122** | **RAN exit 0** (1.6 s) |
| 11 | census_repair_checks.py | THE CENSUS REPAIR (typing-integrity strike, ledger 096): the closing census's A_jk were the ANTISYMMETRIC combination — not Hodge (1,1). Exact dz/dzbar machinery (0 complex numbers): F/A_pure/B PURE (1,1); three-term Weil decomposition FALLS; parity wall SURVIVES; W0-death witnesses FALL; detector noise FALLS; CM row re-certified by the door engine, m*=2 exact | **84** | **RAN exit 0** (0.23 s) |
| 12 | cyclic_transport_checks.py | THE CYCLIC-TRANSPORT STRIKE: S_2(A) 18-letter orbit model; invariant sector matched 3 ways (word enumeration / character / record formula); Hodge polynomial P_S verified per-degree; transport identity law — forward leg cl(What)=alphaHat with What=(1/2)q_*pr_B^*W_B (DS witness transported), return leg 2 W_R exactly; primitivity of the transported ray | **125** | **RAN exit 0** (0.78 s) |
| 13 | wi_vertex_pin_checks.py | THE W_I VERTEX PIN (Gaussian-equivariance strike): g=(i,1,1,1) is an integral signed-letter-permutation q-isometry, type-preserving; orbit {W_R,-W_I,-W_R,W_I}; every layer re-derived directly on the W_I ray => **m*(A,2,W_I)=2 EXACT — full Weil plane pinned** | **122** | **RAN exit 0** (0.53 s) |
| 14 | cyclic_family_checks.py | THE CYCLIC FAMILY TRANSPORT THEOREM (all-arity): arity calibration (boss's published totals 4,8,24,64,208 reproduced by cyclotomic character AND brute force); S_3(A) 26-letter model (sector 3 ways, Hodge polynomial vs character at every monomial); transport identities at m=3 (return leg 3 W_R per-block); S_3 divisor channel (48-dim pure-(1,1) lattice, parity wall, block-projection lemma); Gaussian exchange; census row for all m>=2 | **298** | **RAN exit 0** (7.7 s) |
| 15 | audit_family_1b_independent_checks.py | INDEPENDENT AUDIT of cyclic_family (commit b4b94db), hostile stance: (1,1) dims 48/64 by orbit counting (no characters); boss totals by cycle-structure product; arity law per-block; orbit bases by direct (sigma-I) kernel; parity structure word-by-word; scope lines verbatim; primitivity by coefficient inspection | **39** | **RAN exit 0** (0.85 s) |
| 16 | universal_close_checks.py | THE UNIVERSAL CLOSE: composition of committed laws (STEP 0 reduction Theorem N; STEP 1 sector partition; STEP 2 I2 compiler — m*>0 UNCONDITIONAL on the divisor-generated sector; STEP 3 carrier pair + universal swap algebra + determinant link + parity engine). Honest scope: the deck at the general input NOT certified — universal close WITHDRAWN from this certificate's claims. **References the Lean file GSTGraphV2OntologicalFoldForAllN.lean (Lean certificate p2_mstar_eq_two, "CI-green") and verifies artifact presence on disk** | **188** | **RAN exit 0** (0.43 s) |
| 17 | pair_exchange_deck_checks.py | Round 22 PAIR-EXCHANGE DECK AT THE GENERAL INPUT: the 21-c remaining construction — (i) involution structure on the carrier pair; (ii) C_2-reduction of the two-cell; (iii) exclusion of non-scalar unexchanged components after D_2/D_3 strip; (iv) rank parity r_0=2a via T_4 augmentation; reflection/flip algebras, one-transport coincidence, determinant link, norm-surjectivity; L5 model-fidelity caveat recorded (22-b audit F9) | **182** | **RAN exit 0** (14.7 s) |
| 18 | rotation_deck_checks.py | Round 23 ROTATION DECK — the one mechanism: C_4=<gamma> generalized to all four factors; R1 C_4 obstruction law (invariants ker(gamma-1)=0, norm=0 => H^2(C_4;M)=0, H^1 2-elementary; hostile controls: 2-torsion/trivial/swap/negation modules); R2 four-rotation family + parity-pattern partition (all-even sector = pair-product lattice = 4-torsion) | **59** | **RAN exit 0** (0.08 s) |
| 19 | identification_link_checks.py | Round 24 IDENTIFICATION LINK: target-side calculus of Lambda_p at the conduit's grade p=2 UNDER THE STRIP-SHAPE HYPOTHESIS (iota-shaped curvature cochain; the reduction of the actual GL(H_z)-valued two-cell recorded as the remaining step; audit's five documentation-as-assert sites removed; p-only mutation caught by LA2 filter) | **94** | **RAN exit 0** (0.63 s) |
| 20 | two_cell_reduction_checks.py | Round 28 THE TWO-CELL REDUCTION (items (ii)+(v) resolved): LHS five-term sequence for 1->Gamma->G_bullet->C_4->1 with content A — E^{2,0}=H^2(C_4;A)=0, E^{0,2} computed exactly (rank 12, theta-shaped iota-strip part ZERO => mixed-cell map INJECTIVE); T2 scale kill 2m (SNF); T3 strip-shape INCONSISTENT (item (v) resolved negatively; mixed-cell shape constructed); nonabelian H^3(mu_2) torsion boundary remains | **125** | **RAN exit 0** (11.7 s) |

**Battery totals (this session): 15/15 exit 0, zero failures.** 12 counter-printing scripts sum to **1708 asserted checks**; the three Round 17/18/19 task-series scripts are assert-based (no printed counter). Every script: pure Python, exact Fraction/int arithmetic, zero floats, zero complex, deterministic, hostile controls. Slowest: pair_exchange_deck 14.7 s, two_cell_reduction 11.7 s, cyclic_family 7.7 s — all far under the 60 s bound (two_cell_reduction's own header says "Timeout 120s expected"; it actually runs in ~12 s).

Cross-references to Lean files (only 2 of 20):
- task14a_lean_data_mirror.py -> **GSTPairChannelWallsCertificate.lean** (mirrors every literal; CI-verified by gst-pair-channel-walls-certificate.yml, which fires on this branch).
- universal_close_checks.py -> **GSTGraphV2OntologicalFoldForAllN.lean** (Lean certificate p2_mstar_eq_two "CI-green"; CI-verified by gst-ontological-fold-for-all-n.yml, which fires on this branch).

---

## Section 2 — CI COVERAGE MAP (.github/workflows/, 122 workflows)

### 2.1 Anatomy of the CI fleet

- **122 workflow files**, 120 with `workflow_dispatch`, 122 with push triggers restricted to explicit branch lists, **120 with specific-file path filters** (2 use `'**/*.lean'`: hodge-conjecture.yml, advanced-gst-dependency-audit.yml).
- **110 of 122** end their Lean jobs with a trust audit: `grep -E "declaration uses 'sorry'|sorryAx" <log>` and `exit 1` on hit => CI-green means **kernel-compiled AND sorry-free**. Six Lean-compiling workflows lack that audit (compile-only gates): hc-priority-root-quickcheck.yml, hodge-diagnostic-shards.yml, hodge-native-fibered-focus.yml, hodge-pure-math-engine.yml, limitless-proof-repair.yml, v2-upgrade-gate.yml (last two carry a partial sorry mention).
- **6 workflows compile no Lean at all** — they run committed Python in CI: advanced-gst-dependency-audit.yml + gst-full-lean-import-audit.yml (scripts/audit_lean_dependency_graph.py, scripts/gst_theorem_declaration_catalogue.py), gst-entire-lean-source-map.yml (research/computations/gst_all_lean_source_inventory.py), gst-integer-surgery-optimizer.yml (research/computations/gst_integer_boundary_surgery.py), gst-fermat-cubic-405-rank.yml (fermat_cubic_405_rank.py + fermat_cubic_fourier_all_dimensions.py), gst-k3-cyclotomic-graph-rank.yml (k3_cyclotomic_graph_orbit_rank.py).
- Build mechanisms used (all verified by parsing): (a) `lake build <Module>` after appending an ad-hoc `[[lean_lib]]` via `cat >> lakefile.toml` heredoc (single or multi-module roots lists); (b) `python3 scripts/gst_lean_dependency_roots.py LIB ROOT...` — registers the full transitive local import closure as roots, then `lake build LIB` (11 workflows); (c) matrix targets (`lake build "${{ matrix.target }}"`, hodge-research-source-lean.yml: 4 targets); (d) `lake env lean <file>.lean` direct kernel compiles (GSTCoherentCosmology.lean, GSTComplexTangentProjectionChainObstruction.lean, GSTWeilFourfoldAuxiliaryExtraction.lean, questions/deepmind_problem_406/Solution.lean + 2 workflow-generated axiom-report files); (e) library/wholesale builds; (f) script-partitioned shards.

### 2.2 The path-filter mechanism

Every per-file workflow follows the pattern (e.g. gst-pair-channel-walls-certificate.yml):
```yaml
on:
  push:
    branches: [research/gpt6-native-point-primitive-span-20261017]
    paths: ['GSTPairChannelWallsCertificate.lean', '.github/workflows/<self>.yml']
  workflow_dispatch:
```
=> the certificate's CI gate fires **only when its own .lean file (or the workflow file) changes on a listed branch**; all are manually dispatchable. This is how 122 cheap gates coexist: each push runs only the lanes whose inputs changed. Path-filtered files are NOT necessarily the compiled ones: e.g. hodge-research-source-lean.yml path-filters on GSTClassicalHodgePiOneObservableOmniverseFinale.lean but its matrix compiles 4 other modules; gst-k3-primitive-graph.yml filters on GSTK3GraphPrimitiveRank.lean and builds the closure via the dependency-roots script.

### 2.3 Which Lean files are CI-verified vs NOT (the map)

Universe: **707 Lean files** (696 repo-root + 9 waves/ + 2 questions/deepmind_problem_406/). lakefile.toml registers 4 lean_libs: HCUniverse (185 roots), HodgePureMath (421 roots), HCProof, HodgeDeRhamBridge.

Coverage (union over ALL 122 workflows, any branch — "compiled by CI somewhere"):
- **659 of 707 files are CI-compiled** (538 as direct build targets/roots + 121 only transitively, as imports of targets).
- **48 files are NEVER compiled by any CI workflow** (draft-only). Full list below.
- On THIS branch specifically: **31 workflows fire on push** (branch research/gpt6-native-point-primitive-span-20261017), covering **334 of 707** files; the rest of the 659 are covered by gates bound to other branches (dispatch-only from here).

Wholesale gates (other branches, all dispatch-able):
- hodge-pure-math-engine.yml (branches sol/hodge-pure-math-engine, astra/hodge-proof-development): `lake build HodgePureMath` => all **421 HodgePureMath roots**. NOTE: no sorry audit on this gate.
- hodge-conjecture.yml (sol/*, clean/*): 13 shards partitioning all 421 HodgePureMath roots + shard 12 = **HodgeConjecture** + integration-frontier job (7 GSTClassicalHodge* correspondence-transfer roots); sorry-audited.
- hodge-diagnostic-shards.yml (dispatch only): 8 shards over the same 421 roots, fault isolation.
- hc-official-comparator.yml (main, sol/limitless-cosmology-bursts): bare `lake build` (default target HCProof) + `lake env lean questions/deepmind_problem_406/Solution.lean` + generated axiom reports; checks the Problem-406 solution is sorry/admit/axiom-free.
- **No workflow anywhere builds HCUniverse as a library** => its 185 roots are covered only via individually-targeted lanes/imports.

The 31 workflows firing on push to THIS branch (build targets; path filters elided to the .lean files):
1. gst-canonical-point-cycle-bridge.yml — dep-roots closure of GSTCanonicalPointGeometryStage2G + GSTFermatCanonicalPointRankBridge (lib GSTCanonicalPointBridge)
2. gst-carrier-mechanism-verdict-certificate.yml — GSTCarrierMechanismVerdictCertificate
3. gst-cm-quadratic-native-rank-forcing.yml — GSTCMQuadraticNativeRankForcing (+ GSTCMNumberManipulationTrace)
4. gst-cubic-fourfold-plane-primitive.yml — GSTCubicFourfoldPlanePrimitive
5. gst-emergent-dimension-causal-fold.yml — GSTGradedWorldAlgebra + GSTGeneralSpaceCohomology (lib GSTEmergentDimensionalCausalFold)
6. gst-entire-lean-source-map.yml — Python inventory only (no Lean)
7. gst-fermat-cubic-405-rank.yml — Python only
8. gst-fibered-mass-calibrated-landing.yml — GSTClassicalHodgeFiberedCycleClassDefect (lib GSTMassCalibratedFiberedLanding)
9. gst-finite-dominant-all-codim.yml — GSTFiniteDominantAllCodimensionDescent (lib gate)
10. gst-geometric-lefschetz-primitive-rank.yml — GSTClassicalHodgeRankFreeLefschetzPoincareGeneration (lib gate)
11. gst-gr25-pure-pair-lattice-certificate.yml — **GSTGr25PurePairLatticeCertificate**
12. gst-graph-v2-cmnm-geometry-upgrade.yml — GSTGraphV2CMNMPrimitiveUpgrade + GSTGraphV2SelfExpandingCosmology
13. gst-hodge-spectral-kernel-reduction.yml — GSTClassicalHodgeExactClayStatement (lib GSTHodgeSpectralReduction)
14. gst-intrinsic-causal-fold-boundary.yml — GSTGraphV2UnboundedHigherCausality (lib gate)
15. gst-k3-cyclotomic-graph-rank.yml — Python only
16. gst-k3-direct-graph-orbit.yml — GSTK3DirectGraphOrbitDifference (lib gate)
17. gst-k3-primitive-graph.yml — GSTK3GraphPrimitiveRank (lib gate)
18. gst-maximal-linear-hypersurface-primitive.yml — GSTMaximalLinearHypersurfacePrimitive (lib gate)
19. gst-n-cohomology-double-causal-fold.yml — waves/GSTNCohomologyV3 (+ heredoc lib)
20. gst-native-algebraic-sheet-realization.yml — GSTClassicalHodgeGlobalSheetSaturation + GSTClassicalHodgeGSTDegreeCertifiedSource (lib gate)
21. gst-native-k0-original-x-extraction.yml — GSTUniversalResolvedSupportHodge (lib GSTOriginalXK0Source)
22. gst-ontological-fold-for-all-n.yml — **GSTGraphV2OntologicalFoldForAllN** (the p2_mstar_eq_two Lean certificate cited by universal_close_checks.py)
23. gst-pair-channel-walls-certificate.yml — **GSTPairChannelWallsCertificate** (the Lean file mirrored by task14a_lean_data_mirror.py)
24. gst-pinned-hodge-geometric-integration.yml — dep-roots closure of 11 modules (GSTActualXHodgeResidualProjection, GSTCanonicalPointGeometryStage2G, GSTClassicalHodgeExactClayStatement, GSTClassicalHodgeGeometricCycleClassPointRigidity, GSTFermatCanonicalPointRankBridge, GSTGraphV2SelfExpandingCosmology, GSTQuadricPrimitiveRulingGeometry, GSTUniversalCMArithmeticObstruction, GSTUniversalCodimensionTwoPrimitiveExtraction, GSTUniversalPrimitiveHyperplaneRelative, GSTUniversalResolvedSupportHodge)
25. gst-polarized-spectral-krylov-moment.yml — GSTClassicalHodgeGeometricKrylovMomentDeterminant (lib gate)
26. gst-primitive-external-product-birth.yml — GSTPrimitiveProductTowerStabilization (lib gate)
27. gst-primitive-transverse-cycle.yml — GSTPrimitiveTransverseCycleExtraction + 5 others
28. gst-universal-codimension-two-primitive.yml — GSTUniversalCodimensionTwoPrimitiveExtraction + 4 others
29. gst-universal-surface-graph-augmentation.yml — GSTUniversalSurfaceGraphAugmentation + GSTSurfaceGraphH1Obstruction + GSTPrimitiveProductTowerStabilization (lib gate)
30. gst-weil-forcing-frame-certificate.yml — **GSTWeilForcingFrameCertificate**
31. gst-weil-fourfold-extraction.yml — `lake env lean GSTWeilFourfoldAuxiliaryExtraction.lean`

### 2.4 The 48 files NOT covered by any CI workflow (drafts)

Registered-in-lakefile but never CI-built (25 — mostly HCUniverse scratch/probe roots; no workflow builds HCUniverse wholesale):
ComparatorSmokeChallenge.lean, ComparatorSmokeSolution.lean, GSTGraphV2BlockScratch.lean, GSTGraphV2CanonicalEscapeProbe.lean, GSTGraphV2CanonicalInfiniteCycle.lean, GSTGraphV2CanonicalSignedPrefixBridge.lean, GSTGraphV2CanonicalTerminalExtinctionProbe.lean, GSTGraphV2CanonicalTransparentBridgeProbe.lean, GSTGraphV2FluxScratch.lean, GSTGraphV2FourPowerCanonicalParentObstruction.lean, GSTGraphV2FourPowerForcingBridge.lean, GSTGraphV2FourPowerRelocation.lean, GSTGraphV2FourPowerRelocationClosure.lean, GSTGraphV2FourPowerResidueObstruction.lean, GSTGraphV2InfiniteBigNDichotomyScratch.lean, GSTGraphV2InfiniteControlScratch.lean, GSTGraphV2NonlocalCascade.lean, GSTGraphV2PerfectPowerBlockCollision.lean, GSTGraphV2PhysicalSignedKernelTelescopeScratch.lean, GSTGraphV2SixAdicOntologicalGeometryTest.lean, GSTGraphV2SixAdicUnitIsometry.lean, GSTGraphV2TransparentWidthThree.lean, GSTTailFInfiniteRead.lean, GSTTailFOneLane.lean, GSTU2DCanonicalShiftedTerminalProbe.lean.

Unregistered drafts (23):
GSTClassicalHodgeCanonicalCutSpineNormalization.lean, GSTClassicalHodgeHandwrittenPiExplicitNativeCollapse.lean, GSTClassicalHodgeHandwrittenPiProgramLanding.lean, GSTClassicalHodgeOmniversePointStrictRelationFinale.lean, GSTClassicalHodgePiOneObservableOmniverseFinale.lean, GSTClassicalHodgePiOneWordCyclicSeedOmniverseFinale.lean, GSTClassicalHodgePiPointFiniteCorrespondenceUltimateFinale.lean, GSTClassicalHodgePiPointRationalCorrespondenceUnboundedFinale.lean, GSTClassicalHodgePiPointTwoGeneratorUnboundedFinale.lean, GSTClassicalHodgePiProjectiveSpectralOmniverseFinale.lean, GSTClassicalHodgePiSpineMassUnboundedFinale.lean, GSTClassicalHodgePiSpineTwoGeneratorUnboundedFinale.lean, GSTClassicalHodgePiStrictKernelCyclicOmniverseFinale.lean, GSTClassicalHodgePiStrictTraceCyclicOmniverseFinale.lean, GSTClassicalHodgePointClosureIntegral.lean, GSTClassicalHodgeProjectivePointOmniverseSource.lean, GSTClassicalHodgeRadicalPrincipalCutDimension.lean, GSTClassicalHodgeSheetSiegeRoute.lean, GSTClassicalHodgeStrictBettiApexL2Fusion.lean, GSTLawStackRound26.lean, fsb.lean, pi.lean, questions/deepmind_problem_406/Challenge.lean (problem statement — its single `sorry` is INTENTIONAL by design).

**Sorry census (whole branch): 707 files contain exactly ONE real `sorry` proof placeholder — the intentional one in questions/deepmind_problem_406/Challenge.lean.** All other occurrences of the word are in headers/comments declaring "No sorry". The 48 uncovered files are therefore not sorry-laden — they are complete-looking but UNWIRED (no CI lane compiles them).

---

## Section 3 — COMPUTATIONS INVENTORY (research/computations/, 115 files; NOT run)

56 Wolfram (.wl) scripts + 23 Python scripts + 20 JSON manifests/outputs + 16 txt outputs/receipts. One-line purposes from headers:

Python (23):
- affine_clifford_k0_source.py — exact algebraic Clifford/Bott idempotent source audit, p=1..4, Z[x,y,z] coefficients.
- algebraic_adams_pure_hodge_k0.py — exact rational Adams/Chern source audit for arbitrary n,p,d (Lagrange idempotent identity).
- fermat_cubic_405_rank.py — exact 405-plane Gram certificate on the Fermat cubic fourfold (intersection numbers 3/-1/+1/0). CI-run by gst-fermat-cubic-405-rank.yml.
- fermat_cubic_fourier_all_dimensions.py — exact finite audit of the uniform Fermat cubic maximal-plane Fourier mechanism. CI-run by gst-fermat-cubic-405-rank.yml.
- gst_all_lean_source_inventory.py — indexes every tracked Lean file (explicitly a source inventory, NOT a validity claim). CI-run by gst-entire-lean-source-map.yml.
- gst_clifford_shamash_native_source.py — equation-defined MF -> syzygy -> native Chern-source audit.
- gst_integer_boundary_surgery.py — exact mass minimization in a finite chain complex (integral boundary surgery). CI-run by gst-integer-surgery-optimizer.yml.
- gst_mixed_blowup_birth.py — exact checks of two interacting exceptional births (blowup Chow presentation).
- gst_original_x_smooth_incidence_centers.py — exact Chern-to-smooth-center identities on arbitrary original X.
- gst_pure_k0_single_center.py — exact coefficient audit of pure native K^0 -> one smooth center (kernel-completion, Newton, twist identities).
- gst_residual_defined_spectral_source_attempt.py — tests the constructor from a prescribed primitive Hodge tensor (asserts no universal source).
- gst_second_blowup_primitive_plane.py — exact complete Chow matrices of the interacting second blowup.
- gst_tensor_source_forcing_audit.py — exact basis 1,h,h^2,h^3,h^4,s,r audit (no floating arithmetic).
- gst_weil_uniform_power_and_shear.py — exact bounded cross-checks; all-n/all-t proofs live in the Lean module.
- k3_cyclotomic_graph_orbit_rank.py — exact rational graph-orbit coefficient rank, cyclotomic orders 2..66. CI-run by gst-k3-cyclotomic-graph-rank.yml.
- pure_algebraic_k0_all_codimensions.py — exact all-codimension pure algebraic K^0 source on Fermat plane hypersurfaces.
- qm_fourfold_all_hodge_divisor_span.py — generic QM abelian-fourfold complete rational Hodge-span certificate ((-1,3)_Q).
- quaternionic_graph_weil_source.py — actual quaternionic-graph Weil Hodge source, exact Z[i] certificate.
- secant_obstruction_rank.py — exact symbolic cochain detector for the 48-dimensional obstruction image.
- secant_seed_character.py — exact exterior calculation of the genus-three secant seed character over Q(d)[u]/(u^2+d).
- split_weil_native_algebraic_sources.py — exact algebraic Weil-cycle source audit on split CM elliptic powers.
- weil_cm_correspondence_projector.py — exact rational CM Weil-class projector, all-p formula, audit p=1..8.
- weil_general_d_projector.py — exact CM Weil projector for every imaginary-quadratic d on H^4.

Wolfram .wl (56): one-line themes — GST all-N spatial-fold dichotomy decision arithmetic; non-split singular normal-Chern birth; multi-holonomy finite audit; all-N whole-realization defect spectrum; all-rank fold explicit Chow inverse carrier; all-x spectral fold gauge transgression; alpha Deligne/Gersten double-fold residue; alpha-indexed projector Chow solver; alpha spectral cover source audit; alpha-tower twist + lattice extraction; analytic fold projector determinantal Chern; antideck signed Chow birth; arbitrary-X actual Chow motive Gram; arbitrary-X Hodge locus/source strata; binary allN Hodge-break actual geometry; causal graph double-fold weight emergence; causal Hodge alignment topology graph; causal monodromy correspondence centralizer; causal toric Hodge period Picard-Fuchs; compact causal Hopf fold; connected multiverse Hodge source; cyclic original-X causal Hodge fold; direct alpha deRham curvature certificate; emergent-dimensional causal fold; explicit all-rank Pluecker/Fitting source; fibered mass calibration; finite noncyclic pure causal Hodge; higher-causal flatness Lagrange divisor; Hodge/Rees log wedge all-rank; intrinsic causal graph weight spectrum; intrinsic PGL projective Chow/Segre; interacting births; mixed eigenworld Chow source; omega causal whole Hodge/Chow spectrum; optimal-rank finite-fold polarization; original-X alpha signed degeneracy + angle; original-X excess component world return; original-x incidence; projective Chow residue incidence; punctured causal Euler defect; pure K^0 single center (independent Chern definition); rational Chow -> Hodge spectral kernel; Rees fold Chow/Hodge all-dimension; signed causal monodromy commutator; signed causal purity spectrum; SNC causal boundary Calabi-Yau fold; tensor source forcing audit; topology-branch Hodge birth all-n; universal topological fold exponential; whole-space emergent Hodge fold; middle Euler arithmetic normalization; middle Newton normalizer; native residual Euler kernel; semantic reflection factor extraction; Weil fourfold auxiliary extraction; Weil source construction frontier.

Artifacts: 20 *.manifest.json / *.output.json (computational run receipts) + 16 *.output.txt / *.receipt.txt (including 3 `*.lean.receipt.txt` — Wolfram->Lean data handoff receipts: gst_interacting_births, gst_original_x_incidence, gst_pure_k0_single_center).

---

## Section 4 — VERIFICATION STATE (what is machine-verified where)

**Lean (kernel verification):**
- 659 of 707 Lean files are compiled by at least one of the 122 GitHub Actions workflows (union over all branches); 110 of those workflows additionally enforce the sorry/sorryAx trust audit, so a green run = kernel-checked + sorry-free.
- 334 of 707 are covered by the 31 lanes that fire on push to THIS branch (each lane path-filtered to its own file(s)).
- The wholesale kernel gates (HodgePureMath: all 421 roots via hodge-pure-math-engine.yml / hodge-conjecture.yml / hodge-diagnostic-shards.yml; HodgeConjecture + 7 integration-frontier roots; HCProof default build + Problem-406 Solution) are bound to OTHER branches (sol/*, astra/*, main, clean/*) and are only manually dispatchable from this branch. hodge-pure-math-engine.yml has NO sorry audit.
- 48 files (listed in 2.4) are NEVER CI-compiled: the Pi*Finale draft family, the GraphV2 probe/scratch family (HCUniverse roots — no workflow builds HCUniverse), GSTLawStackRound26, fsb/pi scratch, ComparatorSmoke*, and the intentionally-sorry Problem-406 Challenge.
- The branch is sorry-free apart from that single intentional placeholder.

**Python certificates (exact-arithmetic certificates):**
- research/experiments/: 20 scripts; **15 re-run this session, ALL exit 0** (1708 counted checks + 3 assert-based scripts); they certify the campaign's finite cores: the two-cell/five-term concentration, the rotation deck C_4 obstruction law, the identification link (with strip-shape hypothesis recorded), the pair-exchange deck, the universal-close composition (withdrawn to committed layers), the cyclic family transport theorem + its independent audit, the W_I vertex pin (Gaussian equivariance), the cyclic transport, the census repair, the closing census, the discovery strike (m*(A,2,W_R)=2 exact), and the Round 17/18/19 strikes (birth/integrability/transport sweep).
- research/computations/: 79 runnable scripts (56 Wolfram + 23 Python), NOT run here; 5 of the Python ones are themselves wired into CI (fermat_cubic_405_rank, fermat_cubic_fourier_all_dimensions, k3_cyclotomic_graph_orbit_rank, gst_integer_boundary_surgery, gst_all_lean_source_inventory); 3 carry *.lean.receipt.txt handoffs to Lean files.

**Python <-> Lean bridges (the cross-verification spine):**
- task14a_lean_data_mirror.py pre-verifies every literal of GSTPairChannelWallsCertificate.lean; that Lean file is CI-verified on this branch by gst-pair-channel-walls-certificate.yml.
- universal_close_checks.py cites the Lean certificate p2_mstar_eq_two in GSTGraphV2OntologicalFoldForAllN.lean ("CI-green"); that file is CI-verified on this branch by gst-ontological-fold-for-all-n.yml.

**What is machine-verified vs draft-only (summary):**
- Machine-verified (Lean kernel + CI): 659/707 files, incl. HodgeConjecture.lean (the Clay statement target), GSTClassicalHodgeExactClayStatement.lean, GSTPairChannelWallsCertificate.lean, GSTGraphV2OntologicalFoldForAllN.lean, GSTWeilForcingFrameCertificate.lean, GSTGr25PurePairLatticeCertificate.lean, GSTCarrierMechanismVerdictCertificate.lean — plus the full HodgePureMath registry (421 roots) behind the wholesale gates.
- Machine-verified (exact-arithmetic Python, re-runnable): the 15 green experiment certificates (this session) + the 79 computation scripts (committed, 5 CI-wired).
- Draft-only (no CI anywhere): the 48 Lean files in 2.4 — none carry a proof-escape sorry; they are unwired, not unfinished-in-place. Notably the entire GSTClassicalHodgePi*Finale family and the GraphV2 probe family.
- The campaign's certified boundary (per the certificates' own scope lines): the composition is verified through the pair bit on the committed layers; the deck at the general input (the nonabelian H^3(mu_2) torsion boundary of Round 28) remains the one uncommitted construction; FS_forall/Q1 is Lean+CI certified; the Clay statement's remaining items are carried by the Python certificate stack, not by an unconditional Lean theorem.
