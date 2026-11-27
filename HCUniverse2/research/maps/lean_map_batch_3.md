# Lean batch 3 map — branch research/gpt6-native-point-primitive-span-20261017 (/tmp/hc-clone-23)

Mapper: lean-mapper batch 3 (Task 1-d). 70 files, 19,361 LOC total.
Global scan: **0 `axiom` declarations, 0 `sorry`, 0 `opaque`** in the whole batch (the three grep hits for "axiom" are in comments). All unproven assumptions live in **structure fields / theorem hypotheses** (hypothesis-records). 691 theorems, 262 defs, 36 structures, 382 `#print axioms` receipts.

### GSTActualXHodgeResidualProjection.lean (2574 lines)
- decls: 61 theorems, 2 defs, 6 structures, 0 axioms, 0 sorry
- hypotheses:
  - `ActualXCycleProjectionData.cycle_is_hodge : ∀ Z : codimensionCycles X.X p, H.cycleClass p Z ∈ HodgeSpace X H p` (algebraic ⇒ Hodge; standard, but a field, not proven here)
  - `ActualXCycleProjectionData.independently_geometric_duality : ∀ i j, geometricDetectors i (⟨cycleClass (sourceNativeCycles j), _⟩) = if i = j then 1 else 0` (dual intersection probes to source cycles)
  - `ActualXFiniteProjectiveTrace.projective_hodge_has_cycles : rationalHodgeSubspace (HP.hodgeBigrading p) ≤ LinearMap.range (HP.cycleClass p)` — **the Hodge conjecture for the auxiliary variety P, assumed as a structure field**; plus `push_preserves_hodge`, `pull_preserves_hodge`, `cycleClass_natural`, `trace_degree : bettiPush (bettiPull beta) = degree • beta`, `degree_ne_zero`
  - `ActualXFiniteProjectiveNativeTrace`: `push_cycleClass_natural`, `native_push_pull_degree`
  - `ActualXPrimitiveProjectiveTraceComparison`: `projectivePeriod_injective`, `trueProjectionFormula`
  - `ActualXProjectiveAmbientCupRankOne.projectivePullbackIsHyperplaneSquare : ∀ beta, ∃ c, F.bettiPull beta = (c • L.cupH ambientHyperplane).1`
  - `ActualXAllCodimensionPrimitiveTraceComparison`: `projectivePeriod_injective`, `projectivePrimitiveFormula`
- main content: cycle+residual decomposition `projectNative`/`primitiveResidual` with `algebraic_part_plus_residual`, `residual_zero_iff_constructed_cycle_exact`, `missing_class_has_nonzero_residual`; trace-zero construction through finite projections; Euler-matrix compiler (`eulerCertifiedCycle_of_det_ne_zero`); anti-circularity theorem `nativeEulerFullRank_iff_all_targets` (∃ invertible native Euler source matrix ⟺ every Hodge class has a Chow representative).
- name-vs-content: matches — this really is the arbitrary-X residual machinery, but every exactness theorem is conditional on residual vanishing / matrix invertibility.
- gaps: `projective_hodge_has_cycles` field is conjecture-level; no instance of `ActualXCycleProjectionData` with nonzero detectors is constructed; residual vanishing is never proved.

### GSTMaximalLinearHypersurfacePrimitive.lean (1099 lines)
- decls: 39 theorems, 20 defs, 0 axioms, 0 sorry
- hypotheses: none (pure arithmetic)
- main content: exact integer identities for the 2x2 intersection lattice of hypersurfaces containing a maximal linear subspace: `NormalTopCoeff` recurrence s0=1, s(m+1)=(1-d)s_m+1, discriminant d*s(m)-1 = -(1-d)^(m+1), primitive cycle Z=d[L]-h^m with Z.Z = -d(1-d)^(m+1) ≠ 0; Fermat d-plane Gram `fermatMaximalPlaneGramDetector_kernel_trivial` (rank d for all d>=3, m>=1); Clifford/Shamash period p!·(d-1)^(p+1) > 0; K3xK3 dictionary (norms 768, 16/3); Thom-Porteous twist cancellation (ring identity).
- name-vs-content: overstates — all "geometry" is arithmetic on ZxZ (or Q^3) coordinate models; smoothness/Gysin/Thom-Porteous are external prose.
- gaps: no scheme-level construction of the hypersurface, cycles, or Chern-class comparison — docstring admits "geometric integration … external geometric input facts".

### GSTClassicalHodgeNativeOperatorCohomologyRealization.lean (746 lines)
- decls: 42 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none (KernelStable is a def; operators are inputs)
- main content: descent of a kernel-stable native cycle operator to the cycle-class range and to ambient cohomology via ONE fixed retraction (`classRangeRetraction`); composition coherence (`ambientOperator_comp_coherent`); exact class/defect splitting `ambientClassDefectEquiv`; no-generation law `nonzero_defect_blocks_every_native_operator`; corner-unit obstruction `ambientOperator_id_eq_fullIdentity_iff_fullRange` (identity extension ⟺ cycleClass surjective); `hodgeWeight_iff_intrinsicDefect_zero` (Hodge ≤ range ⟺ defect vanishes on Hodge fiber).
- name-vs-content: fair — a realization/obstruction file, honestly flags that operator rewriting cannot manufacture missing classes.
- gaps: everything is conditional on kernel stability of concrete operators; surjectivity (the Hodge content) is exactly the unproved corner-unit condition.

### GSTGraphV2OmniversalCore.lean (602 lines)
- decls: 30 theorems, 11 defs, 4 structures, 0 axioms, 0 sorry
- hypotheses: none (PathLifting is a Prop-def, not assumed)
- main content: carrier-agnostic three-sector event ontology: `OmniversalGraph`, `Path`, `Reachable`, `Closure` = least event-stable predicate; impredicative completeness `closure_iff_every_stable_semantics`; EventHom functoriality; causal fibration characterization `pathLifting_iff_exact_image_closure`.
- name-vs-content: "Omniversal" is grandiose for a typed graph with closure; no geometry/Hodge.
- gaps: pure interface layer — no mathematical content beyond elementary closure lattice facts.

### GSTGlobalPureHodgeCosmology.lean (544 lines)
- decls: 11 theorems, 17 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: classification of diagonal-supported integer/rational functions on an AxB "world grid": `pureHodgeLinearEquiv : PureWorldHodge A B ≃ₗ[ℤ] (Fin (min A B) → ℤ)`; completed/compact rational versions ≃ (ℕ→ℚ)/(ℕ→₀ℚ); "UNBOUNDED RATIONAL COMPLETED CLAY CLASSIFICATION".
- name-vs-content: large gap — "pure Hodge"/"Clay" here means functions on ℕxℕ supported on the diagonal of a toy cosmos; no varieties, no cohomology.
- gaps: the bridge from this toy diagonal model to actual (p,p) Hodge subspaces is asserted nowhere in this file.

### GSTClassicalHodgeLimitlessSpinePropagation.lean (490 lines)
- decls: 21 theorems, 0 defs, 3 structures, 0 axioms, 0 sorry
- hypotheses:
  - `SpineTowerConservedCharge`: `nativeRead`, `cohomologyRead`, `cycleClass_read`, `base_ne_zero : nativeRead 0 (codimensionZeroFundamentalCycle V) ≠ 0`, `successor_read : nativeRead (p+1) (successorNativeOperator V p Z) = successorScalar p * nativeRead p Z`
  - `NativeMassCycleClassBridge` (the residual semantic laws, unproven): `kernel_mass_zero : ∀ p Z, H.cycleClass p Z = 0 → nativeCycleMass V p Z = 0`; `base_mass_ne_zero : nativeCycleMass V 0 (codimensionZeroFundamentalCycle V) ≠ 0`; `successor_point_mass : ∀ p x, successorMass V p x = successorScalar p`
- main content: recursive spine tower `spineNativeTower`/`spineHodgeSeed` with exact cycle-class law; conservation law `nativeRead_spineNativeTower`; nonvanishing of `H.cycleClass p` and `AlgebraicHodgeSubspace ≠ ⊥` in every weight, conditional on the charge/bridge.
- name-vs-content: "limitless" is accurate (all weights) but all strength is in the unproven mass-bridge fields.
- gaps: the three native-mass laws are assumed, never constructed; boundary audit (GSTResearchGeometricWeightBoundaryAudit) proves they cannot hold unrestricted.

### GSTClassicalHodgeProjectiveDegreeTrace.lean (444 lines)
- decls: 12 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `ProjectiveDegreeTraceSemantics` fields: `trace : ∀ q, H^{2q} →ₗ[ℚ] ℚ`, `pointDegree`, `pointDegree_pos : ∀ q x, 0 < pointDegree q x`, `trace_point_cycleClass : trace q (cycleClass q (pointCycle x)) = pointDegree q x` — the classical projective-degree pairing is packaged as an assumption.
- main content: effective presentations have strictly positive trace (`trace_positive_of_effective_presentation`); nonzero effective cycles are Betti-visible; separator successor has nonzero class (`separator_successor_cycleClass_ne_zero`); ground-floor weight-one seed with `IrreducibleSpace`; `hodge_weight_of_separator_successor` derives Hodge ≤ range from seed + `GeometryFirstTwoGenerator` for every basis index (assumption R).
- name-vs-content: mostly fair; "degree trace artery" is the assumed semantics, not constructed from Mathlib cup/integration.
- gaps: no instance of `ProjectiveDegreeTraceSemantics`; weight-closure still needs the two-generator family R.

### GSTAnalyticAbsorption.lean (412 lines)
- decls: 28 theorems, 1 def, 2 structures, 0 axioms, 0 sorry
- hypotheses: none
- main content: genuine Mathlib instantiations: plane as manifold, x↦x/3^k smooth; circle covering/path-connected/compact; period law hcPeriod(4^t·R)=4^t•hcPeriod(R); Haar probability, Fourier characters norm 1/exponential/unitary, Stone-Weierstrass density, L² Hilbert basis; Liouville: transcendentals dense/residual/nearby; rootsOfUnity = ker(pow), Tate filtration μ_k ≤ μ_l, deg Φ_{4^t} = 2^(2t-1), ZMod(4^t) injects into circle, twist kills embedded torsion.
- name-vs-content: "analytic crown at FULL POWER" = standard Mathlib theorems restated; all true, none new.
- gaps: zero Hodge-conjecture relevance; it is ambience for the GST narrative.

### GSTClassicalHodgeLefschetzPoincareMatrixGeneration.lean (397 lines)
- decls: 8 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: on the finite toy module `RationalPureWindow N`: L²/2 = forward shift S, Poincare conjugate = backward shift T; P0 = I - ST; every matrix unit E_pq = S^q P0 T^p (`lefschetzPoincareMatrixWord_eq`); Lefschetz+Poincare generate the full matrix algebra.
- name-vs-content: sounds like Hard Lefschetz geometry; content is shift-matrix algebra on Fin N → ℚ.
- gaps: no connection to actual Lefschetz operators on cohomology of a variety.

### GSTClassicalHodgeCyclicSpectralGeneration.lean (379 lines)
- decls: 15 theorems, 2 defs, 2 structures, 0 axioms, 0 sorry
- hypotheses: `FiniteSpectralFamily` (observable, vectors, distinct eigenvalues, eigenvector laws); `ClassicalHodgeSpectralOperator` — assumes an ambient linear observable on Betti cohomology that is diagonal with **distinct eigenvalues** on the selected Hodge basis directions (`eigenvector`, `eigenvalue_injective`) **and** stabilizes the point-cycle-class span (`atomic_stable`).
- main content: Lagrange-isolator cyclic generation: a submodule stable under T and containing one cyclic seed contains every eigendirection; `weight_hodge_of_cyclic_spectral_generation` — surjective basisIndex + one algebraic cyclic seed in the atomic span + the spectral operator ⇒ full Hodge inclusion.
- name-vs-content: fair as linear algebra; the geometric existence of the spectral operator is the entire unmet burden.
- gaps: no construction of any observable with distinct eigenvalues on the Hodge basis; the cyclic seed is an input.

### waves/GSTVortexSingularity.lean (355 lines)
- decls: 18 theorems, 4 defs, 0 axioms, 0 sorry
- hypotheses: none (delegates to omega_puncture etc.)
- main content: discrete "vortex" arithmetic: coreRotate 5-cycles and pentagon orbits on the 12-cell space (by decide); spiral incompressibility; lattice curvature zero (commutation of x4 stride and descent); 3-adic cascade stabilization, driver ≡1 mod 3; ignition class K=3^a·core (core≡2 mod 3) forces a Happy cell at row a+1 (`vortex_singularity_forms`, constructive); finite energy (R/3^(R+1)=0).
- name-vs-content: dramatic NS-Millennium framing ("singularity", "vortex") over base-3/base-4 digit arithmetic.
- gaps: the Navier-Stokes analogy is prose; nothing analytic is formalized; content is elementary number theory.

### GSTGraphV2CanonicalTerminalExtinctionProbe.lean (344 lines)
- decls: 11 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: exact signed sums of U-jumps along affine carry words: `seeded_weighted_u_jump_exact` (telescoping identity with 24·(X mod 3^K) correction); Happy gate ⇒ negative weighted prefix; all-bad seed-one parent ⇒ nonnegative prefix; coupled gap positivity; neutral-window vacuum baseline 5 - 4^N·5; unit cell neutralization when 4^(t+1) < 3^p.
- name-vs-content: "terminal extinction probe" is arithmetic on carries; no extinction theorem in a geometric sense.
- gaps: none internally; relevance to Hodge is nil.

### GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull.lean (338 lines)
- decls: 17 theorems, 0 defs, 3 structures, 0 axioms, 0 sorry
- hypotheses: `RightFiniteBettiTrace` fields: `trace : CCoh →ₗ[ℚ] XCoh`, `degree ≠ 0`, `trace_rightPullback : trace.comp (rightCohomologyPullback) = degree • LinearMap.id` (finite-transfer/Gysin trace law); `BiFiniteBettiTrace` (two such); `PointCycleCompatibility.point_natural` (push-pull agrees with incidence action on point cycles).
- main content: normalized trace as exact left inverse; total push-pull `Tr_r ∘ l^*`; carrier decomposition projection/residual; `bettiRelated_iff_residual_and_target`; maximal transfer = push-pull mod ambiguity (`maximalBettiTransfer_eq_pushPull_mod_ambiguity`); `cycleClass_natural` for point-compatible traces.
- name-vs-content: fair — the trace is the assumed input, the push-pull calculus is real.
- gaps: existence of the Betti trace for actual finite correspondences (Gysin integration) is not established here.

### GSTClassicalHodgeLocalizedL2NativeCircularity.lean (325 lines)
- decls: 7 theorems, 3 defs, 0 axioms, 0 sorry
- hypotheses: none (HasNativePointLifts / NativeHodgeOrbitSeed imported)
- main content: **circularity audit**: with one nonzero algebraic seed, the all-target family of localized-L² native point lifts is *equivalent* to the Hodge weight conclusion (`allTarget_localizedL2_native_iff_hodge_weight`); `NativePlaneCompletionAt` (trivial weight ∨ seed+lifts) ⟺ Hodge weight; global `nativePlaneCompletion_iff_bigradedBettiHodge`.
- name-vs-content: honest — it proves the would-be "geometric axiom" is conclusion-strength.
- gaps: by design it proves no new mathematics, only equivalence; the frontier is precisely named.

### GSTClassicalHodgeMinimalNativeGeometricCore.lean (316 lines)
- decls: 9 theorems, 1 def, 1 structure, 0 axioms, 0 sorry
- hypotheses: `MinimalNativeGeometricCore` fields: `pointClass_is_hodge : ∀ p x, cycleClass p (pointCycle x) ∈ rationalHodgeSubspace …` and `principalCut_kernelStable : ∀ p, GradedKernelStable (successorNativeOperator V p)`.
- main content: from the two-field core: whole-cycle Hodge typing (`algebraic_is_hodge`), generated principal-cut operator pairs, full program interpretation `programPair/cycleEval/cohomologyEval` with master naturality; `FullGSTPlaneCompleteness` (def) ⇒ `BigradedBettiHodgeStatement` (`hodge_of_fullGSTPlane`).
- name-vs-content: fair; "minimal core" is accurate — two assumptions replace the old spine data.
- gaps: plane completeness (every Hodge basis sheet = native program output) is an unproven Prop; kernel stability of the cut operator is assumed, not proved.

### GSTClassicalHodgeRootedStrictRelationFan.lean (305 lines)
- decls: 8 theorems, 3 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `RootedStrictRelationFan.ray : ∀ j, StrictRelationRay (rootedFanApex S) (rootedFanTarget S j)` — one locally materialized strict-relation ray per Hodge basis target (edges carry `StrictRelationEdgePacket` correspondence certificates).
- main content: path-local algebraicity propagation (`preserves_algebraic`); `basis_mem_cycleClass_range_of_rootedFan`; `hodge_weight_of_rootedStrictRelationFan` — one algebraic apex + per-target rays ⇒ Hodge weight inclusion; degree-certified specialization.
- name-vs-content: fair description of the reduction (global → per-target rays).
- gaps: existence of the rays/edge packets is the entire unmet geometric burden.

### GSTClassicalHodgePrincipalCutNonzeroForcesExactSuccessor.lean (301 lines)
- decls: 10 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none new (spine G and degree semantics D are inputs)
- main content: nonzero principal-cut point image ⇒ ∃ exact relative successor in ambient codimension p+1 (`exists_exact_relative_successor_of_native_point_nonzero`); equivalences native/cohomological nonvanishing ⟺ exact successor locus nonempty; native Hodge seed from nonzero cut; trace detector equivalences under D.
- name-vs-content: accurate.
- gaps: the initial nonzero principal-cut action is hypothesized (hNative/hCoh), not produced.

### GSTClassicalHodgeAtomicDefectDuality.lean (291 lines)
- decls: 12 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: atomic defect reformulations: `atomicDefectLinearMap` (Hodge fiber → cohomology / span of point-cycle classes); `bigradedBettiHodgeStatement_iff_atomicDefect_zero` (Hodge ⟺ all defect maps vanish); basis-wise test; finsupp pairing nondegeneracy both sides (`fibered_duality_crown`).
- name-vs-content: fair — "defect duality" is a nondegenerate pairing of finsupp vs all functions.
- gaps: purely a reformulation file; the defect vanishing (= Hodge) is not proved.

### GSTGraphV2UnifiedPowerRectangle.lean (285 lines)
- decls: 16 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: reverse-base-4 carry words of graph rectangles: `carryWord_lt_pow_four`, head/tail splits, digit transport mod 3, unified physical state satisfying Old-Sol's invariant with multiplier 4^N, unified Equation III (parent jump - 4^N·child jump = 3·potential difference), potential = horizontal base-4 flux; word concatenation/three-block laws.
- name-vs-content: "unified power rectangle" = carry-word bookkeeping.
- gaps: none internally; disconnected from Hodge.

### GSTClassicalHodgeOmniverseCausalBranchPacket.lean (278 lines)
- decls: 6 theorems, 6 defs, 2 structures, 0 axioms, 0 sorry
- hypotheses: none (BranchLinearRule is data)
- main content: three-sector branch graph on Hodge states; `branch_collapse_identity` (alpha = Σ (α_j/c)·E_ij branches — linear algebra of matrix units); live-support NShape packet with nCoho readout rank; hyper-event system for finite rational synthesis.
- name-vs-content: fair; deliberately contains no algebraicity assertion (docstring says the geometric materialization is downstream).
- gaps: events are matrix-unit transports, not correspondences — the strict-relation layer must still materialize them.

### waves/GSTNCohomologyV3.lean (270 lines)
- decls: 14 theorems, 6 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: honest Kronecker hole basis with unique coefficients (fixes V2's constant "basis"); `nonnegative_linear_native_mass_must_vanish` (a ℚ-linear mass nonnegative everywhere is zero — blocks fake geometric mass); double/multi-causal tensor coordinates with multiplicative rank ∏ holes.
- name-vs-content: fair; "no theorem asserts the universal Hodge conjecture" per its own header.
- gaps: toy model; the current-mass firewall is a negative result only.

### GSTClassicalHodgeAugmentedTargetWindow.lean (267 lines)
- decls: 8 theorems, 5 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: finite observation window = live support ∪ {target j}; augmented coordinate vector; denominator-clearing integral square with live source nonzero on the diagonal; exact single-sheet readback `readAugmentedSquare_target = q • basis j`.
- name-vs-content: accurate bookkeeping.
- gaps: window machinery only; no Hodge progress by itself.

### GSTClassicalHodgeFiberedNativeProjectiveTransport.lean (258 lines)
- decls: 9 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none new (uses imported pointResidueWeight/nativePointPushforward)
- main content: `fiberedNativePushforward` — transport of multiplicity-labelled atoms along a scheme endomorphism; native face = genuine point pushforward; Hodge face carries residue-degree scalar on the sheet; limitless face = residue multiplier on the transfer ray; transport crown.
- name-vs-content: fair.
- gaps: depends on the imported pushforward/presentation API whose geometric realization (Gysin) is elsewhere assumed.

### GSTResidualNormZeroExactHodgeEquivalence.lean (256 lines)
- decls: 8 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: `ExistingNativeImageSpanned` (finitely many cycles span the ENTIRE algebraic image); `hPositive : ∀ v ≠ 0, 0 < Q v v` (positive-definite Hodge-Riemann polarization, assumed); `hGeometricPairing : detectors i x = (Q x) (cycleClass (cycles i))` (detectors = polarization against cycles).
- main content: **the diagnosis file**: `all_residual_norms_zero_iff_full_primitive_hodge` — the requested "Q(r_α,r_α)=0 for all α" is *equivalent* to surjectivity of cycleClass (the Hodge conjecture); residual is orthogonal to every native cycle (`residual_orthogonal_to_every_native_cycle`, `no_native_polarized_detector_of_residual`); a missing class has strictly positive residual energy invisible to all native cycles.
- name-vs-content: honest — header says "a rigorous diagnosis; NOT a proof".
- gaps: proves no residual vanishing; identifies that any proof must add genuinely new geometry implying Hodge itself.

### GSTFiniteDominantAllCodimensionDescent.lean (248 lines)
- decls: 7 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `GeometricFiniteDominantMap` fields: `degree ≠ 0`, nativePush/bettiPush/bettiPull, `pull_preserves_hodge`, `native_betti_natural : cycleClass p (nativePush Z) = bettiPush (cycleClass p Z)`, `push_pull_degree : bettiPush (bettiPull α) = degree • α` (the finite-cover push-pull law); plus imported `SchemeProjectiveBundleGysin`.
- main content: descent: if Y solved at weight p then X solved (`all_target_hodge_at_weight_of_finite_dominant_map`); unrepresented targets pull to unrepresented sources; algebraicity iff finite-pullback algebraicity; projective-bundle pipeline: solved base + Gysin data + finite dominant map ⇒ `BigradedBettiHodgeStatement X`.
- name-vs-content: fair (conditional descent).
- gaps: no `GeometricFiniteDominantMap` instance is constructed for any nontrivial cover; the "solved base" premise is the conjecture for B.

### GSTClassicalHodgeNativeInteractionNormalForm.lean (247 lines)
- decls: 7 theorems, 3 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: joint/marginal decomposition of fibered native states: `interactionRectangle` (4-atom rectangle); interaction projection idempotent; joint kernel = span of rectangles (`jointKernel_eq_rectangleSpan`); all gluings classified (`jointMarginals_iff_interaction_translate`); two-face discovery test for observables (`observable_marginal_formula_iff`).
- name-vs-content: fair ("interaction normal form" = inclusion-exclusion on finsupp atoms).
- gaps: purely structural; no Hodge content.

### GSTClassicalHodgeNativeExecutablePlane.lean (239 lines)
- decls: 9 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: none (plane completeness is a Prop-def)
- main content: `nativeEval` of correspondence/cut programs without any cohomological descent; `NativeExecutableGSTPlaneCompleteness` (every Hodge basis sheet = cycle class of a native program output) ⇒ `BigradedBettiHodgeStatement` and its rational-algebraic / finite-combination forms; `HodgeBasisCycleSupply ⟺ BigradedBettiHodgeStatement` (exact basis normal form).
- name-vs-content: honest — explicitly says plane completeness is conclusion-strength.
- gaps: the plane-completeness Prop is exactly the unproved Hodge statement in program-execution dress.

### GSTClassicalHodgeFiberedNativeRecoordination.lean (233 lines)
- decls: 9 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none
- main content: chart independence: live atoms/fields are invariant under GST world recoordination (all three faces: classical multiplicity, native cycle, limitless address); transport crown.
- name-vs-content: fair.
- gaps: naturality bookkeeping only.

### GSTGraphV2CMNMPrimitiveUpgrade.lean (231 lines)
- decls: 7 theorems, 4 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: conservative graph extension by CM-NM edges: `cmNMNativeGraphCycle` (real/imag CM-weighted pushforward combination — an actual native cycle); certified events; legacy paths survive; closure soundness; **firewall theorem** `certifiedHodgeClosure_iff_native` — the upgraded closure reaches a Hodge node iff a genuine native representative exists.
- name-vs-content: honest; the "CRITICAL FIREWALL" docstring matches content.
- gaps: adding edges proves no new algebraicity (by design); CM weights' arithmetic (imported) is toy Gaussian rationals.

### GSTClassicalHodgeFiberedDefectEquivariance.lean (223 lines)
- decls: 8 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: `TensorIntertwinesAt` / `UniformTensorIntertwiner` (Prop defs: cohomological action on source sheet = native point-transition mass × target sheet; constant mass λ)
- main content: defect equivariance: for a cycle-natural tensor transport, new defect = T(old defect) (`defect_tensorWord_atom_eq_map`); zero-defect propagation; uniform intertwiner carries zero-defect atoms to zero-defect states.
- name-vs-content: fair.
- gaps: intertwining law is a hypothesis; no transport is shown to satisfy it.

### GSTClassicalHodgeGradedCorrespondenceProgramOrbit.lean (222 lines)
- decls: 6 theorems, 2 defs, 1 structure (program syntax), 0 axioms, 0 sorry
- hypotheses: none (GeometricCycleClassSpine G is an imported input)
- main content: graded program language (id | realized correspondence | principal cut | + | • | comp) with exact operator-pair interpretation and master naturality; orbit subspace ≤ cycle-class range; `FullCorrespondenceOrbitCyclic` ⇒ `EveryHodgeClassIsRationalAlgebraic` (and finite-combination form).
- name-vs-content: honest; states plainly "the exact Hodge conjecture is reduced to one noncircular geometric generation statement".
- gaps: orbit cyclicity (every Hodge state in the program orbit) is the unproved input.

### GSTClassicalHodgeDegreeCertifiedOmniverseLiveCollapse.lean (216 lines)
- decls: 3 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `LiveDegreeCertifiedProgramFamily` — for each LIVE coordinate j of α, a `DegreeCertifiedFullCorrespondenceProgram` from the degree-certified source to the j-th sheet (plus the standing live/exact premises hlive, hExact).
- main content: `omniverseLiveCollapseCycle` = finite Σ α_j·Z_j; exact collapse `omniverseLiveCollapseCycle_spec : cycleClass (p+1) Z = α`; existential form.
- name-vs-content: fair (branch-collapse = basis reassembly).
- gaps: the per-live-coordinate programs are precisely the unmaterialized geometry.

### GSTClassicalHodgeFiniteClosedCorrespondenceTranspose.lean (211 lines)
- decls: 10 theorems, 1 def, 1 structure, 0 axioms, 0 sorry
- hypotheses: `BiFiniteClosedCorrespondence.rightFiber_finite` (finite right fibers — honest geometric datum)
- main content: genuine factor-swap automorphism of X×_C X (iso, involutive); transpose of a bi-finite closed correspondence with left/right projection exchange; double transpose recovers projections.
- name-vs-content: accurate scheme-level algebra.
- gaps: none internally; no Hodge claims.

### GSTClassicalHodgeCanonicalCosmicRealizationEquivalence.lean (207 lines)
- decls: 7 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `NativeCanonicalCosmicRealization` fields: `native : End(cycles)`, `naturality : ∀ Z, cycleClass p (native Z) = canonicalCosmicAmbient i j (cycleClass p Z)` — a native lift of each cosmic matrix unit.
- main content: realization ⟺ range-stability (`nativeRealization_of_range_stable` uses range-lifted operators over ℚ-projectivity); family of realizations ⇒ CanonicalCosmicNaturality ⇒ with nonzero algebraic seed, full Hodge weight and AlgebraicHodgeSubspace = ⊤.
- name-vs-content: fair.
- gaps: constructing the native realizations (i.e., cosmic matrix units with native lifts) is the unmet target.

### GSTClassicalHodgeThreeUniverseSeedIdentification.lean (203 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: three-universe seed identity: classical Hodge sheet generator, native point-cycle cosmic shadow, and limitless transfer generator `compactClMono p` are literally equal after identification; mass formula: forgetful image = total basis mass • transfer seed; nonzero Hodge classes tether to a live sheet over the same seed.
- name-vs-content: fair (an identification lemma cluster).
- gaps: delegation file — the identifications were proved elsewhere; no new burden discharged.

### GSTClassicalHodgeGradedOrbitSingleProgramCollapse.lean (200 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none new
- main content: orbit set is already a submodule (programs closed under +/•); `fullCorrespondenceOrbitCyclic ⟺ single-program generation` (every Hodge class = cohomologyEval(P)(origin) for ONE program); finale `exactHodge_of_singleProgramGeneration`.
- name-vs-content: accurate.
- gaps: single-program generation remains the explicit unproved premise.

### GSTGraphV2SixAdicUnitIsometry.lean (199 lines)
- decls: 9 theorems, 2 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: none (`SixAdicUnitCertificate` is an explicit inverse-certificate — data, not an unproven proposition)
- main content: six-adic congruence isometries: translation iff-law, multiplication by a mod-6^k unit reflects; certificate composition; iterated powers; 6· similarity raising resolution by one.
- name-vs-content: fair elementary number theory.
- gaps: none internally.

### GSTClassicalHodgeLiveSupportCorrespondenceSpectralCrown.lean (195 lines)
- decls: 6 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `LiveSupportCorrespondenceSpectralCertificate` fields: `realization : ClosedCorrespondenceWindowRealization G (liveSupportWindow α)` (a realized correspondence code-observable on α's live support) and `visible : ∀ r, realization.PointVisible r` (a visible genuine point per live slot).
- main content: live basis cycles extracted with exact classes; reassembly `reconstructedCycle_spec : cycleClass = α`; crown: certificates for all q,α ⇒ `BigradedBettiHodgeStatement`.
- name-vs-content: fair.
- gaps: the certificate (window realization + visibility) is exactly the unproven geometric existence.

### GSTClassicalHodgePiOmniverseCanonicalSupportSpectral.lean (194 lines)
- decls: 8 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `R : ClosedCorrespondenceWindowRealization G (canonicalLiveWindow α)`, `S : NativeHodgeOrbitSeed`, `hvisible : ∀ r, SeedVisible R S r` (theorem inputs)
- main content: canonical live window = support enumeration (all slots live, all support covered); window rank = N-cohomology holes; `target_cycle_of_canonical_omniverse_spectral_packet` — one observable + one seed visible in every active slot ⇒ native cycle representing α; combined branch-packet + cycle theorem.
- name-vs-content: fair.
- gaps: R/S/visibility are hypotheses; no realization is constructed.

### GSTClassicalHodgeRelativeSuccessorProjectivePrime.lean (187 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: honest Proj algebra: image of closure point lies in projective closure; specialization = homogeneous prime inclusion (`sourcePrime_le_successorPrime`); separator ∉ source prime, ∈ successor prime; hence strict prime interval `sourcePrime_lt_successorPrime_of_mem_cut`; crown for finset-selected successors.
- name-vs-content: accurate.
- gaps: none internally; feeds the successor grading argument.

### GSTPrefixOneOntologicalEscape.lean (187 lines)
- decls: 12 theorems, 0 defs, 1 structure (imported), 0 axioms, 0 sorry
- hypotheses: `FourPowerCreationMaster`, `FourPowerHappyGeThreeProvider` / `FourPowerCommonTwoGeThreeProvider` / `PrefixHitGeThree` provider families / `FourPowerDirectNoBadAffineChannelOne`, and crucially `hClimb : GSTInfiniteFourPowerNavigation.four_power_happy_climb` (the "third-wave climb hypothesis") — all consumed as unproven theorem inputs.
- main content: prefix-one exponents enter the four-power range; POE downstream of creation master; "no-axiom route" transplant entry points replacing the retired inline axiom; third-wave gate delivered from the climb; equivalences thirdWave ↔ CreationCertificate ↔ Navigation.
- name-vs-content: honest about the climb being "the one explicit input, consumed by name".
- gaps: the climb/provider primitives are unproven (Collatz-flavored); nothing here closes them.

### GSTMathboxCorrectedZetaActualHodge.lean (185 lines)
- decls: 4 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `hirred : ActualHodgeCorrespondenceIrreducible` (irreducibility of actual finite-closed correspondence operators); `hMeasure` (geometric readout = zetaAtS · Σ kernel); in the full version, per-weight zeta seed certificates `hZetaGeometry`.
- main content: any nonzero native seed + actual irreducibility ⇒ every Hodge class algebraic; corrected zeta infinite series forces a nonzero native class; `full_hodge_of_corrected_zeta_actual_geometry` — Stage-2G target from weight-local zeta seeds + irreducibility.
- name-vs-content: honest — header: "the HARD universal inputs remain explicit … the all-varieties Hodge conjecture is not declared proved".
- gaps: zeta-value readout law linking analytic series to a rational cycle coordinate is an explicit input; irreducibility unproven.

### GSTClassicalHodgePlaneCompletenessLefschetzCrown.lean (178 lines)
- decls: 5 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: matrix unit = normalized localized bare L² firing (`fixedSource_target_is_normalized_L2`); branch collapse via L² firings; crown `gst_plane_completeness_via_universal_L2` (events + reachability + L² identity + collapse).
- name-vs-content: "Lefschetz crown" is the toy diagonalLefschetzQ operator, not geometric Lefschetz.
- gaps: all statements are about the internal GST operator model; no geometry externalized.

### GSTFourPowerAffinePeelClassifier.lean (178 lines)
- decls: 14 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none
- main content: first/second exponent-trit classifiers via peels; phase-indexed renormalization `peelPhase`; `tail3_affineOrbit_phase_exact`.
- name-vs-content: accurate automaton arithmetic.
- gaps: none internally; Collatz-adjacent content of unclear Hodge relevance.

### GSTMathboxCorrectedZetaGeometry.lean (174 lines)
- decls: 6 theorems, 4 defs, 0 axioms, 0 sorry
- hypotheses: `hActual` (real readout equals the zeta-weighted partial sum) in the detector lemma
- main content: corrected indexed denominator x^(m+1) - y^(m+2); explicit pole at (4,2,1); x=y=2 diagonal = negative geometric series, partial sums strictly negative; zeta-weighted partials nonzero; detector adds a new native direction outside the old span.
- name-vs-content: fair; scope honestly restricted to n ≥ 1.
- gaps: no convergence of the infinite sum here (that is the imported file); geometric comparison identity is an input.

### GSTClassicalHodgeCMSurfaceCupGysinGSTCompiler.lean (171 lines)
- decls: 3 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `CupGysinGSTSheetProgram` — a large packet: `geometry : CrossProductCupGysin …` (product cup/Gysin topology data supplied because Mathlib does not implement the full construction), `finiteIncidence : FiniteCrossCarrierPointKernel`, `geometricPointLaw`, `gstProgram`, `active`/`sourceCycle`/`coefficient`, and `basisPeriodExpansion` (the j-th Hodge basis vector's coordinates equal the program-output period expansion).
- main content: compiles the packet into the CM/GST native sheet program; `nativeBasisCycle_spec` (basis class realized by a genuine native cycle); finite-support and universal versions (`exact_stage2G_of_cupGysin_GST_sheet_packets`).
- name-vs-content: honest; header notes "NEEDS CI RUN LATER" and that surface-kernel realization is NOT assumed for all Hodge tensors.
- gaps: no packet is constructed for any actual surface; cup/Gysin data are supplied fields, not built.

### GSTClassicalHodgeGradedAmbientCorrespondenceKernelAction.lean (170 lines)
- decls: 3 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `GradedBettiKernel` (kernel class + transpose = swap-pullback — data+provable law); ambient cup/Gysin calculus `P : AmbientBettiIntersectionCalculus` is an imported hypothesis-package.
- main content: canonical graded action α ↦ (p₂)!(κ ∪ p₁*α) raising degree by `shift`; transpose kernel with same shift; degree-two weight action H^{2p} → H^{2(p+1)}; totality on all Betti classes.
- name-vs-content: accurate.
- gaps: the intersection calculus (cup/Gysin on X×X) is supplied data since Mathlib lacks it; transpose does NOT give a lowering operator (honestly flagged).

### GSTClassicalHodgePlaneCompletenessUnboundedCrown.lean (163 lines)
- decls: 3 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: every fixed-source target persists at every finite higher-causal dimension; combined certificate (event + reachable + L² + unbounded tower + collapse).
- name-vs-content: "unbounded crown" = stacking the previous crown with an imported tower theorem.
- gaps: no new mathematical content; still internal to the GST model.

### GSTGraphV2CanonicalSheetTranslation.lean (161 lines)
- decls: 8 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: multiplying energy by 4^k is literal horizontal translation of all physical fields; Happy invariance under translation; one-trit and two-trit canonical renormalization with accumulated phase; bad-trace transport.
- name-vs-content: accurate digit arithmetic.
- gaps: none internally.

### GSTClassicalHodgeFiniteSupportProjectiveOrbit.lean (157 lines)
- decls: 4 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `R : ∀ i ∈ support(α), ProjectiveWordLiveSourceTarget G S i` (per-live-slot projective word transports) and `D : FiniteSpineMomentChain G q` per weight (theorem inputs).
- main content: finite-support reassembly `finiteSupportTargetCycle_spec` (cycle class = α); per-class finite brute-force crown ⇒ `BigradedBettiHodgeStatement`.
- name-vs-content: fair.
- gaps: the moment chains and projective words are unproven existentials.

### GSTClassicalHodgeProjectiveGeneratorWordCompiler.lean (154 lines)
- decls: 3 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `R : ∀ j, ProjectiveTwoGenerator … S.sourceIndex j` (two genuine projective primitives per target) + diagonal word `hdiag`
- main content: compiles code ∘ Lefschetz ∘ (id - code) word; faithful evaluation; source action = coordinate × target sheet; every two-generator package supplies the word certificate; `hodge_weight_of_projective_two_generators_via_words`.
- name-vs-content: fair (compiler/compatibility file).
- gaps: ProjectiveTwoGenerator existence is the standing geometric burden.

### GSTFourPowerAffineTwoTritClassifier.lean (149 lines)
- decls: 9 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: two-trit classification of ¬CommonTwo into bad channels; structural (non-table) proofs that K ≡ 5, 6 (mod 9) are killing classes; counterexamples exclude both classes.
- name-vs-content: accurate.
- gaps: none internally; Collatz-flavored.

### GSTClassicalHodgeFiniteClosedKernelBridge.lean (146 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none new (FiniteClosedCorrespondence, RealizedFiniteClosedCorrespondence imported)
- main content: point kernel extracted from a finite closed correspondence reproduces the old native operator exactly (`closedPointKernel_native_eq`); Betti point-incidence derived from the realization theorem; cross-carrier transfer; diagonal graph = explicit assumption-free identity example.
- name-vs-content: honest ("a construction, not a universal Hodge-generation assumption").
- gaps: relies on the realized-correspondence API (cohomology realization fields) from other files.

### GSTClassicalHodgeActualGeometricIdentityClosure.lean (142 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: the diagonal graph's native operator IS the identity on all cycles (via point normal form + residue degree of id); discharges `HasGeometricIdentity` of the expression algebra; geometric powers for all n ≥ 0 with naturality.
- name-vs-content: accurate.
- gaps: none internally.

### GSTInfiniteGateTransport.lean (141 lines)
- decls: 8 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `InfiniteBadCoupledControl` (imported all-depth bad controller) used to derive LatentGateTransfer.
- main content: Happy gate output is 2; next carry 2 or 3 (never 0); mass re-encoding cellMass = 2 + 3·nextCarry; latent-sector decoder (next carry remembers the Happy sector); coupled happy transports information.
- name-vs-content: accurate carry arithmetic.
- gaps: the infinite bad controller is an imported hypothesis (Collatz-style).

### GSTClassicalHodgeRepairToolkit.lean (136 lines)
- decls: 9 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: proof-engineering lemmas: c⁻¹•(c•F)=F and mirrors; smul/comp transport shapes; map-zero contrapositive; finsupp single-sum scalar transport; linearity of finsupp-sum lifts.
- name-vs-content: accurate (a utility file).
- gaps: none.

### GSTClassicalHodgeTwoSlotLefschetzCollapse.lean (135 lines)
- decls: 3 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: in the two-slot pure diagonal window, bare L² = nonzero forward scalar × the unique forward matrix unit (`diagonalLefschetzQ_two_two_eq_scaled_matrixUnit`); lifted to any Hodge basis pair: two-step GST Lefschetz = scalar × rank-free matrix unit.
- name-vs-content: accurate within the toy window model.
- gaps: toy-model computation; the forward scalar positivity is imported.

### GSTGeneralSpaceTopology.lean (128 lines)
- decls: 3 theorems, 6 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: every topological space → GeneralSpace via propositional path reachability (Nonempty (Path x y)); continuous maps → Hom; homeomorphisms preserve/reflect reachability; carrier chart.
- name-vs-content: accurate GST plumbing.
- gaps: proof-irrelevance makes laws strict — deliberately trivial.

### GSTGraphV2SixAdicOntologicalGeometry.lean (127 lines)
- decls: 3 theorems, 10 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: none
- main content: SixAdicIsoAt (difference divisible by 6^k); dyadic/triadic shadows; balls and six child centers; resolved graphs; ResolvedIso is refl/symm/trans (an equivalence).
- name-vs-content: fair ("ontological geometry" = congruence groupoid).
- gaps: no theorems beyond equivalence laws.

### GSTClassicalHodgeIncidenceRealizationEquivalence.lean (120 lines)
- decls: 4 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: imported hypothesis-packages: `RationalBettiIntersectionPrimitives`, `SchemeBiFiniteClosedCorrespondence`, `MiddleBettiCorrespondenceKernel`, and the pointwise `RealizesAmbientOnPoints` predicate.
- main content: direct Gysin/incidence law ⟺ generatorwise realization ⟺ old incidence packet nonempty (three presentations of the same remaining statement); global transfer square forced by point normal form.
- name-vs-content: honest — the header says the incidence law "is not another mysterious axiom", it is the pointwise realization predicate.
- gaps: the realization predicate itself is the unproved low-level statement.

### GSTFourPowerAffineOrbit.lean (118 lines)
- decls: 8 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: affineOrbit (A0=0, A(k+1)=4A_k+1); 4^K = 1 + 3·affineOrbit K; digit shift; CommonTwo power ↔ affine orbit equivalence; affine cocycle `affineOrbit (K+L) = 4^L·affineOrbit K + affineOrbit L`; three-block renormalization ×64 + 21.
- name-vs-content: accurate arithmetic.
- gaps: none internally.

### GSTClassicalHodgeHomogeneousQuotientNonunit.lean (109 lines)
- decls: 4 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: genuine graded-ring algebra: positive homogeneous f has zero degree-zero projection; f·g-1 projects to -1; hence positive homogeneous elements are nonunits modulo any proper homogeneous ideal (prime version corollary).
- name-vs-content: accurate; exactly the separator-quotient lemma it claims.
- gaps: none.

### GSTGraphV2CMNMPrimitiveLefschetzBridge.lean (106 lines)
- decls: 3 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: `hf`/`hg` : primitive test L annihilates the two input pushforward classes (theorem inputs)
- main content: CM-NM cycle stays in the primitive kernel (`cmNMNativeGraphCycle_preserves_primitive_kernel`); reachable + in-kernel certificate at every arithmetic state; re-export of the universal p=2 projective-product primitive profile (coordinate model).
- name-vs-content: fair; flags the cohomology-coordinate model as distinct from actual scheme intersection.
- gaps: the primitive test L (ample Lefschetz cup power) is an input; p=2 profile is a rational cohomology model, not a Mathlib scheme comparison.

### GSTClassicalHodgeSchemeCodimensionStalk.lean (99 lines)
- decls: 4 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none
- main content: stalk Krull dimension = coheight (Mathlib); codimension-p points ↔ stalk dimension p; codimension strata ↔ stalk-dimension strata; crown.
- name-vs-content: accurate bridge file.
- gaps: none (delegation).

### GSTMiddlePrimitiveProjectiveProduct.lean (97 lines)
- decls: 5 theorems, 3 defs, 0 axioms, 0 sorry
- hypotheses: none (external ring identification ℚ[a,b]/(a³,b³) is prose)
- main content: P²×P² coordinate model: hyperplane cup (x,y,z)↦(x+y, y+z); primitive kernel spanned by a²-ab+b² = (P⁰×P²) - (P¹×P¹) + (P²×P⁰); all primitive classes are scalar multiples of the explicit algebraic combination.
- name-vs-content: honest — "for ONE bona fide fourfold, NOT for arbitrary X"; ring identification not formalized.
- gaps: the cohomology-ring identification and subvariety classes are external input.

### GSTCanonicalTailLTE.lean (91 lines)
- decls: 5 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none
- main content: exact LTE: 4^(3^r) = 1 + 3^(r+1)·lteCoeff r with recursive lteCoeff; lteCoeff ≡ 1 (mod 3); scaled multiples ≡ 1 mod next cut; block composition.
- name-vs-content: accurate number theory.
- gaps: none.

### GSTGeneralSpaceManifoldTangentMorphism.lean (89 lines)
- decls: 2 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: none
- main content: LocalMorphism of local families; mfderiv as covariant tangent-family morphism; tangentMap = GST local morphism (rfl).
- name-vs-content: accurate plumbing over Mathlib manifolds.
- gaps: none.

### GSTClassicalHodgeSurjectiveStalkCutDimension.lean (76 lines)
- decls: 2 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: surjective local map with principal kernel ⟨f⟩, f nonzero nonunit, Noetherian local domain ⇒ dim S + 1 = dim R (principal ideal theorem packaging).
- name-vs-content: accurate.
- gaps: none.

### GSTResearchGeometricWeightBoundaryAudit.lean (76 lines)
- decls: 2 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none (audits the imported bridges)
- main content: **impossibility audit**: if any weight p has trivial native cycle module, then `SpineTowerConservedCharge` and `NativeMassCycleClassBridge` cannot exist (`no_unrestricted_native_mass_bridge_at_empty_weight`); unrestricted all-weights native-mass laws cannot be axioms without resolving the finite-dimensional boundary.
- name-vs-content: honest — "a constraint on the GST MASS BRIDGE, not a counterexample to Hodge".
- gaps: shows the bridge must be dimension-bounded; does not repair it.

### GSTGeneralSpaceRealization.lean (67 lines)
- decls: 1 theorem, 2 defs, 3 structures, 0 axioms, 0 sorry
- hypotheses: none (RealizationMap.commute and TransportedRealization.path_naturality are data fields)
- main content: realization faces of a General Space; realization maps with commutation; transported realizations with path naturality; composite naturality.
- name-vs-content: accurate small interface file.
- gaps: none.

---

## BATCH SUMMARY

**Totals**: 70 files, 19,361 LOC; 691 theorems, 262 defs, 36 structures; **0 `axiom` declarations, 0 `sorry`, 0 `opaque`**; 382 `#print axioms` receipts. The batch is "clean" in the compiler sense — every unproven assumption is packaged as a structure field or theorem hypothesis rather than an axiom or sorry.

**Unproven-assumption inventory (hypothesis-records and standing theorem hypotheses):**

Conjecture-level (assume the target itself or an equivalent):
1. `ActualXFiniteProjectiveTrace.projective_hodge_has_cycles` — *rationalHodgeSubspace ≤ range(cycleClass) for the auxiliary P*: the Hodge conjecture for P, as a field (GSTActualXHodgeResidualProjection).
2. `NativePlaneCompletionAt` / `NativeExecutableGSTPlaneCompleteness` / `HodgeBasisCycleSupply` / `FullGSTPlaneCompleteness` / `FullCorrespondenceOrbitCyclic` / single-program generation — conclusion-strength Props (defs) that several files prove equivalent to `BigradedBettiHodgeStatement`; none is instantiated.

Geometric-semantics packages (classical facts supplied as data):
3. `ProjectiveDegreeTraceSemantics` — degree-positive Betti trace with `trace∘(point cycle class) = degree` (GSTClassicalHodgeProjectiveDegreeTrace).
4. `RightFiniteBettiTrace` / `BiFiniteBettiTrace` — `trace ∘ rightPullback = degree • id`, degree ≠ 0 (finite-transfer Gysin trace) (GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull).
5. `GeometricFiniteDominantMap` — degree, push/pull, `push_pull_degree : bettiPush (bettiPull α) = degree • α`, Hodge-preservation of pull (GSTFiniteDominantAllCodimensionDescent); plus imported `SchemeProjectiveBundleGysin`.
6. `AmbientBettiIntersectionCalculus` / `RationalBettiIntersectionPrimitives` / `MiddleBettiCorrespondenceKernel` / `CrossProductCupGysin` / `FiniteCrossCarrierPointKernel` — cup/Gysin/topology data packages (Mathlib's pinned cohomology stack lacks the full construction), consumed by the kernel-action, incidence, and cup/Gysin-compiler files.
7. `MinimalNativeGeometricCore` — `pointClass_is_hodge` (point cycle classes are Hodge) + `principalCut_kernelStable` (kernel stability of the geometry-built successor).
8. `ActualXCycleProjectionData` — `cycle_is_hodge` + `independently_geometric_duality` (dual detectors to source cycles).

Seed/charge/certificate existentials (the "one more geometric fact" family):
9. `NativeHodgeOrbitSeed` (imported; nonzero algebraic cycle + matching Hodge class) — existence is the standing burden, used in ~10 files.
10. `NativeMassCycleClassBridge` — kernel_mass_zero / base_mass_ne_zero / successor_point_mass (GSTClassicalHodgeLimitlessSpinePropagation); `SpineTowerConservedCharge` manufactured from it. Boundary audit proves it cannot exist unrestricted.
11. `ClassicalHodgeSpectralOperator` — observable diagonal with distinct eigenvalues on the Hodge basis + atomic-span stability (GSTClassicalHodgeCyclicSpectralGeneration).
12. `RootedStrictRelationFan.ray` — per-target strict-relation rays (GSTClassicalHodgeRootedStrictRelationFan); `StrictRelationEdgePacket` certificates.
13. `LiveSupportCorrespondenceSpectralCertificate` — window realization + visible points per live slot (GSTClassicalHodgeLiveSupportCorrespondenceSpectralCrown); `ClosedCorrespondenceWindowRealization` + `SeedVisible` (PiOmniverseCanonicalSupportSpectral).
14. `LiveDegreeCertifiedProgramFamily` / `DegreeCertifiedFullCorrespondenceProgram` (DegreeCertifiedOmniverseLiveCollapse); `ProjectiveWordLiveSourceTarget` + `FiniteSpineMomentChain` (FiniteSupportProjectiveOrbit); `ProjectiveTwoGenerator` family (ProjectiveGeneratorWordCompiler).
15. `NativeCanonicalCosmicRealization` — native lifts of cosmic matrix units with commuting square (CanonicalCosmicRealizationEquivalence).
16. `CupGysinGSTSheetProgram` — cup/Gysin geometry + incidence + basis period expansion per sheet (CMSurfaceCupGysinGSTCompiler).
17. `UniformTensorIntertwiner` / `TensorIntertwinesAt` (FiberedDefectEquivariance).
18. Zeta route: `hMeasure` (readout = zeta·Σ kernel), `ActualHodgeCorrespondenceIrreducible`, per-weight `hZetaGeometry` (MathboxCorrectedZetaActualHodge).
19. `ExistingNativeImageSpanned` + positive-definite polarization `hPositive` + `hGeometricPairing` (ResidualNormZeroExactHodgeEquivalence).
20. Four-power/Collatz flank: `four_power_happy_climb` (third-wave climb hypothesis), `FourPowerCreationMaster`, provider families (PrefixOneOntologicalEscape); `InfiniteBadCoupledControl` (InfiniteGateTransport).

**Five most load-bearing files:**
1. **GSTActualXHodgeResidualProjection.lean** — the arbitrary-X cycle+residual engine; contains the anti-circularity theorem `nativeEulerFullRank_iff_all_targets` (full-rank native sources ⟺ Hodge conclusion) and the outright conjecture-assuming field `projective_hodge_has_cycles`.
2. **GSTResidualNormZeroExactHodgeEquivalence.lean** — proves the residual-zero target ≡ cycleClass surjectivity and that no native cycle/polarization can detect the missing residual: the sharpest statement of what any proof must add.
3. **GSTClassicalHodgeMinimalNativeGeometricCore.lean** — the two-field irreducible core over which the entire program algebra runs; `hodge_of_fullGSTPlane` is the canonical conditional Hodge theorem of the batch.
4. **GSTClassicalHodgeProjectiveDegreeTrace.lean** — the assumed degree/trace semantics that powers Betti nonvanishing of successors, seeds, and the whole degree-certified branch of the campaign.
5. **GSTClassicalHodgeLimitlessSpinePropagation.lean** — the native-mass bridge (3 unproven laws) generating the conserved charge that keeps the all-weights spine alive; its impossibility boundary is audited in GSTResearchGeometricWeightBoundaryAudit.

**Single biggest gap:** every route in this batch to `BigradedBettiHodgeStatement` terminates in an explicitly unwitnessed existence premise (strict-relation rays, window realizations, cup/Gysin packets, spectral operators, two-generators, native-mass laws, zeta readouts, or the plane-completion Prop itself) — and the one place the needed statement appears as a field (`projective_hodge_has_cycles`) it *is* the Hodge conjecture. Not a single file constructs any of these hypotheses for a general smooth projective X; the batch's honest self-assessment (ResidualNormZero, LocalizedL2NativeCircularity) confirms the remaining content is exactly the unproved conjecture. The absence of `sorry`/`axiom` means the gap is invisible to CI: it hides in unfilled structure fields.
