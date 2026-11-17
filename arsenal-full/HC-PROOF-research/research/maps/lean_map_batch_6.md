# Lean Batch 6 Map (Task 1-g)

Repo: /tmp/hc-clone-23 @ branch research/gpt6-native-point-primitive-span-20261017.
72 files, 19,376 LOC total. Convention notes: NO `sorry` anywhere in the batch; NO Lean
`axiom` commands anywhere in the batch (the single textual `axiom` hit is the English word
inside a docstring). All unproven mathematical input enters as (a) `structure ... where`
hypothesis-records with proposition fields, (b) `def ... : Prop` hypothesis predicates
("premise defs"), or (c) explicitly-premised conditional theorems. Imported load-bearing
premises (defined in other batches, referenced here): `GeometricCycleClassSpine`,
`GhostWeightNativeSeedSurvival`, `GhostSeedTargetStrictClosure`,
`GSTBranchPacketPlaneRealization` (:= `GhostSeedTargetStrictClosure`, `rfl`),
`OmniversalSeparatorGhost`, `ProjectiveDegreeTraceSemantics`,
`NativePointSuccessorNonvanishing`, `NativeMassCycleClassBridge`.

### GSTClassicalHodgeBranchPacketPlaneRealization.lean (1863 lines)
- decls: 53 theorems, 3 defs, 0 axioms, 0 sorry
- hypotheses: `structure NativeFiniteGraphGenerator V H p where` — fields:
  `analytic : AnalyticEndomorphism H.analytification`, `finite : IsFinite analytic.algebraic.hom`,
  `point_natural : ∀ x : CodimensionPoint V.X p, H.cycleClass p ((finiteGraphStrictCarrier analytic finite)...gradedNativePointImage p x) = rationalCohomologyPullback H.analytification analytic (2*p) (H.cycleClass p (codimensionPointCycle V.X p x))` [naturality of cycle class under the transpose-graph carrier — real trace geometry, here a record premise],
  `hodge_stable : ∀ alpha : ClassicalHodgeFiber V H p, rationalCohomologyPullback ... alpha.1 ∈ rationalHodgeSubspace (H.hodgeBigrading p)` [pullback preserves Hodge subspace].
  Imported unproven law used as premise throughout: `GSTBranchPacketPlaneRealization G` (= `GhostSeedTargetStrictClosure G`, declared UNPROVEN in the "HONEST AXIOM STATUS" header).
- main content: V3 of the branch-packet plane law audit. Genuinely proved: the constructive diagonal fragment (identity-graph strict carrier has graded native point image `= codimensionPointCycle`; every branch node `u` has a strict packet `u ⟶ u` unconditionally); the monomial-sheet ghost constraint (surviving ghosts forced off-diagonal); the exact split theorem `gstBranchPacketPlaneRealization_iff_offDiagonal`; zero-cycle-world boundary theorems (constructive diagonal fragment coexists with an actual ghost, so provably NOT Hodge-sufficient; `(survival ∧ law)` fails on the zero-cycle world); `gstPlane_axiom_status_crown_v3` packaging A/B/C/diagonal/off-diagonal/monomial/boundary/necessity/soundness-firewall; finite-graph word algebra (`finiteGraphNativeWord`, append laws, word-constructs-native-target).
- name-vs-content: name says "realization"; content is the audit *around* an unproven law — the file explicitly says "Any unconditional proof of the law would BE the new mathematical content closing Hodge".
- gaps: the law itself (off-diagonal fragment) is unproven; `NativeFiniteGraphGenerator.point_natural`/`hodge_stable` are premises; the whole `hodge_of_*` family is conditional on `NativeMassCycleClassBridge` + the law.

### HodgeConjecture.lean (1177 lines)
- decls: 40 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: `structure UniverseIndexedRealization V H p ι where` — fields: `realization : CompactHodgeRealization ι (RationalSingularCohomology ...) (codimensionCycles V.X p)`, `hodge_iff : realization.isHodge alpha ↔ alpha ∈ rationalHodgeSubspace ...`, `cycleClass_eq : realization.cycleClass = H.cycleClass p` (repackaging of the Hodge statement itself into a realization record). ~20 external hypothesis structures premised in `classicalHodgeTarget_of_*` theorems: `CMGSTNativeBasisProgramSupply`, `CupGysinGSTSheetProgram`, `UniversalGSTGeometricDeterminantGeneration`, `UniversalGSTTriangularPeriodGeneration`, `UniversalGSTKrylovHankelNondegeneracy`, `UniversalProjectiveDegreeKrylovNondegeneracy`, `ActualHodgeCorrespondenceIrreducible`, `UniversalGSTChargedGeometricFrameGeneration`, `SpineTowerNonvanishing`, `FullProjectiveCosmicExternalization`, `SpineTowerConservedCharge`, `ProjectiveTwoGenerator`, `NativeExecutableGSTPlaneCompleteness`, `Stage2GCompactRealizationObligation`, `HodgeBasisCycleBridge`, `Stage2GHodgeFiniteness`.
- main content: the public landing face. `ClassicalHodgeTarget V H` is *definitional* the Stage-2G statement (every rational (p,p) Hodge class alpha has `∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha`). Proves: iff normal forms (explicit-witness, basis-cycle-bridge, canonical-basis-algebraization), family-of-realizations forms, and an independence countermodel `geometric_spine_laws_alone_cannot_establish_classicalHodgeTarget` (constructs H0 with a spine where the target fails).
- name-vs-content: name says "HodgeConjecture"; content is a router of conditional routes *into* the conjecture, not a proof — honest header: "No internal GST surrogate is substituted".
- gaps: every forward route is premised on an unproven supply/determinant/irreducibility structure; the file itself proves equivalences, re-packagings, and one negative result (spine laws alone insufficient).

### GSTGradedWorldAlgebra.lean (874 lines)
- decls: 49 theorems, 23 defs, 0 axioms, 0 sorry
- hypotheses: none (no proposition-field records; all content proved). `structure CausalHodgeCell where cohomologicalDegree/leftWeight/rightWeight : ℕ` is pure data.
- main content: elementary combinatorial grading algebra of GST "world" cells: degree projectors idempotent/orthogonal/complete; digit/carry shifts raise degree by shift depth; finite-world Kunneth projector polynomial `∃ p : Polynomial Int, c ≠ 0 ∧ ...`; cosmic degree/charge arithmetic + injectivity; `CausalHodgeCell` tensor laws (charge/purityGap additivity), monodromy-lower laws (degree fixed, both weights lowered), signed causal fold laws, nodal vs smooth birth signatures.
- name-vs-content: name accurate — graded arithmetic only; docstrings disclaim geometric realization ("does NOT supply ... a Chow cycle representing an arbitrary rational Hodge class").
- gaps: purely formal shadow; real geometry (scheme realization, MHS comparison, cycle-class map) deferred to research/ .tex derivations, absent here.

### GSTClassicalHodgeCommonClassPlaneReduction.lean (660 lines)
- decls: 18 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: no new structures; premises are imported: `GhostWeightNativeSeedSurvival G`, `GhostSeedTargetStrictClosure G`, `GhostWeightPrimitiveStrictClosure G`, `ProjectiveDegreeTraceSemantics V H`, `NativePointSuccessorNonvanishing V`, `GeometryFirstTwoGenerator` supplies, per-ghost `CodimensionPoint` existence.
- main content: bookkeeping reduction: `Nonempty (CommonClassPlanePacket u v) ↔ Nonempty (StrictRelationEdgePacket u v)` (common-plane layer adds no new existence axiom); ghost trace-pushpull mismatch formula (`ghostSeedTarget_traceMismatch_ne_zero`, `ghostSeedTarget_pushPull_ne_target`); `targetStrictClosure_iff_noGhost_of_survival`; `(survival ∧ targetStrictClosure) ↔ Hodge`; native-cut seed-or-stop certificate (`nativeCutSeedOrStop_hodge_certificate`); bounded-horizon Hodge (`hodgeThroughFiniteNativeHorizon`, `bigradedHodge_of_boundedNativeCuts`) conditioned on no stopped cuts + two-generator supplies per weight.
- name-vs-content: name accurate ("reduction"); it is a reduction layer, not a closure proof.
- gaps: header admits "uniform native principal-cut survival HYPOTHESIS ... The tower does not prove that survival hypothesis"; strict target packet and positive-degree semantics remain explicit premises.

### GSTClassicalHodgeSheetSiegeRoute.lean (574 lines)
- decls: 15 theorems, 7 defs, 0 axioms, 0 sorry
- hypotheses: premise-defs (exact quotes):
  - `SheetSiegeCoheightUpperBound V : ∀ (p : Nat) (x : CodimensionPoint V.X p), ProjectivelyLiveSource V.projective.n (V.projective.immersion x) → ∀ y : {y : pointClosureScheme V x.1 // Order.coheight y = 1}, y ∈ relativeCodimensionOneFinset V x.1 → Order.coheight (ambientSuccessorPoint V x.1 y) ≤ (p + 1 : ℕ∞)` [catenarity/height-additivity residue].
  - `SheetSiegeCoheightAdditivity V : ∀ (p : Nat) (x : CodimensionPoint V.X p), ProjectivelyLiveSource ... → RelativeSuccessorAmbientExact V p x` [L1: separator successors have ambient coheight exactly p+1].
  - `SheetSiegeSeparatorSuccessorExact V : ∀ p x hlive, Order.coheight (ambientSuccessorPoint V x.1 (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1` [L1-min; would discharge ~15 files of downstream `hExact` premises].
  - `SheetSiegeLiveWeightSeeds V H : ∀ q : Nat, Nonempty (NativeHodgeOrbitSeed (V := V) (H := H) (p := q))` [L2 unguarded — REFUTABLE: firewall theorem proves its negation on the zero-cycle world].
  - `SheetSiegeLiveWeightSeedsGuarded V H : ∀ q : Nat, Nonempty (CodimensionPoint V.X q) → Nonempty (NativeHodgeOrbitSeed (V := V) (H := H) (p := q))` [L2 canonical].
  - `SheetSiegeDegreeTraceConstructed V H : Nonempty (ProjectiveDegreeTraceSemantics V H)` [L3-a].
  - `SheetSiegePointDegreeFunctional V H : ∀ q : Nat, ∃ f : RationalSingularCohomology H.analytification (2 * q) →ₗ[ℚ] ℚ, ∀ x : CodimensionPoint V.X q, 0 < f (H.cycleClass q (codimensionPointCycle V.X q x))` [L3-a core: positive point-degree functional].
- main content: Route S (sheet siege) audit. Proved: `hodge_of_geometricPlaneCompleteness` (front door: coverage → orbit cyclicity → ghost extinction → Hodge); L1 lower bound `sheetSiege_successor_coheight_ge`; L1 ⟺ upper-bound residue; L1 ⇒ L1-min; L2 firewall `sheetSiegeLiveWeightSeeds_false_of_zeroCycleClassData`; guarded L2 from spine+degree trace; L3-a ⟺ positivity core (two iff theorems with explicit construction-debt list: cup product, integration over fundamental class, hyperplane class, point-degree positivity).
- name-vs-content: name "Siege Route" accurate: decommissions the branch-packet law as a proof target and prices the remaining debt lemma-by-lemma.
- gaps: L1 upper bound = catenarity (no producer in repo); L2 guarded unproven; L3-a construction inputs (cup product, integration, hyperplane class, positivity) absent from repo and pinned Mathlib; the only in-repo constructor of the degree trace rests on `NativeMassCohomologyFactorization`, false for genuine cycle-class maps.

### GSTClassicalHodgeNativeMassBridgeAudit.lean (403 lines)
- decls: 13 theorems, 2 defs, 0 axioms, 0 sorry (the lone `axiom` textual hit is a docstring word)
- hypotheses: `structure FiniteHorizonNativeMassBridge V H horizon where` — fields (exact):
  `kernel_mass_zero : ∀ (p : Nat), p ≤ horizon → ∀ Z : codimensionCycles V.X p, H.cycleClass p Z = 0 → nativeCycleMass V p Z = 0`;
  `base_mass_ne_zero : nativeCycleMass V 0 (codimensionZeroFundamentalCycle V) ≠ 0`;
  `successor_point_mass : ∀ (p : Nat), p < horizon → ∀ x : CodimensionPoint V.X p, successorMass V p x = successorScalar p` [exact two-successor cardinality law below the horizon].
  (Also documents imported `NativeMassCycleClassBridge` with the same three fields, unrestricted.)
- main content: audit separating the three mass-bridge ingredients: `nativeMassKernelLaw_iff_cohomologyFactorization` (kernel law ⟺ mass factors through cycle class); `baseMass_ne_zero_iff_codimensionZero_nonempty`; `successorScalar_eq_two`; `successorMass_eq_successorScalar_iff_exactRelativeCard_two` (equality is exactly "two exact relative successors at every point"); `nativeMassCycleClassBridge_iff_audited_frontier`; finite-horizon spine conservation (`spine_mass_conserved`, `spine_cycleClass_ne_zero`, `spine_hodgeSeed_ne_zero`); `no_global_nativeMassBridge_of_terminalCut` (terminal point with empty exact-successor locus refutes the global bridge).
- name-vs-content: name "Audit" accurate — a decomposition/honesty module for an imported hypothesis, not a proof of it.
- gaps: the mass bridge (global or finite-horizon) is nowhere constructed; `successor_point_mass` is a strong exact-cardinality constraint (successor locus cardinality = 2) that no positive-dimensional smooth projective variety satisfies globally.

### GSTGraphV2CanonicalEscape.lean (520 lines)
- decls: 21 theorems, 3 defs, 0 axioms, 0 sorry
- hypotheses: none (premise-free ℕ-arithmetic; `SeedHappy`/`HappyCell` conditions appear as hypotheses of individual lemmas, not as global records)
- main content: canonical escape packets for the Graph-V2 ternary/carry world: energy decompositions `4^(3^(s+1)*n)` and parent/child tails; left/right seed adapters and u-jump adapters for `graph` cells; latent gate transfer packets conditioned on `SeedHappy`/bad-parent side conditions; canonical tail cut-quotient exactness; `nat_ternary_support_eventually_zero` / `nat_has_finite_ternary_support` (every ℕ has finite ternary support).
- name-vs-content: accurate — "canonical escape" is the graph-world escape mechanism; no Hodge content at all.
- gaps: none mathematical (self-contained arithmetic); relevance to Hodge is only via the Graph-V2 narrative, not proved here.

### GSTClassicalHodgeFiberedNativeTensorArsenal.lean (472 lines)
- decls: 22 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: none new (operates on already-defined `FiberedNativeAddress`/`CodimensionPoint` structures; all theorems unconditional algebra identities)
- main content: tensor-product operator algebra on (Hodge-multiplicity label × native point) addresses: multiplicity matrix units (atom source/other, composition, projectors, commutation with lifted native operators and projective kernels), tensor words (`tensorWord_atom_source`, `tensorWord_nativeFace`), `fibered_native_tensor_arsenal_crown`, and descent analysis (`tensorWord_descends_native_iff_zero`, `multiplicityMatrixUnit_not_descend_native`).
- name-vs-content: "arsenal" is operator algebra, correctly stated; no Hodge-surjectivity claimed.
- gaps: descent obstruction is *proved* (most tensor words do not descend to native operators); no algebraic-geometric construction of the correspondence operators themselves here.

### GSTUniversalAntigraphDiagonalSurgery.lean (429 lines)
- decls: 16 theorems, 13 defs, 0 axioms, 0 sorry
- hypotheses: none (the geometric interpretation is narrative; the Lean content is ring coefficient identities + a general cellular-basis form stated for arbitrary `term`/`degree` functions)
- main content: for X_n = P^n × P^n with hyperplane classes A,B: `[Γ_c] + [Δ] = 2 Σ_{Even(n-j)} A^(n-j) B^j` (conjugation-graph + diagonal surgery into holomorphic products of linear subspaces), the complementary unsigned decomposition resolving 2Δ, the general cellular version `full_cellular_antigraph_surgery` for any finite basis with a parity involution, and integer-degree-k graph ample surgery (coefficients `k^(n-j)` replaced effectively, `graphAmpleBudget_nonnegative`).
- name-vs-content: honest — docstring: "an exact coefficient theorem, not a claim that every arbitrary X has such an effective basis or antiholomorphic involution".
- gaps: geometric classes (Γ_c, Δ, subspaces) are interpreted, not constructed in Lean; no connection to arbitrary X or to Hodge classes outside P^n×P^n.

### GSTClassicalHodgeOmniverseLefschetzRayCompiler.lean (388 lines)
- decls: 16 theorems, 3 defs, 0 axioms, 0 sorry
- hypotheses: premise-defs (exact quotes):
  - `LocalizedL2PrimitiveRealization : ∀ i j : ClassicalHodgeBasisIndex V H p, ∃ E : RealizedCorrespondenceExpr V H p, ∀ alpha : ClassicalHodgeFiber V H p, E.cohomologyOperator alpha.1 = (liftFiniteHodgeOperator (pairBasisIndex i j) (diagonalLefschetzQ 2 2) alpha).1` [one realized correspondence per ordered basis pair realizes the bare localized two-step Lefschetz operator on the whole fiber].
  - `SourcewiseLocalizedL2PrimitiveRealization : ∀ alpha i j, ∃ E, E.cohomologyOperator alpha.1 = (liftFiniteHodgeOperator (pairBasisIndex i j) (diagonalLefschetzQ 2 2) alpha).1` [source-dependent weakening].
  - `ApexLocalizedL2Realization S : ∀ j, ∃ E, E.cohomologyOperator S.hodge.1 = (liftFiniteHodgeOperator (pairBasisIndex S.sourceIndex j) (diagonalLefschetzQ 2 2) S.hodge).1` [apex-only spokes from one algebraic seed].
- main content: compiler hierarchy proved: global ⇒ sourcewise ⇒ apex; sourcewise ⇒ `PrimitiveBranchCompiler`; diagonal realizes the reflexive branch; causal paths and closure nodes get realized expressions (`causalPath_has_realized_expression`, `closure_node_has_realized_ray`); semantic stability; `hodge_weight_of_apexLocalizedL2` (fixed-weight Hodge landing from apex localized L² + algebraic seed).
- name-vs-content: "compiler" accurate — it compiles geometric input *into* branch events; the geometric input itself is the unproven premise.
- gaps: none of the three realization predicates is constructed anywhere in this file; `RealizedCorrespondenceExpr` cohomology-operator equality with the Lefschetz word is exactly the missing geometry.

### GSTGraphV2ProductionLaws.lean (370 lines)
- decls: 19 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: exact digit/carry/navigation-nullspace laws for the Graph-V2 production cell (`horizontal_digit_exact`, `vertical_carry_exact`, `navigation_nullspace_flux_exact`); origin-frame phased-tail transport (`origin_frame_happy_iff`, `origin_frame_event_exact`); residual-gate neutrality/happy-transport; `production_semantic_transport_crown`; residual level-one width/parent-exponent/energy laws.
- name-vs-content: accurate (production laws of the automaton); zero Hodge content.
- gaps: none internally; external relevance only via the Graph-V2 subprogram narrative.

### GSTClassicalHodgeOmniversalSeparatorGhostCrown.lean (350 lines)
- decls: 10 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: `structure OmniversalSeparatorGhost G where` — fields: `weight : Nat`, `sheet`, `separator : BasisAtomicSeparator V H weight sheet`, `ghost ≠ 0`, `ghost_detects_sheet : fiberedPairing (fiberedWeightCoordinates ... (classicalHodgeBasis V H weight sheet)) ghost ≠ 0`, `kills_all_native_programs : ∀ p P Z, separator.detector (P.cohomologyEval G (H.cycleClass p Z)) = 0`, `backward_atomic : ∀ p P, AnnihilatesPointCycleClasses p (H.cycleClass p) (pullbackDetector G P separator.detector)` — NOTE: this is a *derived obstruction record*, not an assumption: the file proves `not_hodge_iff_nonempty_omniversalSeparatorGhost`. Premised (imported) hypotheses for the positive direction: `OmniversalNativeOrbitPairingTotal G`, `GradedGeometricOrbitModuleCyclic G`.
- main content: ghost crown packaging: `hodge_iff_no_omniversalSeparatorGhost` (Hodge ⟺ no ghost); probe support/annihilation lemmas; `no_omniversalSeparatorGhost_of_nativeOrbitPairingTotal`; `hodge_of_gradedGeometricOrbitModuleCyclic_noGhost`; `hodge_of_nativeOrbitPairingTotal`.
- name-vs-content: "crown" = obstruction equivalence + conditional elimination; accurate.
- gaps: elimination theorems all premised on unproven `OmniversalNativeOrbitPairingTotal` / `GradedGeometricOrbitModuleCyclic`; ghost existence itself is only equivalent to failure, never independently controlled.

### GSTClassicalHodgeSquareStrandLocalization.lean (341 lines)
- decls: 11 theorems, 4 defs, 0 axioms, 0 sorry
- hypotheses: none new (works from `AtomicSeparatorProbe`, imported)
- main content: finite-square localization of Hodge states: `supportDiagonalWorld` pure/zero-charge/eq-zero-iff; `fiberedPairing_eq_squarePoincare` and `fiberedPairing_eq_pureSquarePoincare`; zero-charge probe projection invariance; `atomicSeparatorProbe_has_pureSquare_witness`; `not_hodge_yields_nonzero_pureSquare_pairing` (failure of Hodge ⇔ nonzero pure-vs-pure Poincare pairing inside one finite square world).
- name-vs-content: accurate: a localization/reformulation of the separator witness into finite GST squares.
- gaps: purely repackaging — proves no new algebraicity; the finite-square world is a combinatorial model, not the variety.

### GSTU2DSharpCrossingBlock.lean (329 lines)
- decls: 9 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: none (lemma hypotheses are bounded digit/carries `C t < 4`, `d t < 3`, `outDigit (C t) (d t) = d (t+1)`, `HappyCell (C 0) (d 0)` — local automaton constraints, not global assumption records)
- main content: integer lower-bound inequalities for the reverse-cross code and weighted crossing prefixes of the 2-D graph automaton: `94·4^N + sharpTerminalPotential (d N) ≤ ...`, `sharpTerminalPotential_ge_149`, weighted-crossing global floor and quantized positivity crowns (`0 < weightedCrossPrefix ...`).
- name-vs-content: accurate ("sharp crossing block" = quantitative crossing inequality); no Hodge content.
- gaps: none internal; externally only feeds the Graph-V2 termination narrative.

### GSTUniversalLefschetzPathFormula.lean (321 lines)
- decls: 15 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: exact path calculus on the quotient cohomology ring ℤ[H,V]/(H^B,V^A): binomial expansion `(L)^n = Σ (n choose m) H^m V^(n-m)` (also anisotropic two-coupling version); action-on-cells path formula with wall conditions; boundary coefficient `(C+d choose d)`; the historical 4×3 bottom-to-top coefficient; `universal_lefschetz_path_crown`; cosmic Lefschetz binomial path decomposition.
- name-vs-content: accurate — a universal ring identity; no claim about varieties.
- gaps: model-world algebra only; no transfer to genuine cohomology of any X is asserted here.

### GSTGhostRayExclusion.lean (309 lines)
- decls: 12 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: `def GhostRay (u : Nat) : Prop := ∀ k ≥ 3, 3^(k-1) ≤ (c (k-1) * u) % 3^k < 2 * 3^(k-1)` (a *defined* object of study, not an assumption). The advertised external input — Mahler's 3-adic exponential transcendence — is NOT in this file; it lives in `GSTWorldtraceMahlerRelativePrecision` (outside this batch).
- main content: the arithmetic spine of the Worldtrace ghost-ray exclusion: `ghost_residue_shape` (all-ones tail `2·((c(k-1)·u) % 3^k) + 9 = 2a + 3^k`), `ghost_congruence`, `ghost_tower_lock` (`2u(4^(3^s)−1) − (2a−9)·3^(s+1) = 3^(2s+2)·m`), `ghost_witness`, `ghost_convergence`, `ghost_relative_precision`, `ghost_unbounded_relative_precision` (3-adic convergence of `(4^(3^s)−1)/3^s` to `(6a−27)/(2u)`), `ghost_head_unit`, `exists_three_free_decomp`. Ends with `#print axioms` receipts.
- name-vs-content: "Exclusion" overstates: the file proves the ghost⇒Mahler-witness chain, but the exclusion itself needs the external transcendence input.
- gaps: transcendence denial and the "uniform compression bridge" (every Cantorian counterexample's three-free core lies on a ghost ray) are unproven/external; the terminal closing theorem is absent.

### GSTUniversalExternalProductCurrentSurgery.lean (304 lines)
- decls: 16 theorems, 8 defs, 0 axioms, 0 sorry
- hypotheses: `structure PrimitiveCurrentNumerics where` — fields: `mass : ℚ`, `period : ℚ`, `mass_nonnegative : 0 ≤ mass`, `calibrated_bound : period ≤ mass` [assumed numeric envelope of a primitive carrier; the defect `primitiveDefect S = mass - period ≥ 0` is derived]. No other assumptions.
- main content: exact defect-transport arithmetic for external-product surgery: `external_surgery_exact_mass_drop` (Mass(S×(Γ+Δ)) = 4·Mass(S) → 2·Mass(S)), `external_surgery_exact_defect_drop`, `external_surgery_retains_primitive_defect` (output defect = 2·Defect(S)), `external_surgery_zero_defect_iff_original_calibrated`, general tensor decomposition `generalTensorDefect S a b = a·Defect + ...`, rigidity under repeated/tensor stabilization (`repeated_calibrated_tensor_rigidity`, `zero_tensor_defect_iff_both_factors_calibrated`, `arbitrary_finite_calibrated_tensor_rigidity`).
- name-vs-content: honest — docstring: output defect vanishes ONLY IF S already calibrated; "explicitly tests and REJECTS a possible inference that universal product-based GST surgery eliminates arbitrary primitive Hodge defects".
- gaps: Lean verifies the arithmetic, not GMT (external-product mass/period multiplicativity, rectifiability) — those are narrative; no all-X Hodge assertion.

### GSTTowerFire.lean (297 lines)
- decls: 18 theorems, 3 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: the c-tower `c n = (4^(3^n)−1)/3^(n+1)`: exact LTE decomposition `4^(3^n) = 1 + 3^(n+1)·c n`, cube recursion, congruences `c ≡ 1 mod 3`, `c ≡ 7 mod 9` (n≥1), `c ≡ 16 mod 81` (n≥3); divide-and-mod gluing and prefaced-digit lemma; deep-hider master lemma `tower_digit_read` (rows n+1..2n+1 of `4^(j·3^n)` = digits 0..n of `j·c n`); the three fire laws (`three_pow_fires`, `two_mul_three_pow_fires`, `three_pow_plus_one_fires`); towerReadProfile observability lemmas.
- name-vs-content: accurate (tower digit-fire arithmetic of the Worldtrace lane D).
- gaps: none internal; this is support arithmetic for the Cantorian/ghost-ray subprogram, no Hodge content.

### GSTClassicalHodgePointKernelOperatorLift.lean (287 lines)
- decls: 8 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none new (uses imported `PointClassTransitionKernel` records as *input interface*, proving they manufacture operators)
- main content: the compact-cycle presentation equivalence: `realizePresentationLinear` / `presentationOfNativeCycleLinear` are mutually inverse (`compactCyclePresentationLinearEquiv` apply/symm lemmas) — native codimension-p cycles ≃ finite rational point presentations on compact schemes; a `PointClassTransitionKernel` extends to `presentationOperator`, satisfies finite-point-class naturality, yields `nativeCycleOperator` commuting with the cycle-class map, and assembles a complete `CycleClassOperatorPair`.
- name-vs-content: accurate: a lift/equivalence lemma file, genuinely proved linear algebra.
- gaps: none in scope; it only *packages* kernels, does not construct any geometric transition kernel.

### GSTMathboxCMNumberBridge.lean (280 lines)
- decls: 16 theorems, 4 defs, 0 axioms, 0 sorry
- hypotheses: no records; load-bearing inline premises in the conditional results: `hCM : imagRead (movedSpine G E) = b`, `hb : b ≠ 0` [a *genuinely realized* correspondence E acts on the rank-2 Hodge fiber with a certified nonzero "imaginary" transverse coordinate], plus `hlive : ell (spineHodgeSeed G p) ≠ 0`, `hrank : finrank = 2`.
- main content: adversarial translation of three photographed CM "candidate laws": E1 radicand algebra (`photographedConversion_sq`, nonvanishing under strict positivity — "not by itself a nonvanishing or actual-cycle theorem"); E2 refuted as universal (`photographed_E2_nonzero_not_universal`); E3 finite partial-sum identity and positivity of the repaired kernel `n²+a²+b²`; CM matrix algebra (`cmActionMatrix_det`, `cmChargedWedge_ne_zero_of_imag_ne_zero`); conditional landing `rank_two_hodge_cycle_of_verified_CM_geometry` (verified CM coordinate + rank-2 fiber ⇒ actual rational algebraic cycle for every rational Hodge class in that fiber).
- name-vs-content: "bridge" accurate: the numeric side is real; the geometric side is explicitly displayed as an input.
- gaps: the coordinate bridge `hCM` (a realized correspondence with nonzero transverse coordinate) is nowhere constructed; infinite summability of E3 explicitly NOT claimed.

### GSTClassicalHodgeProjectiveSeparatorSuccessorPoint.lean (276 lines)
- decls: 15 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none beyond the local `ProjectivelyLiveSource n x` premise (defined earlier in the import chain)
- main content: genuine commutative algebra: separator quotient ideal ≠ ⊤; Krull height-one minimal prime; ambient prime is prime/homogeneous/minimal over (source prime ⊔ separator equation); `separatorAmbientPrime_not_irrelevant` (height-one cannot contain the irrelevant ideal of height ≥ 2 at a live source); `source_le_separatorSuccessorPoint`, `separatorSuccessorPoint_ne_source`, membership in the principal section set; crown `projective_separator_successor_crown` (a strictly specialized new Proj point on the chosen principal section).
- name-vs-content: accurate: an actual construction of a projective successor point; explicitly "No Hodge class, cycle-class map, or algebraicity conclusion is used".
- gaps: successor existence is point-level ideal algebra only; connecting it to seeds/mass (successor exactness, degree trace) happens in other files and remains unproven there.

### GSTClassicalHodgeApexSpineFanProgramNormalForm.lean (273 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: no local records; premises: `hne : H.cycleClass p (projectiveCutTower V p) ≠ 0` [nonzero canonical principal-cut tower class at every weight — UNPROVEN] and `F : RootedStrictRelationFan (canonicalCutOrbitSeed G p hne)` [one finite materialized strict-relation ray per weight — UNPROVEN], plus the spine `G`.
- main content: executable normal form: strict-ray programs evaluate as correspondence expressions (`strictRayProgram_eval`, `rootedFanProgram_eval`); root-to-target and root-to-basis single programs act on the geometric origin class (`canonicalRootToTargetProgram_origin_action`, `canonicalRootToBasisProgram_origin_action`); basis membership in the full correspondence orbit module; `exists_singleProgram_of_canonicalCut_rootedFan` (every rational Hodge class = one graded correspondence program output from the origin); `exactHodge_of_canonicalCut_rootedFans` (crown).
- name-vs-content: "normal form" accurate: it compiles ray+spine to one program; the two geometric burdens are named honestly.
- gaps: exactly the two listed burdens (nonzero cut-tower class; materialized fans) are unproven; nothing here reduces them.

### GSTClassicalHodgeProjectiveSpanWordSaturation.lean (264 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `structure ProjectiveSpanLiveSourceTarget S j where` — fields: `kernel : ProjectiveNativeKernel V p`, `native_source_class : H.cycleClass p (kernel.1 S.cycle) = (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex • (classicalHodgeBasis V H p j).1` [one native cycle-class equation: a genuine projective correspondence sends the live source cycle to the correct scalar multiple of the target sheet]. Premised imports: `GeometricCycleClassSpine`, `SpineTowerConservedCharge`.
- main content: span-to-word compilation (`exists_projectiveOperatorWord_of_mem_span`, unconditional, by span-induction); `compileProjectiveNativeKernelWord_eval`; `basis_mem_direct_geometric_orbit`; crowns `bigradedBettiHodge_of_projectiveSpan_live_source` and `every_hodge_class_has_native_cycle_of_projectiveSpan_live_source`.
- name-vs-content: accurate: saturation = compiling span elements into words; the Hodge crowns remain conditional.
- gaps: `ProjectiveSpanLiveSourceTarget` for every target direction is exactly the missing geometric input (a projective correspondence realizing each basis sheet from the live source); `SpineTowerConservedCharge` likewise unproven.

### GSTClassicalHodgePiSpineMassUnboundedFinale.lean (260 lines)
- decls: 8 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: no local records; premises: `M : NativeMassCycleClassBridge V H` (imported hypothesis structure) and `hgeom : ∀ p : Nat, ∀ {u v : HodgeBranchNode ...}, (hodgeBranchGraph ...).Event u v → StrictlyMaterializedBranch u v` [every branch-graph event is strictly materialized — UNPROVEN omniverse premise].
- main content: canonical-source Pi-wide route: `spineSeed_in_cycleClassRange`, `spineSeed_nonzero_algebraic` (under M), all-sector unbounded algebraic branches (`spineSeed_allSectors_unbounded`, `targetBasis_allSectors_unbounded_algebraic_branch`), exact N-cohomology support (`spineSeed_exact_ncohomology`), `targetCycle_of_spineMass_unboundedOmniverse`, `bigradedBettiHodge_of_spineMass_unboundedOmniverse`, and the operational crown `pi_spineMass_fullOmniverse_crown`.
- name-vs-content: "finale" is a conditional crown, honestly labeled ("No Hodge target is assumed algebraic" — but the mass bridge and materialization premises are assumed).
- gaps: `NativeMassCycleClassBridge` (kernel mass law + base nonvanishing + exact two-successor cardinality) and `StrictlyMaterializedBranch` for all events are both unproven; the whole Pi route is conditional.

### GSTClassicalHodgeBareLefschetzSpineFinale.lean (253 lines)
- decls: 8 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: no local records; premises: `SpineTowerConservedCharge G` or `NativeMassCycleClassBridge V H` (imported), and `hL : ∀ M : MinimalPrimitiveGhost G, HasNativePointLifts (ambientTwoStepLefschetz ...)` / uniform form `hL : ∀ p i j, HasNativePointLifts ...` where `HasNativePointLifts T : ∀ x : CodimensionPoint X p, ∃ Z : codimensionCycles X p, cl Z = T (cl (codimensionPointCycle X p x))` [each transformed genuine point class has a native algebraic representative — the "bare L² native point-lift law", UNPROVEN].
- main content: reduction chain conserved-charge → nonzero canonical spine seed at minimal bad weight → algebraic local source → bare two-slot L² point-lift → minimal ghost contradiction → Hodge: `minimalGhost_false_of_spine_bareLefschetz`, `bigradedBettiHodge_of_conservedCharge_and_bareLefschetz`, `bigradedBettiHodge_of_nativeMassBridge_and_bareLefschetz` (+ uniform variants), `isEmpty_minimalPrimitiveGhost_of_hodge`, `minimalGhostBareL2Closure_iff_hodge` (equivalence).
- name-vs-content: honest — header: "a genuine reduction theorem. It does not claim the remaining bare L² native point-lift law or the native-mass bridge is already constructed."
- gaps: both the point-lift law (algebraicity of L²-transformed point classes) and the mass bridge remain open; the file is a conditional pipeline.

### GSTTowerAxis.lean (253 lines)
- decls: 10 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none (class-membership premises only, e.g. `c % 9 = 1`)
- main content: structural kill of s≥1 exponent families via the deep-hider lemma: level one (c ≡ 1 mod 9 fires at row s+2), `c_mod27_ge_two` (c ≡ 16 mod 27 for s ≥ 2), level two (c ≡ 13,25 mod 27), level three (c ≡ 4,34,49,70 mod 81); uniform fire window and navigation boundedness; `not_cantorian_of_tower_axis` (three infinite families are non-Cantorian); `tower_axis_uniform_crown`.
- name-vs-content: accurate (tower-axis digit arithmetic); no Hodge content.
- gaps: none internal; residual "tower-axis dust" survivors (c ≡ 4,22 mod 27, etc.) explicitly remain — the Cantorian classification is incomplete by design.

### GSTClassicalHodgeLocalSeedBareLefschetzExtinction.lean (242 lines)
- decls: 5 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: two local hypothesis-records (exact fields):
  - `structure MinimalGhostLocalSeed G M where`: `source : ClassicalHodgeFiber V H M.weight`, `source_algebraic : source ∈ AlgebraicHodgeSubspace V H M.weight`, `sourceIndex`, `sourceCoefficient_ne_zero : hodgeCoordinate sourceIndex source ≠ 0` [one genuine algebraic Hodge source with a live coordinate at the ghost weight].
  - `structure PositiveWeightSeparatorSeed G M where`: `prevWeight`, `weight_eq : M.weight = prevWeight + 1`, `sourcePoint : CodimensionPoint V.X prevWeight`, `source_live`, `successor_exact : Order.coheight (ambientSuccessorPoint V sourcePoint.1 (relativeHeightOneSeparatorSuccessor V sourcePoint.1 source_live)) = prevWeight + 1` [the L1-min catenarity premise again], `degreeTrace : ProjectiveDegreeTraceSemantics V H` [L3-a again].
  Plus premise `HasNativePointLifts (ambientTwoStepLefschetz S.sourceIndex M.sheet)` [bare L² point-lift].
- main content: `ambientTwoStepLefschetz_on_hodge_coordinate` (bare L² = nonzero scalar × matrix unit on the i-coordinate); `atomicStable_of_nativePointLifts`; THE extinction theorem `minimalGhost_false_of_localSeed_bareLefschetz` (one bare GST L² motion kills the minimal ghost — False); `PositiveWeightSeparatorSeed.localSeed` (separator-successor packet constructs the local seed); `bigradedBettiHodge_of_localSeeds_bareLefschetz` (global criterion in smallest local form). `#print axioms` receipts at end.
- name-vs-content: accurate: the extinction theorem is genuinely proved — from its premises.
- gaps: local-seed supply, successor exactness (catenarity), degree trace, and point-lifts are all unproven; this file is the conditional engine room of the bare-Lefschetz route.

### GSTClassicalHodgeFullLimitlessExternalization.lean (241 lines)
- decls: 7 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: `def AtomCosmicExternalization G i j K : ∀ alpha : ClassicalHodgeFiber V H p, (projectiveCorrespondencePair G K).cohomologyOperator alpha.1 = canonicalCosmicAmbient i j alpha.1` [the single commuting-square equation: a genuine projective correspondence's cohomology action equals the canonical cosmic matrix unit on the whole fiber — UNPROVEN]; plus spine `G`, per-pair kernels `K : ∀ i j, ProjectiveNativeKernel V p`, and an `AlgebraicFiber` seed premise.
- main content: unconditional tensor-word identities (`cosmicNativeTensorWord_nativeFace/hodgeFace/commutation`); externalization is invariant under finite-world recoordination; conditional crowns `canonicalCosmicNaturality_of_fullLimitlessExternalization`, `hodgeWeight_of_fullLimitlessExternalization`, `full_limitless_externalization_crown`.
- name-vs-content: "full externalization" is the conditional crown; the equation itself is the displayed input.
- gaps: `AtomCosmicExternalization` per ordered basis pair is exactly the missing comparison law (geometric correspondence = GST cosmic matrix unit); nothing constructs it.

### GSTClassicalHodgeGroundFloorSiegePropagation.lean (233 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: no local records; premises: `ProjectivelyLiveSource`, `ProjectiveDegreeTraceSemantics V H` (L3-a, imported), `HasNativePointLifts (ambientTwoStepLefschetz ...)` (bare L² point-lift), `GeometryFirstTwoGenerator` supplies at weight 1; instance `[IrreducibleSpace V.X]`.
- main content: GENUINELY discharges the L1 exact-stratum premise at codimension zero: `separatorSuccessorAmbientExact_of_ground` / `separatorSuccessorAmbientCoheight_one_of_ground` (canonical separator successor has ambient coheight exactly one); `groundSeparatorSuccessor_cycleClass_ne_zero` (degree trace detects nonzero Betti class); `hodge_weight_one_of_groundSeparator`; `weightOnePositiveWeightSeparatorSeed` constructs the positive-weight packet with NO successor_exact witness; `minimalGhost_false_of_weightOne_groundSiege`.
- name-vs-content: accurate — this layer removes one external geometric premise from the live route (p = 0).
- gaps: only weight ONE is covered; general weights still need catenarity (L1 upper bound) or alternative seeds; degree trace and point lifts remain premises.

### GSTClassicalHodgePointwiseNativeCosmicClosure.lean (228 lines)
- decls: 7 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: `def CosmicNativePointLifts i j : HasNativePointLifts (p := p) (cl := H.cycleClass p) (canonicalCosmicAmbient i j)` i.e. `∀ x : CodimensionPoint X p, ∃ Z : codimensionCycles X p, cl Z = (canonicalCosmicAmbient i j) (cl (codimensionPointCycle X p x))` [every matrix-unit-transformed genuine point class has a native algebraic-cycle representative]; plus per-weight `NativeHodgeOrbitSeed` supply in the bigraded crown.
- main content: `cosmicNativePointLifts_iff`, `cosmic_atomicSpanStable`, `hodgeMatrixUnit_mem_algebraic_of_pointLifts`, `every_basis_algebraic_of_liveSource_pointLifts` (source-to-target point lifts from one nonzero algebraic seed saturate the whole Hodge fiber), `hodge_weight_of_liveSource_pointLifts`, `bigradedBettiHodge_of_liveSource_pointLifts`.
- name-vs-content: accurate: closure = reduction of externalization to generatorwise point lifts — the smallest interface.
- gaps: point-lift existence for cosmic matrix units is unproven (it is a per-point algebraicity statement of Hodge-difficulty); seed supply per populated weight also unproven.

### GSTClassicalHodgeGeometricCycleClassPointRigidity.lean (226 lines)
- decls: 8 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: the cycle-class map is FORCED by point fundamental classes: `cycleClass_ext_points` (agreement on all point cycles ⇒ equality of linear maps), `suppliedCycleClass_eq_geometric`, `cycleClassFromPointGeometry_range_eq_pointSpan`, `suppliedCycleClass_range_eq_pointSpan`, finite-sum forms.
- name-vs-content: accurate (rigidity of the cycle-class map on native cycles); a real, unconditional linear-algebra fact given the point normal form.
- gaps: none in scope; says nothing about which classes ARE in the range (that is the Hodge problem).

### GSTGraphV2HandwrittenExponentialLTE.lean (222 lines)
- decls: 10 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none (index bounds only)
- main content: exact LTE boundary of the handwritten exponential cascade: `4^(3^r) = 1 + 3^(r+1)·lteCoeff`, `lteCoeff % 3 = 1`, scaled-residue laws, cut neutrality (`carry = 0 ∧ digit = 0`) at the defining cut, `pow4_scaled_cut_not_happy`, `uTailEnergy_cut_null_sector`.
- name-vs-content: accurate (LTE arithmetic of the cascade tail).
- gaps: none internal; Graph-V2 support module.

### GSTTheAct.lean (215 lines)
- decls: 13 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: `def the_act : Prop := ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false` [every 4^K from K = 8 on owns a ternary digit 2 — THE ACT, the exact unproven content of the whole Erdős-ternary-2 subprogram]; boundary inputs (from MonolithBoundary): `erdos_even_conjecture_iff_tailF` (PROVEN only in the external monolith), `erdos_ternary_2_conjecture_odd` (odd half).
- main content: the identity architecture: `the_act_iff_hTailF` (act ⟺ tailF input, via the monolith iff), `the_act_of_full_erdos`, `hTailF_of_full_erdos`, `full_erdos_of_the_act`, `the_act_iff_full_erdos`, `act_tailF_full_equivalence` (triple equivalence), `climb_gives_the_act` (the climb premise carries strictly more than the act), and the front law `digit3 (4^(3^v·a)) (v+1) = a % 3` with classifier crown.
- name-vs-content: honest: "the exact missing object, named once" — the file proves equivalences, never the act.
- gaps: `the_act`/`hTailF` unproven; equivalences route through monolith boundary objects whose proofs live outside this repo.

### GSTClassicalHodgeFiberedCosmology.lean (211 lines)
- decls: 6 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none ("No algebraic-cycle representative is assumed or constructed here")
- main content: the rank-free coordinate bridge: `fiberedWeightCoordinates_basis`, injectivity, `forgetMultiplicityToGST_single`, `classical_basis_projects_to_gst_diagonal` / `_cosmic_diagonal`, `fibered_limitless_hodge_crown` (injective embedding of classical Hodge fibers into the limitless GST universe, every basis direction projecting to the cosmic diagonal (p,p)).
- name-vs-content: accurate: cosmology = coordinate bookkeeping.
- gaps: none claimed; purely the bridge needed before attacking algebraicity.

### GSTClassicalHodgeSpectralSeparatorCollision.lean (208 lines)
- decls: 4 theorems, 1 structure, 0 axioms, 0 sorry
- hypotheses: `structure RawClassicalHodgeSpectralObservable ... where` — fields: `basisIndex` (injective), `observable` (linear map), `eigenvalue` (injective), `eigenvector : ∀ i, observable (basis i) = eigenvalue i • basis i` [a spectral observable on selected Hodge basis directions — data + eigencondition, deliberately NOT assuming atomic-span preservation]. Theorem premises: `hseed` (cyclic combination inside the point-cycle span), `hstable` (observable preserves the span).
- main content: the collision engine: `separator_forces_observable_instability` (Lagrange calculus isolates the detected sheet ⇒ separator must vanish and not vanish), `no_separator_of_stable_cyclic_seed`, `basisSeparator_forces_not_atomicStable`, `isEmpty_basisAtomicSeparator_of_stable_seed`.
- name-vs-content: accurate: contradiction engine isolated from observables.
- gaps: producing a natural observable (stability on genuine algebraic classes) + a cyclic atomic seed is exactly the remaining attack; not done here.

### GSTClassicalHodgeMinimalPrimitiveSeparatorGhost.lean (202 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none assumed — `structure MinimalPrimitiveGhost G where` (weight, sheet, separator, `minimal : ∀ q < weight, ¬ HasBasisSeparator q`, ghost ≠ 0, `primitive : ∀ q < weight, ∀ P, separator.detector (P.cohomologyEval G alpha.1) = 0`) is a DERIVED obstruction: `minimalPrimitiveGhostOfFailure` constructs one from any failure.
- main content: well-founded descent on the Hodge weight: `exists_separator_weight`, `minimalSeparatorWeight_spec`, `no_separator_below_minimal`, `minimalSeparator_kills_lower_basis_programs`, `minimalSeparator_pullback_basis_zero`, `minimalSeparator_pullback_zero_on_hodge` — every genuine Hodge failure contains a least-weight primitive ghost.
- name-vs-content: accurate: the obstruction is intrinsic and primitive.
- gaps: constructing/killing the minimal ghost is the open problem handled elsewhere (bare-Lefschetz extinction needs its premises).

### GSTSurfaceGraphH1Obstruction.lean (201 lines)
- decls: 4 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: no local records; imported premises: `P : GeometricHigherLefschetzData G 4` [hard-Lefschetz/cup data as a record], `h11 : DivisorsRepresentHodge11 H := ∀ beta : ClassicalHodgeFiber V H 1, ∃ D : codimensionCycles V.X 1, H.cycleClass 1 D = beta.1` [the Lefschetz (1,1) theorem as an explicit hypothesis], plus `hKunnethSeparate`, `hKillsLefschetz` measurement-law premises.
- main content: exact H¹ obstruction for surface automorphism graph cycles: `graph_orbit_primitive_of_two_moment_cancellation` / `_iff_` (primitive iff coefficient sum AND weighted H¹-action annihilated), `primitiveization_preserves_transcendental_measure`, `primitive_graph_orbit_transcendental_rank_certificate`.
- name-vs-content: accurate (obstruction criterion); honest that H¹/Kunneth comparisons are explicit geometric measurement inputs.
- gaps: `DivisorsRepresentHodge11` (classical (1,1) theorem) and `GeometricHigherLefschetzData` are assumed, not proved; graph cycles must still be exhibited for concrete surfaces.

### GSTClassicalHodgeMicroscopicProjectorCriterion.lean (198 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `structure BasisProjectorCertificate V H p i where` — fields: `N`, `slot`, `spectral : RawClassicalHodgeSpectralObservable`, `targets_basis`, `transitions : spectral.PointTransitionKernel` [generatorwise point-transition kernel for the observable — the geometric input], `seedPresentation`, `isolatedCoefficient ≠ 0`, `isolator_seed : linearPolyEval spectral.observable (F.isolatorPolynomial slot) (finitePointCycleClassMap p (H.cycleClass p) seedPresentation) = (isolatedCoefficient * F.isolatorScale slot) • (classicalHodgeBasis V H p i).1` [the Lagrange isolator sends the seed class to a nonzero multiple of the target sheet].
- main content: certificate machinery: `seedCycle_class`, `extractedBasisCycle_spec` (extracted cycle's class IS the basis sheet), `basis_mem_atomicSpan`, `no_basis_separator`, crowns `bigradedBettiHodge_of_basisProjectorCertificates` and `basisProjectorCertificates_construct_basis_cycles`.
- name-vs-content: accurate: per-sheet microscopic certificates ⇒ Hodge.
- gaps: certificates nowhere constructed — the projector equation + transition kernel per sheet are as hard as the target statement.

### GSTClassicalHodgeSupportCardinalityBridge.lean (197 lines)
- decls: 8 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: pure bookkeeping: `HodgeSupportIndex alpha` ≃ `LiveFiberedAddress (fiberedWeightCoordinates ... alpha)` (witness + both directions), `liveRank_eq_fiberedSupportSize`, `liveBasisIndex_fibered`, square-sheet alignment `supportDiagonalWorld_squareSheetOfLiveSlot`, `integralHodgeSquare_squareSheet_ne_zero`.
- name-vs-content: accurate: cardinality/alignment bridge between two index types.
- gaps: none; no Hodge content.

### GSTClassicalHodgeCorrespondenceInvariantGhost.lean (192 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: no local records; premises: `hE : HodgeCompatible E` [realized correspondence preserves the rational (p,p) Hodge fiber] inside the invariance theorem; `hirr : ∀ q, ActualHodgeCorrespondenceIrreducible ...` [the geometric correspondence algebra acts irreducibly on every nonzero Hodge fiber] in the crown.
- main content: `maps_algebraicHodgeSubspace`, `algebraicHodgeSubspace_correspondenceInvariant`, `failure_gives_proper_invariant_ghost` (Hodge failure ⇒ proper Hodge submodule invariant under EVERY Hodge-compatible realized correspondence), `algebraicHodgeSubspace_eq_top_of_actualCorrespondenceIrreducible`, `exactHodge_of_actualCorrespondenceIrreducible`, `finiteCombination_of_actualCorrespondenceIrreducible`.
- name-vs-content: accurate: identifies the rigid invariant-ghost target for the irreducibility artillery.
- gaps: irreducibility of the actual correspondence algebra on Hodge fibers is unproven (it is a strong, likely-false-in-general demand); zero fibers handled, but nothing more.

### GSTGraphV2CMNMCoupledUniverse.lean (191 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry (plus data structures `CoupledNode` = arithmetic × geometry product)
- hypotheses: none
- main content: coupled arithmetic/CM-NM-constructor graph: horizontal/vertical events preserve the geometry component; `coupledEvent_algebraic_stable`; `coupledClosure_sound`; `exact_all_dimension_stage_union` (indexed union of finite stages has EXACT reachability semantics); `geometric_step_at_any_arithmetic_address`; any reachable Hodge node retains a real algebraic-cycle witness.
- name-vs-content: accurate: coupling universe with soundness (no invented connectivity).
- gaps: graph-level completeness (reachability covering all Hodge nodes) is explicitly future work requiring "genuine new geometry".

### GSTClassicalHodgeNativeGeometricPowerOrbit.lean (185 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: no records; premise `hdet : (geometricPowerHodgeMatrix G E).det ≠ 0` [the determinant of the constructed power-orbit cycles is nonzero — explicitly NOT asserted for every variety]
- main content: finite polynomial orbits of actual correspondences: `nativePowerOrbit_succ/_cycleClass`, `nativePolynomialOrbit_cycleClass`, `bettiPolynomialOrbit_has_native_cycle`, `bettiPolynomialOrbit_is_hodge`, and the matrix-inversion landing `actual_power_matrix_native_cycle` (any Hodge class = rational combination of constructed orbit cycles when the determinant is nonzero).
- name-vs-content: honest: "In some varieties this construction may be highly degenerate."
- gaps: determinant nonvanishing is unproven and likely needs projective intersection/motivic geometry; also only one correspondence expression E is used.

### GSTClassicalHodgeLimitlessTowerOrbitCrown.lean (182 lines)
- decls: 5 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `structure ProjectiveTowerHodgeIntertwining where` — fields (exact): `seed : ∀ p : Nat, ClassicalHodgeFiber V H p`, `seed_ne_zero : ∀ p, seed p ≠ 0`, `class_zero : H.cycleClass 0 (projectiveCutTower V 0) = (seed 0).1`, `kernelStable : ∀ p, GradedKernelStable (ProjectiveSuccessor p)`, `successor_formula : ∀ p, gradedAmbientOperator (ProjectiveSuccessor p) (kernelStable p) (seed p).1 = successorScalar p • (seed (p+1)).1` [the universal comparison intertwining the projective successor operator with the limitless Lefschetz action — UNPROVEN].
- main content: `successorScalar_ne_zero`, `successorScalar_eq_cosmic` (successor scalar = coefficient of two cosmic Lefschetz steps), `normalizedTowerCycle_spec`, `bigradedBettiHodge` (crown under the intertwining), `classical_hodge_from_limitless_projective_cosmic_arsenal`.
- name-vs-content: "crown" is conditional on the intertwining record; accurate.
- gaps: the intertwining (nonzero seed family + kernel stability + successor formula at every weight) is a strong unproven package; `GradedKernelStable` likewise imported/unproven.

### GSTLefschetzPoincareReciprocity.lean (181 lines)
- decls: 9 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: exact time-reversal reciprocity in the world model: `worldForward_dual_iff`, distance dual-reversal laws, `lefschetz_kernel_poincare_reciprocity` (K_n(s,t) = K_n(worldDual t, worldDual s)), `nonzero_transition_dual_iff`, `dual_transition_time_exact`, `dual_transition_degree_balance`, `lefschetz_poincare_reciprocity_crown`.
- name-vs-content: accurate: a combinatorial reciprocity identity of the graded world.
- gaps: none internal; no claim about actual varieties.

### GSTClassicalHodgeGeometryFirstNativeWord.lean (176 lines)
- decls: 5 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: no local records; premises: `hZ0 : H.cycleClass p Z0 = (classicalHodgeBasis V H p source).1` [ONE native cycle representative of ONE source basis vector] and `R : ∀ j, GeometryFirstTwoGenerator ...` per target (imported hypothesis structure: the two externalized noncommuting GST primitives as native operators).
- main content: the projector/Lefschetz/Poincare word built directly on native cycles: `cycleClass_nativeSource`, `cycleClass_nativeWord`, `nativeWord_cycleClass_of_source`; `hodge_weight_of_one_source_and_native_words` (one source representative + words ⇒ every basis direction algebraic); `bigradedBettiHodge_of_native_words` (all weights).
- name-vs-content: accurate: native word construction from one source.
- gaps: the single source representative per weight and the `GeometryFirstTwoGenerator` supplies are both unproven geometric inputs.

### GSTClassicalHodgeStrictBettiApexL2Fusion.lean (176 lines)
- decls: 3 theorems, 1 structure, 0 axioms, 0 sorry
- hypotheses: `structure StrictBettiApexL2Fan S where spoke : ∀ j, StrictBettiApexL2Spoke S j` [one strict-relation spoke per target sheet; `StrictBettiApexL2Spoke` imported]; crowns premised on `ExactVerticalCutRayCertificate V q` per live weight (imported: endpoint + exact vertical cut ray) + `ProjectiveDegreeTraceSemantics` + spine.
- main content: `expression_on_apex` (spoke expressions realize the apex-localized L² target), `transferObstruction_apex_eq_zero`, `exactHodge_of_verticalRays_and_strictBettiApexL2Fans` (fusion crown: vertical cut rays + strict Betti apex fans ⇒ exact Hodge).
- name-vs-content: accurate: fusion of the strict-Betti horizontal input with the apex-L² omniverse input.
- gaps: both input families (vertical cut ray certificates, strict Betti apex fans per weight) are unproven; the degree trace is still assumed.

### InformationGeometryScratch.lean (171 lines)
- decls: 8 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none ("No Erdős theorem and no global wave assumption is used here")
- main content: pure arithmetic of the shared GST information integer: low/high coordinate reads (`gst_information_low/high_coordinatesS`), bottom-top coordinate theorem, word bound, gate endpoint, `four_pow_succ_lt_three_pow_doubleS`, bridge bound/null.
- name-vs-content: accurate ("scratch" arithmetic).
- gaps: none; legacy branch file (label #0154/1132), no Hodge content.

### GSTClassicalHodgeRootedStrictRelationTree.lean (167 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `structure RootedStrictRelationTrunkFan S where` — fields: `hub : HodgeBranchNode`, `trunk : StrictRelationRay (rootedFanApex S) hub`, `branch : ∀ j, StrictRelationRay hub (rootedFanTarget S j)` [one shared trunk + short branches; the rays are the unproven geometric input].
- main content: ray concatenation algebra (`nil_comp`, `comp_nil`, `toPath_comp`, `preserves_algebraic_comp`); `hub_algebraic`, `target_algebraic` (algebraicity transported through the shared trunk then fanned out), `hodge_weight`.
- name-vs-content: accurate: reuse of common ray prefixes to reduce duplicated geometric obligations.
- gaps: strict-relation rays themselves are never constructed; the fan/trunk record is pure hypothesis.

### GSTClassicalHodgeCanonicalCutProgramSpine.lean (166 lines)
- decls: 5 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: no local records; premises: `hne : H.cycleClass p (projectiveCutTower V p) != 0` [the concrete vertical nonvanishing statement — reduced elsewhere to spineHodgeSeed ≠ 0], `hstrict : StrictlyMaterializedBranch ...` per target.
- main content: the canonical principal-cut program `cut 0 ; cut 1 ; ... ; cut (p-1)`: `canonicalCutProgram_cycleEval_succ`, `canonicalCutProgram_origin_cycle` (native execution on the fundamental cycle IS projectiveCutTower), `canonicalCutProgram_origin_class` (master naturality square), `canonicalCutProgram_origin_ne_zero_iff`, `native_cycle_of_canonicalCut_strict_branches`.
- name-vs-content: accurate: no free source program remains.
- gaps: the vertical nonvanishing equation and strict branch materialization are the remaining unproven statements (pointed at the limitless tower identification).

### GSTClassicalHodgeSpineRankOneGeometricRealization.lean (160 lines)
- decls: 5 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: premises: `hnz : spineHodgeSeed G p ≠ 0` (or `SpineTowerConservedCharge G`), `hrank : Module.finrank ℚ (ClassicalHodgeFiber V H p) = 1` [rank-one restriction]
- main content: an ACTUAL construction in rank-one fibers: `explicit_spine_native_cycle_of_rank_one` (witness = explicit rational scalar multiple of `spineNativeTower G p`), `every_rank_one_hodge_class_is_native`, `every_rank_one_hodge_class_of_conserved_charge`, `charged_normalized_spine_cycle_spec`, `chargedNormalizedSpineCycle_correct`.
- name-vs-content: honest: "No claim is made here to have established the general rational Hodge conjecture" — rank one only.
- gaps: general ranks need the determinant/irreducibility machinery; nonzero spine seed needs the conserved charge or mass bridge.

### GSTClassicalHodgeFiniteSupportProjectiveSpanOrbit.lean (157 lines)
- decls: 4 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: no local records; premises: `D : ∀ q alpha ≠ 0, FiniteSpineMomentChain G q` (imported hypothesis structure: read functionals with `base_ne_zero` and `successor_read : read (q+1) ((principalCutPair q).cohomologyOperator (spineHodgeSeed q)) = successorScalar q * read q (spineHodgeSeed q)`) and `R : ProjectiveSpanLiveSourceTarget` per support sheet.
- main content: per-class brute-force route: `finiteSupportProjectiveSpanCycle_spec`, `hodgeClass_has_cycle_of_finite_projectiveSpan_support`, `bigradedBettiHodge_of_per_class_finite_projectiveSpan_orbits`, `every_hodge_class_has_native_cycle_of_per_class_projectiveSpan`.
- name-vs-content: accurate: finite-support orbit construction from finite native data.
- gaps: moment chains and span source equations per class are unproven; no whole-weight families are supplied, which is the point, but the per-class burden remains.

### GSTK3DiagonalActualStage2G.lean (153 lines)
- decls: 4 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `structure GenuineK3ProductDiagonalPacket Y H where` — fields: `diagonal/pointLeft/pointRight/hCrossH : codimensionCycles Y.X 2`, `degree ≠ 0`, `lefschetz` (cup map H⁴→H⁶), `leftNearTop/rightNearTop`, four Lefschetz identities (`diagonal_lefschetz : lefschetz (cl diagonal) = 2•(left+right)` etc.), `cycle_is_hodge : ∀ Z, H.cycleClass 2 Z ∈ rationalHodgeSubspace ...` [all algebraic cycles have Hodge type (2,2)], `transversePairing`, `transverseValue ≠ 0`, and four transversality laws (`diagonal_transverse`, left/right/cross = 0) — the whole packet is the unproven geometric input.
- main content: literal native-cycle K3 diagonal primitive: `genuineNativePrimitive` (assembled from the four cycles), `genuineNativePrimitive_lefschetz_zero` (primitive), `_is_hodge`, `_nonzero` (transcendental cup readout), `_outside_divisor_span` (strictly enlarges divisor-word directions).
- name-vs-content: honest: "The scheme product Y=S×S and the four listed cycles/identities still require genuine instantiation in Mathlib."
- gaps: the packet is uninstantiated — no actual K3 surface in Mathlib is wired in; no claim toward arbitrary X.

### GSTClassicalHodgeCanonicalCutSpineNormalization.lean (150 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: the normalization equation: `towerScale_ne_zero`, `successor_spineNativeTower`, `projectiveCutTower_eq_scale_spineNativeTower` (the two towers differ exactly by the product of successor scalars), `projectiveCutTower_cycleClass_eq_scale_spineHodgeSeed`, `projectiveCutTower_class_ne_zero_iff_spineHodgeSeed_ne_zero`, `canonicalCutProgram_origin_ne_zero_iff_spineHodgeSeed_ne_zero`.
- name-vs-content: accurate: bookkeeping normalization, no new assumptions.
- gaps: reduces vertical nonvanishing to `spineHodgeSeed ≠ 0`, which itself needs the conserved charge / mass bridge (unproven).

### GSTClassicalHodgeAlgebraicArsenalSaturation.lean (145 lines)
- decls: 5 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `structure AlgebraicArsenalSeed V H p where` — fields (exact): `seed : ClassicalHodgeFiber V H p`, `seed_ne_zero : seed ≠ 0`, `seed_algebraic : seed ∈ AlgebraicHodgeSubspace V H p`, `orbit_algebraic : ∀ i j : ClassicalHodgeBasisIndex V H p, hodgeMatrixUnit i j seed ∈ AlgebraicHodgeSubspace V H p` [one nonzero algebraic seed whose ENTIRE GST matrix-unit orbit stays algebraic — closure premise].
- main content: `orbitSpan_le_algebraic`, `algebraicHodgeSubspace_eq_top`, `every_hodge_class_has_native_cycle`, `atomicDefect_eq_zero`, `bigradedBettiHodge_of_algebraicArsenalSeeds` (per nontrivial weight).
- name-vs-content: accurate: one seed + orbit closure forces the whole weight.
- gaps: the orbit-closure field is precisely the algebraicity content in disguise (as the non-circularity audit in a sibling file warns); unproven.

### GSTCanonicalPolarizedHodgeGhost.lean (143 lines)
- decls: 4 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: no local records; premises: `hGeometricPairing` (detectors = Q on cycle classes), `hNativeImageSpanned : ∀ Z, ∃ coeff, P.cycleClass Z = ∑ coeff • cycleClass (cycles i)` [finite independent family spans the native algebraic image], `hPositive : ∀ v ≠ 0, 0 < (Q v) v` [positive definite pairing], `hmissing : alpha ∉ LinearMap.range P.cycleClass`.
- main content: canonical ghost construction from actual primitive Hodge-Riemann intersection geometry: `canonicalGhost_annihilates_every_native_generator`, `canonicalGhost_detection_equals_residual_norm` (detection = exact positive polarization residual norm, not arbitrary scalar), `canonicalGhost_annihilates_entire_native_cycleClass_image`, `missing_Hodge_class_produces_positive_canonical_ghost`.
- name-vs-content: accurate: SPECIFIC canonical candidate ghost, contrasted with arbitrary quotient-duality ghosts.
- gaps: `GeometricDualCyclePacket` (the packet with cycles/detectors/pairing compatibility) is imported and its realization for a genuine variety is unproven; span premise unproven.

### GSTClassicalHodgePrincipalSectionNoetherian.lean (140 lines)
- decls: 3 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none ("No Hodge data, cycle-class map, or algebraicity conclusion occurs here")
- main content: genuine geometry: generator-specific principal sections are closed subschemes of the smooth projective carrier ⇒ compact; closed immersion into locally Noetherian ⇒ locally Noetherian; `finite_principalSectionAt_irreducibleComponents` (finitely many irreducible components); `principalSectionAt_support_ne_univ` (proper closed support); `principalSectionAt_strict_cut_crown`.
- name-vs-content: accurate: the Noetherian cutting engine feeding native codimension cycles.
- gaps: none in scope; the recursive cutting engine itself is downstream.

### GSTGeneralSpaceFunctorialRealization.lean (137 lines)
- decls: 4 theorems, 5 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: GST ontology functoriality: `pullback_observe` (charts pull back along GeneralSpace morphisms), `pullback_realize`, `pullback_transport`, `pulledBack_path_naturality`, reversible recoordination functoriality.
- name-vs-content: accurate: ontology-level mechanism, no mathematics beyond type-level naturality.
- gaps: purely foundational; comparison of manifold/graph/scheme/Betti/Hodge sectors is set up but no Hodge content.

### GSTClassicalHodgeSeparatorProjectiveDefectSurvival.lean (134 lines)
- decls: 4 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: local premises: `hcod : Order.coheight (f x.1) = p` [codimension preserved by the self-map], `hdeg : pointResidueWeight f x.1 ≠ 0` [nonzero residue degree]
- main content: rigidity/negative result: `separator_reads_projective_transport_defect`, `separator_detects_projective_transport_defect`, `projective_transport_defect_ne_zero`, `not_defectZero_after_sameSheet_projective_transport` — a microscopic separator defect SURVIVES ordinary same-sheet projective point transport.
- name-vs-content: accurate: survival of the defect under plain transport.
- gaps: by design this shows plain projective transport cannot solve the multiplicity problem — successful geometry must mix Hodge sheets; constructive mixing is elsewhere and open.

### GSTGraphV2CanonicalEscapeProbe.lean (129 lines)
- decls: 1 theorem, 0 defs, 0 axioms, 0 sorry
- hypotheses: none (HappyCell/bad-parent side conditions of the probe)
- main content: single probe theorem `canonical_bad_parent_forces_unbounded_origin_support_probe`: a canonical bad parent forces unbounded origin support (arithmetic escape probe for the Graph-V2 canonical escape).
- name-vs-content: accurate ("probe").
- gaps: standalone arithmetic probe; terminal escape statement not here.

### GSTUniversalHyperplaneAndCMObstruction.lean (127 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none (unconditional kernels)
- main content: `lower_power_nonzero_of_top_power_nonzero` (graded ring: h^d ≠ 0 ⇒ h^p ≠ 0 for all p ≤ d), `all_admissible_hyperplane_powers_nonzero`, `top_hyperplane_power_nonzero_of_positive_degree`, `all_hyperplane_sources_of_top_intersection` (with positive degree functional), and the Riemann-Hurwitz obstruction `no_elliptic_cover_of_hyperbolic_curve` (no nonconstant finite cover from an elliptic curve onto a genus ≥ 2 curve) — killing any universal "CM elliptic power dominates every projective variety" transfer claim.
- name-vs-content: accurate: unconditional algebra kernels + a domination boundary.
- gaps: honest header: these facts do NOT establish the universal Hodge conjecture; CM+NM must produce directions beyond the ample-hyperplane subalgebra — not done.

### GSTClassicalHodgeArsenalNonCircularity.lean (119 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: premise `hseed : AlgebraicHodgeSubspace V H p ≠ ⊥` in the iff theorems
- main content: logical firewall: `rankFreeInvariant_of_eq_top`, `universalTwoSlotInvariant_of_eq_top`, `rankFreeInvariant_iff_eq_top_of_seed`, `universalTwoSlotInvariant_iff_eq_top_of_seed`, `algebraicHodgeSubspace_eq_top_iff`, `arsenal_noncircularity_crown` — invariance under all abstract matrix units is EQUIVALENT to the conclusion (given a nonzero seed), so it must not be assumed but derived from constructed geometric transports.
- name-vs-content: accurate: an audit preventing a coordinate reformulation from masquerading as proof.
- gaps: the audit itself proves no geometry; it constrains what may be assumed downstream.

### GSTResidualZeroLogicalCountermodel.lean (119 lines)
- decls: 5 theorems, 5 defs, 0 axioms, 0 sorry
- hypotheses: none (it CONSTRUCTS a countermodel: V = ℚ², N = ℚ, class z ↦ (z,0), alpha = (0,1))
- main content: exact rational linear-algebra countermodel: `native_projection_zero`, `residual_is_nonzero_second_direction`, `residual_energy_eq_one`, `residual_energy_ne_zero`, and the theorem `existing_dual_projection_axioms_do_not_force_zero_energy` — the existing GST axioms (algebraic projection, positivity, duality/naturality) do NOT force universal residual zero.
- name-vs-content: accurate and important: "NOT a counterexample to the Hodge conjecture" — a countermodel to a claimed logical implication.
- gaps: demonstrates that genuinely new geometric information specific to smooth projective varieties is mandatory; provides none.

### GSTClassicalHodgeCMThetaPeriodExtraction.lean (108 lines)
- decls: 3 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none (combinatorial extraction over any field)
- main content: `nonzero_finite_sum_has_nonzero_term`, `nonzero_mixed_period_has_nonzero_component` (nonzero finite double sum of weighted periods ⇒ ONE pair with nonzero period), `nonzero_period_under_integer_multipliers`.
- name-vs-content: accurate: the finite-family extraction step of the CM theta-period argument.
- gaps: constructing the nonzero analytic mixed period on a projective surface "requires additional geometry; NOT asserted unconditionally"; header says "NEEDS CI RUN LATER".

### GSTResearchFixedZetaGeometricSource.lean (108 lines)
- decls: 2 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: premise `hnorm : FundamentalDegreeNormalization G` [Betti degree-normalization: the fundamental cycle's class measures as 1 — UNPROVABLE from current `HodgeBigradedBettiData` fields, per the zero-cycle countermodel]
- main content: `fixed_zetazero_corrected_scalar` (the corrected indexed zeta equation has exact sum −1 at x=y=2 — proved), `actual_codimension_zero_source_of_degree_normalization` (the fixed scalar −1/2 = ζ(0) is realized by the canonical codimension-zero fundamental cycle with a half-degree readout; nonzero source follows).
- name-vs-content: accurate: a *codimension-zero* construction with a fixed (not free) scalar.
- gaps: the p > 0 geometric source mechanism is explicitly still missing; degree normalization is an input the current data record cannot supply.

### GSTNIntegralCalibrationGap.lean (98 lines)
- decls: 6 theorems, 3 defs, 0 axioms, 0 sorry
- hypotheses: none (finite two-channel integer lattice model)
- main content: the integrality gap made exact: `integral_class_one_exists` (signed integral chain of period 1), `no_nonnegative_integral_carrier_for_period_one`, `every_integral_carrier_has_defect_at_least_four`, `sharp_integral_carrier_defect`, `rational_carrier_is_calibrated` (rational nonnegative calibrated carrier exists), `no_integral_fixed_class_defect_vanishing` (no integer sequence of fixed-class carriers has vanishing defect).
- name-vs-content: accurate: "calibration gap" — rational positivity + integrality ≠ integral almost-calibrated approximants.
- gaps: a finite arithmetical model, not geometry; forbidding this gap for shifted Hodge classes on genuine varieties requires new geometry (not supplied).

### HodgeConjectureBruteforceFinale.lean (96 lines)
- decls: 2 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: no local records; premises: `D : ∀ p alpha ≠ 0, FiniteSpineMomentChain G p` (finite cohomological spine-moment chain from weight 0 to the class's own weight — imported hypothesis structure) and `R : ∀ p alpha i, ProjectiveWordLiveSourceTarget G (topOrbitSeed) i` where the record fields are `word : ProjectiveOperatorWord V p` and `source_action : (word.operatorPair G).cohomologyOperator S.hodge.1 = (repr coefficient) • (basis j).1` [one finite noncommutative word in genuine projective self-transports per live support sheet, sending the live source to the target sheet].
- main content: public landing of the strengthened geometry route: `unified_hodge_bruteforce_finale` (Stage-2G Hodge from spine + moment chains + per-support words), `explicit_hodge_cycle_of_bruteforce_geometry` (the explicit native cycle with the exact requested class).
- name-vs-content: honest finale: it advertises minimal inputs (no all-weight tower, no mass bridge, no cosmic externalization, no two generators per pair) — but the two inputs it keeps are unproven.
- gaps: `FiniteSpineMomentChain` and `ProjectiveWordLiveSourceTarget` per class/sheet are the remaining debt; nothing here constructs them.

### GSTClassicalHodgeRaiseLowerIrreducibility.lean (93 lines)
- decls: 3 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `h : RaiseLowerInvariant S` premise (submodule stable under normalized raise U and exact lower D)
- main content: `fullArsenalInvariant_of_raiseLower` (Π₀ = I − UD preserves S, hence every matrix unit E_ij = U^j Π₀ D^i preserves S), `raiseLowerInvariant_eq_top` (nonzero raise/lower-stable submodule = whole pure-Hodge window), `raise_lower_irreducibility_crown`.
- name-vs-content: accurate: finite-dimensional sl₂-type irreducibility without Poincare reversal as a primitive.
- gaps: realizing U by projective incidence and D by its algebraic transpose on genuine cohomology is the unproven external step.

### MonolithBoundary.lean (86 lines)
- decls: 1 theorem, 4 defs, 0 axioms, 0 sorry
- hypotheses: four NAMED PROPOSITIONS with asserted-but-external proof status (the boundary objects):
  - `erdos_even_conjecture_iff_tailF : (∀ K ≥ 8, noTernaryTwo (4^K) = false) ↔ four_power_omega_shadow_wave_tailF` [monolith §7.15 terminal identity];
  - `erdos_ternary_2_universal_of_tailF : ∀ hTailF n ≥ 9, noTernaryTwo (2^n) = false` [every 2^n from 9 on owns ternary digit 2];
  - `infinite_controller_ternary_two_chokehold` (graph reading of the verdict);
  - `erdos_ternary_2_conjecture_odd : ∀ n ≥ 9 odd, noTernaryTwo (2^n) = false` [odd-exponent half].
  All are `def ... : Prop` taken as EXPLICIT HYPOTHESES downstream (`hB : erdos_even_conjecture_iff_tailF`) — proof status "PROVEN in the source monolith kyo-oo/erdosternary2" is asserted verbally, NOT verified in this repo (authored in a sandbox with no Lean toolchain; comparator CI is the verifier of record).
- main content: the single adapter `erdos_even_conjecture_of_tailF_boundary`.
- name-vs-content: accurate and crucial: this is the declared trust boundary of the campaign.
- gaps: the monolith's 18,500-line campaign is NOT re-carried here; the closing content (`tailF` itself / the act) enters only through these unverified-in-repo boundary propositions.

### GSTNCurrentCalibrationCompatibility.lean (85 lines)
- decls: 3 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none (works on the actual `nativeCycleMass` rational-linear functional)
- main content: PROVED mismatch: `native_linear_mass_nonnegative_implies_zero` (a linear mass nonnegative on all signed cycles must vanish), `nonzero_native_linear_mass_has_negative_signed_cycle`, `nonzero_native_linear_mass_not_globally_nonnegative` — the GST native mass cannot serve as a rectifiable-current mass for calibration bounds.
- name-vs-content: accurate: a compatibility/limitation theorem.
- gaps: geometric mass, integer rectifiability, and class-preserving cycle realization remain absent; the all-variety integral-current goal is untouched.

### GSTCanonicalCarryDynamics.lean (71 lines)
- decls: 5 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none
- main content: exact carry dynamics of the ternary/base-4 cascade: `carry4_lt_four`, `carry4_forward_exact`, `carry4_state_decomposition` (carry + 4·digit decomposition), `carry4Emit_lt_three`, `carry4_transition_packet` (the exact transition recurrence).
- name-vs-content: accurate (dynamics of the carry automaton).
- gaps: none internal; arithmetic support for the Graph-V2 lane.

### GSTGeneralSpaceSchemeStalkFamily.lean (61 lines)
- decls: 3 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none
- main content: scheme stalk family in GST: `schemeStalkFamily_fiber` (stalk at each point), `schemeStalk_dimension_eq_coheight` (Krull dimension observed on the stalk fiber), `every_scheme_has_stalk_family`.
- name-vs-content: accurate: the local algebra layer for the principal-cut frontier.
- gaps: none in scope; observation of dimension only, no Hodge content.

### ComparatorSmokeSolution.lean (19 lines)
- decls: 1 theorem, 0 defs, 0 axioms, 0 sorry
- hypotheses: none
- main content: `comparator_smoke : (1 : Nat) = 1` (rfl) — a CI comparator smoke test.
- name-vs-content: accurate: infrastructure smoke test, no mathematics.
- gaps: none.

---

## BATCH SUMMARY

**Totals**: 72 files, 19,376 LOC; 690 theorems, 0 lemmas, 126 defs, 26 structure/class declarations, 410 `#print axioms` receipts, **0 `sorry`, 0 Lean `axiom` commands, 0 `opaque`**. Every unproven mathematical input is carried as hypothesis-records / premise-Prop-defs / explicit theorem premises — the corpus is deliberately CI-clean, which makes the *named* hypotheses below the entire load-bearing surface.

### Unproven-assumption inventory (the "ForAllN idiom" census of this batch)

**A. Hypothesis-records and premise-defs DEFINED in batch-6 files** (fields quoted in the per-file sections):

Hodge-geometric supply (the true load-bearing family):
1. `NativeFiniteGraphGenerator` (BranchPacketPlaneRealization) — cycle-class naturality under finite-graph strict carriers + Hodge stability of pullback.
2. `FiniteHorizonNativeMassBridge` (NativeMassBridgeAudit) — kernel_mass_zero / base_mass_ne_zero / successor_point_mass (= exactly two exact successors per point below a horizon).
3. `SheetSiegeCoheightAdditivity` + `SheetSiegeCoheightUpperBound` (L1, catenarity) and `SheetSiegeSeparatorSuccessorExact` (L1-min) (SheetSiegeRoute).
4. `SheetSiegeLiveWeightSeeds` (L2 — REFUTABLE as stated) and `SheetSiegeLiveWeightSeedsGuarded` (L2 canonical) (SheetSiegeRoute).
5. `SheetSiegeDegreeTraceConstructed` ≡ `SheetSiegePointDegreeFunctional` (L3-a: a rational functional on each H^{2q} strictly positive on every codimension-q point class) (SheetSiegeRoute).
6. `LocalizedL2PrimitiveRealization` / `SourcewiseLocalizedL2PrimitiveRealization` / `ApexLocalizedL2Realization` (OmniverseLefschetzRayCompiler) — realized correspondences realizing the bare two-slot L² operator.
7. `MinimalGhostLocalSeed` + `PositiveWeightSeparatorSeed` (LocalSeedBareLefschetzExtinction) — one algebraic source + live coordinate; successor exactness + degree trace.
8. `StrictBettiApexL2Fan` (StrictBettiApexL2Fusion) — strict-relation spokes per target sheet.
9. `RootedStrictRelationTrunkFan` (RootedStrictRelationTree) — shared trunk + branch rays.
10. `ProjectiveTowerHodgeIntertwining` (LimitlessTowerOrbitCrown) — nonzero seed family + kernel stability + successor intertwining formula.
11. `AlgebraicArsenalSeed` (AlgebraicArsenalSaturation) — nonzero algebraic seed with fully algebraic matrix-unit orbit.
12. `BasisProjectorCertificate` (MicroscopicProjectorCriterion) — spectral observable + point-transition kernel + nonzero Lagrange-isolator equation.
13. `ProjectiveSpanLiveSourceTarget` (ProjectiveSpanWordSaturation) — one projective correspondence with the native source-class equation per target sheet.
14. `UniverseIndexedRealization` (HodgeConjecture) — repackaged Hodge statement as a realization record.
15. `AtomCosmicExternalization` (FullLimitlessExternalization) — projective correspondence action = cosmic matrix unit on the whole fiber.
16. `CosmicNativePointLifts` (PointwiseNativeCosmicClosure) — generatorwise algebraicity of matrix-unit images of point classes.
17. `GenuineK3ProductDiagonalPacket` (K3DiagonalActualStage2G) — the four K3-product cycles + Lefschetz/transversality identities + `cycle_is_hodge`.
18. `PrimitiveCurrentNumerics` (ExternalProductCurrentSurgery) — mass/period calibration envelope (used to prove defect rigidity, not Hodge).
19. `FundamentalDegreeNormalization` premise (ResearchFixedZetaGeometricSource) — Betti degree normalization, underivable from current data records.

Erdős-ternary / Worldtrace subprogram:
20. `the_act : ∀ K ≥ 8, noTernaryTwo (4^K) = false` (GSTTheAct) — THE unproven kernel of the whole Graph-V2/Worldtrace lane.
21. MonolithBoundary boundary objects (4): `erdos_even_conjecture_iff_tailF`, `erdos_ternary_2_universal_of_tailF`, `infinite_controller_ternary_two_chokehold`, `erdos_ternary_2_conjecture_odd` — "PROVEN in the external monolith" by assertion only; consumed as explicit hypotheses; NOT verified in this repo.
22. `GhostRay` (GhostRayExclusion) — defined object of study; the exclusion needs the external Mahler 3-adic transcendence input (lives outside the batch).

**B. Imported load-bearing premises used pervasively but defined in other batches** (name + role): `GeometricCycleClassSpine V H` (the base semantic premise, with in-repo countermodel `zeroCycleClassSpine`), `GhostWeightNativeSeedSurvival`, `GhostSeedTargetStrictClosure` = `GSTBranchPacketPlaneRealization` (the UNPROVEN law, `rfl`-equal), `NativeMassCycleClassBridge` (global two-successor mass law — refuted by terminal cuts), `SpineTowerConservedCharge`, `ProjectiveDegreeTraceSemantics` (= L3-a), `NativePointSuccessorNonvanishing` (tower law, refutable on finite-dimensional worlds), `HasNativePointLifts` (generatorwise algebraicity of transformed point classes — the bare-L² point-lift law), `GradedGeometricOrbitModuleCyclic`, `OmniversalNativeOrbitPairingTotal`, `StrictlyMaterializedBranch`, `FiniteSpineMomentChain`, `ProjectiveWordLiveSourceTarget`, `ExactVerticalCutRayCertificate`, `GeometryFirstTwoGenerator`, `RootedStrictRelationFan`, `StrictRelationRay/StrictRelationEdgePacket`, `DivisorsRepresentHodge11` (Lefschetz (1,1) as a premise), `GeometricHigherLefschetzData`, `HodgeCompatible`, `ActualHodgeCorrespondenceIrreducible`, `NativeExecutableGSTPlaneCompleteness`, `Stage2GHodgeFiniteness`, and the ~15 `Universal*Generation` supply structures consumed by HodgeConjecture.lean.

**C. Derived (NOT assumed) obstruction records** — constructed from failure, the honest duals of the hypotheses: `OmniversalSeparatorGhost`, `MinimalPrimitiveGhost` (+ `minimalPrimitiveGhostOfFailure`).

### Five most load-bearing files
1. **GSTClassicalHodgeBranchPacketPlaneRealization.lean** (1863 LOC, 53 thms) — the V3 audit of the central unproven law `GSTBranchPacketPlaneRealization` (= target strict closure); fixes the exact split: diagonal fragment = theorem, off-diagonal fragment = exactly the missing Hodge content; packages the crown, the necessity firewall and the zero-cycle boundary.
2. **HodgeConjecture.lean** (1177 LOC, 40 thms) — the public landing face; fixes the DEFINITION of the target (`ClassicalHodgeTarget` = Stage-2G statement) and routes ~20 conditional supply structures into it; also proves the independence countermodel (spine laws alone cannot establish the target).
3. **GSTClassicalHodgeSheetSiegeRoute.lean** (574 LOC) — the priced attack plan: L1 catenarity, L2 guarded seeds (with refutability firewall), L3-a positivity core, each reduced to an exactly-named residue with kill-switches; the front door `hodge_of_geometricPlaneCompleteness`.
4. **GSTTheAct.lean + MonolithBoundary.lean** (215 + 86 LOC) — the Erdős-ternary-2/Worldtrace terminal identity stack: `the_act` named as the exact missing object, triple-equivalenced to the monolith boundary objects whose proofs are external-by-assertion; this is where the campaign's "closing string" is either real or not.
5. **GSTClassicalHodgeLocalSeedBareLefschetzExtinction.lean + GSTClassicalHodgeGroundFloorSiegePropagation.lean** (242 + 233 LOC) — the bare-Lefschetz extinction engine: one bare L² motion kills the minimal ghost, given local seeds + point lifts; the ground-floor file genuinely discharges successor exactness at codimension 0 — the only place in the batch where a previously external geometric premise is actually removed.

### The single biggest gap
The Hodge content itself is nowhere constructed: every "Hodge-proving" theorem in the batch is conditional, and the conjunction of missing inputs collapses to two irreducible cores — (i) on the geometry side, generatorwise algebraicity of transformed point classes (`HasNativePointLifts` / `CosmicNativePointLifts` / `AtomCosmicExternalization` — each an instance of "algebraic cycles are closed under the relevant correspondence operators", exactly Hodge-level difficulty, plus the L3-a positive degree functional whose construction inputs (cup product, integration over the fundamental class, hyperplane class, point-degree positivity) do not exist in the repo or pinned Mathlib), and (ii) on the arithmetic side, `the_act`/`tailF` — the even-exponent Erdős ternary digit-two statement — whose only route into the repo runs through MonolithBoundary objects verified nowhere in this repository. The corpus's own zero-cycle countermodels prove that no combination of its present unconditional content can close either core.
