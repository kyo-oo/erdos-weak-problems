# Lean batch 5 map (task 1-f)

Repo: /tmp/hc-clone-23 @ 6c20bb7, branch research/gpt6-native-point-primitive-span-20261017.
Batch: 70 files, 19,364 LOC, 852 theorems + 50 lemmas, 218 defs, 26 real `structure` declarations, 390 `#print axioms` receipts.
**Zero `axiom`, zero `opaque`, zero `sorry` in the whole batch** (the only textual "sorry"/"axiom" hits are comments saying "no sorry / no custom axioms"). All unproven content enters as (a) named `Prop` defs consumed as theorem hypotheses (Erdos track), or (b) hypothesis-records: `structure ... where` fields that are unproven mathematical propositions (Hodge track). The batch is therefore "clean by construction": it never assumes sorry-style cheating, it packages exactly the missing geometry as explicit interface records.

Legend for "hypotheses": verbatim quoted fields of hypothesis-records (the load-bearing unproven assumptions).

---

### GSTTailFFourthDimension.lean (2416 lines)
- decls: 141 theorems, 12 defs, 0 axioms, 0 sorry (75 `#print axioms`)
- hypotheses: two named `Prop` defs consumed as hypotheses (the "two named primitives"):
  - `def tailF_row_primitive : Prop := forall core : Nat, 500 < core -> ~ 3 | core -> (core % 9 = 1 \/ core % 9 = 4) -> exists j : Nat, 2 * 3^j <= (omegaCutWord 0 core) % 3^(j+1)` — the sheet-zero family's whole carried content (row word of every 3-free class-one core fires its top third at some depth).
  - `def tailF_tower_primitive : Prop := forall s core : Nat, 1 <= s -> ~ 3 | core -> (core % 9 = 4 \/ core % 9 = 7) -> (forall k, 3 <= k -> k <= s+1 -> (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1)) -> exists i, s+2 <= i /\ 2 * 3^i <= (omegaCutWord s core) % 3^(i+1)` — deep-tail firing of every diagonal-dodging tower.
  - plus imported boundary inputs taken as theorem hypotheses: `erdos_even_conjecture_iff_tailF`, `erdos_ternary_2_universal_of_tailF` (comment: proven in external repo kyo-oo/erdosternary2 section 7.15).
- main content: unconditional 3-adic machinery for the Erdos ternary-digit problem for powers of 4: extended observation law (`tower_observation_digit_two` — every tower digit at every depth reads off the cut word), cube-lift stabilization, descent blade (`omega_tower_kill_of_diagonal_two` — ONE primitive diagonal trit two kills the tower dodge at every sheet level), diagonal ignition bands as exact residue tests at mod 9/27/81/243/729/2187/6561 (dozens of `four_pow_*_mod*` constants by decide/norm_num), the decomposition theorem `tailF_of_row_and_tower` (the two primitives compose to the full `four_power_omega_shadow_wave_tailF` input), and band-death theorems.
- name-vs-content: "Fourth dimension" is theatre; actual content is honest, fully proven 3-adic digit arithmetic for 4^(3^s*core) — but the two named primitives (the actual conjectural content) are hypotheses.
- gaps: row/tower primitives unproven; the file openly states "stated as `def`s, consumed as hypotheses, disclosed at every surface"; ignition bands only cover finitely many residue classes per modulus (243->729->2187->6561 ladder never terminates — see GSTTailFInfiniteRead).

### fsb.lean (1138 lines)
- decls: 96 theorems, 50 lemmas, 0 defs, 0 axioms, 0 sorry (0 `#print axioms`)
- hypotheses: none.
- main content: verbatim vendored copy of Mathlib's `Mathlib.Algebra.BigOperators.Group.Finset` (Johannes Hoelzl header, `module`/`public import` Lean module-system syntax): products over `Finset` — prod_cons, prod_insert, prod_union, prod_biUnion, fiberwise products, Multiset/List product interchange.
- name-vs-content: no gap and no custom content — pure Mathlib vendoring (probably a module-system experiment).
- gaps: none; contributes zero original mathematics.

### GSTCubicFourfoldPlanePrimitive.lean (811 lines)
- decls: 43 theorems, 22 defs, 0 axioms, 0 sorry (10 `#print axioms`)
- hypotheses: none (no records); all statements unconditional.
- main content: exact Z/Q lattice arithmetic for the rank-two algebraic plane lattice of a cubic fourfold containing a plane: Gram matrix [[3,1],[1,3]], primitive cycle 3[P]-h^2 with self-intersection 24, discriminant 8, divisibility/integrality laws; generalized to degree-d hypersurfaces with maximal planes, an explicit two-plane cubic F(x,y)=sum(x^2 y + x y^2) with Jacobian nonsingularity proven as polynomial algebra, and the Fermat d-root-plane family with Gram-detector kernel triviality (`fermatPrimitiveGramDetector_kernel_trivial`).
- name-vs-content: "genuinely geometric codimension-two primitive" — only the intersection *numbers* and polynomial Jacobian algebra are verified; no schemes, no cohomology, no cycle-class map appear.
- gaps: the passage "to actual projective smoothness, subvariety cohomology classes and canonical cycleClass uses the corresponding projective geometric constructions" — i.e., the actual geometry linking these numbers to Hodge classes of a real cubic fourfold is not in this file.

### GSTCMFiniteGeometricDegreeDescent.lean (630 lines)
- decls: 17 theorems, 5 defs, 4 structures, 0 axioms, 0 sorry (10 `#print axioms`)
- hypotheses (hypothesis-records; the load-bearing unproven assumptions):
  - `CMNativeProductRealization`: genuine Chow product on the source + rational Betti product + soundness fields `nativeUnit_sound : H.cycleClass 0 nativeUnit = bettiUnit`, `nativeDivisor_sound : forall i j, H.cycleClass 1 (nativeDivisor i j) = bettiDivisor i j`, `bettiDivisor_hodge : forall i j, bettiDivisor i j in rationalHodgeSubspace (H.hodgeBigrading 1)` (plus multiplication laws) — an actual algebraic-cycle ring matching Betti classes.
  - `CMActualHodgeCharacterExpansion`: `expansion : forall alpha in rationalHodgeSubspace (H.hodgeBigrading p) -> exists coeff : iota -> Q, (sum i, coeff i * cmBettiDivisorWord F p (word i).paired) = alpha` — **every rational Hodge class expands in balanced CM character words** (the CM-theory input; unproven).
  - `CMGeometricFieldCharacterExpansion`: the same expansion over an algebra Q K, with basis-repr coefficient comparison (algebraMap Q K ((b.repr alpha) j) = sum i, coeff i * ...).
  - imported records used as hypotheses: `CrossCarrierTransfer A X HA HX p p` (per-weight), `BigradedBettiHodgeStatement A HA` (source algebraicity).
- main content: the degree-split descent mechanism is genuinely proven: `hodge_at_weight_of_geometric_degree_split` (finite dominant f with f_* f^* = d*id, source Hodge-algebraic => target Hodge-algebraic, via alpha -> f^*alpha -> source cycle C -> d^-1 f_* C); combinatorial proof that torus invariant monomials factor into quadratic weight-zero generators; native divisor-word cycle-class computation `cm_native_word_cycleClass`; assembly `hodge_on_target_of_cm_character_products_and_geometric_degree`.
- name-vs-content: "universal transfer" in the header overstates: the file itself warns "DO NOT MISREAD: this theorem does not manufacture f : A -> X for an arbitrary X... there are projective varieties not dominated by abelian varieties."
- gaps: existence of the CM character expansions and of the generically finite source->target morphism are exactly the unproven inputs; the source `BigradedBettiHodgeStatement` is itself the Hodge conjecture for the CM source.

### GSTClassicalHodgeCoherentNativeDescent.lean (568 lines)
- decls: 24 theorems, 6 defs, 0 axioms, 0 sorry (14 `#print axioms`)
- hypotheses: none (pure module theory).
- main content: real linear algebra of the labelled ("fibered") cycle universe: native kernel generation by sheet differences (`nativeKernel_eq_sheetDifferenceSpan`), descent classification (`native_descent_iff_constant_columns` — an operator descends iff its native columns are constant), unrestricted routing law (`routedNativeOperator_descends`), all-coherent-lifts normal form, two-obstruction law for cycle-class descent (`cycleClass_descent_iff`), finite tensor-block column-sum law (`finiteTensorBlock_descends_iff`).
- name-vs-content: name says "Hodge descent"; content is honest bookkeeping algebra of the GST label scaffolding (FiberedNativeAddress over codimensionCycles), no Hodge geometry.
- gaps: none internally; it clarifies (rather than closes) the gap between labelled GST operators and genuine cycle classes.

### GSTHodgeAssault.lean (499 lines)
- decls: 19 theorems, 4 defs, 0 axioms, 0 sorry (19 `#print axioms`)
- hypotheses: none.
- main content: the "Hodge conjecture" proven in the absorbed twelve-cell wave world: `hodge_conjecture (p < 3) (f : WaveCoef) (hf : isHodgeClass p f) : exists z : Z, forall c, f c = z * cycleClass p c`, rank-one classification, torsion-free law, pure-sector decomposition, separation law, all bundled in `the_hodge_assault`. Includes the honest alias `finite_gst_hodge_classification` ("audit-accurate name... without identifying WaveCoef with the cohomology of an arbitrary external variety").
- name-vs-content: `hodge_conjecture`/`the_hodge_assault` suggest the Clay problem; proven statement is about a 12-cell combinatorial lattice where Hodge classes are rank one by construction.
- gaps: no bridge from the 12-cell wave world to actual varieties (the file itself provides the audit-accurate renaming).

### GSTClassicalHodgeGSTPlaneAxiomStatus.lean (440 lines)
- decls: 16 theorems, 1 def, 0 axioms, 0 sorry (15 `#print axioms`)
- hypotheses: none as records; crown theorems take `GhostWeightNativeSeedSurvival G` / `SpineTowerConservedCharge` / `NativeMassCycleClassBridge` as hypotheses (imported hypothesis-props).
- main content: the **axiom-status audit** of the whole GST plane program: (A) intrinsic GST plane completeness is a theorem; (A-/->Hodge) `no_intrinsicGSTPlane_to_hodge_unconditionally` via the zero-cycle-class countermodel; `any_hodge_sufficient_premise_fails_zeroCycleWorld` (any Hodge-sufficient premise must fail in the zero-cycle world); (B/C) common-class plane iff strict relation packet; (D) `targetStrictClosure_iff_noGhost` (minimal target closure iff ghost extinction given source survival); `branch_exists_but_D_packet_empty`; `coherentNativeLayer_misses_ghost_target` (native coherence alone cannot supply D); source survival from conserved charge / native mass bridge; master crown `gstPlane_axiom_status_crown`.
- name-vs-content: none — this is precisely an honest ledger: "It does not relabel the Hodge target as a theorem."
- gaps: the two genuinely geometric bridges (conserved charge / mass bridge; ghost-eliminating D closure) are exactly the unproven content, and the file proves they cannot be intrinsic.

### GSTClassicalHodgeFiberedNativeOperatorLift.lean (409 lines)
- decls: 21 theorems, 0 defs, 0 axioms, 0 sorry (8 `#print axioms`)
- hypotheses: none.
- main content: canonical lift of native operators to the labelled pullback universe: strict commuting square `toNativeCycle o lift(A) = A o toNativeCycle`, composition/additivity/injectivity laws, single-sheet intertwining, fibered crown.
- name-vs-content: matches content (operator-lift algebra).
- gaps: none internal; pure GST scaffolding algebra.

### GSTTailFInfiniteRead.lean (397 lines)
- decls: 11 theorems, 1 def, 0 axioms, 0 sorry (10 `#print axioms`)
- hypotheses: `erdos_even_conjecture_iff_tailF` (imported boundary input) for the final iff.
- main content: the **negative result** closing the Erdos tailF route at the finite level: child anatomy of the survivor dust, the split (one of three children always fires, one always survives), **dust immortality** `dust_immortal : forall m >= 3, exists c > 0, DustAt m c` (the Cantor dust never empties at any finite level), blade composition, and `the_infinite_read` bundling: dust immortal + blade eats one of three + survivors branch + non-dust towers die + tailF iff even-exponent statement.
- name-vs-content: matches; "the infinite read" is exactly the obstruction read.
- gaps: proves that no finite assembly of level receipts (729, 2187, 6561, ...) can exhaust the dust — the row/tower primitives of GSTTailFFourthDimension cannot be proven by finite level checks.

### GSTClassicalHodgeGeometryFirstTwoGenerator.lean (373 lines)
- decls: 12 theorems, 0 defs, 2 structures, 0 axioms, 0 sorry (6 `#print axioms`)
- hypotheses (records):
  - `NativeHodgePrimitive (T : Module.End Q (HodgeFiber V H p))`: `cycleOperator : NativeCycles V p ->_l[Q] NativeCycles V p`, `cohomologyOperator`, `cycleClass_natural : forall Z, H.cycleClass p (cycleOperator Z) = cohomologyOperator (H.cycleClass p Z)`, `restricts_to_hodge : forall alpha, cohomologyOperator alpha.1 = (T alpha).1` — a genuine native cycle operator realizing a prescribed Hodge-fiber operator T.
  - `GeometryFirstTwoGenerator (i j)`: `code : NativeHodgePrimitive (twoSlotCodeHodge i j)` and `lefschetz : NativeHodgePrimitive (twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2))` — the two primitives (two-slot code observable + two-step Lefschetz) realized geometrically.
- main content: geometry-first externalization: kernel-stable native operators automatically have native point lifts; the two primitives generate the whole normalized two-slot word; crowns `rankFreeArsenalInvariant_of_geometryFirstTwoGenerators` and `algebraicHodgeSubspace_eq_top_of_geometryFirstTwoGenerators` (with `R : forall i j, GeometryFirstTwoGenerator i j` as hypothesis).
- name-vs-content: "geometry-first two-generator externalization" is accurate; the geometric realization itself is the hypothesis.
- gaps: existence of `GeometryFirstTwoGenerator` for actual varieties is the unproven geometric core (two native operators restricting to the code/Lefschetz primitives on the (p,p) fiber).

### GSTClassicalHodgePlaneCompletenessTheorem.lean (368 lines)
- decls: 18 theorems, 0 defs, 0 axioms, 0 sorry (9 `#print axioms`)
- hypotheses: none for the unconditional part; ghost-package parts are equivalences with `GhostSeedTargetStrictClosure` / `GhostWeightNativeSeedSurvival` (imported props).
- main content: unconditional intrinsic GST plane completeness (`gst_plane_completeness`, `intrinsic_gst_plane_completeness`: one live source fires to every target sheet in every sector, exact finite rational collapse); **circularity certificates**: `ghostAdaptiveCommonClassPlanes_iff_hodge`, `survival_and_strictClosure_iff_hodge`, `survival_and_commonClassClosure_iff_hodge`, `ghost_plane_circularity_crown` (ghost-indexed plane axioms are consequence-normal forms of the Hodge target itself, "forbidden as foundational assumptions in a noncircular route"); `bareStage2G_cannot_be_unconditional_geometric_landing`; separation crown `gstPlane_complete_but_bareStage2G_not_geometrically_complete`.
- name-vs-content: none — file explicitly separates the provable intrinsic statement from the circular geometric package.
- gaps: the geometric (ghost-extinguishing) plane package is equivalent to the target — so nothing short of the Hodge content itself can supply it.

### GSTGraphV2CanonicalInfiniteCycle.lean (343 lines)
- decls: 14 theorems, 2 defs, 0 axioms, 0 sorry (8 `#print axioms`)
- hypotheses: none.
- main content: periodicity laws of the coupled Graph-V2 controller orbit attached to the canonical perfect-power block: `coupledOrbit_cycle_all_turns`, pairwise/multiple cycle laws, `IsCoupledPeriod` additive monoid structure, `coupled_period_additive_crown`.
- name-vs-content: matches (graph-orbit algebra).
- gaps: internal to the Graph-V2 arithmetic engine; no direct Hodge content.

### GSTFourPowerDirectResidue.lean (332 lines)
- decls: 15 theorems, 2 defs, 0 axioms, 0 sorry (10 `#print axioms`)
- hypotheses: none.
- main content: self-contained Erdos-engine kernel: `digit3`, exact LTE identity `pow4_three_power_lte_exact : 4^(3^r) = 1 + 3^(r+1) * lteCoeff r` (recursive coefficient), `lteCoeff_mod3_one`, digit periodicity `pow4_digit_period`, exponent-trit lifts, and the mod-9 row-two overlap classification (`row_two_overlap_iff_mod9_five_or_six`, `no_common_two_forbids_mod9_five_six`).
- name-vs-content: matches.
- gaps: pure unconditional arithmetic; the conjectural step lives in the dependent TailF files.

### GSTWorldPoincareDuality.lean (325 lines)
- decls: 18 theorems, 7 defs, 0 axioms, 0 sorry (8 `#print axioms`)
- hypotheses: none.
- main content: dimension-free Poincare duality for the A x B GST world lattice: complement involution `(C,d) -> (A-1-C, B-1-d)`, degree duality, sector nondegeneracy, integrally perfect anti-diagonal top pairing, `world_poincare_duality_crown`.
- name-vs-content: honest ("GST world", i.e., the combinatorial lattice, not varieties).
- gaps: none internal; it is the combinatorial shadow of Poincare duality used by the arsenal machinery.

### GSTClassicalHodgeFullArsenalIrreducibility.lean (315 lines)
- decls: 17 theorems, 5 defs, 0 axioms, 0 sorry (4 `#print axioms`)
- hypotheses: none (works on the GST world/finite-window model).
- main content: finite-window arsenal irreducibility: sheet projectors + universal Lefschetz kernel (central binomial scalars) + Poincare mirror generate every matrix unit; `fullArsenalInvariant_eq_top` (a nonzero invariant submodule is everything), `every_basis_from_nonzero_seed`, `full_arsenal_irreducibility_crown`.
- name-vs-content: "full arsenal" is the GST operator algebra — statement is about the combinatorial/window model, not the genuine Hodge fiber.
- gaps: the intertwining of this arsenal with genuine geometry is supplied elsewhere (GeometryFirstTwoGenerator records).

### GSTClassicalHodgeFiniteSpineMomentOrbit.lean (306 lines)
- decls: 7 theorems, 0 defs, 2 structures, 0 axioms, 0 sorry (7 `#print axioms`)
- hypotheses (records):
  - `FiniteSpineMomentChain (G) (top)`: `read : forall q, RationalSingularCohomology ... ->_l[Q] Q`, `base_ne_zero : read 0 (spineHodgeSeed G 0).1 != 0`, `successor_read : forall q < top, read (q+1) ((G.principalCutPair q).cohomologyOperator (spineHodgeSeed G q).1) = successorScalar q * read q (spineHodgeSeed G q).1` — a nonzero finite-prefix spine moment chain.
  - `ProjectiveLiveSourceTarget (G) (S) (j)`: `kernel : ProjectiveNativeKernel V p`, `source_action : (projectiveCorrespondencePair G kernel).cohomologyOperator S.hodge.1 = (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex * (classicalHodgeBasis V H p j).1` — one genuine projective-correspondence kernel per target sheet hitting the live source.
- main content: crown `bigradedBettiHodge_of_finite_spine_moments_and_projective_live_source` (finite relevant spine moment + one-source projective orbit => full `BigradedBettiHodgeStatement`); `every_hodge_class_has_native_cycle_of_finite_spine_moments`.
- name-vs-content: accurate description of the conditional interface.
- gaps: the two records are the unproven geometric inputs (nonzero spine mass in the finite prefix; per-target correspondence source action).

### GSTClassicalHodgePiOneSourceCompositionalCorrespondenceFinale.lean (300 lines)
- decls: 9 theorems, 1 def, 1 structure, 0 axioms, 0 sorry (7 `#print axioms`)
- hypotheses (record): `OneSourceCompositionalCorrespondenceRealization (p)`: `seed : NativeHodgeOrbitSeed`, `expression : forall j, RealizedCorrespondenceExpr V H p`, `scalar : ... -> Q`, `scalar_ne_zero`, `source_hit : forall j, (expression j).cohomologyOperator seed.hodge.1 = scalar j * (classicalHodgeBasis V H p j).1` — for each basis sheet one noncommutative correspondence expression hitting the single source by a nonzero scalar.
- main content: `bigradedBettiHodge_of_piOneSourceCompositionalCorrespondences` (record => full Hodge statement), Clay-wording corollary `everyHodgeClassIsFiniteRationalCombination_of_piOneSource...`, N-cohomology packet, unbounded crown.
- name-vs-content: "Finale" is a conditional interface, not a terminal proof.
- gaps: existence of the correspondence expressions with `source_hit` is precisely the geometric content (essentially: enough correspondences to move one source to every Hodge sheet).

### GSTTransferBridgeV2.lean (295 lines)
- decls: 18 theorems, 2 defs, 0 axioms, 0 sorry (7 `#print axioms`)
- hypotheses: none.
- main content: all-weight exact address classification for the twelve-coordinate bridge (`transfer_hodge_iff_all_weights`, `transferred_coefficient_unique`, `transfer_v2_crown`), compact code (pairing p,p) rank-one classification, limitless/cosmic integration crowns.
- name-vs-content: matches; still inside the 12-cell wave world.
- gaps: none internal; the bridge target is the toy lattice, not varieties.

### GSTClassicalHodgeDegreeCertifiedStrictRelationFinale.lean (282 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry (5 `#print axioms`)
- hypotheses (imported records/props as theorem hyps): `GeometricCycleClassSpine G`, `ProjectiveDegreeTraceSemantics D`, live/exact successor conditions, and per-target-sheet packages `SchemeBiFiniteClosedCorrespondence K j`, `RightFiniteBettiTrace T j`, `PointCycleCompatibility C j`, and the raw geometric relation `hrel : BettiRelated ... l^*(source) = r^*(sourceScalar * targetBasis)`.
- main content: trace-based strict-relation reduction: nonzero right Betti trace makes r^* injective, related targets unique; `hodge_weight_of_degreeCertifiedStrictRelations` (strict relations => cycle-class range contains Hodge subspace at weight q+1); `everyHodgeClass_weightSucc_of_degreeCertifiedStrictRelations`.
- name-vs-content: "Finale" = conditional reduction removing the source-action equation; still needs the strict relations supplied.
- gaps: the `BettiRelated` relations (actual pullback equations of real correspondences) are the unproven geometric input.

### GSTClassicalHodgeFiniteClosedCorrespondence.lean (277 lines)
- decls: 9 theorems, 2 defs, 1 structure, 0 axioms, 0 sorry (3 `#print axioms`)
- hypotheses (record): `FiniteClosedCorrespondence (V)`: `carrier : Scheme`, `intoProduct : carrier -> selfProduct V`, `closedImmersion : IsClosedImmersion intoProduct`, `leftFiber_finite : forall x : V.X, ({z : carrier | (intoProduct >> fst V) z = x} : Set carrier).Finite` — a genuine scheme correspondence (constructible data, not itself an unproven proposition). The unproven interface is `RealizesCosmicOnPoints` (defined here as a predicate).
- main content: first correspondence-valued point transport: finite left-fiber enumeration, right-projection residue-degree weighting (graph-compatible pushforward convention), `targetAtomPresentation`, `cosmicNativePointLifts`, `hodge_weight_of_liveSource_correspondences` (with `RealizesCosmicOnPoints` hypotheses), graph correspondences as special case.
- name-vs-content: matches.
- gaps: left fibers treated set-theoretically with multiplicity one (scheme-theoretic pullback refinement "may replace" it later); `RealizesCosmicOnPoints` is the missing identification with GST matrix units.

### GSTClassicalHodgeStage2GCompactAssembly.lean (274 lines)
- decls: 7 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry (6 `#print axioms`)
- hypotheses (record): `NatHodgeCoordinateChart (V) (H) (p)`: `encode : RationalSingularCohomology ... ->_l[Q] (N ->0 Q)`, `encode_injective : Function.Injective encode`, `hodgeSupport : Set N`, `hodge_supported : forall alpha in rationalHodgeSubspace ... -> forall n in (encode alpha).support, n in hodgeSupport`, `basisIndex`, `basis_address : forall n, encode (classicalHodgeBasis V H p (basisIndex n)).1 = Finsupp.single n.1 1` — an injective finite-support encoding of actual cohomology addressing the classical basis. Plus imported `BasisProjectorCertificate` nonemptiness.
- main content: field-by-field Task-6 assembly: `bigradedBettiHodge_of_natCharts_and_projectors` (charts + projector certificates => full Hodge statement).
- name-vs-content: accurate assembly file; the header itself flags the boundary.
- gaps: "this file does NOT assert that a `NatHodgeCoordinateChart` exists for every arbitrary `HodgeBigradedBettiData`. Producing that actual semantic chart is precisely the remaining Task-4 boundary."

### GSTHodgeChannelRetract.lean (264 lines)
- decls: 9 theorems, 1 def, 1 structure, 0 axioms, 0 sorry (5 `#print axioms`)
- hypotheses (record): `ChannelHodgeRetract (p) ... (hodge : Submodule Q Coh) (cycleClass : CycleQ ->_l[Q] Coh)`: `encode : hodge ->_l[Q] FixedWeightChannelCoordinates shape p`, `decode : ... ->_l[Q] hodge`, `decode_encode : forall alpha : hodge, decode (encode alpha) = alpha` (split retract), `channelCycle : HodgeChannel shape -> CycleQ`, `channelCycle_mem : forall i, cycleClass (channelCycle i) in hodge`, `channelCycle_decodes : forall i, (cycleClass (channelCycle i) : hodge) = decode (channelBasis shape p i)` — every channel basis vector decodes to the class of an actual cycle.
- main content: split-retract materialization: `retractHodgeWitness_eq`, `hodge_class_has_retract_cycle`, `hodge_channel_retract_crown` (retract family per weight => `BigradedBettiHodgeStatement`).
- name-vs-content: accurate; "retract" flexibility honestly described.
- gaps: existence of the retract + decodable channel cycles is the unproven input (equivalent-strength geometric packaging).

### GSTClassicalHodgeProjectivePrincipalSection.lean (258 lines)
- decls: 8 theorems, 1 def, 1 structure, 0 axioms, 0 sorry (5 `#print axioms`)
- hypotheses: none — `PositiveHomogeneousSeparator` is data+proof and is constructed (`positiveHomogeneousSeparator` via `Classical.choice` from `x.not_irrelevant_le`).
- main content: genuine projective scheme geometry: every Proj point admits a positive-degree homogeneous equation nonzero at it; reduced principal closed subschemes; pullback along the projective embedding; support characterizations (`mem_principalSection_support_iff`, `source_not_mem_principalSection`).
- name-vs-content: matches ("no Hodge data and no cycle-class map occur here").
- gaps: none internal; it is a real-geometry utility layer for later cuts.

### GSTClassicalHodgePiOmniverseBranchSynthesis.lean (255 lines)
- decls: 7 theorems, 4 defs, 1 structure, 0 axioms, 0 sorry (5 `#print axioms`)
- hypotheses: `ProjectiveHodgeWorld` is pure data (V, H, weight — no propositions); `PrimitiveBranchCompiler : Prop` is the conditional interface (compiling primitive GST events into the realized correspondence expression algebra).
- main content: interpretation of `Pi` as the dependent universe of projective Hodge worlds; `exprMaterializesBranch_preserves_range`; full omniverse algebraic stability `algebraicBranchNode_semanticallyStable`, `generated_from_algebraic_seeds_is_algebraic`; `pi_omniverse_branch_packet`; de-Rham/Betti synchronization.
- name-vs-content: grandiose naming ("omniverse") for a stability theorem about an expression algebra under generated events.
- gaps: `PrimitiveBranchCompiler` content (real correspondence expressions materializing GST branch events) is the unproven half.

### GSTGeometricRealizationStage2D.lean (250 lines)
- decls: 7 theorems, 2 defs, 1 structure, 0 axioms, 0 sorry (6 `#print axioms`)
- hypotheses (record): `CodimensionHodgeRealization (N p X Coh)`: `hodge : Submodule Q Coh`, `cycleClass : codimensionCycles X p ->_l[Q] Coh`, `encode : Coh ->_l[Q] RatAddress N`, `encode_injective`, `hodgeSupport : Finset (Fin N)`, `hodge_supported : forall alpha in hodge -> SupportedOn hodgeSupport (encode alpha)`, `basisCycle : Fin N -> codimensionCycles X p`, `basisCycle_address : forall i in hodgeSupport, encode (cycleClass (basisCycle i)) = addressBasis i` — the Stage-2D "supplied semantics" record.
- main content: defines the actual native cycle space: `codimensionCycles X p` = rational Mathlib `AlgebraicCycle`s supported on the coheight-p locus (p=1 = Weil divisor support); membership laws; `hodge_class_has_codimension_cycle` (record => per-class native cycle); `universal_codimension_hodge_of_realization_family`.
- name-vs-content: honest; header lists exactly which semantics remain supplied (rational degree-2p cohomology, (p,p) subspace, cycle-class map, smooth-projective eligibility).
- gaps: the four supplied-semantics objects are not constructed from Mathlib; they are the standing interface hypotheses of the whole campaign.

### GSTClassicalHodgeRankFreeArsenalIrreducibility.lean (246 lines)
- decls: 12 theorems, 1 def, 0 axioms, 0 sorry (4 `#print axioms`)
- hypotheses: none (the seed is a hypothesis in the crowns: one nonzero algebraic seed + arsenal invariance).
- main content: rank-free (arbitrary basis cardinality) matrix-unit arsenal irreducibility on the genuine Hodge fiber: `rankFreeArsenalInvariant_eq_top`, `algebraicHodgeSubspace_eq_top_of_seed_and_arsenal`, `atomicDefect_eq_zero_of_seed_and_arsenal`, `bigradedBettiHodge_of_rankFree_arsenal`.
- name-vs-content: accurate; the "limitless colimit" is a clean algebraic statement.
- gaps: needs (i) one nonzero algebraic seed in the (p,p) fiber and (ii) full-arsenal naturality of the algebraic subspace — both geometric, both unproven here.

### GSTClassicalHodgeAmbientCorrespondenceIncidenceNaturality.lean (237 lines)
- decls: 8 theorems, 0 defs, 2 structures, 0 axioms, 0 sorry (2 `#print axioms`)
- hypotheses (records):
  - `PointFiberIntersectionLaw (P) (K) (kappa)`: `fiberIntersectionClass : CodimensionPoint V.X p -> X2IncidenceCoh`, `kernel_cup_pointPullback : forall x, P.cup (2*d) (2*p) kappa.kernelClass (fstCohomologyPullback ... (H.cycleClass p (codimensionPointCycle V.X p x))) = fiberIntersectionClass x`, plus the proper-projection field: fiber-intersection class's projection = cycle class of the constructed finite incidence image — i.e., the classical `p2_*([C] cup p1^* cl([x])) = cl(p2_*(C intersect ({x} x X)))` incidence chain.
  - `BiPointFiberIntersectionLaw`: forward + transpose laws.
- main content: point incidence theorem `action_on_point`, global cycle-class naturality `cycleClass_nativeOperator`, `forward_and_transpose_cycleClass_natural`, transpose = projective incidence.
- name-vs-content: accurate; header states the classical equalities being packaged.
- gaps: the incidence laws (cycle-class/intersection theorem + proper-pushforward naturality) are supplied as record fields, not proven — they are exactly the Kunneth/Gysin content Mathlib lacks.

### GSTClassicalHodgePiStrictTraceCyclicOmniverseFinale.lean (237 lines)
- decls: 8 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry (4 `#print axioms`)
- hypotheses (record): `StrictTraceCyclicPacket (alpha)`: `correspondence : SchemeBiFiniteClosedCorrespondence V`, `trace : RightFiniteBettiTrace ...`, `pointCompatibility : PointCycleCompatibility ...`, `eigenvalue : Fin (liveRank alpha) -> Q`, `eigenvalue_injective : Function.Injective eigenvalue`, `eigenvector : forall i, trace.pushPull ((classicalHodgeBasis V H p (liveBasisIndex alpha i)).1) = eigenvalue i * (classicalHodgeBasis V H p (liveBasisIndex alpha i)).1`, `coefficient ... != 0`, `seedCycle`, `seed_class : H.cycleClass p seedCycle = ...` — one strict correspondence with pairwise-distinct eigenvalues and a cyclic native source.
- main content: `bigradedBettiHodge_of_strictTraceCyclicPackets` (packets at all weights => full Hodge statement); live-basis algebraization, target collapse, limitless address.
- name-vs-content: "Omniverse Finale" = conditional spectral-interpolation interface.
- gaps: constructing the eigenvalue-separated correspondence + cyclic source per Hodge state is the unproven geometric content.

### GSTClassicalHodgeTwoGeneratorNativeArsenal.lean (227 lines)
- decls: 10 theorems, 1 def, 1 structure, 0 axioms, 0 sorry (4 `#print axioms`)
- hypotheses (record): `TwoGeneratorNative (i j)`: `code : HasNativePointLifts (ambientTwoSlotCode i j)`, `lefschetz : HasNativePointLifts (ambientTwoStepLefschetz i j ...)` — native point-lift naturality for the two ambient primitives.
- main content: on Fin 2 the code observable D=diag(0,1) generates both projectors polynomially; `idSubCode_nativePointLifts`, `codeLefschetzCodeWord_nativePointLifts`, `normalizedWord_nativePointLifts` — two primitives externalize the whole arsenal.
- name-vs-content: accurate.
- gaps: `HasNativePointLifts` for the two primitives (geometric realization) is the hypothesis.

### GSTClassicalHodgeSingleSheetCrown.lean (226 lines)
- decls: 8 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry (5 `#print axioms`)
- hypotheses (record): `BasisAtomicSeparator (V) (H) (p) (i)`: `detector : RationalSingularCohomology ... ->_l[Q] Q`, `annihilates_atoms : AnnihilatesPointCycleClasses p (H.cycleClass p) detector`, `detects_basis : detector (classicalHodgeBasis V H p i).1 != 0` — a counterexample-shaped witness (detector killing all point-cycle classes but seeing one basis direction).
- main content: the microscopic reduction: `basis_mem_atomicSpan_iff_no_separator`, `bigradedBettiHodgeStatement_iff_no_basis_separator`, `classical_hodge_single_sheet_crown` (no separator anywhere iff full Hodge statement), plus sheet/cosmic-address identifications.
- name-vs-content: accurate ("smallest possible obstruction").
- gaps: eliminating separators = the Hodge statement itself (equivalence), so nothing is proven about nonexistence.

### GSTGraphV2NonEuclideanLaws.lean (219 lines)
- decls: 15 theorems, 0 defs, 0 axioms, 0 sorry (7 `#print axioms`)
- hypotheses: none.
- main content: Graph-V2 non-Euclidean axis laws: forward edges, strict boundary descent, n-axis = n/3 descent, null/gstPlus big2 regeneration, witness forward-fate dichotomy crown, physical projection exactness, `physical_happy_iff_ambient_witness`.
- name-vs-content: matches (graph-arithmetic engine).
- gaps: internal to the Erdos graph engine.

### GSTGraphV2CanonicalPhaseSteering.lean (218 lines)
- decls: 11 theorems, 1 def, 0 axioms, 0 sorry (3 `#print axioms`)
- hypotheses: none.
- main content: canonical right-seed phase steering: `lteCoeff_mod9_seven_of_one_le`, phase transfer spectrum, branch-free next-seed law `canonical_right_next_seed_exact`, injectivity on trits, `canonical_right_next_seed_eq_iff_phase_eq`.
- name-vs-content: matches.
- gaps: none internal (Erdos engine arithmetic).

### GSTClassicalHodgeProjectiveHyperplaneSection.lean (211 lines)
- decls: 6 theorems, 2 defs, 0 axioms, 0 sorry (5 `#print axioms`)
- hypotheses: none.
- main content: genuine projective scheme geometry: coordinate hyperplane as reduced closed subscheme of Proj via `IdealSheafData`, closed immersion, pullback along the projective embedding, support characterizations (`mem_hyperplaneSection_support_iff_coordinate`).
- name-vs-content: matches ("pure projective scheme geometry... nothing mentions the Hodge conjecture").
- gaps: none internal; utility layer.

### GSTClassicalHodgePointKernelCyclicCrown.lean (207 lines)
- decls: 5 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry (6 `#print axioms`)
- hypotheses (record): `PointKernelCyclicCertificate (V) (H) (p) (alpha)`: `spectral : RawClassicalHodgeSpectralObservable ...`, `spectral_basisIndex = HodgeSupportIndex.include`, `transitions : spectral.PointTransitionKernel`, `coefficient : HodgeSupportIndex alpha -> Q`, `coefficient_ne_zero`, `seedPresentation : FiniteCodimensionPresentation V.X p`, `seedClass_spec : finitePointCycleClassMap p (H.cycleClass p) seedPresentation = sum i, coefficient i * (classicalHodgeBasis V H p i.1).1` — spectral observable + point-transition kernel + finite seed presentation with all-live coefficients.
- main content: generator-level cyclic certificate: `exists_native_cycle`, `bigradedBettiHodge_of_pointKernelCyclicCertificates`, `pointKernelCyclic_constructive_crown`.
- name-vs-content: accurate ("completely generator-level certificate").
- gaps: supplying the certificate (distinct eigenvalues + point kernel + seed class equation) is the unproven geometric work.

### GSTClassicalHodgeLimitlessCosmicLefschetzPropagation.lean (202 lines)
- decls: 10 theorems, 1 def, 0 axioms, 0 sorry (6 `#print axioms`)
- hypotheses: none.
- main content: cross-weight Lefschetz scalar computed, not assumed: unique mixed path (q-p digit + q-p carry moves), central-binomial coefficient, `limitlessLefschetzScalar_eq_cosmic_coefficient`, `cosmicLefschetz_target_coefficient_ne_zero`, `limitless_cosmic_lefschetz_crown`.
- name-vs-content: honest (GST cosmos combinatorics).
- gaps: none internal; cosmos model is the 12-cell-world generalization, not variety cohomology.

### GSTClassicalHodgeProjectorSeedLanding.lean (201 lines)
- decls: 5 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry (4 `#print axioms`)
- hypotheses (record): `ProjectorSeedCertificate`: `spectral`, `spectral_basisIndex`, `transitions`, `seedPresentation`, `isolatedCoefficient ... != 0`, `isolator_seed : forall i, linearPolyEval spectral.observable (F.isolatorPolynomial i) (finitePointCycleClassMap p (H.cycleClass p) seedPresentation) = (isolatedCoefficient i * F.isolatorScale i) * ...` — Lagrange isolators applied to a genuine seed give nonzero multiples of each live sheet.
- main content: projector-seed extraction (`extractedLiveBasisCycle_spec`, `reconstructedCycle_spec`, `exists_native_cycle`), criterion `bigradedBettiHodge_of_projectorSeedCertificates`.
- name-vs-content: accurate relaxation (seed need not lie exactly in selected span).
- gaps: certificate existence unproven.

### GSTClassicalHodgeGSTSourceProgramCompiler.lean (198 lines)
- decls: 5 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry (3 `#print axioms`)
- hypotheses (record): `GSTSourceTargetProgram (G) (S) (j)`: `program : GradedGeometricProgram V p p`, `source_action : program.cohomologyEval G S.hodge.1 = (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex * (classicalHodgeBasis V H p j).1` — one genuine graded geometric program agreeing with the GST matrix-unit prediction on the source only.
- main content: source-specific synchronization: `targetCycle_spec`, `target_mem_cycleClass_range`, `source_action_matches_global_sheet_move`, projective-word specialization.
- name-vs-content: accurate (explicitly "source-specific... no target algebraicity... stored").
- gaps: the program realizing the GST move on the live source is the unproven geometric input.

### GSTClassicalHodgePerSheetProjectorLanding.lean (197 lines)
- decls: 5 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry (4 `#print axioms`)
- hypotheses (record): `PerSheetProjectorCertificate`: per-sheet `seedPresentation : HodgeSupportIndex alpha -> FiniteCodimensionPresentation V.X p`, `isolatedCoefficient != 0`, `isolator_seed` (independent per-sheet seeds with isolator equations).
- main content: independent-sheet extraction, `bigradedBettiHodge_of_perSheetProjectorCertificates`.
- name-vs-content: accurate relaxation (no common seed needed).
- gaps: certificate existence unproven.

### GSTCarrierMechanismVerdictCertificate.lean (192 lines)
- decls: 9 theorems, 4 defs, 0 axioms, 0 sorry (3 `#print axioms`)
- hypotheses: none (period constants taken as explicit rational hypotheses `iWRtheta2`, `iWR2` in the chi arithmetic; header: "No sorry, no custom axioms, no native_decide").
- main content: exact finite algebra certifying the carrier-mechanism no-go derivation: (A) 48 ordered pairings of W_R monomials with theta^2 pair-words all have repeated indices => INT W_R theta^2 = 0 (`weil_WR_theta2_collision` by full evaluation); theta^4 surjection count = 24 of 256 (`theta4_surjection_count`); (B) single-band kill (`wit_kill`: cohomology concentrated in one degree with chi=0 is zero), twist-chi arithmetic `carrier_twist_chi = r*k^4` (independent of m), End-twist `end_twist_chi = r^2 k^4 + 8 m^2`; capstones A/B/C.
- name-vs-content: accurate and unusually careful: header separates "what is certified (exact finite algebra)" from "what is NOT certified (Pic^0 lemma, HRR, Chern-character multiplicativity, Fourier-Mukai toolkit, Mukai semi-homogeneous band theorem — external .tex leaves E5/E8/E12/E13/E14)".
- gaps: all scheme-level steps of the no-go theorem live in the .tex on declared leaves; Lean certifies only the finite arithmetic core.

### GSTClassicalHodgeIntegralWorldEmbedding.lean (191 lines)
- decls: 8 theorems, 1 def, 0 axioms, 0 sorry (5 `#print axioms`)
- hypotheses: none.
- main content: integralization: clearing rational Hodge coefficients to Z, canonical live world (1 row x N columns), exact code projectors on integral coordinates, recoordination functoriality, `integral_world_embedding_crown`.
- name-vs-content: accurate (GST world bookkeeping).
- gaps: none internal; combinatorial shadow only.

### GSTClassicalHodgeLimitlessCosmicNoEscape.lean (185 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry (4 `#print axioms`)
- hypotheses: geometry-first records (imported) for the two primitives.
- main content: fusion of the two-slot word identification with the geometry-first native word: the limitless cosmic matrix-unit action on the Hodge fiber is the cohomological face of an actual native cycle operator; `limitlessCosmic_preserves_cycleClass_range_on_hodge`, `no_limitlessCosmicEscape`, `algebraicFiber_eq_top_of_geometryFirst_and_seed`, `hodge_weight_of_geometryFirst_noEscape`.
- name-vs-content: accurate.
- gaps: conditional on the geometry-first two-generator realization (same unproven records as GSTClassicalHodgeGeometryFirstTwoGenerator).

### GSTClassicalHodgeGSTDefectExtinction.lean (183 lines)
- decls: 8 theorems, 0 defs, 0 axioms, 0 sorry (5 `#print axioms`)
- hypotheses: source-program records (`GSTSourceTargetProgram` via compiler import) / canonical spine programs.
- main content: collision argument: separator annihilates the atomic cycle-class span while a synchronized program puts the detected basis sheet in that span => contradiction; `separator_false_of_sourceProgram`, `isEmpty_fiberedDefectEvent_of_sourceProgram`, `no_basis_separator_of_canonicalSpinePrograms`, `every_basis_mem_cycleClassRange_of_canonicalSpinePrograms`.
- name-vs-content: accurate.
- gaps: conditional on synchronized GST/geometric programs existing (the compiler's record).

### GSTFourPowerAffineExponentPeel.lean (180 lines)
- decls: 15 theorems, 3 defs, 0 axioms, 0 sorry (1 `#print axioms`)
- hypotheses: none.
- main content: exact exponent-trit peel polynomials for the affine orbit (`peel0/1/2` with `affineOrbit (3q + j) = j + 3 * peel_j (affineOrbit q)`), digit peels, low-trit conjugacy crown.
- name-vs-content: matches.
- gaps: none internal (Erdos engine arithmetic).

### GSTPureHodgeLefschetzKernel.lean (177 lines)
- decls: 6 theorems, 1 def, 0 axioms, 0 sorry (4 `#print axioms`)
- hypotheses: none.
- main content: closed diagonal-to-diagonal Lefschetz kernel law: reachability only forward, unique time 2(q-p), exact central-binomial coefficient; `pure_diagonal_lefschetz_kernel`, `hc_pure_zero_to_two_kernel`, crown.
- name-vs-content: accurate (GST cosmos kernel classification).
- gaps: none internal.

### GSTK3DiagonalPrimitive.lean (173 lines)
- decls: 5 theorems, 1 def, 0 axioms, 0 sorry (2 `#print axioms`)
- hypotheses: none (works on an abstract rational model of H^4(S x S)).
- main content: the K3 diagonal primitive P = Delta - U - V - (1/d)B: exact class constructor, Lefschetz-kernel cancellation H*cl(P)=0, primitivity, nonzero transcendental readout, `diagonalPrimitiveCycle_outside_divisor_words` (P is not a divisor-word combination when u,v orthogonal to NS(S)).
- name-vs-content: honest: header says "The Lean kernel below verifies the exact rational cycle constructor... The actual K3 scheme construction, Betti/Kunneth comparison, diagonal Gysin identities and Neron-Severi nondegeneracy [are the remaining instantiation]".
- gaps: geometry (K3 scheme, Kunneth ring, Gysin identities) is asserted in comments, not constructed; Lean verifies the rational-linear model algebra.

### GSTPrimitiveAlgebraicMotiveProjector.lean (172 lines)
- decls: 8 theorems, 0 defs, 0 axioms, 0 sorry (1 `#print axioms`)
- hypotheses: dual-cycle packet (Gram matrix invertibility) imported; target directions orthogonal to detectors.
- main content: explicit algebraic projector algebra: A^2=A, R=id-A idempotent, AR=RA=0, A fixes generators, R kills algebraic generators and fixes orthogonal directions, `nonrepresented_target_survives_algebraic_complement`.
- name-vs-content: unusually honest header: "The explicit Pi_A cycle itself is a standard valid geometric formula, but it has NOT been formally constructed inside Mathlib's Chow product API in this module. Do not infer that R=0."
- gaps: projector verified only on cohomology; Chow-idempotence modulo rational equivalence not asserted; the Gram/cup/Gysin instantiation for actual X not done.

### OriginTransducerScratch.lean (170 lines)
- decls: 9 theorems, 0 defs, 0 axioms, 0 sorry (0 `#print axioms`)
- hypotheses: none ("No Erdos theorem and no extra axiom: all canonical decomposition data enters as explicit theorem hypotheses").
- main content: scratch kernel for the natural-origin information transducer: navigation cancellation algebra (`origin_navigation_algebraS`), digit recurrences, affine origin steps, div3 strict descent, three-phase GST orbit exactness (`gst_phase_one/two/wrap_exactS`), low prefix bands.
- name-vs-content: matches (scratch file with git-history banner, branch sol_physical-phase-crossing-surgery).
- gaps: scratch layer; feeds the Erdos engine's origin/phase bookkeeping.

### GSTClassicalHodgeCrossCarrierCupGysinConstruction.lean (161 lines)
- decls: 3 theorems, 1 def, 1 structure, 0 axioms, 0 sorry (1 `#print axioms`)
- hypotheses (record): `CrossProductCupGysin (S V D H PCoh d p q e)`: `degree_balance : 2*e + 2*p = 2*d + 2*q`, `sourcePullback`, `kernelClass : PCoh (2*e)`, `cup`, `targetGysin` — the typed degree-graded shape of the cup/Gysin correspondence action on S x V, with the product-cohomology operations as **supplied primitives** ("the current Mathlib stack does not yet construct their required Kunneth/Gysin operations for general S x V").
- main content: kernel cycle-class naturality `cupGysin_kernel_cycleClass_natural` and native output law under a pointwise agreement hypothesis.
- name-vs-content: accurate; explicitly marked "NEEDS CI RUN LATER".
- gaps: Kunneth/Gysin for S x V are not built; the point-incidence agreement is the decisive independent input.

### GSTClassicalHodgeLimitlessSemanticSeparation.lean (161 lines)
- decls: 9 theorems, 0 defs, 0 axioms, 0 sorry (2 `#print axioms`)
- hypotheses: none.
- main content: **audit theorem**: replacing `cycleClass` by the zero map leaves every GST/Hodge/cosmic construction unchanged (`rationalHodgeSubspace_zeroCycleClassData`, `hodgeMatrixUnit_zeroCycleClassData`, ...), while a nonzero Hodge class is not in the zero range; hence `final_externalization_must_use_cycleClass_semantics` — the final landing must externalize through genuine geometry.
- name-vs-content: accurate ("target-localization theorem... introduces no new mathematical hypothesis").
- gaps: none internal — it *is* the gap statement: internal coordinate algebra can never close the Hodge target.

### GSTClassicalHodgeSingleExactSuccessorSurvival.lean (159 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry (4 `#print axioms`)
- hypotheses: one explicitly-constructed relative successor with ambient coheight p+1 (`separator_successor_survives_of_ambient_exact` hypothesis form).
- main content: exact-survivor count formula: successor mass = cardinality of the filtered exact-successor locus (each exact successor +1, no cancellation); ONE exact successor forces nonzero native principal-cut image.
- name-vs-content: accurate surgical interface.
- gaps: existence of the exact successor at each step is the remaining geometric input (supplied by separator-successor constructions elsewhere).

### GSTClassicalHodgeCanonicalAmbientArsenal.lean (153 lines)
- decls: 4 theorems, 0 defs, 0 axioms, 0 sorry (4 `#print axioms`)
- hypotheses: point-kernel lift input (finite point transition law).
- main content: canonical ambient extension: over Q any Hodge-fiber matrix unit extends to ambient cohomology; `ambientHodgeMatrixUnit_on_hodge`, native matrix-unit operator pair action, `nativeArsenalRepresentationOfPointKernels`.
- name-vs-content: accurate.
- gaps: extension is pure linear algebra (subspace -> space over a field); geometric content sits in the point-kernel input.

### GSTClassicalHodgeCMSurfaceTensorContraction.lean (150 lines)
- decls: 5 theorems, 1 def, 0 axioms, 0 sorry (1 `#print axioms`)
- hypotheses: point-incidence equality between genuine correspondence on native cycles and the cohomological rank-one kernel (decisive independent input; the CM paper's divisor/Kunneth/Gysin construction "is not manufactured in this file").
- main content: algebraic core of the surface-to-tensor Gysin extraction (OpenAI/math CM-abelian paper section 3): rank-one Betti contraction kernel, composition law, `surface_period_normalizes_native_tensor`, `surface_period_target_is_algebraic` — period normalization DERIVED, not hypothesized.
- name-vs-content: accurate; "NEEDS CI RUN LATER".
- gaps: scheme-theoretic construction of the incidence identity not done here.

### GSTPerfectPowerTailNavigation.lean (146 lines)
- decls: 9 theorems, 1 def, 0 axioms, 0 sorry (0 `#print axioms`)
- hypotheses: none.
- main content: canonical tail decomposition `4^(3^s b) = 1 + 3^(s+1) * canonicalTail s b`, digit-from-residue law, forced-prefix not-happy, happy position >= cut, tail lift/projection, navigation equivalence crowns.
- name-vs-content: matches.
- gaps: none internal (Erdos engine).

### GSTClassicalHodgeDualArsenalExtinction.lean (141 lines)
- decls: 4 theorems, 0 defs, 0 axioms, 0 sorry (3 `#print axioms`)
- hypotheses: algebraic orbit of one nonzero seed stays algebraic (per weight).
- main content: dual form of arsenal irreducibility: a detector vanishing on the full one-step orbit of a nonzero state vanishes on the whole Hodge fiber; `atomicSeparator_vanishes_of_algebraic_orbit`, `bigradedBettiHodge_of_dualArsenalExtinction`.
- name-vs-content: accurate.
- gaps: same seed+orbit-algebraicity inputs as the primal crown.

### GSTClassicalHodgePrincipalCutCorrespondenceGhostStrike.lean (141 lines)
- decls: 3 theorems, 0 defs, 0 axioms, 0 sorry (3 `#print axioms`)
- hypotheses: one realized correspondence word W and scalar c with `W(cl(Seed.cycle)) = c * basis_j` (the microscopic target).
- main content: fusion: nonzero principal-cut action gives an explicit native seed; one correspondence word carrying it to a nonzero multiple of a target sheet kills the separator: `nativeCycleHit_of_principalCut_word`, `isEmpty_separator_of_principalCut_word`, `separator_forbids_principalCut_word`.
- name-vs-content: accurate ("microscopic" target honestly stated).
- gaps: constructing W per sheet is the unproven geometric work.

### GSTClassicalHodgeOmniverseTwoSlotLefschetzBranch.lean (137 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry (4 `#print axioms`)
- hypotheses: none.
- main content: on the ordered two-slot chart, the bare rationalized two-step Lefschetz operator IS the nonzero scalar times the matrix unit: `localized_L2_eq_scaled_matrixUnit`, `matrixUnit_eq_normalized_localized_L2`, `branch_collapse_via_localized_L2` — every primitive causal arrow is a normalized local L^2 firing.
- name-vs-content: accurate GST-internal result.
- gaps: "This is the equation that should be geometrically externalized" — the externalization is not done here.

### GSTFourPowerNo22Magnitude.lean (135 lines)
- decls: 6 theorems, 1 def, 0 axioms, 0 sorry (5 `#print axioms`)
- hypotheses: none.
- main content: the no-adjacent-22 ternary language: suffix-cut stability, low-pair <= 7, magnitude bound (`no22_nine_power_bound`: a No22 number with n digits is < 9^n), all-tails version.
- name-vs-content: matches.
- gaps: none internal; supports the Erdos engine's magnitude bookkeeping.

### InformationRegenerationScratch.lean (128 lines)
- decls: 8 theorems, 1 def, 0 axioms, 0 sorry (0 `#print axioms`)
- hypotheses: none.
- main content: scratch file (git-history banner, branch sol_physical-phase-crossing-surgery): seeded bad-trace language `GSTSeededBadTraceS`, relative affine tail/emitted-digit laws, canonical information regeneration, child/parent seed regeneration, null/plus gate seed regeneration.
- name-vs-content: matches (scratch).
- gaps: scratch layer of the Erdos information-state engine.

### GSTK3GraphPrimitiveRank.lean (127 lines)
- decls: 4 theorems, 1 def, 0 axioms, 0 sorry (1 `#print axioms`)
- hypotheses: measurement/entry hypotheses for the independence theorem (geometric Gram entries via an explicit measurement map), imported primitiveization.
- main content: quartic-K3 cyclotomic rotation model (order-4 automorphism acting as [[0,-1],[1,0]] on Q x Q): `quarticK3Rotation_orbit_rank_two`; primitiveization of the two graph cycles Gamma_id, Gamma_g; `two_primitive_graph_classes_independent` (rational independence of the two primitive graph classes under the stated measurements).
- name-vs-content: header honest: "The analytic graph/Kunneth comparison for the explicit quartic K3 is the next scheme-to-Betti instantiation of that measurement."
- gaps: the measurement comparison (fundamental classes, Kunneth) is not constructed; independence is conditional on the Gram entries.

### GSTComplexTangentProjectionChainObstruction.lean (120 lines)
- decls: 7 theorems, 4 defs, 0 axioms, 0 sorry (1 `#print axioms`)
- hypotheses: none.
- main content: **genuine differential-geometric obstruction**: in a rational Fourier-block model of E x E, the real (1,1)-type projector does NOT commute with d (`type_projector_breaks_closedness`: d(pi11 omega) = -(sin x/2) dx^dy^dv != 0), so no pointwise complex-tangent projection can be a chain-level Hodge projector; also complex projection of a simple bivector is not simple.
- name-vs-content: accurate ("NO claim of Hodge completion or a bogus all-X geometric calibration operator").
- gaps: Lean verifies the rational Fourier coefficient matrix, not the full analytic manifold theorem — but the negativity is the content.

### GSTMathboxCorrectedZetaSafeDomain.lean (118 lines)
- decls: 5 theorems, 0 defs, 0 axioms, 0 sorry (2 `#print axioms`)
- hypotheses: none (y >= 1, x > y^2 as premises of the regime).
- main content: corrected zeta-family domain: `correctedDenominator_pos` (x^n - y^(n+1) > 0 for all n under 1 <= y < sqrt x), all-indices legality, kernel positivity, partial-sum positivity/nonvanishing.
- name-vs-content: matches.
- gaps: convergence of the corrected infinite sum is explained in a doc, only finite cutoffs are Lean-proven here.

### GSTFermatCanonicalPointRankBridge.lean (109 lines)
- decls: 1 theorem, 0 defs, 0 axioms, 0 sorry (1 `#print axioms`)
- hypotheses (explicit): measurement map `M : ... ->_l[Q] (Fin d -> Q)` with Gram-entry hypothesis `hEntry : forall i j, (M (cl(Z_i))) j = if i = j then d^2 * NormalTopCoeff - d else -d` — the explicit Fermat normal-Chern intersection measurements as input.
- main content: `genuine_point_generated_fermat_rank`: rational linear independence of the d native point-generated Fermat primitive cycles (d*[P_zeta] - h^p) under the stated Gram measurements.
- name-vs-content: accurate conditional; header: "Integration target: derive the measurement comparison from canonical analytic fundamental classes, then extend...".
- gaps: the measurement comparison (analytic fundamental classes) is future work — the Gram matrix is a hypothesis.

### GSTClassicalHodgeLimitlessExactClayFinale.lean (105 lines)
- decls: 4 theorems, 0 defs, 0 axioms, 0 sorry (4 `#print axioms`)
- hypotheses (the three terminal unproven bridges, imported records):
  - `G : GeometricCycleClassSpine V H` (the canonical spine),
  - `M : NativeMassCycleClassBridge V H` (native-mass => live spine-mass survival),
  - `R : FullProjectiveCosmicExternalization G` (limitless cosmic read/write algebra realized by genuine projective correspondence operators).
- main content: the literal Clay-statement landing file: `everyHodgeClassIsRationalAlgebraic_of_fullLimitless` (every rational (p,p) class is the class of an actual rational codimension-p algebraic cycle), Clay-wording corollaries (finite rational combinations of irreducible cycle classes), elementwise native-cycle and finite-presentation forms.
- name-vs-content: "Limitless Exact Clay Finale" — the *statement* is the exact Clay formulation, but all three load-bearing inputs are unproven records; the file is a composition layer, not a proof of the conjecture.
- gaps: exactly G + M + R: spine mass survival and full projective externalization are the standing unproven geometric content (the "closing string" of the campaign).

### GSTResearchDimensionCorrectedHodgeSynthesis.lean (104 lines)
- decls: 1 theorem, 1 def, 0 axioms, 0 sorry (1 `#print axioms`)
- hypotheses (three explicit geometric premises):
  - `D : BoundedGeometricDegreeCharge G d` — a dimension-bounded Betti-degree charge on the native projective successor tower factoring through actual cycle class (nonzero algebraic Hodge seed at each p <= d);
  - `hvanish : forall p > d, forall a : ClassicalHodgeFiber V H p, a = 0` — weights above the geometric dimension have zero rational Hodge fiber;
  - `hcyclic : NativeGeometricCyclicityInWindow G d` — `forall p <= d, forall Z, geometricHodgeClass G Z != 0 -> SeedCyclicForActualGeometry G Z` (local actual-geometric cyclicity).
- main content: `hodge_of_bounded_degree_and_native_geometric_cyclicity`: the all-weight rational Hodge target FROM these premises, with no out-of-dimension source.
- name-vs-content: honest: "this theorem does NOT prove that all projective varieties satisfy the bounded degree and cyclicity premises. Their uniform independent geometric constructions remain the Hodge task."
- gaps: all three premises unproven; the dimension-corrected route is a conditional synthesis.

### GSTClassicalHodgeStrictGraphCorrespondence.lean (94 lines)
- decls: 4 theorems, 1 def, 0 axioms, 0 sorry (4 `#print axioms`)
- hypotheses: none (a finite endomorphism is input data).
- main content: graphs of finite complex-scheme endomorphisms promoted to strict scheme-bi-finite correspondences: identity left projection, finite right projection, transpose with identity right projection.
- name-vs-content: matches.
- gaps: none internal; genuine scheme-level construction.

### GSTClassicalHodgeHomogeneousMinimalPrime.lean (90 lines)
- decls: 3 theorems, 0 defs, 0 axioms, 0 sorry (2 `#print axioms`)
- hypotheses: none.
- main content: graded commutative algebra: every minimal prime over a homogeneous ideal is homogeneous (`minimalPrime_isHomogeneous`), bundled homogeneous minimal-prime API.
- name-vs-content: matches ("pure graded commutative algebra... no GST coordinate assumption").
- gaps: none internal.

### GSTU2DCanonicalShiftedTerminalProbe.lean (89 lines)
- decls: 3 theorems, 0 defs, 0 axioms, 0 sorry (3 `#print axioms`)
- hypotheses: none.
- main content: exact 8x3 density-rectangle telescoping identity on shifted vertical windows of the Graph-V2 carry/digit graph; carry-neutral boundary vanishing; shifted terminal form.
- name-vs-content: matches (U2D engine arithmetic).
- gaps: none internal.

### GSTGeneralSpaceManifoldReversibleCharts.lean (76 lines)
- decls: 2 theorems, 2 defs, 0 axioms, 0 sorry (0 `#print axioms`)
- hypotheses: none.
- main content: every Mathlib `ChartedSpace` chart imported as a reversible partial GST coordinatization (`manifoldReversibleChart`), chart recovery, point-indexed atlas.
- name-vs-content: matches (GST foundational glue to Mathlib manifolds).
- gaps: none internal.

### GSTGeneralSpaceSchemeStalkComorphism.lean (75 lines)
- decls: 3 theorems, 1 def, 1 structure, 0 axioms, 0 sorry (0 `#print axioms`)
- hypotheses: none — `LocalComorphism` is pure data (`map : forall x, K.Fiber (f.mapPoint x) -> F.Fiber x`), not a hypothesis-record.
- main content: mixed-variance record of scheme morphisms (covariant on points, contravariant on stalks): `schemeStalkComorphism`, stalk-map defeq, closed-immersion stalk surjectivity, subscheme specialization.
- name-vs-content: matches.
- gaps: none internal.

### GSTGraphV2GeneralSpaceRealization.lean (71 lines)
- decls: 0 theorems, 9 defs, 0 axioms, 0 sorry (0 `#print axioms`)
- hypotheses: none.
- main content: realization of the Graph-V2 seven-axis states as a `GeneralSpace` (paths = refl-trans chains of forward edges), charts, observables (space/digit/carry), witness predicate, physical point realization.
- name-vs-content: matches (definitional glue; no theorems).
- gaps: none internal.

---

## BATCH SUMMARY

**Totals.** 70 files, 19,364 LOC. 852 theorems + 50 lemmas (all 50 in the vendored Mathlib file `fsb.lean`), 218 defs, 26 genuine `structure` declarations (2 more textual matches are doc-comments), 390 `#print axioms` receipts. **0 `axiom`, 0 `opaque`, 0 `sorry`.** This batch is axiom-free and sorry-free: every unproven assumption is an explicit hypothesis (named `Prop` or record field) — the honest "hypothesis-record / named-primitive" discipline.

**Unproven-assumption inventory (the load-bearing hypotheses).** No custom axioms. The assumptions are:

*Hodge track — hypothesis-records (structure fields = unproven mathematical propositions):*
1. `CMNativeProductRealization` (GSTCMFiniteGeometricDegreeDescent): an actual Chow ring of divisor products on the CM source whose cycle classes match rational Betti classes (`nativeUnit_sound`, `nativeDivisor_sound`, `bettiDivisor_hodge`, multiplication soundness).
2. `CMActualHodgeCharacterExpansion`: every rational Hodge class of the CM source is a Q-combination of balanced CM character divisor-words (`expansion`).
3. `CMGeometricFieldCharacterExpansion`: the same expansion over Q->K with basis-coefficient comparison.
4. `BigradedBettiHodgeStatement A HA` + `CrossCarrierTransfer` + degree identity `f_* f^* = d*id` (CM descent inputs) — source algebraicity + a generically finite source->target morphism.
5. `NativeHodgePrimitive` / `GeometryFirstTwoGenerator` (GeometryFirstTwoGenerator): genuine native cycle operators with the cycle-class commuting square whose restriction to the (p,p) fiber is the two-slot code and the two-step Lefschetz primitive.
6. `TwoGeneratorNative`: `HasNativePointLifts` for the two ambient primitives.
7. `FiniteSpineMomentChain`: nonzero finite-prefix spine moment chain (`base_ne_zero`, `successor_read`).
8. `ProjectiveLiveSourceTarget`: one genuine projective-correspondence kernel per target sheet sending the live source to a scalar multiple of the target basis vector.
9. `OneSourceCompositionalCorrespondenceRealization`: noncommutative correspondence expressions hitting one source per sheet (`source_hit`).
10. `NatHodgeCoordinateChart` (Stage2GCompactAssembly): injective finite-support N-addressing of actual cohomology matching the classical Hodge basis — the self-declared "remaining Task-4 boundary".
11. `ChannelHodgeRetract`: split retract of the Hodge sector with every channel basis decoded to the class of an actual cycle.
12. `CodimensionHodgeRealization` (Stage2D) and the Stage-2D supplied semantics: rational degree-2p cohomology, the genuine (p,p) Hodge subspace, the cohomological cycle-class map, smooth-projective eligibility — the four objects the Mathlib stack does not natively provide.
13. `PointFiberIntersectionLaw` / `BiPointFiberIntersectionLaw`: the classical incidence chain `p2_*([C] cup p1^*cl([x])) = cl(p2_*(C cap ({x} x X)))` (Kunneth/Gysin/proper-pushforward content).
14. `StrictTraceCyclicPacket`: one bi-finite correspondence with injective eigenvalues on the live support, eigenvector equations, and a cyclic native source seed.
15. `BasisAtomicSeparator` (counterexample-shaped): a detector annihilating all point-cycle classes while detecting a basis direction (equivalent to Hodge failure).
16. `PointKernelCyclicCertificate` / `ProjectorSeedCertificate` / `PerSheetProjectorCertificate`: spectral observable + point-transition kernel + finite seed presentation with Lagrange-isolator equations.
17. `GSTSourceTargetProgram`: a genuine graded geometric program whose cohomological execution on the live source equals the GST matrix-unit prediction.
18. `CrossProductCupGysin`: the typed cup/Gysin shape on S x V with Kunneth/Gysin operations as supplied primitives.
19. Terminal finale bridges: `GeometricCycleClassSpine G`, `NativeMassCycleClassBridge M`, `FullProjectiveCosmicExternalization R` (LimitlessExactClayFinale); `BoundedGeometricDegreeCharge D` + `NativeGeometricCyclicityInWindow` + p>d vanishing (ResearchDimensionCorrectedHodgeSynthesis); `GhostWeightNativeSeedSurvival` / `GhostSeedTargetStrictClosure` (PlaneAxiomStatus crowns).
20. `RealizesCosmicOnPoints` (FiniteClosedCorrespondence): identification of a genuine correspondence with a GST matrix unit on points.

*Erdos track — named-Prop / explicit hypotheses:*
21. `tailF_row_primitive`: every 3-free class-one core (>500) fires its row word's top third at some depth.
22. `tailF_tower_primitive`: every diagonal-dodging tower fires its deep tail (depth >= s+2).
23. Mod-243/729/2187 row-primitive variants (the finite-window ladder), `erdos_even_conjecture_iff_tailF`, `erdos_ternary_2_universal_of_tailF` (imported boundary inputs).
24. `hEntry` Gram-measurement hypothesis (FermatCanonicalPointRankBridge), K3 measurement hypotheses (K3GraphPrimitiveRank), CM point-incidence equality (CMSurfaceTensorContraction), `BettiRelated` strict relations (DegreeCertifiedStrictRelationFinale).

**The 5 most load-bearing files:**
1. **GSTClassicalHodgeGSTPlaneAxiomStatus.lean** — the axiom-status ledger: proves the intrinsic GST plane does NOT imply the Hodge statement (zero-cycle countermodel), reduces Hodge to ghost extinction (D) + source survival, and blocks every circular packaging. It defines what counts as noncircular for the whole campaign.
2. **GSTClassicalHodgeLimitlessExactClayFinale.lean** — the literal Clay-statement landing: shows in four lines exactly which three unproven bridges (spine G, mass bridge M, full projective externalization R) stand between the repo and the conjecture.
3. **GSTCMFiniteGeometricDegreeDescent.lean** — the only genuine transfer mechanism to *arbitrary* targets (finite-degree descent), plus the CM character-expansion hypothesis chain; its own header warns the universal dominance morphism does not exist.
4. **GSTTailFFourthDimension.lean** — the Erdos-assault engine (2,416 lines of unconditional 3-adic machinery) whose two named primitives (`tailF_row_primitive`, `tailF_tower_primitive`) are the entire unproven content of that route.
5. **GSTClassicalHodgePlaneCompletenessTheorem.lean** — unconditional intrinsic plane completeness + the circularity certificates (ghost-adaptive planes iff Hodge), the firewall that keeps the plane axioms out of the foundations.
(Honorable mentions: GSTTailFInfiniteRead — proves the survivor dust is immortal, i.e., the finite modulus ladder can never close; GSTGeometricRealizationStage2D — the definition of actual native cycle spaces underlying all "genuine" claims.)

**The single biggest gap:** the geometric bridge itself. Every "finale/crown" theorem in this batch conditionally converts GST's internally-complete operator algebra into the Hodge statement, and the conversion always runs through the same unproven content: real cycle-class realizations of GST operators — packaged as `GhostSeedTargetStrictClosure`/`NativeMassCycleClassBridge`/`FullProjectiveCosmicExternalization`/`GeometryFirstTwoGenerator`/`CMActualHodgeCharacterExpansion` — and the batch's own audit files (PlaneAxiomStatus, LimitlessSemanticSeparation, PlaneCompletenessTheorem) PROVE that no intrinsic GST construction can supply it (zero-cycle-class countermodel; immortal dust on the Erdos side). The conjectural content is thus exactly isolated, honestly disclosed, and still open.
