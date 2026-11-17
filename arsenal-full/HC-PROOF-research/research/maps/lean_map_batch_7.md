# Lean Batch 7 Map — Task 1-h

Repo: /tmp/hc-clone-23 @ 6c20bb7, branch research/gpt6-native-point-primitive-span-20261017.
Batch: 72 files, 19,374 LOC, 716 theorems, 0 lemmas, 150 defs, 40 structures, **0 `axiom` declarations, 0 real `sorry`** (3 textual "sorry" matches are docstring disclaimers), 414 `#print axioms` commands.
Idiom throughout: unproven mathematics lives in **named `Prop`s and hypothesis-record structures** passed as explicit binders (the "ForAllN hypothesis idiom"), never as `axiom`.

---

### GSTWeilFourfoldAuxiliaryExtraction.lean (1617 lines)
- decls: 63 theorems, 28 defs, 0 axioms, 0 sorry (45 #print axioms)
- hypotheses: none declared. Geometry is *abstract*: `projectiveBundleChow_*` theorems take `pull : ChowY →+* ChowP`, `push : ChowP →ₗ[ℚ] ChowY` with the projection formula `hProjection : push (pull y * x) = y * push x` and fibre integration `p_*(ζ^f)=1` as *hypotheses*; `cycleClassY/cycleClassP` ring maps as parameters. Header explicitly disclaims: "does NOT construct abelian varieties, Chow intersections, Betti cycle classes, or the secant-sheaf cycle… external inputs to the manuscript, not axioms."
- main content: exact ℚ-arithmetic for a Weil fourfold: intersection form on (Γ_u,F1,F2,Δ) (`auxiliary_graph_pairings`: Γ²=-2, Γ·Γ̃=0, Γ̃²=-2d); tensor balance/contraction injectivity on the Weil sector; 4th/6th-power CM orbit determinants strictly positive for d>0 (`extracted_fourth_power_orbit_has_rank_two`, `secantSeedCanonicalCMOrbitDet_pos`); nilpotent geometric-series inverse (1+u)·Σ(-u)^k = 1-(-u)^n; projective-bundle Chow/Betti pushforward extraction *given* abstract pull/push/cycle-class maps; secant-seed trilinear vanishing combinatorics; period-transport linear algebra; Weil projector polynomial identities (`weilProjectorQuadraticReduction`, native Horner coefficients exact).
- name-vs-content: "Weil fourfold auxiliary extraction" = rational arithmetic + abstract ring lemmas; the actual geometry is parameterized away.
- gaps: all geometric content (abelian varieties, Gysin, Betti classes, semiregularity pipeline) is external; theorems hold only for maps satisfying the supplied hypotheses.

### GSTClimbInfiniteFamily.lean (1222 lines)
- decls: 64 theorems, 3 defs, 0 axioms, 0 sorry (64 #print axioms)
- hypotheses: none declared; receipt theorems take `hB : erdos_even_conjecture_iff_tailF` (named Prop from `MonolithBoundary.lean`: `four_power_omega_shadow_wave_tailF ↔ ∀ K ≥ 8, noTernaryTwo (4^K) = false` — the Erdős even-exponent ternary statement, imported, unproven). `CantorianPower K := ∀ p ≥ 1, digit3 (4^K) p ≠ 2`; `NeverFiringTower core := ∀ S p, digit3 (4^(3^S·core)) (S+1+p) ≠ 2`.
- main content: unconditional base-3 digit analysis of powers of 4: pair law (4^K,4^(K+1) share trit u%3 at cut), infinite deep-family climb witnesses, `prefaced_window_law` (full diagonal window law for every cut/core/remainder), dust cascade kills (mod 9/27/81 residue classes), `the_act_iff_no_cantorian` (the act ⟺ no Cantorian exponent ≥ 8), `hTailF_of_no_cantorian`, tower-dust emptiness for 3∤core and core%3∈{1,2}, lattice mod laws (4^m mod 2187 pinned by m mod 729, etc.).
- name-vs-content: "infinite family" is honest for the digit combinatorics; the terminal receipts are conditional on `hB`.
- gaps: `the_act` / tailF / full Erdős statement all conditional on the named seam; the actual hard existence of digit 2 for every K ≥ 8 is not proven here.

### GSTClassicalHodgeKernelStableOperatorAlgebra.lean (959 lines)
- decls: 46 theorems, 0 defs, 0 axioms, 0 sorry (12 #print axioms)
- hypotheses: none declared; works over imported records `V : SmoothProjectiveComplexScheme`, `H : HodgeBigradedBettiData V` (fields: analytification, hodgeBigrading, cycleClass — assumed data).
- main content: the full operator algebra of kernel-stable native endomorphisms (`NativeEnd = codimensionCycles →ₗ cycles`): closure of `KernelStable` under 0, id, +, -, smul, comp, pow, finset sums, projective correspondences; block-operator decomposition (kernel/class × kernel/class) with `nativeBlockOperator_reconstruct`, `nativeBlockOperator_eq_iff`; `cohomologyNativeRealizable_iff_classToDefectBlock_zero` (linear lifting classification); `pureClassToDefectOperator_nonGeometric` (nonzero escape block ⇒ NO native realization); defect-quotient dynamics (`cohomologyDefectAction` is a monoid representation; `nonzero_defect_survives_injective_dynamics`).
- name-vs-content: matches content — genuine, unconditional linear algebra over the assumed H/cycle-class data.
- gaps: everything is relative to the unconstructed `HodgeBigradedBettiData`; no geometry is produced.

### GSTClassicalHodgeFullCorrespondenceGSTPlaneCompletion.lean (665 lines)
- decls: 26 theorems, 2 defs, 0 axioms, 0 sorry (17 #print axioms)
- hypotheses: unproven Props (the load-bearing inputs): `FullCorrespondenceGSTPlaneCompleteness G := ∀ q j, ∃ P : GradedCorrespondenceProgram V H 0 q, P.cohomologyEval G origin = (classicalHodgeBasis V H q j).1` (every Hodge basis sheet is the output of one actual correspondence/cut program); `FullCorrespondenceOrbitCyclic`; `FullCorrespondenceNativeOrbitPairingTotal`.
- main content: a pure equivalence web: plane completeness ⟺ orbit cyclicity ⟺ single-program generation ⟺ pairing totality ⟺ `NativeExecutableGSTPlaneCompleteness` (`completedGSTPlane_equivalence_crown`); then `hodge_of_fullCorrespondenceGSTPlane : FullCorrespondenceGSTPlaneCompleteness G → BigradedBettiHodgeStatement V H` and `nativeCycle_of_fullCorrespondenceGSTPlane : … → ∃ Z, H.cycleClass q Z = α` for every rational Hodge α.
- name-vs-content: "Completion" suggests a finished construction; actually a reduction among equivalent unproven hypotheses.
- gaps: the plane-completeness hypothesis is Hodge-conjecture-strength; nothing here produces a program P.

### GSTClassicalHodgeRangeLiftedSpectralOperator.lean (577 lines)
- decls: 31 theorems, 0 defs, 0 axioms, 0 sorry (10 #print axioms)
- hypotheses: crown takes `hlocal : ∀ p α, Nonempty (LocalCyclicRealization V H p α)` (imported hypothesis-record; unproven).
- main content: `cycleClassRangeSection` via `Classical.choose` (projectivity of ℚ-vector spaces); lifted cycle operators with exact commuting cycle-class squares; native class/kernel projections and decompositions; `nativeLift_iff_kernelPerturbation`, uniqueness; `constructive_hodge_of_local_cyclic_realizations : (∀ p α, Nonempty (LocalCyclicRealization …)) → BigradedBettiHodgeStatement V H ∧ (∀ α ∃ Z, cycleClass Z = α) ∧ finite point presentations`.
- name-vs-content: honest — a constructive *upgrade* of an existing criterion, not a proof of it.
- gaps: `LocalCyclicRealization` per class is the unproven input (cyclic spectral generation of each Hodge class).

### GSTClassicalHodgeStrictGraphBettiTrace.lean (527 lines)
- decls: 21 theorems, 0 defs, 0 axioms, 0 sorry (11 #print axioms)
- hypotheses: works over `A : AnalytificationData V` (imported record: topological `space` + `pointsEquiv : ComplexPoint V ≃ space` — the genuine ℂ-analytification topology is assumed, not constructed).
- main content: constructs the degree-one `RightFiniteBettiTrace` for transposed strict graph correspondences *without a trace axiom*: transposed-graph carrier points are exactly (f^an(x), x); analytic section of the right projection; pullback along the section is an exact left inverse; `transposedStrictGraph_normalizedTrace_eq_section`, right-pullback injectivity, carrier/source residuals and `transferObstruction_eq_zero`, `transposedStrictGraph_pushPull_eq_nativePullback`, `transposedStrictGraph_related_iff_nativePullback`.
- name-vs-content: matches — a genuine construction of the Betti trace for graph transposes.
- gaps: limited to transposed *graph* correspondences of endomorphisms; general closed correspondences not treated here; depends on `AnalytificationData`.

### waves/GSTWaveCohomology.lean (478 lines)
- decls: 16 theorems, 19 defs, 2 structures (WaveCell: carry/digit + bounds — pure data; WaveWindow: lo/hi — pure data), 0 axioms, 0 sorry (2 #print axioms)
- hypotheses: none (self-contained 12-cell combinatorics).
- main content: "Wave I": the 12-cell (carry<4, digit<3) system as a discrete de Rham complex: `wave_cell_decomposition` (mixedDensity = horizontal + vertical coboundary + 56·SURVIVE source), row/rectangle Stokes laws (`window_integral_decomposition`, `rectangle_gauss_law`), total matter = 224 (`decide`), 9 harmonic cells, transport cocycle `rowClass R p (M+N) = rowClass R p M + rowClass (4^M·R) p N`, mode spectrum separation of the two Happy chords.
- name-vs-content: "Hodge wave cohomology" is base-3/base-4 digit bookkeeping; `HodgeWave R` ("every window class integral") is tautological (windowClass is ℤ-valued by definition).
- gaps: no actual Hodge theory; the "upgrade" is a relabelling of the digit lattice by ℤ-amplitudes.

### GSTTailFProof.lean (466 lines)
- decls: 25 theorems, 0 defs, 0 axioms, 0 sorry (23 #print axioms)
- hypotheses: `hClimb : GSTInfiniteFourPowerNavigation.four_power_happy_climb` (named unproven Prop: `∀ K ≥ 8, ∃ p ≥ 3, HappyCell (carry4 (4^K) p) (digit3 (4^K) p)` — the third-wave climb, empirically certified at N=1500, proven nowhere); `hB : erdos_even_conjecture_iff_tailF`; `hTower : tailF_tower_primitive`, `hRowMod : tailF_row_primitive_mod729/2187` (named primitives).
- main content: unconditional observation laws (row eye, tower eye, wave face, ontological current), emergent-diagonal stabilization/descent/kill, level-6/7 lattice cycle laws; the terminal `theorem hTailF (hClimb : four_power_happy_climb) : four_power_omega_shadow_wave_tailF` (one-line from the climb), `hTailF_iff_even_conjecture (hB)`, `meta_view_all_classes_all_levels (hB)`, `even_conjecture_of_climb (hB) (hClimb)`.
- name-vs-content: "THE PROOF OF hTailF" is a 3-line reduction to the named climb seam; everything else is proven digit arithmetic.
- gaps: the climb itself (every exponent ≥ 8 owns a Happy row) is the open seam; the file says so explicitly.

### GSTUniversalFourfoldPrimitiveExtraction.lean (409 lines)
- decls: 12 theorems, 1 def, 1 structure, 0 axioms, 0 sorry (6 #print axioms)
- hypotheses: `GeometricFourfoldLefschetzData` fields (verbatim): `hardLefschetz : Function.Surjective cupH2` (**Hard Lefschetz assumed**), `twoStepCompatibility : ∀ beta, primitiveTest (cupH beta) = cupH2 beta`, `nativeCupH` + `nativeNaturality : ∀ D, nativeToHodgeFiberLinear G (nativeCupH D) = cupH (nativeToHodgeFiberLinear G D)`; plus binder `h11 : DivisorsRepresentHodge11 H` (= `∀ beta : ClassicalHodgeFiber V H 1, ∃ D, H.cycleClass 1 D = beta.1` — Lefschetz (1,1) as named Prop, imported).
- main content: for every (2,2) Hodge class α on any fourfold: `Hodge_class_eq_primitive_plus_native_cycle` — α = primitiveHodgeRemainder + nativeToHodgeFiber(algebraicLefschetzCorrection) where the Lβ complement is an explicitly constructed actual algebraic cycle h·D; primitivization of native cycles; Gram-detector rank lemmas; `reconstruct_from_algebraic_primitive_remainder` (primitive algebraicity is EXACTLY what remains).
- name-vs-content: honest — header: "does NOT produce an algebraic representative of α_0 in general and therefore does NOT solve Hodge for arbitrary fourfolds."
- gaps: primitive (2,2) algebraicity is the open residue; Hard Lefschetz and Lefschetz (1,1) are assumed inputs.

### GSTClassicalHodgeCoherentNativeGhostObstruction.lean (393 lines)
- decls: 12 theorems, 0 defs, 0 axioms, 0 sorry (8 #print axioms)
- hypotheses: `E : OmniversalSeparatorGhost G` (imported hypothesis-record with fields `ghost_ne_zero`, `ghost_detects_sheet`, `kills_all_native_programs : ∀ p P Z, separator.detector (P.cohomologyEval G (H.cycleClass p Z)) = 0`, `backward_atomic`); `S : NativeHodgeOrbitSeed`; commuting-square binder `hT`.
- main content: rigid obstruction arithmetic: ghosts kill native cycle classes and descending actions on seeds; `ghostSeedTarget_descendingAction_mismatch_formula` (detector of discrepancy = −sourceCoefficient·detectedBasisSheet ≠ 0); no descending, routed, or finite-tensor-block ambient action realizes the ghost-selected matrix-unit target.
- name-vs-content: matches — negative/obstruction theorems, honestly conditional on the assumed ghost.
- gaps: ghost existence is itself only produced by *failure* of the Hodge statement (contrapositive elsewhere); nothing here closes anything.

### GSTClassicalHodgeSynchronizedDefectOrbit.lean (371 lines)
- decls: 8 theorems, 0 defs, 2 structures, 0 axioms, 0 sorry (4 #print axioms)
- hypotheses: `SynchronizedState` (native cycle + classical cohomology class — pure data); `NativeHodgeOrbitSeed` fields: `hodge_ne_zero : hodge ≠ 0`, `class_eq : H.cycleClass p cycle = hodge.1` (a *witness* that some nonzero Hodge class is algebraic — the assumed seed); crown also assumes `R : ∀ j, GeometryFirstTwoGenerator …` (imported hypothesis-record).
- main content: operator-pair algebra (pairId/Sub/Comp/Smul, geometry-first word `D∘L²∘(I-D)`); `synchronizedDefect_map` (defect equivariance: defect(S.map T) = T.cohomology(defect S)); `targetCycle_spec` (normalized GST word produces an actual native cycle with class = any requested basis vector); `bigradedBettiHodge_of_synchronized_limitless_orbits (seed) (R) : BigradedBettiHodgeStatement V H`.
- name-vs-content: honest reduction: one nonzero algebraic Hodge state per weight + two-generator realizations ⇒ Hodge.
- gaps: both inputs unproven; the seed assumption is a nontrivial slice of the conjecture.

### GSTUniversalPrimitiveHyperplaneRelative.lean (357 lines)
- decls: 9 theorems, 1 def, 2 structures, 0 axioms, 0 sorry (1 #print axioms)
- hypotheses: `SmoothMiddleHyperplaneBetti` fields (verbatim): `gysin_injective : Function.Injective middleGysin` (weak Lefschetz), `self_intersection : ∀ a, middleGysin (middleRestriction a) = ampleCup a` (i_*i^* = L), `relative_exact : ∀ a, middleRestriction a = 0 ↔ a ∈ LinearMap.range relativeToX`; `SmoothCompleteIntersectionMiddleBridge` fields: `restriction_injective` (weak Lefschetz), `complete_intersection_self_intersection`, `cup_power_compatibility`, `gysin_projection`.
- main content: primitive middle class ⟺ restriction to hyperplane vanishes; primitive classes have relative Betti lifts; `no_recovery_from_restriction` (a single hyperplane loses EVERY primitive direction — no linear recovery); boundary-matched cycle differences Z0−Z1 are primitive and nonzero when classes differ; primitive classes restrict primitively to middle dimensions of complete intersections.
- name-vs-content: honest — standard weak-Lefschetz consequences, packaged as records.
- gaps: the topology (weak Lefschetz, Gysin identities) is assumed, not proven; the algebraic transfer from relative Betti lifts to cycles is explicitly the open obligation.

### HodgeDeRhamBridge.lean (346 lines)
- decls: 23 theorems, 5 defs, 0 axioms, 0 sorry (14 #print axioms)
- hypotheses: **POSTULATE H1** `ReverseOntologicalWindow : Prop := ∀ (E N b q : Nat), 0 < graphOntWindow E N b (q+1) → HappyCell (graph E 0 (b+q)).seven.carry (graph E 0 (b+q)).seven.digit` (every strictly positive production window is sourced at a signature/Happy cell — the reverse of the proven forward direction; the file's own "open input of the absorption", NOT an axiom). Also names `HCUniverseChokehold : ∀ K ≥ 8, ∃ p, 4^K/3^p % 3 = 2`.
- main content: the GST↔Hodge dictionary: 6^j = 2^j·3^j (mixed period), CRT comparison `SixAdicIsoAt k x y ↔ DyadicShadowAt ∧ TriadicShadowAt`, finite Tate-twist skew laws, `finite_hodge_characterization : HappyCell C d ↔ 0 < ontDensity C d` (12-cell table, decide), the full ontDensity table (values −54…84), period rebase 4^(1+3m) = 4·64^m; conditional crowns under `ReverseOntologicalWindow`.
- name-vs-content: "the HC absorption" is a relabelling dictionary between digit arithmetic and cohomological vocabulary; the cohomology is CRT on shadows.
- gaps: POSTULATE H1 (reverse window) is open; no actual de Rham/Betti theory beyond CRT arithmetic.

### GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra.lean (336 lines)
- decls: 9 theorems, 2 defs, 1 structure, 0 axioms, 0 sorry (4 #print axioms)
- hypotheses: `RealizedFiniteClosedCorrespondence` field: `realizes_on_points : geometry.RealizesAmbientOnPoints (H := H) cohomologyOperator` (an independently proved cohomological realization on point atoms — supplied per instance); crown hypothesis `hreach : ∀ i j, MatrixUnitReachableByClosedCorrespondences i j` (every GST matrix unit is the cohomology action of a finite word in actual realized closed correspondences — unproven).
- main content: operator pairs from realized correspondences (range stability, atomic-span stability, exact naturality); rational word algebra (zero/smul/add/comp, realizedWordPair); graphs are certified realized correspondences via the spine's pushforward naturality; `algebraicHodgeSubspace_eq_top_of_closedCorrespondenceReachability` (seed + hreach ⇒ whole Hodge fiber algebraic).
- name-vs-content: honest — the arena is built; the reachability input is named.
- gaps: reachability of matrix units by genuine correspondence words is exactly the missing geometry.

### GSTClassicalHodgePointNormalForm.lean (327 lines)
- decls: 10 theorems, 2 defs, 0 axioms, 0 sorry (8 #print axioms)
- hypotheses: none beyond V/H records.
- main content: `realizeFiniteCodimensionPresentation_apply` (pointwise evaluation of a realized finite presentation = finite rational combination of point indicators); `realize_presentationOfNativeCycle` (compact native cycles are reconstructed exactly from their point presentations); normal-form equivalences: `bigradedBettiHodgeStatement_iff_finite_presentations`, `…_iff_point_class_equations`, `…_iff_limitless_global_atlas` (Hodge ⟺ ∃ global fibered atlas, ClassExact ∧ CosmicExact; the cosmic half is unconditional); `nativeLinearMap_eq_zero_of_points` (native operators are determined by their values on points).
- name-vs-content: honest — normal forms of the target, not a proof of it.
- gaps: the ClassExact existence is the Hodge statement itself, restated.

### GSTFinalPrefixOneStep6Infinite.lean (314 lines)
- decls: 11 theorems, 6 defs, 0 axioms, 0 sorry (10 #print axioms)
- hypotheses: `hRightBad : ∀ j, ¬ HappyCell (graph … (b+j))` (badness profile binder in `canonical_infinite_bad_control`).
- main content: unconditional graph-controller arithmetic: zero base carry of the canonical child, all-depth bad-coupled control packaging, past/future synchronized ledger, cross/mixed divergence identities (weighted row/rectangle emergences with arbitrary weights), reverse-code exactness, `canonical_controller_rebase_all_depth` / `action_crown` (coupledOrbit (4^infN) is a literal Nat-action: state at K+L = rebase at K then L).
- name-vs-content: matches (Graph-V2 controller combinatorics).
- gaps: part of the Erdős-digit support stack; carries no Hodge content; the hard existence input lives elsewhere.

### GSTMathboxIndependentGeometricCoordinate.lean (306 lines)
- decls: 11 theorems, 4 defs, 0 axioms, 0 sorry (5 #print axioms)
- hypotheses: none (elementary linear algebra); the "novel universal existence claim … is NOT smuggled in as a new law/axiom" (header).
- main content: third-coordinate functional kills axes 1–2, detects axis 3 (`independent_geometric_third_axis`); radical nonvanishing criteria for the photographed 99·√(·) law; `detected_native_cycle_outside_old_span` (a detector killing all old classes and detecting a new cycle ⇒ the new cycle is outside the old span, arbitrary rank); realized-correspondence fresh-direction certificates.
- name-vs-content: honest; the "mathbox" photographic formula is reduced to coordinate semantics.
- gaps: constructing a detected new cycle for every missing Hodge direction remains an explicit target.

### GSTUniversalSelfProductPrimitive.lean (299 lines)
- decls: 12 theorems, 2 defs, 0 axioms, 0 sorry (4 #print axioms)
- hypotheses: nilpotence `ha : a^(d+1) = 0`, `hb : b^(d+1) = 0` (dimension bound) and `htop : a^d * b^d ≠ 0` (positive top intersection) as binders.
- main content: pure commutative-ring algebra of P_d = Σ(−1)^j a^(d−j) b^j: telescoping `(a+b)P_d = a^(d+1) − (−b)^(d+1)`; middle-Lefschetz kernel membership; integer-coefficient nativeness; top pairing `P_d·b^d = a^d·b^d`; nonzero detection; exact self-intersection `P_d² = (d+1)(−1)^d a^d b^d` (Hodge–Riemann sign shape).
- name-vs-content: honest — "universal" means ring-theoretic; the Künneth/top-degree geometry is explicitly NOT formalized here.
- gaps: no actual X×X cohomology, no positivity of ∫h^d — external.

### GSTWorldtraceMahlerRelativePrecision.lean (296 lines)
- decls: 15 theorems, 6 defs, 3 structures (all `: Prop`), 0 axioms, 0 sorry (9 #print axioms)
- hypotheses (the file IS the assumption hub): `MahlerSharp : ¬∃ (a u : Nat), (a<9 ∧ ¬3∣a) ∧ (¬3∣u) ∧ ∀ q, ∃ S, ∀ s ≥ S, 3^(s+q) ∣ 2u(4^(3^s)−1) − (6a−27)3^s` (the corrected pure-integer Mahler input — no admissible rational candidate receives precision above baseline); `WorldtraceScaledCompression : ∀ K>500, K=3^σ·u, ¬3∣u → CantorianPower K → RelativeLock u`; `WorldtraceMahlerTheory := ⟨mahler, compression⟩`; crown also takes `hB : infinite_controller_ternary_two_chokehold`, `hBIff : erdos_even_conjecture_iff_tailF`, `hOdd : erdos_ternary_2_conjecture_odd` (imported named Props).
- main content: unconditional: witness factorization `W_s(u) = 3^(s+1)(2u·c(s) − 2A(u) + 9)`, baseline divisibility, ghost ⇒ RelativeLock, MahlerSharp ⇒ fracture q ≥ 2, core-spectrum dichotomy. Conditional: extinction `¬CantorianPower K` for K>500, `worldtrace_mahler_no_cantorian` (with `modular_check_base` for K ≤ 500), `worldtrace_mahler_kill_all` (∀ K ≥ 8, ∃ p, digit3 (4^K) p = 2), `worldtrace_mahler_relative_precision_crown : … → WorldtraceMahlerCrown` (noCantorian + killAll + theAct + tailF + fullErdos (∀ n ≥ 9, noTernaryTwo (2^n) = false) + controller).
- name-vs-content: honest conditional theory object; the whole Erdős conclusion is packaged as explicit hypotheses.
- gaps: MahlerSharp and WorldtraceScaledCompression are unproven (Mahler-type 3-adic input); the crown is only as good as its inputs.

### GSTClassicalHodgePiPointTwoGeneratorUnboundedFinale.lean (282 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry (5 #print axioms)
- hypotheses: `G : GeometricCycleClassSpine V H`, `D : ProjectiveDegreeTraceSemantics V H` (imported records); `hpoint : ∀ p (Hodge fiber ≠ ⊥), Nonempty (CodimensionPoint V.X p)`; `R : ∀ p j, ProjectiveTwoGenerator … (seed.sourceIndex) j` (two actual projective primitives per target — unproven).
- main content: one genuine codimension-p point (nonzero by projective degree) is a NativeHodgeOrbitSeed; two projective primitives generate the exact GST rank-one word to every basis direction; `point_twoGenerator_fullOmniverse_crown` (target cycle + N-cohomology packet + three-sector unbounded algebraic branches); `bigradedBettiHodge_of_point_projectiveTwoGenerator_omniverse : … → BigradedBettiHodgeStatement V H`.
- name-vs-content: "UnboundedFinale" is a conditional reduction, not a finale of the conjecture.
- gaps: existence of the ProjectiveTwoGenerator family (and degree-trace semantics record) is the open geometric input.

### GSTClassicalHodgeGeometricPeriodDeterminant.lean (277 lines)
- decls: 6 theorems, 3 defs, 0 axioms, 0 sorry (1 #print axioms)
- hypotheses: `hPeriod : (nativeGSTPeriodMatrix G programs detectors).det ≠ 0` (binder); `UniversalGSTTriangularPeriodGeneration G F : Prop` (per weight, correspondence programs + detectors with upper-triangular period matrix, nonzero diagonal — unproven); `F : Stage2GHodgeFiniteness V H`.
- main content: A = P·M ⇒ det(A) ≠ 0 forces det(M) ≠ 0 (basis-coordinate matrix of native program outputs); `native_cycle_of_nonzero_GST_period_determinant` (every Hodge class gets a cycle from one nonzero period determinant); triangular version; `full_rational_hodge_of_universal_GST_triangular_geometry : UniversalGSTTriangularPeriodGeneration → BigradedBettiHodgeStatement`.
- name-vs-content: honest ("practical improvement" of the criterion), header admits "NEEDS CI RUN LATER".
- gaps: constructing n programs with nonzero intersection determinant on arbitrary V is explicitly NOT postulated — it is the remaining geometric task.

### GSTClassicalHodgePiOneObservableOmniverseFinale.lean (271 lines)
- decls: 6 theorems, 2 defs, 0 axioms, 0 sorry (4 #print axioms)
- hypotheses: `packet : ∀ p α ≠ 0, ∃ x : CodimensionPoint V.X p, ∃ R : ClosedCorrespondenceWindowRealization G (canonicalLiveWindow α), DegreePointVisibleOnCanonicalPacket G D α x R` (one realized spectral observable per live Hodge state with the point visible — unproven); plus G, D records.
- main content: class-local visibility predicates (PointSource/DegreePointVisibleOnCanonicalPacket, proven equivalent); `target_cycle_of_oneObservable_pointPacket` (visible packet ⇒ actual native cycle with class α); `oneObservable_pi_omniverse_crown` (cycle + N-cohomology channels + unbounded causal certificates); `bigradedBettiHodge_of_oneObservablePiPackets : packet → BigradedBettiHodgeStatement`.
- name-vs-content: "OmniverseFinale" = conditional elementwise landing.
- gaps: the per-class packet hypothesis localizes but does not remove the geometric obligation.

### GSTClassicalHodgeLimitlessSeparatorGhost.lean (265 lines)
- decls: 9 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry (4 #print axioms)
- hypotheses: `LimitlessSeparatorGhost` fields: `probe_ne_zero : probe ≠ 0`, `detects_sheet : fiberedPairing (fiberedWeightCoordinates … basis sheet) probe ≠ 0`, `annihilates_atomic : ∀ α ∈ pointCycleClassSpan, fiberedPairing … probe = 0` — a DERIVED obstruction record (constructed from any `BasisAtomicSeparator`).
- main content: separator probes support/annihilate correctly; every algebraic Hodge vector and every graded program-orbit state is invisible to the ghost; `not_hodge_yields_limitless_separatorGhost` (Hodge failure ⇒ Nonempty ghost); `bigradedBettiHodge_of_no_limitless_separatorGhost` (IsEmpty ghost ⇒ Hodge statement).
- name-vs-content: honest contrapositive packaging.
- gaps: proving IsEmpty of the ghost class is the open task (= Hodge).

### GSTGraphV2DescentOntology.lean (261 lines)
- decls: 15 theorems, 0 defs, 0 axioms, 0 sorry (6 #print axioms)
- hypotheses: none.
- main content: exact vertical/horizontal decomposition of the quotient field Q(t,p) = ⌊4^t E/3^p⌋: vertical digit+3·next; horizontal affine step descent(t+1) = carry + 4·descent(t); width-N carry-word blocks; carryWord cocycle; coupledInvariant Euclidean decode and sector bounds; child extreme-sector law; childTail/parentOffset/parentWord/childResidue descent equations.
- name-vs-content: matches (descent-coordinate arithmetic memory of the graph).
- gaps: none for what it claims; pure elementary number theory.

### GSTClassicalHodgeGeneratorwiseAtomicStability.lean (253 lines)
- decls: 8 theorems, 3 defs, 1 structure, 0 axioms, 0 sorry (6 #print axioms)
- hypotheses: `PointClassTransitionKernel` fields: `transition : CodimensionPoint X p → FiniteCodimensionPresentation X p`, `transition_spec : ∀ x, finitePointCycleClassMap p cl (transition x) = T (cl (codimensionPointCycle X p x))` (an explicit finite point-cycle presentation of the transformed class per point generator — unproven for concrete operators); collision theorems also take `hseed : Σ a j • basis sheets ∈ pointCycleClassSpan`.
- main content: AtomicSpanStable ⟺ PointGeneratorStable ⟺ HasFinitePointTransitions; kernel ⇒ global stability; `isEmpty_basisAtomicSeparator_of_transitionKernel` (kernel + cyclic seed ⇒ no separator on selected sheets).
- name-vs-content: honest equivalence machinery.
- gaps: transition kernels and the cyclic atomic seed are the inputs.

### GSTClassicalHodgeCanonicalIncidenceKernelReduction.lean (252 lines)
- decls: 6 theorems, 2 defs, 1 structure, 0 axioms, 0 sorry (3 #print axioms)
- hypotheses: `CanonicalMiddleBettiKernel` (data: kernelClass — the middle Betti class of the correspondence, supplied); `DirectIncidenceProjectionLaw P K κ pt : ∀ x, sndGysin (cup kernelClass (fstPullback (pt x))) = GeometricCycleClass (K.nativePointImage p x)` — the one irreducible point-incidence equation left (unproven input).
- main content: canonicalization of the historical three-layer packet (transpose class = swap pullback; canonical point cylinder; canonical fiber intersection); `geometricIncidencePrimitives_nonempty_iff_directLaw` (the full incidence packet exists ⟺ the direct law); supplied cycleClass/nativeOperator reconstruction from the direct law.
- name-vs-content: honest reduction of interface noise to one law.
- gaps: the direct incidence law itself is the geometric obligation.

### GSTClassicalHodgeCMNativeRationalDescent.lean (243 lines)
- decls: 5 theorems, 0 defs, 0 axioms, 0 sorry (2 #print axioms)
- hypotheses: `hExtended` (coordinate identity: α's basis coordinates = Σ K-coefficients × native cycle class coordinates — binder).
- main content: `rational_native_cycle_of_extended_span` (a rational Betti class that is a finite extension-linear combination of native cycle classes IS the class of an actual rational cycle — no rationality/Galois/degree hypothesis on the extension); range version; rational coefficient projection; multisource CM field spanning.
- name-vs-content: honest descent lemma ("coefficient-descent part of the CM surface proof").
- gaps: header: "NEEDS CI RUN LATER"; the geometric spanning hypothesis must be instantiated by real CM geometry.

### GSTClassicalHodgeGlobalSheetCosmos.lean (240 lines)
- decls: 14 theorems, 0 defs, 0 axioms, 0 sorry (4 #print axioms)
- hypotheses: none beyond V/H.
- main content: global sheet probes (`Finsupp.lapply`) and global sheet matrix units on `FiberedHodgeAddress = (Σ p, BasisIndex) →₀ ℚ`; probe/matrix-unit algebra (comp, comp_zero, target weight); `sheetMatrixUnit_intertwines_hodgeMatrixUnit` (global action intertwines the rank-free Hodge matrix units at fixed weight); forget-multiplicity compatibility; `global_sheet_cosmos_crown`.
- name-vs-content: honest internal GST linear algebra.
- gaps: none claimed; all unconditional.

### GSTWeilForcingFrameCertificate.lean (234 lines)
- decls: 15 theorems, 6 defs, 0 axioms, 0 sorry (3 #print axioms)
- hypotheses (Part C binders, "declared as hypotheses; external leaves E8, E9"): `heuler : chi = h0 − h1 + h2 − h3 + h4`, `hdual3 : h3 = h1`, `hdual4 : h4 = h0` (Serre duality), `hRR : chi = (m*m)*8` (Riemann–Roch with td=1).
- main content: Part A: exact ℚ polynomial arithmetic of the Weil projector P_W(t) = −((t−25)(39t−79)(t²−30t+625))/44000000 — expansion, correspondence coefficients a_0…a_4, key identity pwN + G_W·M = 44000000, spectral evaluations (P_W=1 on Weil factor, 0 on mixed/ambient). Part B: exterior sign-count certificate INT W_R² = 8 by full `decide` over the eight ±1 monomial pairs. Part C: End-mass arithmetic: chi = +8m² > 0, h0 + h2/2 = h1 + 4m², no-go bounds (h2 ≥ 8m²−2 for simple carriers).
- name-vs-content: honest — "exact finite algebra"; scheme-level statements (GAGA, HRR, Künnteth unimodularity, external leaves E1…E9) explicitly outside the certified scope.
- gaps: the geometric identification of the Weil plane with ℚ[t]/(t²+14t+625), correspondence-action compatibility, and the RR/duality inputs are external.

### GSTU2DAtomicBridge.lean (228 lines)
- decls: 8 theorems, 0 defs, 0 axioms, 0 sorry (5 #print axioms)
- hypotheses: `hInv : PhysicalInvariant A st` (defined Prop), cell-gluing binders in the emergence laws.
- main content: U-charge = 8C − carryPotential; Equation-III potential as a mixed boundary; weighted row/rectangle emergence laws with arbitrary weights; source extraction/divisibility; infoPotential nonpositivity.
- name-vs-content: matches (arithmetic bridge between coupled-U chart and 2D mixed system).
- gaps: none claimed; unconditional ℤ-identities.

### GSTClassicalHodgeGradedSeparatorBackpropagation.lean (226 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry (5 #print axioms)
- hypotheses: detector binders (`hell : ∀ Z, ell (cycleClass q Z) = 0`); spine G.
- main content: pullback of detectors through graded geometric programs (`pullbackDetector`); range/atom annihilation pullback; `exists_backpropagated_separator_of_basis_transport` (program transporting a source basis vector with nonzero coefficient into a detected target ⇒ separator backpropagates to the source weight); `basisSeparator_kills_every_program_cycle`, `kills_geometricOrigin_orbit`, `no_basisSeparator_of_origin_reaches_basis`.
- name-vs-content: honest: an obstruction must be primitive w.r.t. every descending geometric channel.
- gaps: no closure — sharpens where obstructions can live.

### GSTGraphV2NonEuclidean.lean (222 lines)
- decls: 5 theorems, 9 defs, 6 structures (SevenAxes, Overlay, Vertex, Graph, PhysicalProjection, ForwardPath — all pure data), 0 axioms, 0 sorry (0 #print axioms)
- hypotheses: none.
- main content: the seven-axis data model (x, x', y, y'∈Space, z, z', nAxis) with `axes R N p`, WitnessAt (digit 2 in null/gst+ space); embeddings of the old arithmetic sheet (`physicalProjection`, `projectPhysicalCell`); forward-path calculus (edges exact, rebase exact/assoc, x/nAxis coordinates exact).
- name-vs-content: matches — a data model with trivial theorems.
- gaps: definitional layer only; no mathematical content proven.

### GSTClassicalHodgeAmbientCorrespondenceKernelAction.lean (214 lines)
- decls: 3 theorems, 0 defs, 2 structures, 0 axioms, 0 sorry (3 #print axioms)
- hypotheses: `AmbientBettiIntersectionCalculus` fields (verbatim): `cup`, `sndGysin`, `fstGysin` (maps) + `swap_cup : swap (cup a b u v) = cup a b (swap u) (swap v)`, `sndGysin_swap : sndGysin (swap z) = fstGysin z`, `fstGysin_swap` — the standard cup/Gysin compatibilities of X_an×X_an ASSUMED as fields; `MiddleBettiCorrespondenceKernel` fields: `kernelClass`, `transposeClass`, `transposeClass_eq_swap : transposeClass = swapCohomologyPullback (2*d) kernelClass`.
- main content: the classical correspondence action T_C(α) = p₂_*([C] ∪ p₁^*α) constructed from the calculus; `transpose_action_apply` (transpose action = fstGysin of kernel cup snd-pullback — cohomological factor-swap/incidence compatibility, no formal coefficient transpose); transpose kernel involution; action totality.
- name-vs-content: honest — "the ambient construction is total by construction".
- gaps: the intersection calculus itself (cup, Gysin, and their laws) is an assumed record, not constructed geometry.

### GSTClassicalHodgeGeometricCycleClassSpine.lean (213 lines)
- decls: 5 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: **the central spine record**, fields verbatim: `algebraic_is_hodge : ∀ p Z, H.cycleClass p Z ∈ rationalHodgeSubspace (H.hodgeBigrading p)` (algebraic ⇒ (p,p)); `pushforward_naturality : ∀ p f, GeometricPushforwardNaturality V H p f`; `principalCutPair : ∀ p, GradedCycleClassOperatorPair V H p (p+1)`; `principalCutPair_native`; `principalCut_hodge : α ∈ Hodge(p) → cohomologyOperator α ∈ Hodge(p+1)`.
- main content: derived consequences (point classes are Hodge, projective operator pairs, correspondence-span kernel stability, principal-cut transport of algebraic Hodge classes, codim-0 fundamental class is Hodge). **Self-audit:** `zeroCycleClassSpine` (the zero cycle-class map satisfies EVERY spine field) and `spine_laws_do_not_force_hodge` (nonzero Hodge fiber ⇒ a spine coexists with failure of the Hodge statement) — the spine interface is provably non-determining.
- name-vs-content: "genuine geometric cycle-class spine" is an interface, and the file proves the zero countermodel.
- gaps: the actual classical cycle-class construction (with nonzero values) is not supplied anywhere; consumed as assumption by ~30 files of this batch.

### GSTCanonicalPointGeometryStage2G.lean (206 lines)
- decls: 5 theorems, 0 defs, 0 axioms, 0 sorry (3 #print axioms)
- hypotheses: `pt : AllCodimensionPointBettiClasses H` (a coherent family of point Betti fundamental classes — supplied data).
- main content: `pointGeneratedHodgeData` (cycleClass built from irreducible-subvariety point data); exactness on point cycles; range = span of point fundamental classes; `pointGeneratedHodgeStatement_iff_actual_point_span` (Hodge ⟺ every rational Hodge subspace ≤ span of actual point fundamental classes, per codimension); native projection finite-source/residual and Euler identities.
- name-vs-content: honest re-encoding of the target in point-geometric semantics.
- gaps: analytic fundamental classes and the spanning theorem are the "next geometric integration" (not here).

### GSTGraphV2CoupledUPhysicalBridge.lean (205 lines)
- decls: 8 theorems, 4 defs, 1 structure (PhysicalState: data), 0 axioms, 0 sorry (3 #print axioms)
- hypotheses: `hInv : PhysicalInvariant A st` (defined Prop: parentSeed + 4·parentOffset = childResidue + A·childCarry).
- main content: potential rewrite through the fifth coordinate; base-4 digit prefix reconstruction `Σ 4^i·digit = S mod 4^N`; horizontal flux telescopes (raw and closed forms); `coupled_potential_is_horizontal_base4_flux`; prefix+tail reconstruction and extensionality.
- name-vs-content: matches (elementary base-4 arithmetic).
- gaps: none claimed.

### GSTClassicalHodgeLimitlessDefectOrbitLanding.lean (200 lines)
- decls: 7 theorems, 0 defs, 2 structures, 0 axioms, 0 sorry (3 #print axioms)
- hypotheses: `DefectZeroPointSeed` field: `class_eq : H.cycleClass p (codimensionPointCycle V.X p point) = (classicalHodgeBasis V H p source).1` (a point cycle class EQUALS a basis vector — assumed); `GenuineTargetTransport` fields: `intertwines : TensorIntertwinesAt pair source target point`, `mass_ne_zero : pointTransitionMass pair.cycleOperator point ≠ 0`.
- main content: seed atom has zero defect; raw/normalized orbit states have zero defect by equivariance; `normalizedState_hodge_exact` (Hodge face = target basis vector); `normalizedState_cycleClass` (native face is an actual cycle representing the target); `bigradedBettiHodge_of_defect_orbits` (seed + transports to every sheet ⇒ Hodge statement).
- name-vs-content: honest reduction.
- gaps: both structures are unproven geometric inputs (equivalent slices of the conjecture).

### GSTClassicalHodgeSelfExpandingClosure.lean (198 lines)
- decls: 5 theorems, 4 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `HodgeRecursiveRealization` fields include `hodgeState_realizes_cycle : ∀ p α, algebraic (hodgeState p α) → ∃ Z, D.cycleClass p Z = α.1` (semantic algebraicity ⇒ actual cycle); the crown hypothesis is `HodgeStateClosure` (every Hodge state in the state-closure of cycle seeds).
- main content: cycle seeds are algebraic; state closure propagates algebraicity; `exactHodge_of_hodgeStateClosure` / `exactHodge_of_completeCosmicClosure` / `finiteCombination_of_completeCosmicClosure` (closure ⇒ exact rational Hodge, and its finite-combination wording).
- name-vs-content: honest re-encoding of Hodge as reachability in an abstract cosmos.
- gaps: the cosmos is abstract bookkeeping; the closure hypothesis is exactly the missing content.

### GSTClassicalHodgeSynchronizedSeedFiberedLanding.lean (195 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry (3 #print axioms)
- hypotheses: `SeedFiberedMassBalance S : classicalHodgeMass V H p S.hodge = nativeCycleMass V p S.cycle` (the single scalar compatibility — unproven).
- main content: canonical Hodge/native marginals of a synchronized seed; `exists_seedJointState_iff_massBalance` (joint fibered representative ⟺ mass balance); joint state reconstructs the seed cycle, Hodge face, and has zero defect; `exists_defectZero_seedJointState_iff_massBalance`.
- name-vs-content: honest gluing criterion.
- gaps: the mass balance law is the open scalar conservation input.

### GSTClassicalHodgeOmniverseProjectiveApexSpokes.lean (193 lines)
- decls: 5 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry (4 #print axioms)
- hypotheses: `ProjectiveApexL2Spoke` fields: `map : ComplexSchemeEndomorphism V`, `naturality : GeometricPushforwardNaturality V H p map.hom`, `source_action : naturality.cohomologyPushforward S.hodge.1 = (liftFiniteHodgeOperator (pairBasisIndex source j) (diagonalLefschetzQ 2 2) S.hodge).1` (the localized two-slot L² equation at the single apex state — unproven).
- main content: apex normalization nonzero; `operatorPair_on_apex` (geometric pushforward = nonzero scalar • target basis); `targetCycle_spec` (one spoke ⇒ exact target basis cycle); `hodge_weight_of_projectiveApexL2Spokes` (spoke family ⇒ whole Hodge weight in cycle-class range).
- name-vs-content: honest — one genuine map per target sheet suffices, IF supplied.
- gaps: existence of L² spokes (maps whose pushforward equals the Lefschetz action at the seed) is the geometric input.

### GSTClassicalHodgeCrossCarrierGeometricTransfer.lean (190 lines)
- decls: 3 theorems, 4 defs, 1 structure, 0 axioms, 0 sorry (1 #print axioms)
- hypotheses: `CrossCarrierTransfer` fields: `native`, `betti` (linear maps) + `naturality : ∀ Z, J.cycleClass q (native Z) = betti (H.cycleClass p Z)` ("must be proved from geometry" — per instance).
- main content: identity/compose/add/rescale of transfers; `native_range_preserved`; `native_target_of_nonzero_geometric_period` (transported class = k•target with k≠0 ⇒ ∃ actual target cycle with exactly that class — the CM surface-switch normalization); composed-period version.
- name-vs-content: honest abstract lemma; header: "No Hodge conjecture, CM-paper claim, or ghost-extinction statement is asserted unconditionally."
- gaps: constructing the surface/divisor kernels and proving the period identity are "separate nontrivial geometric problems".

### GSTHodgeChannelFinale.lean (186 lines)
- decls: 5 theorems, 1 def, 1 structure, 0 axioms, 0 sorry (4 #print axioms)
- hypotheses: `Stage2GHodgeFiniteness` field: `finite : ∀ p, FiniteDimensional ℚ (rationalHodgeSubspace (H.hodgeBigrading p))` (classical finite-dimensionality of rational Hodge fibers — standard but NOT constructed by the pinned stack; recorded separately); the obligation Prop `Stage2GCanonicalBasisAlgebraizationObligation := ∀ p, Nonempty (CanonicalBasisCycleSupply …)`.
- main content: the irreducible frontier equivalence `canonical_basis_algebraization_iff_hodge : Stage2GCanonicalBasisAlgebraizationObligation ↔ BigradedBettiHodgeStatement` (under finiteness, "every vector of Mathlib's canonical finite basis of H^(p,p)_ℚ is the class of a native cycle" is EXACTLY the Hodge statement); channel-quotient generation is downstream; `hodge_channel_finale_crown` (unbounded same-weight rank + the equivalence + quotient implication).
- name-vs-content: honest: "all GST/Wave-II architecture above that sentence is derived, not assumed."
- gaps: the finiteness layer and the basis-cycle supply are both unproven inputs.

### GSTClassicalHodgeOmniversalClosure.lean (182 lines)
- decls: 7 theorems, 2 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `HodgeClosureSemantics` fields: `seed_algebraic`, `event_preserves_algebraic`, `hodgeNode_realizes_cycle : ∀ q α, algebraic (hodgeNode q α) → ∃ Z, D.cycleClass q Z = α.1`; crown hypothesis `CompleteUnaryClosure` / `CompleteHyperClosure K` (+ `hStable`).
- main content: `exactHodge_of_completeUnaryClosure` (closure of Hodge nodes from algebraic seeds ⇒ EveryHodgeClassIsRationalAlgebraic); hyper-event version (cup/Gysin/correspondence as certified hyper-events); finite-combination wordings; contrapositive diagnostics `not_completeUnaryClosure_of_not_exactHodge` (prevents graph-connectivity masquerading as proof).
- name-vs-content: honest closure-semantics re-encoding.
- gaps: the closure property is the open content.

### GSTClassicalHodgeAnalytificationFunctoriality.lean (180 lines)
- decls: 6 theorems, 4 defs, 3 structures, 0 axioms, 0 sorry (5 #print axioms)
- hypotheses: `ComplexSchemeEndomorphism` (hom + over_base — data); `AnalyticEndomorphism` field `continuous_toFun : Continuous (transportedPointMap A algebraic)` (continuity per map); `EndomorphismAnalytification` fields: `lift`, `lift_algebraic`, `lift_id`, `lift_comp : lift (f.comp g) = (lift f).comp (lift g)` (functoriality for ALL endomorphisms — the genuine analytification functoriality assumed as a record).
- main content: exact point-level action of C-scheme endomorphisms (id/comp laws, no topology); transported maps through `pointsEquiv`; TopCat morphism packaging with id/comp compatibility.
- name-vs-content: honest — "No algebraic-cycle or Hodge conclusion occurs here."
- gaps: no actual analytification functor is constructed (only the record interface).

### GSTSquarePureHodgeDuality.lean (178 lines)
- decls: 7 theorems, 4 defs, 0 axioms, 0 sorry (5 #print axioms)
- hypotheses: none (internal GST world-cosmology).
- main content: mirror involution on pure diagonal coordinates; `worldDual_pureDiagonalState` (Poincare complement of a pure diagonal cell = mirrored cell); restriction to the pure-Hodge submodule is an involutive ℤ-linear automorphism; `pureHodgeLinearEquiv_conjugates_duality` (under canonical coordinates the duality IS reversal of the diagonal string); `square_pure_hodge_duality_crown`.
- name-vs-content: "pure-Hodge duality" is GST-internal combinatorics on rectangular worlds, not classical pure Hodge structures.
- gaps: none claimed; unconditional.

### GSTClassicalHodgeExactKugaSatakeCliffordAction.lean (172 lines)
- decls: 10 theorems, 0 defs, 0 axioms, 0 sorry (1 #print axioms)
- hypotheses: `hwinv : w * winv = 1` (right inverse binder) or quadratic-relation binders.
- main content: the exact Kuga–Satake tensor j_w(v)(a) = v·a·w in any ℚ-algebra: ℚ-linearity in both arguments; `exactKugaSatakeMap_one` (evaluation at 1 = v·w); injectivity when w has a right inverse; composition with REVERSED right multipliers; scaling; cancellation; quadratic-relation inverses (rational explicit) and injectivity thereof.
- name-vs-content: honest: "We do not assert that the corresponding Hodge tensor is ALGEBRAIC on a K3 surface or any abelian variety."
- gaps: header "NEEDS CI RUN LATER"; no Clifford algebra instance, no K3/abelian geometry.

### GSTClassicalHodgeRealizedCorrespondenceCyclicSpectralFinale.lean (172 lines)
- decls: 5 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry (4 #print axioms)
- hypotheses: `RealizedCyclicSpectralCertificate` fields (verbatim): `word : RealizedCorrespondenceWord V H p`, `eigenvalue`, `eigenvalue_injective : Function.Injective eigenvalue`, `eigenvector : ∀ i, (realizedWordPair word).cohomologyOperator (classicalHodgeBasis V H p i).1 = eigenvalue i • (classicalHodgeBasis V H p i).1` (one actual closed-correspondence observable with SIMPLE spectrum on the whole Hodge basis), `coefficient`, `coefficient_ne_zero`, `seedCycle`, `seedClass_spec : H.cycleClass p seedCycle = ∑ i, coefficient i • (classicalHodgeBasis V H p i).1`.
- main content: certificate ⇒ spectral operator (atomic stability derived); cyclic seed in atomic span; `weight_hodge` (rational Hodge subspace ≤ pointCycleClassSpan); `exactHodge_of_realizedCyclicSpectralCertificates` (∀ q, Nonempty certificate ⇒ EveryHodgeClassIsRationalAlgebraic) + finite-combination wording.
- name-vs-content: honest reduction; certificate existence = the open input.
- gaps: constructing a simple-spectrum correspondence + cyclic algebraic seed on arbitrary V is exactly the hard geometry.

### GSTClassicalHodgeCrossCarrierGSTProgramFusion.lean (170 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry (1 #print axioms)
- hypotheses: `R : CrossCarrierTransfer`, `Tmap : CrossCarrierTransfer` (incoming/outgoing correspondences — supplied), spine G.
- main content: GST graded programs instantiate cross-carrier transfers; three-stage sandwich (auxiliary → GST cuts → target) with full naturality; `sandwich_output_algebraic` (native output always lands in the target cycle-class range); `normalized_sandwich_target` (nonzero period identity k•target ⇒ actual algebraic cycle for target).
- name-vs-content: honest fusion file ("NEEDS CI RUN LATER").
- gaps: no global existence of incoming/outgoing correspondences assumed or proven; period identity must come from Kuga–Satake/Gale-type geometry.

### GSTClassicalHodgeArbitraryRankChargeFrames.lean (165 lines)
- decls: 3 theorems, 1 def, 0 axioms, 0 sorry (2 #print axioms)
- hypotheses: `hdet : (chargedFrameHodgeMatrix G ell E).det ≠ 0` (binder); `UniversalGSTChargedGeometricFrameGeneration G F : Prop` (in every weight some finite collection of genuine correspondences constructs a charged frame with nonsingular Hodge matrix — named, checkable, NOT an axiom, NOT proven).
- main content: native charged frame (spine column + geometric charge wedges) at FULL Hodge-fiber rank; `chargedFrameInverseCycle_spec` (determinant ≠ 0 ⇒ explicit native cycle with exactly the prescribed class); `every_hodge_class_of_nonzero_charged_geometric_frame`; `exact_hodge_of_universal_charged_geometric_frames`.
- name-vs-content: honest; header: "The purely geometric existence statement … is NOT proved by this module. Rewriting it as an axiom or a law would hide precisely the universal Hodge difficulty."
- gaps: full-rank frame existence is the open geometric core.

### GSTFourPowerAffineBadState.lean (160 lines)
- decls: 9 theorems, 1 def, 0 axioms, 0 sorry (4 #print axioms)
- hypotheses: none.
- main content: `CommonTwo K ⟺ AffineCommonTwo K`; affine-peel equivalences per residue class mod 3 (lowest trit 0/1/2 reduce to exact tail pairs peel0/peel1/peel2); state-3 transition; no-affine-common-two restatements.
- name-vs-content: matches — digit-combinatorics equivalences for the Erdős-type problem.
- gaps: none claimed; the hard existence content lives in the climb seam.

### GSTClassicalHodgeOpenAIGeometryNoncircularityAudit.lean (157 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry (1 #print axioms)
- hypotheses: none (audit file); operates on imported `GeometricSourcePeriodCertificate`.
- main content: anti-circularity: `certificateOfAlreadyAlgebraicBasis` (the IDENTITY correspondence turns any basis cycle into a certificate — so generic certificates are equivalent to basis-cycle witnesses); `geometricCertificate_iff_basisCycle`; `completeCertificates_iff_basisCycleSupply`; `completeCertificates_iff_exactHodge` (universal certificate existence ⟺ BigradedBettiHodgeStatement — "MUST NOT be made into a new axiom"); separators forbid certificates and vice versa.
- name-vs-content: honest audit preventing a logical cycle in the proof graph.
- gaps: by design proves no new geometry; it fences the circular direction.

### GSTUniversalPrimitiveDivisorConstruction.lean (153 lines)
- decls: 3 theorems, 1 def, 0 axioms, 0 sorry (2 #print axioms)
- hypotheses: `degree : ClassicalHodgeFiber V H 1 →ₗ[ℚ] ℚ` (a true intersection-pairing degree functional — supplied), `hdegree ≠ 0`, `h11 : DivisorsRepresentHodge11 H` (Lefschetz (1,1) as named Prop).
- main content: p=1 universal primitive normalization D ↦ D − (deg(D·h^{d−1})/deg(h^d))·h: `normalizeNativeDivisor_primitive` (degree zero against h^{d−1}), exact class agreement, `nativePrimitiveDivisorOf_correct` (every primitive rational (1,1) Hodge class is the class of an actual rational algebraic divisor).
- name-vs-content: honest — the p=1 case only, via Lefschetz (1,1) whose analytic proof is outside the repo.
- gaps: nothing for p ≥ 2 ("still-open middle primitive Hodge classes"); degree functional supplied abstractly.

### GSTClassicalHodgeGeneralSpaceRealization.lean (150 lines)
- decls: 4 theorems, 6 defs, 0 axioms, 0 sorry (2 #print axioms)
- hypotheses: spine G (imported record).
- main content: the even Betti universe as a `GeneralSpace` (points = Σ p, H^{2p}; paths = genuine geometric-program reachability); `bettiRealization`; HodgeLocus/NativeLocus; `nativePartialRealization` with `nativeLocus_pathClosed` (algebraic locus closed under all genuine paths — from the master naturality law); `exactHodge_iff_hodgeLocus_le_nativeLocus` (the Hodge conjecture IS the locus inclusion).
- name-vs-content: honest re-encoding in General Space Theory vocabulary.
- gaps: the inclusion is the open statement; GST adds language, not mathematics.

### GSTClassicalHodgeGSTExactFinale.lean (145 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry (5 #print axioms)
- hypotheses: `G : GeometricCycleClassSpine V H`, `M : NativeMassCycleClassBridge V H` (imported hypothesis-record: the native-mass/conserved-charge bridge), `R : CanonicalSpineGSTProgramFamily G M := ∀ p j, CanonicalSpineGSTProgram G M p j` (source-specific GST programs matching the GST action on the canonical spine source — unproven).
- main content: `all_basis_separators_empty`; `gst_bigradedBettiHodge : (G, M, R) → BigradedBettiHodgeStatement V H`; `gst_everyHodgeClassIsRationalAlgebraic` ("EXACT RATIONAL HODGE CONJECTURE — ALGEBRAIC-CYCLE FORM"); finite-combination and finite-presentation wordings.
- name-vs-content: **largest name-vs-content gap of the batch**: titled "Exact Finale" with theorems named `gst_everyHodgeClassIsRationalAlgebraic`, but all of it is conditional on three unproven records (M and R in particular).
- gaps: NativeMassCycleClassBridge and the canonical-spine GST program family are exactly the missing geometry.

### GSTClassicalHodgeGeometricCorrespondencePolynomialCalculus.lean (143 lines)
- decls: 3 theorems, 2 defs, 0 axioms, 0 sorry (3 #print axioms)
- hypotheses: eigenvector binder `hT : T.cohomologyOperator α = λ • α`.
- main content: Horner compilation of rational coefficient lists into the realized-correspondence expression algebra (identity = the actual diagonal correspondence); `hornerExpr_on_eigenvector` (geometric polynomial acts by scalar Horner value — the socket for spectral isolation); `hornerExpr_cycleClass_natural`, `hornerExpr_range_stable`.
- name-vs-content: matches.
- gaps: none claimed; algebra only.

### GSTClassicalHodgeStrictCorrespondenceChainTranspose.lean (140 lines)
- decls: 4 theorems, 0 defs, 0 axioms, 0 sorry (3 #print axioms)
- hypotheses: `A : AnalytificationData V` (imported record).
- main content: coordinate-swap homeomorphism between the intrinsic analytic carriers of K and K^t (isomorphism with inverse); analytic left/right transpose laws; singular-chain-level transpose compatibility (`transposeChain_left/right`).
- name-vs-content: matches.
- gaps: carrier-level only; cohomology transpose lives elsewhere.

### GSTGraphV2FourPowerRelocationClosure.lean (137 lines)
- decls: 9 theorems, 0 defs, 0 axioms, 0 sorry (11 #print axioms)
- hypotheses: intended: `four_power_happy_climb` (via `four_power_happy_ge_three`). **ANOMALY:** lines 24 and 76 call `GSTInfiniteFourPowerNavigation.four_power_happy_ge_three (K+1) (by omega)` / `… K hK` — only TWO of the THREE explicit arguments required by its declaration `(hClimb : four_power_happy_climb) (k : Nat) (hk : 8 ≤ k)` (GSTInfiniteFourPowerNavigation.lean:148-152). Other call sites (GSTFourPowerDirectExistenceFromHappy.lean:133) pass all three. `four_power_happy_climb` is proven NOWHERE in the repo (it is the declared open seam).
- main content (as named): `four_power_happy_propagates`, base witnesses at K = 5/6/8 (unconditional, via digit-overlap bases), `four_power_happy_all_from_eight` (climb-dependent), `four_power_graph_forcing`, `four_power_creation_master`, `four_power_direct_existence : FourPowerDirectExistence` (= ∀ K ≥ 5, K ≠ 7 → CommonTwo K — the Erdős digit-two statement), `four_power_closed_interface_crown`.
- name-vs-content: claims the direct arithmetic target "outright"; the proof chain bottoms out at the unproven climb, and the invocation appears to silently drop the climb argument.
- gaps: **integrity risk**: unless an alternate elaboration resolves the 2-argument call, this file does not compile as written, and its "closed" Erdős interfaces are climb-conditional. Flag for CI verification.

### GSTProjectiveOverC.lean (134 lines)
- decls: 4 theorems, 0 defs, 2 structures, 0 axioms, 0 sorry (4 #print axioms)
- hypotheses: none — genuine Mathlib geometry: `complexBase := Spec (.of ℂ)`, `projectiveSpace n := Proj (MvPolynomial.homogeneousSubmodule …)`, structure map via `Proj.toSpecZero`.
- main content: `ProjectiveOverC` (n, closed immersion into Proj, over_base compatibility); `SmoothProjectiveComplexScheme` (X + Smooth + projective witness); `exists_closed_projective_embedding`, `smooth_projective_geometry_crown`.
- name-vs-content: matches — the real geometric carrier of the whole classical side.
- gaps: no Hodge data at all here (that is `HodgeBigradedBettiData`, imported from GSTGeometricRealizationStage2G with assumed analytification/bigrading/cycleClass fields).

### GSTClassicalHodgeClosedCorrespondenceFailurePacket.lean (128 lines)
- decls: 4 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry (3 #print axioms)
- hypotheses: `UnreachableCosmicSheet` is a DERIVED obstruction record (separator + `unreachable : ¬ ClosedCorrespondenceHitsSheet sheet` + cosmic_exact).
- main content: `basisSeparator_forbids_closedCorrespondenceHit`; `not_hodge_yields_unreachableCosmicSheet` (Hodge failure ⇒ an exact limitless GST diagonal generator unreachable by ANY finite rational word of realized closed correspondences from ANY point); `hodge_iff_no_unreachableCosmicSheet` (exact equivalence at the frontier).
- name-vs-content: honest failure-packet packaging.
- gaps: ruling out unreachable sheets = the remaining cosmology task (= Hodge).

### GSTClassicalHodgeSeparatorPointClosureLift.lean (127 lines)
- decls: 4 theorems, 0 defs, 0 axioms, 0 sorry (3 #print axioms)
- hypotheses: `hlive : ProjectivelyLiveSource n (immersion x)` (binder).
- main content: descended separator successor lies in the singleton closure of its source (via closed-immersion embedding topology); canonical point of the reduced point-closure scheme; successor ≠ generic point; lift crown.
- name-vs-content: matches ("No Hodge datum occurs").
- gaps: none claimed.

### GSTResearchFullOrbitZetaSynthesis.lean (123 lines)
- decls: 2 theorems, 0 defs, 0 axioms, 0 sorry (2 #print axioms)
- hypotheses: `hActualMeasurement : ((read (geometricHodgeClass G Z) : ℚ) : ℝ) = zetaAtS * (∑' m, indexedKernel 2 2 m)` (the corrected zeta-series measurement equation for a source cycle), `hirred : ActualHodgeCorrespondenceIrreducible` (geometric irreducibility of the correspondence action), `hZeta ≠ 0`; all-weight version assumes such sources for every nonzero fiber.
- main content: `every_hodge_class_from_corrected_zeta_constructed_orbit` (measured nonzero source + irreducibility ⇒ every Hodge class has a cycle); `full_hodge_of_Research_corrected_zeta_native_orbit : … → BigradedBettiHodgeStatement`.
- name-vs-content: honest ("a conditional universal Hodge route, not the completed unconditional Hodge conjecture").
- gaps: the measurement equation and irreducibility are explicit hypotheses (see the audit file GSTResearchZetaMeasurementAudit for why a free zeta scalar is circular).

### GSTClassicalHodgePointClosureIrreducible.lean (113 lines)
- decls: 5 theorems, 0 defs, 0 axioms, 0 sorry (4 #print axioms)
- hypotheses: none.
- main content: point-closure ideal support = closed set; range of the point-closure inclusion = closure {x}; homeomorphism to the topological closure; singleton closures are irreducible ⇒ every pointClosureScheme is an IrreducibleSpace; canonical generic point.
- name-vs-content: matches (genuine Mathlib scheme/topology).
- gaps: none claimed.

### GSTGraphV2PerfectPowerAncestry.lean (112 lines)
- decls: 5 theorems, 0 defs, 0 axioms, 0 sorry (4 #print axioms)
- hypotheses: none.
- main content: `power_origin_observables_exact` (graph(4^K, t, p) observables = graph(1, K+t, p) observables — carry, digit, eventCode, uCharge, mixedCharge, crossingCharge, survive); Happy/event-eight invariance; perfect-power rebasing identities.
- name-vs-content: matches.
- gaps: none claimed.

### GSTClassicalHodgePointReducedGeometricSpine.lean (105 lines)
- decls: 2 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry (2 #print axioms)
- hypotheses: `PointReducedGeometricCycleClassSpine` fields (verbatim): `pointClass_is_hodge : ∀ p x, H.cycleClass p (codimensionPointCycle V.X p x) ∈ rationalHodgeSubspace (H.hodgeBigrading p)`, `pushforward_kernelStable : ∀ p f, KernelStable (smoothProjectiveNativePushforward V f p)`, `principalCut : PrincipalCutKernelRealization`.
- main content: point normal form upgrades point Hodge type to ALL native cycles (`algebraic_is_hodge`); manufactures the kernel-reduced and full historical spines.
- name-vs-content: honest interface reduction (whole-cycle field made redundant).
- gaps: the three fields are the non-packaging data (still assumptions).

### GSTResearchZetaMeasurementAudit.lean (104 lines)
- decls: 1 theorem, 2 defs, 0 axioms, 0 sorry (1 #print axioms)
- hypotheses: none (audit).
- main content: `freely_adjusted_zeta_certificate_iff_nonzero_native_class` — with a FREE real zeta multiplier, the corrected-series certificate is EQUIVALENT to the mere existence of a nonzero native class (tsum = −1 lets the coefficient absorb anything); hence a free zeta scalar adds NO geometry. The genuinely new input must be a FIXED analytic zeta value + canonical period + proved equality + realized correspondences.
- name-vs-content: honest adversarial audit ("guards the original Hodge conjecture from an accidental circularity").
- gaps: by design; it fences, not proves.

### GSTClassicalHodgeCMExtendedRangeRigidity.lean (93 lines)
- decls: 2 theorems, 0 defs, 0 axioms, 0 sorry (1 #print axioms)
- hypotheses: none (field K/ℚ arbitrary).
- main content: `finiteExtendedNativePresentation_iff_nativeRange` (a rational Betti class is in the ℚ-algebraic range ⟺ it is a finite K-linear combination of native cycle classes, for ANY extension K/ℚ — backward by coefficient descent); `hodgeSubspace_le_extendedNative_iff`.
- name-vs-content: honest rigidity/descent equivalence for CM outputs over ℚ̄.
- gaps: header "NEEDS CI RUN LATER"; recognizes but does not produce algebraicity.

### GSTClassicalHodgeCrossCarrierSelfProductCompatibility.lean (91 lines)
- decls: 2 theorems, 0 defs, 0 axioms, 0 sorry (1 #print axioms)
- hypotheses: `P : RationalBettiIntersectionPrimitives`, `kappa : MiddleBettiCorrespondenceKernel` (imported records).
- main content: same-variety specialization of the cross-carrier cup/Gysin packet; `crossProductOfExistingSelfKernel_action_eq` (the new cross-carrier action IS the original ambient correspondence action, definitionally); computational form per class.
- name-vs-content: honest integration check.
- gaps: "NEEDS CI RUN LATER".

### GSTCMNumberManipulationDualDetector.lean (88 lines)
- decls: 4 theorems, 1 def, 0 axioms, 0 sorry (3 #print axioms)
- hypotheses: `hlegal : cmIndexedDenominator x y m ≠ 0` (binder).
- main content: dual ℚ-rational CM channels (Re/Im traces) detect every nonzero Gaussian-rational value (a single trace can kill purely imaginary periods — the pair cannot); verified multiplicative inverses nonzero; corrected CM-indexed NM dual detector; fixed ζ(0)=−1/2 scaling preserves nonvanishing.
- name-vs-content: honest ("a concrete dual-NM arithmetic detector, not yet a canonical abelian-variety period map").
- gaps: forcing Hodge cycle directions via cup/Gysin realization of these readouts is future work.

### GSTClassicalHodgeRelativeSuccessorNonempty.lean (84 lines)
- decls: 3 theorems, 0 defs, 0 axioms, 0 sorry (3 #print axioms)
- hypotheses: `hlive : ProjectivelyLiveSource n (immersion x)`.
- main content: the explicit separator successor belongs to the finite relative codimension-one successor finset; the finset is nonempty / has positive cardinality at every projectively live source.
- name-vs-content: matches ("No Hodge data or cycle-class map occurs").
- gaps: none claimed.

### GSTGeneralSpaceRecoordination.lean (71 lines)
- decls: 0 theorems, 4 defs, 1 structure, 0 axioms, 0 sorry (0 #print axioms)
- hypotheses: none (`Recoordination` = forward/backward paths + invertibility laws — definitional groupoid data).
- main content: refl/symm/trans of recoordination witnesses; `transportEquiv` (any functorial state transport sends a recoordination to an equivalence).
- name-vs-content: matches (abstract bookkeeping).
- gaps: none.

### GSTGeneralSpaceManifoldCharts.lean (59 lines)
- decls: 2 theorems, 2 defs, 0 axioms, 0 sorry (0 #print axioms)
- hypotheses: none.
- main content: Mathlib `chartAt` as a GST `PartialChart` (domain = chart source, observation = the chart map); every point lies in its own chart's domain; observation is definitionally the chart map; point-indexed atlas.
- name-vs-content: matches (glue between Mathlib manifolds and GST).
- gaps: none.

### ComparatorSmokeChallenge.lean (19 lines)
- decls: 1 theorem, 0 defs, 0 axioms, 0 sorry (0 #print axioms)
- hypotheses: none.
- main content: `comparator_smoke : (1 : Nat) = 1 := rfl` — an engineering-only CI smoke theorem (git-history header shows it was a CI check on a solution branch).
- name-vs-content: matches.
- gaps: none (trivial).

---

## BATCH SUMMARY

**Totals:** 72 files, 19,374 LOC, 716 theorems, 150 defs, 40 structures, **0 axioms, 0 sorry, 0 opaque**, 414 `#print axioms`. Method: every file read (full reads for ~40 files; header + all declaration statements + structure fields + crown theorems for the remainder); no compilation attempted.

**Threads in the batch:** (1) the *classical-Hodge reduction tower* (~45 files: Stage-2G spine → operator algebra → separator ghosts → per-route crown reductions); (2) the *Erdős ternary-digit campaign* (~15 files: powers of 4, Happy cells, climb seam, Mahler/worldtrace); (3) *GST internal cosmology* (waves, graphs, general spaces — combinatorial bookkeeping); (4) *CM/Kuga–Satake arithmetic* (Weil projector, descent, dual detectors); (5) *meta-audits* (noncircularity, zeta audit, spine countermodel).

**Unproven-assumption inventory (no `axiom` keyword anywhere — all hypotheses are named Props / hypothesis-records / explicit binders):**

Imported load-bearing named Props/records (used by this batch, defined outside it):
- `erdos_even_conjecture_iff_tailF` (MonolithBoundary): tailF ⟺ ∀ K ≥ 8, noTernaryTwo (4^K) = false.
- `four_power_happy_climb` (GSTInfiniteFourPowerNavigation): ∀ K ≥ 8, ∃ p ≥ 3, HappyCell (carry4 (4^K) p) (digit3 (4^K) p) — the declared open seam, empirically certified at N = 1500, proven nowhere.
- `DivisorsRepresentHodge11` (GSTUniversalLefschetzCurveCycles): every rational (1,1) Hodge class is a codimension-1 cycle class (Lefschetz (1,1)).
- `HodgeBigradedBettiData` (GSTGeometricRealizationStage2G, record): assumed analytification (space + point equiv), assumed Hodge bigrading, assumed linear cycle-class map — the base record under ~40 files.
- `infinite_controller_ternary_two_chokehold`, `erdos_ternary_2_conjecture_odd`, `tailF_tower_primitive`, `tailF_row_primitive_mod729/2187`, `GSTGhostRay.GhostRay`, `NativeMassCycleClassBridge`, `ProjectiveDegreeTraceSemantics`, `GeometryFirstTwoGenerator`, `ProjectiveTwoGenerator`, `LocalCyclicRealization`, `ClosedCorrespondenceWindowRealization`, `OmniversalSeparatorGhost`, `AnalytificationData` — imported hypothesis-records/Props consumed as assumptions.

Declared in this batch:
- `ReverseOntologicalWindow` (POSTULATE H1, HodgeDeRhamBridge): every strictly positive ontological window sourced at a Happy signature cell — the finite Hodge-conjecture analog, open.
- `MahlerSharp`, `WorldtraceScaledCompression`, `WorldtraceMahlerTheory/Spectrum/Crown` (GSTWorldtraceMahlerRelativePrecision): the 3-adic Mahler fracture + compression inputs.
- `Stage2GHodgeFiniteness` (GSTHodgeChannelFinale): finite-dimensionality of rational Hodge fibers.
- `Stage2GCanonicalBasisAlgebraizationObligation`, `UniversalGSTTriangularPeriodGeneration`, `UniversalGSTChargedGeometricFrameGeneration`, `MatrixUnitReachableByClosedCorrespondences`, `FullCorrespondenceGSTPlaneCompleteness/OrbitCyclic/PairingTotal`, `CompleteCosmicClosure`, `HodgeStateClosure`, `CompleteUnaryClosure/CompleteHyperClosure`, `SeedFiberedMassBalance`, `DirectIncidenceProjectionLaw`, `HasFinitePointTransitions`/`PointClassTransitionKernel` — the named frontier Props, each proven EQUIVALENT to (a slice of) the Hodge statement.
- Hypothesis-records with mathematical fields: `GeometricCycleClassSpine` (algebraic_is_hodge / pushforward_naturality / principalCutPair+hodge), `PointReducedGeometricCycleClassSpine`, `GeometricFourfoldLefschetzData` (**hardLefschetz : Function.Surjective cupH2** assumed), `SmoothMiddleHyperplaneBetti` (gysin_injective / self_intersection / relative_exact — weak Lefschetz + relative sequence assumed), `SmoothCompleteIntersectionMiddleBridge`, `AmbientBettiIntersectionCalculus` (cup/Gysin + swap laws assumed), `MiddleBettiCorrespondenceKernel`/`CanonicalMiddleBettiKernel`, `RealizedFiniteClosedCorrespondence` (realizes_on_points), `RealizedCyclicSpectralCertificate` (simple-spectrum + cyclic seed), `CrossCarrierTransfer` (naturality), `ProjectiveApexL2Spoke` (source_action L² equation), `DefectZeroPointSeed` (class_eq), `GenuineTargetTransport` (intertwines + mass_ne_zero), `NativeHodgeOrbitSeed` (nonzero algebraic Hodge state witness), `HodgeRecursiveRealization` (hodgeState_realizes_cycle), `HodgeClosureSemantics` (hodgeNode_realizes_cycle), `EndomorphismAnalytification` (functoriality), `AnalyticEndomorphism` (continuity), `LimitlessSeparatorGhost`/`UnreachableCosmicSheet` (derived obstructions).

**Five most load-bearing files (and why):**
1. `GSTProjectiveOverC.lean` — the only genuine Mathlib geometry in the batch (Spec ℂ, Proj, closed immersions); every classical file's carrier `SmoothProjectiveComplexScheme` comes from here.
2. `GSTClassicalHodgeGeometricCycleClassSpine.lean` — defines the spine record consumed by ~30 files; crucially proves the zero-countermodel (`spine_laws_do_not_force_hodge`), i.e., the whole tower's base interface is non-determining.
3. `GSTClassicalHodgeSynchronizedDefectOrbit.lean` — `NativeHodgeOrbitSeed` + the seed/two-generator reduction chain feeding the point/two-generator/omniverse finales.
4. `GSTWorldtraceMahlerRelativePrecision.lean` — the assumption hub of the Erdős-digit thread: MahlerSharp + compression theory object; its crown is the batch's largest named-hypothesis stack (four unproven inputs).
5. `GSTHodgeChannelFinale.lean` — states the irreducible frontier (`canonical_basis_algebraization_iff_hodge`): everything above "every canonical-basis vector has a native cycle" is derived — the honest boundary of the classical side.

**Single biggest gap:** the classical-Hodge side of this batch is a *complete conditional tower with zero unconditional content toward Hodge*: every "Hodge statement" theorem reduces to hypothesis-records (assumed `HodgeBigradedBettiData` + spine + a route-specific geometric input such as two-generator families, spectral certificates, charged frames, or period determinants — each itself equivalent to the Hodge statement). Compounding this, one concrete integrity anomaly: `GSTGraphV2FourPowerRelocationClosure.lean:24,76` invokes `four_power_happy_ge_three` without its required `hClimb : four_power_happy_climb` argument (the repo's declared open seam, proven nowhere), so the file's "closed interface crown" (`four_power_direct_existence` = the Erdős digit-two statement) is at best climb-conditional and at worst does not compile — this is the batch's highest-priority CI verification item.
