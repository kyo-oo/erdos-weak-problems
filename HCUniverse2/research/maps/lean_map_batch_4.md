# LEAN MAP — BATCH 4 (Task 1-e)

Repo: /tmp/hc-clone-23 @ 6c20bb7, branch research/gpt6-native-point-primitive-span-20261017.
Batch: 71 files, 19,383 LOC, 726 theorems, 6 lemmas (all in vendored `pi.lean`), 184 defs,
43 structures/inductives, **0 `axiom` declarations, 0 `opaque`, 0 real `sorry`** (the two grep
hits for "sorry" are the word inside docstrings), 375 `#print axioms` receipts.

**CI status caveat (audit finding).** 10 of the 71 files are NOT in `lakefile.toml` roots and have
no import chain reaching a root ⇒ they are never compiled by CI (dead text): GSTPrimitiveTransverseCycleExtraction, GSTQuadricPrimitiveRulingGeometry, GSTLawStackRound26, GSTAllDimensionProjectivePrimitiveCycles, GSTClassicalHodgePiProjectiveSpectralOmniverseFinale, pi.lean, GSTPrimitiveMiddleHyperplaneRelative, GSTK3ActualPrimitiveRankTwo, GSTNAmpleShiftIntegralRealization, GSTK3PrimitiveOmniversalGraph. Two more (GSTClassicalHodgeCMFourFactorSwitch, GSTClassicalHodgeCMSurfaceDegreeParity) self-declare "NEEDS CI RUN LATER" but ARE roots. GSTLawStackRound26 self-declares DRAFT-NOT-COMPILED. The other 59 files are lakefile roots (compiled by CI, assuming they build).

Per-file sections follow in batch-list order.

---

### GSTGraphV2SelfExpandingCosmology.lean (2483 lines)
- decls: 82 theorems, 23 defs, 6 structures, 0 axioms, 0 sorry (file >1200 lines: header + all structures + main theorem statements read; grep for the rest)
- hypotheses: hypothesis-records over abstract ℚ-modules: `TwoSourceBirth.decompose : ∀ alpha : HT, ∃ a : HA, ∃ b : HB, hodgeA a + hodgeB b = alpha`; `GeometricCycleBirthRealization.allHodgeFromSources : ∀ (e : Birth src target) (alpha : Law target), ∃ h : (i : I) → Law (src i), assembleHodge e h = alpha`; `SplitTwoSourceBirth.leftInverseA/B`; `SplitGeometricCycleBirthRealization.backSound/backAfterInclude`; `DegreePacket` (degree ≠ 0, `nativePush_sound`, `degree_projection : ∀ alpha : HT, hodgePush (hodgePull alpha) = degree • alpha`)
- main content: impredicative world-closure algebra (seed/birth/induction), newborn completeness iff source completeness under split records; blowup block-diagonal cycle-class surjectivity iff base ∧ center surjective; "counterexample iff base-or-center" (missing class persists); finite-degree pullback injective; exceptional-lift returns/ambient-projector idempotence; Picard-Ch³ twist recovery; heterogeneous middle native blocks; Newton-iteration normal roots (finiteNormalRoot), Euler-sign positivity, Segre/Chern normalizer identities — all over abstract ℚ-vector spaces with linear maps, no Mathlib geometry.
- name-vs-content: "Self-Expanding Cosmology" promises a universe theorem; content is closure/bookkeeping algebra on record-based ℚ-modules plus honest iff-criteria.
- gaps: every geometric instantiation (real cohomology of a real blowup, actual exceptional divisors) is unproven; theorem hypotheses (surjectivity of cycleA/cycleB, split records) carry the load.

### GSTPrimitiveTransverseCycleExtraction.lean (1121 lines) — NOT CI-COMPILED
- decls: 32 theorems, 4 defs, 2 structures, 0 axioms, 0 sorry
- hypotheses: (i) theorem hypotheses `h11 : DivisorsRepresentHodge11 H` (Lefschetz (1,1) as hypothesis) and `hInject : Function.Injective P.cupH2` (Hard-Lefschetz injectivity); (ii) `GenuineBlowupThreeSectorPrimitivePacket`: exceptionalNative cycle with `exceptional_ambient_zero`, `exceptional_first_one`, `exceptional_second_zero` (readouts 0/1/0) and `divisor_cup_coordinates : ∀ beta, ∃ x y, ambientCoordinate (P.cupH beta) = x ∧ first (P.cupH beta) = y - t*x ∧ second (P.cupH beta) = -t*y`, `slope_ne_zero`; (iii) `GenuineBlowupPicardPrimitivePacket`: `exceptional_center_exact : ∀ a, centerReadout (cl (nativeFirstExceptional a)) = a` plus the same cup-coordinate law — i.e. the full three-sector blowup cohomology splitting is ASSUMED.
- main content: given the packets: exceptional cycle is transverse to the Lefschetz divisor image; construction of nonzero algebraic primitive cycles; primitive projection is a ℚ-linear idempotent; Picard module injects into the primitive kernel (all-rank); tangent-Chern source c₂(T_X) analysis with explicit K3×K3 coordinates (norm 192(a+b)²/ab) and the cubic-fourfold no-go (c₂ = 6h² ⇒ zero primitive output); rank-two discriminant twist-invariance 4c₂−c₁² and all-codimension multicharge splitting-principle identities (pure ring identities).
- name-vs-content: suggests extracting primitive cycles generally; content is exact conditional algebra + universal ring identities; docstrings honestly separate the unproven geometric instantiation.
- gaps: geometric realization of the blowup packets, holomorphic-bundle existence for the Chern-charge route ("that unproved analytic integrability step is still required"), and the file is dead text (never compiled).

### GSTClassicalHodgeFiberedNativePullback.lean (782 lines)
- decls: 29 theorems, 3 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none (pure Finsupp/linear algebra)
- main content: common-refinement atoms (multiplicity sheet × codim-p point); forgetful maps; commuting "fibered native pullback square" (classical projection = native shadow on the same limitless ray); gluing of two marginals iff equal mass; anchored normalization, idempotent; circulation sector = finite sums of anchored rectangles (rectangle normal form).
- name-vs-content: "Fibered Native Pullback Universe" is accurate for its bookkeeping content — but it is pure address bookkeeping, no geometry.
- gaps: none internal; everything rests on imported abstractions (CodimensionPoint, realizeFiniteCodimensionPresentation) whose geometric fidelity is established elsewhere.

### GSTTheActConstruction.lean (619 lines)
- decls: 28 theorems, 1 def, 0 structures, 0 axioms, 0 sorry
- hypotheses: theorem hypothesis `hB : erdos_even_conjecture_iff_tailF` (a Prop, the standing "green bridge" equivalence supplied as argument) in the socket/receipt theorems
- main content: unconditional elementary number theory: `self_read` (digit3 (4^K) (j+1) = digit3 (4^(K%3^j)) (j+1) + digit3 K j mod 3); the act (no K≥8 is Cantorian) iff every K≥8 fires in the feedback tree; uniform kill engine `feedback_fire_of_class`; cascade levels 4 and 5 (8 and 16 new firing residue classes mod 243/729); Cantorian dust pinned to 16 residues mod 243, 32 mod 729; unique dead child; receipts.
- name-vs-content: "The Act Construction" = the Erdős-type ternary-digit statement for powers of 4; the name obscures that only the conditional reduction is proven, not the act itself.
- gaps: the act/tree-escape (equivalently WindowCleanDust emptiness) is open; only passes to hTailF via the assumed green-bridge hB.

### GSTQuadricPrimitiveRulingGeometry.lean (558 lines) — NOT CI-COMPILED
- decls: 28 theorems, 26 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none as records; the docstring states the external geometric inputs: quadric cellular decomposition H^{2m}(Q^{2m}) = Q[A]⊕Q[B], blowup Chow/Betti comparison, very-ampleness of L_r — none proven here.
- main content: exact ℚ-coordinate arithmetic: parity-dependent intersection forms, primitive ruling (1,−1) with self-intersection ±2, every middle class = ample + primitive combination; two-birth blowup mixed readout = −1 (unit); m=1 second world with 5-coordinate cup matrix, Gram matrix [[1009,−681],[−681,513]], explicit inverse, matrix-unit composition law; r parallel births with positive Schur complement (det factor r(105+411r+596r²+384r³)/(36(1+2r)²)) and explicit primitive reconstruction.
- name-vs-content: suggests quadric Hodge theorem for all dimensions; content is exact coordinate laws in a coordinate model of quadrics/blowups.
- gaps: identification of the coordinate model with actual cohomology rings is entirely external; dead text.

### GSTDiagonalRead.lean (501 lines)
- decls: 28 theorems, 1 def, 0 structures, 0 axioms, 0 sorry
- hypotheses: `hB : erdos_even_conjecture_iff_tailF` in socket/receipt theorems
- main content: window law (digits of 4^(3^v·u) in rows v+1..2v+1 = digits of u·lteCoeff v); frozen diagonal (lteCoeff stability, residues 7 mod 9, 16 mod 27/81); three uniform fire families; triage: every K≥8 fires or is `WindowCleanDust`; least-fire-row rigidity; dust-empty ⇒ the act ⇒ hTailF.
- name-vs-content: accurate ("diagonal read" of the power tower); cosmological language for base-3 arithmetic.
- gaps: `WindowCleanDust` emptiness (the "one remaining mathematical object") is open.

### GSTGraphV2Ontological.lean (433 lines)
- decls: 17 theorems, 7 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none
- main content: 12-cell finite certificate: `ontDensity` (base-7/base-3 potentials) separates Happy cells (≥42) from bad (≤0) with forbidden gap 1..41; exact telescoping of reverse-base-7 codes; no-erasure lower bound 33·7^N+63 ≤ 7·code_N; weighted prefix positivity when the top row is Happy; graph window positivity.
- name-vs-content: "ontological current" = a hand-tuned integer potential on a 12-state automaton; fully proven, honest.
- gaps: none internal; it is one tile of the larger unproven Erdős-type program.

### GSTFinalPurePowerResidueTransplant.lean (418 lines)
- decls: 25 theorems, 5 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none
- main content: exact Nat identities: strip quotient/carry recursion (mod 4 information digits), wide carry/digit decomposition for B·R, conservation `B·wideDigit R p + wideCarry B R p = wideDigit (B*R) p + 3·wideCarry B R (p+1)`; exponent-trit lift laws; residue tower (1+3D(T mod 3^q)) refinement/monotonicity/digit readout; 4^K mod 3^{s+2+q} strip identifies exact power carries.
- name-vs-content: "transplant" is literal (arithmetic copied forward); accurate.
- gaps: none internal.

### GSTLawStackRound26.lean (394 lines) — NOT CI-COMPILED, self-declared DRAFT-NOT-COMPILED
- decls: 18 theorems, 2 defs, 3 structures, 0 axioms, 0 sorry ("sorry" appears only in the docstring "no `sorry`, no new `axiom`")
- hypotheses: **the campaign's central hypothesis-record set**: `OpenItems (I) : Prop` with five placeholder fields — `involution`, `twoCellReduction`, `nonScalarExclusion`, `rankParity` ("the rank parity: the even split r₀ = 2a"), `stripReduction` (each a bare `Prop`, content only in the LaTeX derivation); `CompositionOn.pair_bit_of_items : OpenItems I → ∃ v : PairWit, landing v ∧ scale v ≠ 0` (STEP 4, OPEN); `CompositionOn.algebraic_of_pair : ∀ v, landing v → scale v ≠ 0 → ∃ Z : I.Cyc, I.cl Z = I.alpha` (STEP 1, "COMMITTED": Lemma N Newton conductor + determinantal machine + GAGA); `cyclo_engine_of_factorization` hypothesis `hfact : ∏ k ∈ range L, (X − C (ζ k)) = X^L − 1`.
- main content: kernel-level C₄ deck laws (norm degeneration 1+γ+γ²+γ³=0; invariants vanish on torsion-free modules; 2•v ∈ (γ−1)M with witness −(1+γ)v); Weil-plane door-parity (m•W_R dies iff 2∣m; range of γ−1 = parity sublattice, obstruction ZMod 2); cyclotomic engine ∏(1+ζk) = 1−(−1)^L given the factorization; symmetrizer ∑γ^j u = m•u; conditional composition: items + record ⇒ IsRationalAlgebraic at each input; for-all-inputs one-directional form; boundary_exact falsifiability receipt.
- name-vs-content: "Law Stack Round 26" is accurate; the file is scrupulously honest about being text, not proof.
- gaps: everything load-bearing (OpenItems (i)–(v), pair_bit_of_items, algebraic_of_pair) is assumed; and the file is not even in the build registry.

### waves/GSTNCohomology.lean (373 lines)
- decls: 15 theorems, 10 defs, 1 structure, 0 axioms, 0 sorry (root waves.GSTNCohomology — compiled)
- hypotheses: `NShape.distinct` (injective channel map — data, not math hypothesis)
- main content: Wave II of the "wave cohomology" of the digit automaton: tower windows as digit-difference profiles; interference pairing decomposes exactly as horizontal + vertical + 56·source pairing; source null-sterile (NULL chord source 0), GST+ chord source 112; shape signature nonempty on Ω-class-two exponents (via imported omega_wave_existence_class_two).
- name-vs-content: "N-cohomology" suggests cohomology theory; content is exact ℤ-valued sums over digit readouts plus an upgraded (formerly false) spec.
- gaps: the analogies to topology are decorative; the machinery serves the Erdős-type campaign, not Hodge.

### GSTGeneralSpaceCohomology.lean (358 lines)
- decls: 9 theorems, 1 def, 4 structures, 0 axioms, 0 sorry
- hypotheses: `CohomologyGeometry` (graded cup with zero laws — interface), `CyclePathRealization` (cycleClass + transports + `naturality : cl (nativeTransport γ Z) = hodgeTransport γ (cl Z)`)
- main content: algebraicity ∈ range(cl) is invariant under reversible recoordination and under irreversible split causal folds (with compatible native/hodge returns), at any finite tower depth; missing directions persist. Honest docstring: does not disprove Hodge, only bounds one GST operator class.
- name-vs-content: "General Space Cohomology" is interface algebra; accurate as far as it goes.
- gaps: all content conditional on the CyclePathRealization interface being instantiated by real geometry.

### GSTGeometricRealizationStage2.lean (347 lines)
- decls: 13 theorems, 4 defs, 2 structures, 0 axioms, 0 sorry
- hypotheses: **`FiniteHodgeRealization`** with load-bearing field `basisCycle_address : ∀ i ∈ hodgeSupport, encode (cycleClass (basisCycle i)) = addressBasis i` (every Hodge-support basis coordinate is realized by an algebraic cycle) + `encode_injective`, `hodge_supported`; and the Finsupp version `CompactHodgeRealization.basisCycle_address`.
- main content: given those data, every Hodge class has a cycle preimage (witness = Σ coeff • basisCycle); UniversalHodgeStatement follows from fiberwise realizations; selector Skolemization. Docstring is explicit: non-circular but "what remains … is an instantiation … Current Mathlib does not yet expose the complete classical Hodge/Chow/cycle-class stack".
- name-vs-content: "Geometric Realization" = trivial linear combination from assumed basis cycles.
- gaps: THE instantiation (basisCycle for a real variety) is exactly the Hodge conjecture's content; this file is the template all later "finale" files instantiate with their own hypothesis-records.

### GSTUniversalAddressBridge.lean (338 lines)
- decls: 18 theorems, 9 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none
- main content: every N-state GST world shape has canonical linear equiv ShapeCoef ≃ (Fin N → ℤ); chart-independence under recoordination; sector/polynomial operator naturality; N=12 recovers the historical carrier; cosmic cells ≃ ℕ (pair/unpair), completed cosmos ≃ (ℕ→ℤ), compact cosmos ≃ (ℕ →₀ ℤ).
- name-vs-content: accurate; pure dictionary bookkeeping.
- gaps: none internal.

### GSTBladeWave.lean (322 lines)
- decls: 15 theorems, 1 def, 0 structures, 0 axioms, 0 sorry
- hypotheses: none
- main content: dust-root laws digit3(4^{1+3m}) rows 2–4 = m%3, (m/3)%3, ((m/9)%3 + C(m,2))%3 (blade correction = binomial); 4^{1+3m} ≡ 4+252m+324C(m,2) mod 243; cube/tower/one-plus-power 3-adic divisibility; wave congruence and full prefix periodicity (digits of 4^{3^a·core} depend only on core mod 3^n).
- name-vs-content: accurate (LTE-style arithmetic); no Hodge content.
- gaps: none internal.

### GSTClassicalHodgeFiniteSupportChart.lean (317 lines)
- decls: 8 theorems, 5 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none in-file (uses imported AtomicSeparatorProbe)
- main content: finite-support local charts: live support of one Hodge state ↔ finite GST world (N×1 shape); limitless fibered pairing = finite rational Poincaré pairing on the chart; nondegeneracy ⇒ nonzero address has finite probe; failure of Stage-2G yields a finite GST Poincaré witness.
- name-vs-content: accurate bookkeeping; "local-to-global interface" is address-level, not geometry.
- gaps: depends entirely on imported Stage-2G/separator machinery.

### GSTClassicalHodgeAmbientBettiSelfProduct.lean (308 lines)
- decls: 9 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none (A : AnalytificationData V supplied as variable — an imported data record)
- main content: genuine Mathlib: X_an × X_an as TopCat; singular chain/cochain complexes; projections and factor swap; homology-level pullbacks; swap exchanges projections; swap involution on cohomology.
- name-vs-content: accurate; honest "no correspondence operator … is supplied".
- gaps: only the ambient carrier; no cycle classes, no correspondences yet.

### GSTClassicalHodgeFiberedTransferCompletion.lean (298 lines)
- decls: 12 theorems, 2 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none
- main content: sheet generators over (weight, basis-index); every genuine Hodge class = unique finite rational combination of independent sheet generators; projection to the single cosmic diagonal generator; crown.
- name-vs-content: "Transfer Completion" = Finsupp bookkeeping of multiplicity sheets.
- gaps: none internal.

### GSTClassicalHodgeProjectiveWordOrbit.lean (295 lines)
- decls: 12 theorems, 0 defs, 1 structure (+ inductive ProjectiveOperatorWord), 0 axioms, 0 sorry
- hypotheses: `ProjectiveWordLiveSourceTarget.source_action : (word.operatorPair G).cohomologyOperator S.hodge.1 = coeff • (basis j).1` (word's action maps the live seed onto each requested sheet); finale hypotheses D (FiniteSpineMomentChain per live weight) and R (such targets for every basis sheet).
- main content: free noncommutative word algebra on genuine scheme self-maps; eval is kernel-stable (cycle-class functoriality); targetCycle represents the requested sheet; bigradedBettiHodge follows from D + R.
- name-vs-content: accurate; the word algebra is real syntax, the Hodge content is exactly the assumed R.
- gaps: existence of words with the source_action property (the "spread the seed" step) is unproven.

### GSTAllDimensionProjectivePrimitiveCycles.lean (283 lines) — NOT CI-COMPILED
- decls: 13 theorems, 5 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none as records; identification with actual Betti cup/intersection of P^m×P^m and the projective bundle formula are external (docstring).
- main content: for all m: middle Lefschetz kernel of P^m×P^m (cup h adds adjacent coefficients) is exactly the alternating line c_j = c_0(−1)^j; explicit algebraic primitive Σ(−1)^j H_1^{m−j}H_2^j; product stabilization X×P^m: signed telescoping certificate (interior cancellation, top boundary = primitivity), uniqueness and bidirectional equivalence.
- name-vs-content: "All-Dimension Projective Primitive Cycles" is accurate for the coordinate model; honest "does NOT prove primitive Hodge surjectivity for arbitrary varieties".
- gaps: geometric identification unproven; dead text.

### GSTClassicalHodgeCycleOperatorNaturality.lean (276 lines)
- decls: 7 theorems, 0 defs, 3 structures, 0 axioms, 0 sorry
- hypotheses: `CycleClassOperatorPair.cycleClass_natural` (commuting square); `SpectralCycleOperator.eigenvector : operator (basis i) = eigenvalue i • basis i` with injective eigenvalues/basisIndex; `CyclicSeed.class_eq : cl cycle = Σ coeff i • basis i` with all coeff ≠ 0 (assumed algebraic seed).
- main content: polynomial functional calculus intertwines; Lagrange isolator extracts each Hodge sheet as an actual native cycle from one seed; crown `finite_hodge_family_from_one_seed`.
- name-vs-content: accurate; clean conditional statement.
- gaps: existence of the spectral operator with distinct eigenvalues on the Hodge basis and of the cyclic seed is the unproven burden.

### GSTHodgeBigradedCosmology.lean (275 lines)
- decls: 12 theorems, 3 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none
- main content: world cell ↔ (Lefschetz degree k = C+d, Hodge charge q = C−d) injective (multiplicity-free bigrading); projectors commute/idempotent/orthogonal; digit/carry shifts move bidegree by (n,−n)/(n,+n); Poincaré dual bidegree equivalence; Hodge class iff fixed by projector (2p,0).
- name-vs-content: accurate combinatorics of the GST world lattice; "Hodge" is the label q=0, not Hodge theory.
- gaps: none internal.

### GSTClassicalHodgeCMFourFactorSwitch.lean (262 lines)
- decls: 13 theorems, 7 defs, 0 structures, 0 axioms, 0 sorry (root; header says "NEEDS CI RUN LATER")
- hypotheses: none (IsOddCMType/ConjugationInvariant are definitions)
- main content: Boolean CM sign combinatorics: splice/complementarySplice conserve pair charge at every label; preserve odd CM type under conjugation-invariant masks; complete normal form (balanced iff splice form) and conjugate-switch version.
- name-vs-content: honest: "algebraicity does not [follow]" — sign combinatorics only.
- gaps: no connection to actual CM abelian varieties or tensor algebraicity.

### GSTClassicalHodgePiProjectiveSpectralOmniverseFinale.lean (260 lines) — NOT CI-COMPILED
- decls: 7 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `CanonicalProjectiveSpectralPacket` (spectral : ProjectiveWordSpectralFamily on the live support, basisIndex_eq, visible) — assumes a projective word diagonalized on the live support with coordinate visibility; finale assumes such packets for every nonzero Hodge class.
- main content: packet ⇒ native cycle representing alpha; cyclic atomic seed; N-cohomology packet coincidence; branch persistence through the higher-causal tower; crown; `bigradedBettiHodge_of_canonicalProjectiveSpectralPackets`.
- name-vs-content: grandiose "Omniverse Finale"; content is a repackaging conditional on the packet.
- gaps: packet existence unproven; dead text.

### GSTGraphV2Scratch.lean (254 lines)
- decls: 11 theorems, 4 defs, 2 structures, 0 axioms, 0 sorry (root)
- hypotheses: none
- main content: V2 seven-axis vertex/overlay records; mod-12 parent-happy residue compression; micro-output phase recurrences (ring identities); seeded happy iff common digit two; local five-rotation law (decided on 12 cells).
- name-vs-content: "scratch" is accurate; git-history header included.
- gaps: none internal (automaton arithmetic).

### pi.lean (251 lines) — NOT CI-COMPILED
- decls: 18 theorems, 1 def, 0 structures, 0 axioms, 0 sorry — plus 6 `lemma`s
- hypotheses: none
- main content: **a vendored copy of Mathlib's `Mathlib/Algebra/BigOperators/Pi.lean`** (Simon Hudon/Patrick Massot copyright header, `module`/`public import` syntax): prod/sum over pi types, mulSingle induction, monoidHom MulEquiv, indicator products.
- name-vs-content: the filename suggests a GST "pi" theory; it is a copied Mathlib reference file.
- gaps: not part of any build; presumably a template/reference. No original content.

### GSTClassicalHodgeExactClayStatement.lean (245 lines)
- decls: 7 theorems, 3 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: `hG : LinearMap.ker (G p) = (H.hodgeBigrading p).ppComponent` (spectral generator realizes (p,p)); `CycleClassHodgeCompatible : ∀ p, range (H.cycleClass p) ≤ rationalHodgeSubspace (…)` (cycle classes are Hodge — the "SOURCE-SEMANTICS hypothesis").
- main content: defines the literal target `EveryHodgeClassIsRationalAlgebraic` (= ∀ p, ∀ alpha ∈ Hodge, ∃ Z, cl Z = alpha) and `EveryHodgeClassIsFiniteRationalCombination`; proves both ↔ BigradedBettiHodgeStatement (Stage-2G) ↔ spectral-kernel-range and = spectral-kernel (under hcycle).
- name-vs-content: accurate — this is the acceptance specification file; it proves equivalences of formulations, not the statement.
- gaps: the target itself is unproven; CycleClassHodgeCompatible retained as explicit hypothesis.

### waves/CardinalWorldsPostulateLaw.lean (238 lines)
- decls: 10 theorems, 2 defs, 1 structure, 0 axioms, 0 sorry (root waves.CardinalWorldsPostulateLaw)
- hypotheses: `ControlledTower` fields controller (level j = bridge j (level j)) and ledger (level (j+1) = bridge j (level j)) — trivially satisfiable invariants, not mathematical hypotheses
- main content: POSTULATE III "Law of Controlled Emergence": controlled towers are constant level families; emergentDimension T N = N (definitional count); infinite dimension as unbounded readouts; colimit uniqueness; the law (admissible = controlled ⇒ finitely presented).
- name-vs-content: "postulate" is a definition here, not an axiom; content is trivial ℕ recursion dressed cosmologically.
- gaps: none mathematical; rhetoric ≫ content.

### GSTClassicalHodgeWeightedCyclicCriterion.lean (234 lines)
- decls: 7 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `WeightedLocalCyclicRealization`: spectral operator on the live support + `coefficient_ne_zero` + `seed_mem_atomic : (Σ coeff i • basis i) ∈ pointCycleClassSpan p (cl)` (assumed atomic algebraic seed)
- main content: weighted seed suffices: every live sheet lands in the atomic span; upgrade to an actual native seed cycle; exists_native_cycle / point presentation; crown: hlocal (per-class realizations) ⇒ BigradedBettiHodgeStatement.
- name-vs-content: accurate criterion; the criterion's premise is the unproven part.
- gaps: existence of weighted local cyclic realizations for every class.

### GSTClassicalHodgeGSTProjectiveWordExactFinale.lean (229 lines)
- decls: 5 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: `hW : ∀ p j, (W p j).cohomologyOperator (spine seed) = coeff • (basis j).1` (projective word action on the canonical spine seed hits every sheet) or `R : ∀ p j, ProjectiveTwoGenerator …` + `hdiag`; imported M : NativeMassCycleClassBridge, G : spine.
- main content: compiles projective words / two-generator pairs into CanonicalSpineGSTProgram; everyHodgeClassIsRationalAlgebraic and the finite-combination wording follow.
- name-vs-content: "Exact Finale" is accurate formally; the burden is the assumed hW/R.
- gaps: construction of the words/generators with the required spectral action is unproven.

### GSTClassicalHodgePrincipalCutSuccessorOperator.lean (226 lines)
- decls: 5 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none in-file
- main content: geometry-built graded successor operator codim-p → codim-(p+1): exact-stratum filter on relative principal-cut successors; free linear extension; finite target presentations. Docstring: nonvanishing/exhaustion "must prove … it is not assumed here".
- name-vs-content: accurate; constructive plumbing.
- gaps: the cut's nonvanishing/exhaustion (needed for Lefschetz propagation) unproven.

### GSTClassicalHodgeSuccessorSeedEscapeDichotomy.lean (220 lines)
- decls: 6 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `PositiveCosmicHomologyEscape` is a witness-structure (mass ≠ 0, shadow ≠ 0, class = 0), not an assumption; theorems take hlive/hExact and hNoEscape.
- main content: separator successor gives a NativeHodgeOrbitSeed OR an explicit positive cosmic homology escape; escape lies on the standard transfer ray; no-escape ⇒ seed.
- name-vs-content: accurate dichotomy.
- gaps: exclusion of the escape branch (a "projective degree/Poincaré compatibility theorem") unproven; seed existence conditional on hExact.

### GSTPrimitiveMiddleHyperplaneRelative.lean (218 lines) — NOT CI-COMPILED
- decls: 7 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `HyperplanePoincareData` fields — `weakLefschetzLow : Function.Surjective pullLow`, `poincareY` (nondegeneracy), `projection`, `cupAdjoint` (standard geometric identities as record fields); `hGysin : gysin (pullMid a) = lefschetzMid a`; `hexact : range toAbsolute = ker pullMid`.
- main content: primitive middle classes restrict to zero on hyperplanes (weak Lefschetz + Poincaré + projection formula); primitive ⇔ hyperplane-invisible (with Gysin); relative lift ⇔ primitive; NO linear recovery of nonzero primitives from hyperplane data.
- name-vs-content: accurate; a genuine (abstract, linear-algebraic) theorem of the standard kind; docstring honest about impossibility of the naive strategy.
- gaps: instantiation on actual cohomology not done; dead text.

### GSTClassicalHodgeSeparatorProbe.lean (209 lines)
- decls: 5 theorems, 3 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `AtomicSeparatorProbe` is a witness structure (alpha, detector, annihilates_atoms, pairing_nonzero) — definitional
- main content: ambient detectors ↔ completed coordinate probes; failure of Stage-2G ⇔ existence of a separator probe at some weight; positive form (no probes anywhere ⇔ Stage-2G).
- name-vs-content: accurate duality bookkeeping.
- gaps: none internal (relies on imported annihilator equivalence).

### GSTClassicalHodgeDegreeCertifiedStrictPrimitiveFinale.lean (208 lines)
- decls: 3 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: imported primitive records (RationalBettiIntersectionPrimitives, SchemeBiFiniteClosedCorrespondence K, MiddleBettiCorrespondenceKernel kappa, PointBettiClass pt, GeometricIncidencePrimitives I) + `hpoint` (point cycle classes = pt) + `hact` (kernel action = eigen-scaled sheet)
- main content: builds a RealizedFiniteClosedCorrespondence from strict primitives; targetCycle exists with class = requested basis sheet; degree-certified version.
- name-vs-content: "Strict-Primitive Finale" is plumbing of imported interfaces; the geometry is in the assumed I/hact.
- gaps: all geometric content (incidence primitives, kernel action) assumed; only 3 theorems.

### GSTClassicalHodgeCrossWeightNativePropagation.lean (202 lines)
- decls: 6 theorems, 1 def, 3 structures, 0 axioms, 0 sorry
- hypotheses: `PureLefschetzSeedTransport.transport_formula : cohomologyOperator source = limitlessLefschetzScalar p q • target` (binomial scalar); `SeedPropagationFamily` (transports at every weight)
- main content: central binomial coefficient nonzero over ℚ; target cycle formula; algebraic seed propagates to every later weight; family induction.
- name-vs-content: accurate; propagation lemma conditional on transports.
- gaps: existence of the graded transports realizing the Lefschetz steps unproven.

### GSTClassicalHodgeDirectOrbitWordSaturation.lean (201 lines)
- decls: 7 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: D : SpineTowerConservedCharge; `R : ∀ q j, ProjectiveWordLiveSourceTarget G (conservedSpineOrbitSeed G D q) j`
- main content: live-source word composed after the normalized spine program reaches each sheet exactly; direct orbit saturation ⇒ GradedGeometricOrbitModuleCyclic ⇒ BigradedBettiHodgeStatement; native-mass variant.
- name-vs-content: accurate; "removes packaging", content still carried by R.
- gaps: word reachability (R) unproven.

### GSTHodgeAssaultV2.lean (199 lines)
- decls: 9 theorems, 1 def, 0 structures, 0 axioms, 0 sorry
- hypotheses: none
- main content: finite GST diagonal algebra: for p < 3 every Hodge class is a rank-one multiple of cycleClass p (unique coefficient = diagonal coordinate); for p ≥ 3 only the zero cochain; pure Hodge expansion in ℤ³.
- name-vs-content: "Hodge Assault V2" overstates; content is a 3-weight finite classification; explicitly "No claim about arbitrary external varieties".
- gaps: no connection to actual varieties (by design).

### GSTClassicalHodgeRealizedCorrespondenceKrylovFinale.lean (195 lines)
- decls: 6 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `RealizedCorrespondenceKrylovCertificate` (word_hodge: correspondence preserves the Hodge fiber; seedCycle with Hodge class) + `IsKrylovCyclic : span (range hodgeOrbit) = ⊤`
- main content: native orbit classes match Hodge orbit (commuting square); orbit vectors algebraic; cyclicity ⇒ AlgebraicHodgeSubspace = ⊤ ⇒ EveryHodgeClassIsRationalAlgebraic / finite combination.
- name-vs-content: accurate, "basis-free cyclic reduction"; the cleanest statement of what remains.
- gaps: existence of one cyclic correspondence orbit per weight is the entire unproven burden.

### GSTClassicalHodgeCanonicalProjectorLanding.lean (193 lines)
- decls: 5 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `CanonicalProjectorCertificate`: window + `transitions : PointClassTransitionKernel` (observable induced on native cycles) + seedPresentation + `augmented_projector_seed : projector (seed class) = isolatedCoefficient ≠ 0 • (basis i)`
- main content: canonical augmented Lagrange projector extracts each basis sheet as a native cycle; certificates everywhere ⇒ BigradedBettiHodgeStatement.
- name-vs-content: accurate; "everything else is manufactured by the limitless spectral calculus".
- gaps: certificate existence (the projector-seed nonzero component) unproven.

### GSTClassicalHodgeRecoordinationArsenalCrown.lean (192 lines)
- decls: 6 theorems, 5 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none
- main content: live support ↔ canonical one-row GST chart; rational code projectors commute with world recoordinations; slot isolation; nonzero live coordinate survives recoordination.
- name-vs-content: accurate groupoid bookkeeping.
- gaps: none internal.

### GSTClassicalHodgePointClosurePrincipalCut.lean (185 lines)
- decls: 2 theorems, 7 defs/instances, 0 structures, 0 axioms, 0 sorry
- hypotheses: none
- main content: genuine Mathlib scheme constructions: closure({x}) as reduced closed subscheme (vanishing ideal), scheme-theoretic intersection with the point-specific principal section via pullback; both projections closed immersions; Noetherian + compact instances.
- name-vs-content: accurate geometric plumbing; "no Hodge data or cycle-class map is used".
- gaps: only the carrier; Krull principal ideal theorem consequences live in later files.

### GSTGraphV2CanonicalNWave.lean (181 lines)
- decls: 9 theorems, 2 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none
- main content: canonical n-wave transport: physical carry/digit state of canonicalEnergy equals that of the stripped tail with accumulated phase shift; all observables/predicates/Happy gates invariant; terminal energy = 1 once origin exhausted.
- name-vs-content: accurate automaton arithmetic.
- gaps: none internal.

### GSTGraphV2SeededPrefix.lean (181 lines)
- decls: 10 theorems, 4 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none
- main content: lossless seeded-prefix coordinates (D, k retained exactly); strip laws (one and two digits) for residue/carry/digit; SeedHappy invariance; seed-zero = ordinary tail cell; (1,1)-prefix = existing controller.
- name-vs-content: accurate.
- gaps: none internal.

### GSTClassicalHodgeZeroWeightLocalSeed.lean (177 lines)
- decls: 3 theorems, 4 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: imported D : ProjectiveDegreeTraceSemantics, G : GeometricCycleClassSpine; final theorem hypothesis hL (native point lifts for the two-step Lefschetz)
- main content: generic point of an irreducible component is maximal in the specialization order (sober space) ⇒ genuine codimension-0 point; degree trace ⇒ its cycle class ≠ 0; weight-zero native Hodge seed; weight-zero minimal ghost contradiction (False) given hL.
- name-vs-content: accurate; genuine Mathlib (Sober, irreducibleComponents).
- gaps: hL (bare-Lefschetz native point lifts) assumed; only weight zero.

### GSTClassicalHodgeCodimensionZeroDegreeApex.lean (173 lines)
- decls: 6 theorems, 4 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: imported G (spine), D (degree trace); final theorem assumes F : RootedStrictRelationFan
- main content: apex irreducible component/generic point is codimension-0; degree forces nonzero cycle class; codimensionZeroDegreeApex seed; weight-0 Hodge from degree apex + rooted fan.
- name-vs-content: accurate; the "omniverse apex" is a generic-point cycle.
- gaps: rooted fan F imported hypothesis; weight 0 only.

### GSTGeneralSpaceMorphisms.lean (172 lines)
- decls: 2 theorems, 7 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: none
- main content: category of General Spaces: Hom (point/path preserving maps), id/comp, products with PSigma paths, projections, pairing, discrete embedding of arbitrary functions.
- name-vs-content: accurate; elementary category theory.
- gaps: none internal.

### GSTClassicalHodgeSeparatorRelativeCover.lean (170 lines)
- decls: 5 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: hlive (ProjectivelyLiveSource) in the main theorems
- main content: real Mathlib projective algebra: specialization = reverse inclusion of homogeneous primes; primes between source and separator; unique strict generalization of the lifted separator successor = generic point (no intermediate points).
- name-vs-content: accurate; "no Hodge datum occurs".
- gaps: hlive condition (dimension ≥ 2 source) not discharged in general.

### GSTV2InfiniteCore.lean (162 lines)
- decls: 9 theorems, 7 defs, 1 inductive (Space), 0 axioms, 0 sorry
- hypotheses: none
- main content: all-Nat control primitives: cell mass conservation; omega past/future; exact prefix value; past closed = 3^{t+1}(N mod 3^K); past+future conservation; multiscale cocycle (past add exact), future semigroup, two-stage conservation.
- name-vs-content: accurate; deliberately independent of the Erdős monolith.
- gaps: none internal.

### GSTClassicalHodgeProjectiveDefectTransport.lean (161 lines)
- decls: 5 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: `ProjectiveSheetIntertwines` (cohomology pushforward acts by the residue scalar or 0 on the sheet) + imported N : GeometricPushforwardNaturality
- main content: transportAtom's Hodge face = residue weight • basis sheet (or 0 off codimension); defect equivariance under genuine projective transport; zero-defect stability; classical landing preserved.
- name-vs-content: accurate; conditional on the intertwining law.
- gaps: intertwining for actual endomorphisms unproven (relies on the imported naturality record).

### CardinalWorldsV2.lean (158 lines)
- decls: 12 theorems, 1 def, 0 structures, 0 axioms, 0 sorry
- hypotheses: none
- main content: hasTernaryTwo ↔ ¬noTernaryTwo with first-signature minimality; carryAtPos 1 = R % 3; 2-adic depth invariant under 3^a scaling; three-world exponential packets (2^j,3^j,6^j) coordinatewise multiplicative; joined-prefix recurrence.
- name-vs-content: accurate reader/packet arithmetic.
- gaps: none internal.

### GSTClassicalHodgeSingularCohomologyFunctoriality.lean (154 lines)
- decls: 4 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none (A : AnalytificationData, E : EndomorphismAnalytification are data)
- main content: genuine Mathlib homological algebra: singularChainMap functorial (id/comp); cochain pullback via linear Yoneda; homologyMap gives contravariant Betti representation of analytic (hence algebraic) endomorphisms.
- name-vs-content: accurate; "removes the arbitrary cohomology operator".
- gaps: analyticity/lift of algebraic endomorphisms supplied by imported E.

### GSTK3ActualPrimitiveRankTwo.lean (149 lines) — NOT CI-COMPILED
- decls: 5 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: imported `GenuineK3ProductDiagonalPacket` G (transversePairing values, lefschetz kills, degree ≠ 0, etc.); `GenuineK3DivisorIntersection`: productDetector with `cross_value : productDetector (cl hCrossH) = degree²`, left/right = 0
- main content: second primitive Q = (h×h) − d(U+V) is primitive (2,2)-Hodge, killed by the transcendental detector, paired = d² by the divisor detector; P, Q linearly independent (a = b = 0).
- name-vs-content: accurate; honest "no toy Hodge carrier" (but conditional on the packet).
- gaps: the K3-product geometry packet + intersection detector are assumed; dead text.

### GSTGraphV2PhysicalSignedKernelTelescopeScratch.lean (146 lines)
- decls: 7 theorems, 5 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none
- main content: physical binary-column telescope: microOutput = next column digit; signedKernelTwice identity per column; telescope = boundary flux + 7·Σ survive indicators; no-survive ⇒ pure boundary flux.
- name-vs-content: accurate standalone arithmetic; "does not assert the final Erdos crossing theorem".
- gaps: none internal.

### GSTClassicalHodgeCompositionalCorrespondenceCyclicAttack.lean (141 lines)
- decls: 5 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: `IsCompositionalCyclicSeed` (algebraic seed + `ExprReaches` for every target: some noncommutative realized-correspondence expression maps seed to target)
- main content: reached targets stay algebraic (range stability); cyclic seed ⇒ AlgebraicHodgeSubspace = ⊤ ⇒ EveryHodgeClassIsRationalAlgebraic / finite combination; word reachability embeds into expression reachability.
- name-vs-content: accurate; docstring: "The only remaining content of the cyclicity statement is therefore geometric".
- gaps: cyclicity of the correspondence algebra unproven.

### GSTClassicalHodgePrimitivePushforwardNaturality.lean (141 lines)
- decls: 4 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `GeometricPushforwardNaturality.naturality : cl (nativePushforward Z) = cohomologyPushforward (cl Z)` (standard cycle-class functoriality as record field); finale assumes it for every endomorphism
- main content: naturality ⇒ kernel stability ⇒ atomic-span stability ⇒ whole correspondence span kernel-stable ⇒ canonical operator pair.
- name-vs-content: accurate; "strictly an operator-naturality law".
- gaps: the naturality square for actual pushforwards is supplied, not proven here.

### GSTGraphV2TransparentWidthThree.lean (138 lines)
- decls: 6 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: hChild/hRight (Happy cell gates) in the pressure theorems
- main content: width-three exact conservation (B = 64 strip law); U-jump sign classification (Happy < 0, non-Happy ≥ 0); Happy-disappearance forces strictly positive, integer-quantized vertical U pressure.
- name-vs-content: accurate automaton arithmetic.
- gaps: none internal.

### GSTGraphV2NonlocalCascade.lean (132 lines)
- decls: 4 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none (hHappy hypotheses)
- main content: Happy-cell transport dichotomy: a Happy cell either stays Happy one x4 wave later or is a forced latent packet (digit 2, carry ∈ {1,2}, next carry = 3).
- name-vs-content: accurate.
- gaps: none internal.

### GSTClassicalHodgeGeneralSpaceDefectExtinction.lean (131 lines)
- decls: 6 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: `HodgeNativeSaturation` (a named target: every Hodge state reachable by a synchronized path from a native state)
- main content: defects unreachable from native states; saturation ⇔ EveryHodgeClassIsRationalAlgebraic; defect extinction ⇔ same; finite-combination endpoint.
- name-vs-content: accurate restatement file; nothing proven, everything equivalenced ("stated as a target, not assumed").
- gaps: saturation is exactly the unproven conjecture.

### GSTAnalyticAbsorptionV2.lean (125 lines)
- decls: 11 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none
- main content: AddCircle period equivariance under arbitrary multipliers; descent semigroup; rootsOfUnity tower monotonicity; cyclotomic degree quadrupling 4·natDegree; rebased towers; transcendental points near every tower point.
- name-vs-content: accurate; "does not add a new geometric interpretation".
- gaps: none internal.

### GSTClassicalHodgeNativePointSeedDegreeUpgrade.lean (124 lines)
- decls: 2 theorems, 4 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: imported G (spine), D (degree trace semantics); `hpoint : ∀ E ghost, Nonempty (CodimensionPoint V.X E.weight)`
- main content: point seeds derived (Hodge type from spine, nonvanishing from positive degree) instead of assumed; one codimension point ⇒ nonzero native Hodge orbit seed; ghost-weight native-seed survival reduced to point existence; no degree-trace exists for the zero-cycle-class counterinstance.
- name-vs-content: accurate upgrade/repair file.
- gaps: ghost point existence per weight unproven; relies on imported D/G records.

### GSTClassicalHodgeHeightOneProjectiveRelevance.lean (112 lines)
- decls: 4 theorems, 2 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: `ProjectivelyLiveSource` (height of irrelevant-ideal image ≥ 2) — a dimension condition, honest
- main content: real Mathlib commutative algebra: height-one primes cannot contain height-≥2 ideals; height-one separator components are projectively relevant (comap avoids the irrelevant ideal).
- name-vs-content: accurate; "No Hodge data occurs".
- gaps: liveness (dim ≥ 1 source) assumed per point.

### GSTGraphV2CanonicalSignedPrefixBridge.lean (112 lines)
- decls: 4 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: hChild (SeedHappy at child tail) and hRightBad (all-bad parent tail)
- main content: canonical seeded U-gap positivity; the same on the literal physical canonical block; potential growth positivity; bicocycle (vertical flux) positivity.
- name-vs-content: accurate arithmetic obstruction certificate.
- gaps: hypotheses on canonical tails not discharged in general.

### GSTClassicalHodgeExactClayCorrespondenceRoute.lean (105 lines)
- decls: 5 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: `UniversalClosedCorrespondenceSheetReachability` (every Hodge basis sheet reached, up to nonzero scalar, from one genuine algebraic point class by a finite rational word of realized closed correspondences) — the named remaining burden
- main content: reachability ⇒ Stage-2G ⇒ EveryHodgeClassIsRationalAlgebraic / finite combination; contrapositive audits (failure of Hodge forces reachability failure).
- name-vs-content: accurate; explicitly "No reachability theorem is smuggled in here".
- gaps: reachability is precisely the open geometric content.

### GSTNAmpleShiftIntegralRealization.lean (104 lines) — NOT CI-COMPILED
- decls: 6 theorems, 3 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none (toy 2-channel model with periods 2, 3)
- main content: after positive ample shift 12 = 2·3+3·2, integer nonnegative representatives a(n) = −n+3|n|, b(n) = n+2|n| give period n+12|n| and calibration defect 0; concrete period-13 instance.
- name-vs-content: honest: "an honest finite lattice/calibration result, not a claimed all-X Chow cycle".
- gaps: geometric generators spanning the target Hodge class are "precisely the missing, nontrivial geometric realization"; dead text.

### GSTClassicalHodgePrincipalCutStalkCosmos.lean (94 lines)
- decls: 2 theorems, 4 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none
- main content: genuine Mathlib local algebra: closed immersion ⇒ surjective stalk map; first isomorphism: cut stalk ≃ point-closure stalk ⧸ kernel; equal Krull dimensions.
- name-vs-content: accurate ("cosmos" is rhetoric for a quotient equiv).
- gaps: none internal.

### GSTK3PrimitiveOmniversalGraph.lean (91 lines) — NOT CI-COMPILED
- decls: 4 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: imported `GenuineK3ProductDiagonalPacket` G (the whole K3-product geometry: diagonal, point sections, h×h, degree, transverse pairing, Lefschetz operator with their laws); D submodule ≤ ker transversePairing in the last theorem
- main content: K3 diagonal primitive enters the omniversal constructor graph as a real cycle→Hodge event; primitive Lefschetz equation; nonzero; outside any divisor submodule killed by the transverse pairing.
- name-vs-content: accurate; honest "universal closure of ALL rational Hodge nodes remains unproved".
- gaps: packet unproven; graph closure unproven; dead text.

### HCProofHodgeChannels.lean (87 lines)
- decls: 0 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry; 10 #print axioms + ~50 #check
- hypotheses: none (receipt file)
- main content: pure CI verification receipt: imports the 8-module multi-channel architecture (HCProof, GSTMultiChannelHodgeCosmology, address bridge, materialization, retract, quotient, finite basis, finale) and prints axiom profiles of the crown theorems (e.g. `canonical_basis_algebraization_iff_hodge`, `hodge_channel_finale_crown`).
- name-vs-content: accurate receipt; "remains separate from HCProof.lean while GLM repairs the main entry face".
- gaps: contains no new mathematics; the architecture it certifies is in other batches.

### GSTClassicalHodgeCMSurfaceDegreeParity.lean (84 lines)
- decls: 8 theorems, 1 def, 0 structures, 0 axioms, 0 sorry (root; header: "NEEDS CI RUN LATER")
- hypotheses: none
- main content: four-divisor Koszul crossing count 3+2+1 = 6 ⇒ sign (+1); codimension/degree arithmetic for the surface-pushforward route (codim n−2 → n+2 → 2; degree 2n+4 → 4; balance 2e+2p = 2d+2q).
- name-vs-content: accurate parity/degree bookkeeping for the OpenAI/math CM paper; trivially provable facts.
- gaps: only arithmetic shadows of the CM surface criterion; no varieties.

### GSTWorldCosmologyGeneralSpaceRealization.lean (72 lines)
- decls: 1 theorem, 7 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none
- main content: the Nat×Nat cosmic-cell poset (paths = componentwise ≤) as a GeneralSpace; identity chart; shift/carry/digit paths; completed/compact fields as Realizations; finite observation = chart restriction.
- name-vs-content: accurate re-labeling of the old carrier as one chart.
- gaps: none internal.

### GSTGeneralSpaceDuality.lean (47 lines)
- decls: 2 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `DualityGeometry` (bilinear pair with left/right nondegeneracy — standard algebra as fields)
- main content: nonzero state has a detecting dual probe (and co-probe).
- name-vs-content: accurate; minimal.
- gaps: none internal.

### GSTGraphV2SixAdicOntologicalGeometryTest.lean (39 lines)
- decls: 0 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry; 5 `example`s + #check
- hypotheses: none
- main content: test harness: re-proves five imported six-adic isometry laws as anonymous examples (reflexivity, non-Archimedean transitivity, child centers in parent ball, injectivity, x4-chart preservation) and #checks the geometry laws.
- name-vs-content: accurate ("Test").
- gaps: none internal; verification-only file.

---

## BATCH SUMMARY

**Totals.** 71 files, 19,383 LOC, 726 theorems + 6 lemmas, 184 defs, 43 structures/inductives, 375 `#print axioms`. **Zero `axiom`/`opaque` declarations and zero real `sorry`s in the whole batch** — the unproven mathematics enters exclusively through (a) hypothesis-record structures whose fields are unproven propositions/functional laws, and (b) explicit theorem hypotheses. 10 files (≈3,200 LOC, incl. the two largest mathematical construction files) are dead text: not lakefile roots, never imported by any root ⇒ never CI-compiled.

### Unproven-assumption inventory (custom axioms / hypothesis-records)

No `axiom` keywords. The load-bearing unproven assumptions, by file (verbatim field content where decisive):

1. **GSTGeometricRealizationStage2** — `FiniteHodgeRealization.basisCycle_address : ∀ i ∈ hodgeSupport, encode (cycleClass (basisCycle i)) = addressBasis i` (each Hodge basis coordinate realized by an algebraic cycle); same for `CompactHodgeRealization`. *This is the ur-assumption: it literally says "supply algebraic cycles for a Hodge basis" — the Hodge conjecture in miniature.*
2. **GSTLawStackRound26** (DRAFT, never compiled) — `OpenItems` fields `involution`, `twoCellReduction`, `nonScalarExclusion`, `rankParity` ("the even split r₀ = 2a"), `stripReduction` (bare Props, the five open items (i)–(v)); `CompositionOn.pair_bit_of_items : OpenItems I → ∃ v, landing v ∧ scale v ≠ 0` (OPEN STEP 4); `CompositionOn.algebraic_of_pair : ∀ v, landing v → scale v ≠ 0 → ∃ Z : I.Cyc, I.cl Z = I.alpha` (STEP 1 "COMMITTED": Lemma N Newton conductor + determinantal machine + GAGA); `cyclo_engine_of_factorization` hypothesis `hfact : ∏ (X − C (ζ k)) = X^L − 1`.
3. **GSTPrimitiveTransverseCycleExtraction** (dead) — theorem hypotheses `h11 : DivisorsRepresentHodge11 H` (Lefschetz (1,1) assumed), `hInject : Injective P.cupH2` (Hard Lefschetz injectivity assumed); `GenuineBlowupThreeSectorPrimitivePacket` fields `exceptional_ambient_zero/first_one/second_zero` + `divisor_cup_coordinates : ∀ beta, ∃ x y, ambient (cupH β) = x ∧ first (cupH β) = y − t·x ∧ second (cupH β) = −t·y`; `GenuineBlowupPicardPrimitivePacket.exceptional_center_exact : centerReadout (cl (nativeFirstExceptional a)) = a` — the full three-sector blowup cohomology splitting is assumed, not constructed.
4. **GSTClassicalHodgeProjectiveWordOrbit** — `ProjectiveWordLiveSourceTarget.source_action` (word's cohomology action sends the live seed to a nonzero multiple of each requested Hodge sheet); finale additionally assumes `FiniteSpineMomentChain` per live weight (imported).
5. **GSTClassicalHodgeCycleOperatorNaturality** — `SpectralCycleOperator.eigenvector : operator (basis i) = eigenvalue i • basis i` (injective eigenvalues on the Hodge basis) and `CyclicSeed.class_eq : cl cycle = Σ coeff i • basis i` with all `coefficient ≠ 0` (an assumed algebraic seed hitting every selected Hodge direction).
6. **GSTClassicalHodgePiProjectiveSpectralOmniverseFinale** (dead) — `CanonicalProjectiveSpectralPacket` (ProjectiveWordSpectralFamily diagonalized on the live support + `visible`); finale assumes packets for every nonzero Hodge class.
7. **GSTClassicalHodgeWeightedCyclicCriterion** — `WeightedLocalCyclicRealization.seed_mem_atomic : (Σ coeff i • basis i) ∈ pointCycleClassSpan p (cl)` (+ nonzero coefficients, spectral operator).
8. **GSTClassicalHodgeGSTProjectiveWordExactFinale** — `hW : ∀ p j, (W p j).cohomologyOperator (spine seed) = coeff • (basis j).1`, or `R : ProjectiveTwoGenerator` family (+ `hdiag`); imported `NativeMassCycleClassBridge`.
9. **GSTClassicalHodgeCrossWeightNativePropagation** — `PureLefschetzSeedTransport.transport_formula : cohomologyOperator source = (C(2(q−p), q−p) : ℚ) • target`; `SeedPropagationFamily` (one transport per weight).
10. **GSTClassicalHodgeRealizedCorrespondenceKrylovFinale** — `RealizedCorrespondenceKrylovCertificate` (`word_hodge` fiber preservation + Hodge-typed seed cycle) + `IsKrylovCyclic : span (range hodgeOrbit) = ⊤` per weight.
11. **GSTClassicalHodgeCanonicalProjectorLanding** — `CanonicalProjectorCertificate`: `transitions : PointClassTransitionKernel` + `augmented_projector_seed : projector (seed class) = isolatedCoefficient ≠ 0 • (basis i)`.
12. **GSTClassicalHodgeDegreeCertifiedStrictPrimitiveFinale** — imported primitive stack (`RationalBettiIntersectionPrimitives`, `SchemeBiFiniteClosedCorrespondence`, `MiddleBettiCorrespondenceKernel`, `PointBettiClass`, `GeometricIncidencePrimitives`) + `hpoint` + `hact` (kernel action = eigen-scaled sheet).
13. **GSTPrimitiveMiddleHyperplaneRelative** (dead) — `HyperplanePoincareData`: `weakLefschetzLow : Surjective pullLow`, `poincareY`, `projection`, `cupAdjoint`; plus `hGysin`, `hexact` (standard identities, supplied).
14. **GSTClassicalHodgeProjectiveDefectTransport / GSTClassicalHodgePrimitivePushforwardNaturality** — `GeometricPushforwardNaturality.naturality : cl (pushforward Z) = cohomologyPushforward (cl Z)` (cycle-class functoriality as a record field) + `ProjectiveSheetIntertwines`.
15. **GSTClassicalHodgeDirectOrbitWordSaturation** — `R : ∀ q j, ProjectiveWordLiveSourceTarget …` (word reachability of every sheet) + `D : SpineTowerConservedCharge`.
16. **GSTClassicalHodgeCompositionalCorrespondenceCyclicAttack** — `IsCompositionalCyclicSeed` (algebraic seed + `ExprReaches` every target via the realized-correspondence expression algebra).
17. **GSTClassicalHodgeExactClayStatement** — `hG : ker (G p) = ppComponent` and `CycleClassHodgeCompatible : range (cl) ≤ rationalHodgeSubspace` (cycle classes are Hodge — "SOURCE-SEMANTICS hypothesis").
18. **GSTClassicalHodgeExactClayCorrespondenceRoute** — `UniversalClosedCorrespondenceSheetReachability` (named, honestly left open).
19. **GSTClassicalHodgeGeneralSpaceDefectExtinction** — `HodgeNativeSaturation` (named target).
20. **GSTK3ActualPrimitiveRankTwo / GSTK3PrimitiveOmniversalGraph** (both dead) — imported `GenuineK3ProductDiagonalPacket` (the entire K3-product geometry with its intersection/Lefschetz/transverse laws) + `GenuineK3DivisorIntersection` (`cross_value = degree²`, left/right = 0).
21. **GSTGeneralSpaceCohomology / GSTGeneralSpaceDuality / waves/CardinalWorldsPostulateLaw** — interface records (`CyclePathRealization.naturality`, nondegenerate pairing, ControlledTower controller/ledger — the last trivially satisfiable).
22. Pervasive **imported** (out-of-batch) hypothesis-records on which nearly every GSTClassicalHodge file stands: `HodgeBigradedBettiData` (the entire Hodge bigrading + cycle-class map supplied as data), `GeometricCycleClassSpine` (`algebraic_is_hodge`, pushforward naturality), `ProjectiveDegreeTraceSemantics` (`trace_point_cycleClass`, `pointDegree_pos`), `DivisorsRepresentHodge11`, `GeometricHigherLefschetzData.hardLefschetz`, `NativeMassCycleClassBridge`, `FiniteSpineMomentChain`, `GenuineK3ProductDiagonalPacket`.

Also: two Erdős-campaign "green bridge" hypotheses used as theorem arguments — `hB : erdos_even_conjecture_iff_tailF` (GSTTheActConstruction, GSTDiagonalRead) — and the open object `WindowCleanDust` emptiness / `the_act` (never proven, never assumed as axiom).

### The 5 most load-bearing files and why
1. **GSTGeometricRealizationStage2.lean** — defines the `FiniteHodgeRealization`/`CompactHodgeRealization` idiom (`basisCycle_address` = "assume algebraic cycles realize the Hodge basis"); it is the template every downstream "crown/finale" file re-instantiates with renamed hypothesis-records. Remove it and the whole conditional tower loses its shared shape.
2. **GSTLawStackRound26.lean** — the Round-26 conditional composition face: `CompositionOn.algebraic_of_pair` (the two-center conduit: Newton conductor + determinantal machine + GAGA) + `OpenItems` (i)–(v) encode the campaign's actual open boundary; and it is DRAFT-NOT-COMPILED (not a build root) — the honest mathematical core exists only as unverified text.
3. **GSTClassicalHodgeExactClayStatement.lean** — pins the literal Clay-style target (`EveryHodgeClassIsRationalAlgebraic`, finite-combination wording) and its equivalences to Stage-2G/spectral-kernel range; every finale in this batch discharges into its vocabulary; it also keeps `CycleClassHodgeCompatible` visible as an unproven source-semantics hypothesis.
4. **GSTPrimitiveTransverseCycleExtraction.lean** — the batch's largest genuine construction effort (primitive projector linearity/idempotence, all-rank Picard embedding into the primitive kernel, tangent-Chern sources, K3×K3 and cubic-fourfold analyses) — but it is dead (never compiled) and everything is conditional on `DivisorsRepresentHodge11`, Hard-Lefschetz injectivity, and the assumed blowup packets; it is the main place where "new primitive cycles" would have to become real.
5. **GSTClassicalHodgeProjectiveWordOrbit.lean** — the `ProjectiveOperatorWord` algebra + `ProjectiveWordLiveSourceTarget.source_action` interface that GSTProjectiveWordExactFinale, DirectOrbitWordSaturation and PiProjectiveSpectralOmniverseFinale all reuse; it states most compactly the one assumption ("a projective word spreads the seed onto every Hodge sheet") that the whole projective-word route needs and does not prove.

(Honorable mention: HCProofHodgeChannels.lean — the CI receipt that axiom-checks the multi-channel architecture, the only file whose whole purpose is verification rather than mathematics.)

### The single biggest gap
**The instantiation layer is missing, and the strongest candidates for it are dead text.** Across all 71 files not one theorem constructs, for an actual smooth projective variety, any of: a Hodge basis direction realized by an algebraic cycle (`basisCycle_address`), a cyclic/Krylov/projective-word/compositional seed reaching the Hodge fiber, a realized blowup/K3 packet, or the STEP-1 two-center conduit `algebraic_of_pair` — every "Hodge" theorem in the batch is conditional on such an input being supplied as a record field or theorem hypothesis. Worse, the files that come closest to constructing geometric content (GSTPrimitiveTransverseCycleExtraction, GSTQuadricPrimitiveRulingGeometry, GSTK3ActualPrimitiveRankTwo, GSTK3PrimitiveOmniversalGraph, GSTLawStackRound26, GSTNAmpleShiftIntegralRealization, GSTAllDimensionProjectivePrimitiveCycles, GSTPrimitiveMiddleHyperplaneRelative, GSTClassicalHodgePiProjectiveSpectralOmniverseFinale, pi.lean) are absent from the lakefile roots with no importing root, so their `#print axioms` receipts were never checked by CI: the campaign's constructive front is unverified text, while the verified front is bookkeeping around assumed inputs.
