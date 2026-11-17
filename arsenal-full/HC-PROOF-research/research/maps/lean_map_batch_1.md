# LEAN MAP — BATCH 1 (71 files, 19,379 LOC)

Repo: /tmp/hc-clone-23 @ 6c20bb7, branch research/gpt6-native-point-primitive-span-20261017.
Batch-wide totals: 720 theorems + 1 lemma, 174 defs, 23 structures, **0 `axiom` declarations, 0 `opaque`**, 1 `sorry` (intentional, challenge side of the DeepMind-406 comparator), ~362 `#print axioms` receipts.
Reading rule: every file ≤1200 lines read in full; GSTGraphV2OmegaWaveLaw.lean (3155 lines) read via header docstring + theorem-statement sweep + key sections (no `axiom` lines, no real `structure` decls exist in it).
Key idiom: this batch contains **no custom `axiom`s at all**; all load-bearing unproven assumptions enter as (a) `def ... : Prop` hypothesis-props passed as theorem arguments, or (b) `structure` records whose fields are unproven mathematical laws ("hypothesis-records"). These are inventoried per file and summarized at the end.

---

### GSTGraphV2OmegaWaveLaw.lean (3155 lines)
- decls: 125 theorems, 22 defs, 0 axioms, 0 sorry (75 #print axioms)
- hypotheses: (all `def : Prop` residual inputs, NOT proven here) `four_power_omega_shadow_wave : ∀ K : Nat, 8 ≤ K → omegaShadow K → ∃ p : Nat, digit3 (4^K) p = 2` where `omegaShadow K := ∃ s core, K = 3^s * core ∧ ¬3 ∣ core ∧ (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7))`; weaker residuals `four_power_omega_shadow_wave_tail`, `_tail2..tail5`, `_tailE`, `_tailF` (e.g. tailF: `∀ K : Nat, 500 < K → omegaShadowTailF K → ∃ p, digit3 (4^K) p = 2` with a 6-clause cut-word certificate).
- main content: the "Ω-wave law": exact ternary-digit arithmetic of 4^K — Ω-cut tower `4^K = 1 + 3^(a+1)·(lteCoeff a · omegaGeoSum a core)`, `digit3 (4^(3^a·core)) (a+1) = core % 3`, level-2..7 digit/cut-word laws mod 9/27/81/243/729/2187, exponent-cycle gates, LTE-coefficient stabilization, "two-observer crown" iff-classifiers, and a hypothesis-free creation certificate for the class-two family (core ≡ 2 mod 3).
- name-vs-content: "the final stroke of the GST Ontological V2 Graph route" is elementary number theory of ternary digits of powers of 4; full coverage is conditional on the unproven shadow-wave input.
- gaps: the shadow/dust exponent classes (core ≡ 4 mod 9, sheet-0 core ≡ 1 mod 9, core ≡ 7 mod 9 above sheet 0) are not covered unconditionally; `four_power_omega_shadow_wave_tailF` is identified (in other files) with the open Erdős ternary-2 statement.

### GSTClassicalHodgeKernelMassCalibration.lean (864 lines)
- decls: 41 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: `NativeMassKernelLawAtWeight : ∀ K : codimensionCycles V.X p, H.cycleClass p K = 0 → nativeCycleMass V p K = 0` — a def-Prop, used only as a case of a proven dichotomy, never assumed.
- main content: affine mass-calibration of a synchronized seed along a null-class cycle (class preserved, mass set to the Hodge-coordinate mass); unconditional dichotomy "native mass kills the class kernel OR every already-algebraic seed gets a defect-zero joint state"; exact landing classification: zero-defect landing ⟺ alpha.1 ∈ range(cycleClass) ∧ (kernel-law alternatives); repaired native transport equivariance.
- name-vs-content: honest — docstring explicitly says "not a construction of previously nonalgebraic target Hodge basis cycles".
- gaps: algebraicity is necessary (landing iff class is already in the cycle-class range); nothing here makes non-algebraic Hodge classes algebraic.

### GSTCoherentCosmology.lean (631 lines)
- decls: 40 theorems, 29 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: none (structure `WindowTower` is pure data + elementary arithmetic laws: `level : Nat → Nat`, `bounded : ∀ k, level k < 3^k`, `coherent : ∀ k s, k ≤ s → level s % 3^k = level k` — all discharged by construction for its inhabitants).
- main content: dual-current injectivity on the 4×3 cell grid; 3-adic window towers, unique innovation-stream presentation, diagonal no-countable-catalogue argument, all-two tower not natural, rectangle Gauss law on towers, and a genuine discrete ℤ-cochain complex (CosmicH1 = ker d₁ / range d₀) with observe/restrict naturality.
- name-vs-content: "Coherent GST cosmology" is finite combinatorics + elementary cochain algebra; no geometry.
- gaps: the "cosmology" is a ℕ-indexed 3-adic model; no connection to schemes or Hodge theory.

### GSTGraphV2InfiniteControlScratch.lean (574 lines)
- decls: 27 theorems, 31 defs, 3 structures, 0 axioms, 0 sorry
- hypotheses: none load-bearing; `GSTBig1ClearInfinitePathS` (structure : Prop) defines a path class by elementary constraints (bits < 2, digits < 3, d ≠ 1, bridge-step law), discharged for its inhabitants.
- main content: exact base-3/4 carry recurrences; binary-bridge event law `J + 9a' = 7d + 3a`; "I ≠ BIG1" nonzero path forced to the SURVIVE cell at every depth (base-6 maximal prefixes 6^K−1); Ω-transfer prefix sums stabilize to 3^(t+1)·N; 4^(3^t·n) energy conservation; U-charge telescoping bound; master two-regime control theorem.
- name-vs-content: "kernelizes the handwritten V2/Omega/Pi/U layer" — accurate for this standalone digit-arithmetic file.
- gaps: purely arithmetic ontology; none of it touches algebraic geometry.

### GSTK3PrimitiveGram.lean (519 lines)
- decls: 22 theorems, 14 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: none declared; the K3 geometry is hard-coded into the *definition* of `intersection d` (Gram matrix [[24,1,1,d],[1,0,1,0],[1,1,0,0],[d,0,0,d²]]) — an implicit unproven geometric input (Δ²=24, ΔU=ΔV=UV=1, B²=d²).
- main content: exact ℚ-arithmetic on formal 4-coordinate cycle classes: P=Δ−U−V−(1/d)B with P·P=21, Q=B−d(U+V) with Q·Q=3d², P·Q=0, det=63d²; K₀-source reconstruction (tangent 4[O]−[T] → norm 768; diagonal sheaf orthogonalization → P); target-period compiler (a²/768+b²/21); blowup line-bundle ch₃ returns annihilate P; Euler-pairing sign bookkeeping.
- name-vs-content: docstring is honest — "checks the full 4×4 intersection arithmetic in Lean, not the K3 Gysin/Betti comparison. It does NOT assert an arbitrary Hodge class is algebraic."
- gaps: the identification of the formal coordinates/bilinear form with genuine K3×K3 cohomology is not formalized; "rank-two primitive family for EVERY projective K3" holds only inside this model.

### GSTNAllChannelAmpleSaturation.lean (466 lines)
- decls: 23 theorems, 7 defs, 0 axioms, 0 sorry
- hypotheses: none (docstring: "That surjectivity is not assumed or proved here").
- main content: all-N integer channel model: ample shift M=Σ|a_i| makes coordinates nonnegative; calibrationDefect = Σ wᵢ(|aᵢ|−aᵢ); zero defect ⟺ all coordinates ≥ 0 (positive weights); minimal (Nat.find) shift, exact phase transition (zero defect iff k ≥ leastAmpleShift), weight-invariance of the zero locus, defect homogeneity under integer scaling.
- name-vs-content: "constructive integral ample-shift saturation in ALL finite ranks" is a finite-lattice combinatorics theorem, not geometry.
- gaps: explicitly "an independently proved geometric cycle-class realization must identify EVERY rational Hodge direction ... not assumed or proved here".

### GSTClassicalHodgeGeometricKrylovMomentDeterminant.lean (421 lines)
- decls: 10 theorems, 4 defs, 0 axioms, 0 sorry
- hypotheses: `UniversalGSTKrylovHankelNondegeneracy F : ∀ q, ∃ C : RealizedCorrespondenceKrylovCertificate V H q, ∃ trace, (krylovHankelMatrix C trace).det ≠ 0` (def-Prop, unproven); also `UniversalProjectiveDegreeKrylovNondegeneracy` (projective-degree trace variant).
- main content: Krylov/Hankel moment matrix H_ij = ℓ(T^{i+j} cl(Z)); det H ≠ 0 ⇒ the native orbit {T^j Z} spans the Hodge fiber ⇒ ∃Z, cycleClass Z = alpha for arbitrary alpha; spectral factorization det H = (det A)²·∏w_k (proven linear algebra); degree-eigenfunctional obstruction (degree-scaling correspondence ⇒ 2×2 minor zero).
- name-vs-content: "THE FULL HODGE ATTACK" — the attack is a conditional reduction; docstring: "This DOES NOT prove nonvanishing for every V."
- gaps: existence of one realized correspondence + seed + trace with nonvanishing Hankel determinant on every weight is the open input; scalar-acting words obstruct the shortcut.

### GSTClassicalHodgeClosedCorrespondenceSpectralAmplifier.lean (401 lines)
- decls: 10 theorems, 1 def, 1 structure, 0 axioms, 0 sorry
- hypotheses: `ClosedCorrespondenceWindowRealization` fields: `word : RealizedCorrespondenceWord V H p` (data) and **`on_hodge : ∀ alpha : ClassicalHodgeFiber V H p, (realizedWordPair word).cohomologyOperator alpha.1 = W.zeroComplementObservable alpha.1`** — assumes one genuine realized closed-correspondence word implements the canonical zero-complement spectral observable on the Hodge fiber; plus `PointVisible` (def-Prop: some point cycle has nonzero coordinate in sheet i).
- main content: augmented Lagrange-isolator polynomial = scaled rank-one projector on the entire Hodge fiber (proven); polynomial calculus intertwining; extraction of an exact basis cycle from one visible point; selected window algebraic.
- name-vs-content: "ONE CLOSED-CORRESPONDENCE OBSERVABLE" accurately describes the reduction, but the observable's realization is an input, not a result.
- gaps: existence of the realizing word (the "one geometric operator-realization problem") and point visibility per sheet are both unproven.

### GSTClassicalHodgeFiberedDefectProjectiveGlobalCocycle.lean (384 lines)
- decls: 17 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none of its own (consumes imported `GeometricPushforwardNaturality` records as arguments).
- main content: global functoriality of the fibered-native pushforward on native faces; exact defect cocycle `defect(f_*Φ) = f_*^H(defect Φ) + (f_*^H(hodgeFace Φ) − hodgeFace(f_*Φ))`; telescoping finite-word defect law; zero-defect transport criterion (iff Hodge-face naturality).
- name-vs-content: accurate — linear bookkeeping of the "defect" formalism.
- gaps: the whole FiberedNativeAddress/defect framework is imported; no new geometry proven here.

### GSTTailFOneLane.lean (369 lines)
- decls: 11 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: binder `hB : erdos_even_conjecture_iff_tailF` (imported iff: tailF ⟺ even-exponent Erdős ternary statement) on the two summary theorems.
- main content: one-lane case map: every exponent K+1 either owns a ternary digit 2 in 4^(K+1) or carries the complete "dust certificate" (shadow family + cut word never firing its top third at ANY depth); certificate faces imply the shadow-package clauses; the "one-lane receipt" bundles cube lift, three-window dichotomy, dust shape, and the floor identity `four_power_omega_shadow_wave_tailF ↔ ∀ K ≥ 8, noTernaryTwo (4^K) = false`.
- name-vs-content: "zero hypotheses" claim holds for the case map (one_lane_complete) but the receipt theorems do carry `hB`.
- gaps: dust-certificate emptiness (i.e. the Erdős statement) is exactly the unproven input.

### GSTClassicalHodgePiPointFiniteCorrespondenceUltimateFinale.lean (349 lines)
- decls: 10 theorems, 1 def, 1 structure, 0 axioms, 0 sorry
- hypotheses: `PointFiniteCorrespondenceWeightRealization` fields: `source : CodimensionPoint V.X p` (data), `correspondence : ∀ j, FiniteClosedCorrespondence V` (data), **`realizes : ∀ j : ClassicalHodgeBasisIndex V H p, (correspondence j).RealizesCosmicOnPoints (pointOrbitSeed G D p source).sourceIndex j`** — the GST matrix-unit realization law on every point cycle; and `PiPointFiniteCorrespondenceRealization : ∀ p, rationalHodgeSubspace … ≠ ⊥ → Nonempty (…)` (def-Prop).
- main content: point seed is a nonzero synchronized algebraic seed; per-sheet finite-support collapse `cycleClass (collapseCycle α) = α`; omniverse branch/cosmos certificates; **`bigradedBettiHodge_of_piPointFiniteCorrespondenceRealization`**: the Clay-shaped `BigradedBettiHodgeStatement V H` follows from the realization principle.
- name-vs-content: "ULTIMATE FINALE" is a conditional reduction, not a proof of the statement named.
- gaps: existence of the finite closed correspondences realizing the matrix units on every live weight is entirely open.

### GSTNPrimitiveGeometricSurgery.lean (340 lines)
- decls: 14 theorems, 8 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: none (structure `GeometricCycle` is pure ℤ³ data; the geometric relation [A]+[Y]=2[F] is hard-coded into `homology`/`surgery`).
- main content: P¹×P¹ three-current model: surgery T↦(anti−k, diag−k, ruling+2k) preserves the homology signature; defect drops by 2k; complete orbit classification (equal homology ⟺ surgery-orbit); effective-cone iff anti ≤ diagonal; ℓ¹ mass lower bound and global mass minimality of the holomorphic replacement.
- name-vs-content: honest — "a concrete geometry-specific GST N-channel boundary surgery, not a universal all-X Hodge solver".
- gaps: no actual 3-current or geometric incidence built in Lean ("NO explicit 3-current is built in Lean here"); model-level only.

### GSTClassicalHodgeGeometricMatrixRankLanding.lean (328 lines)
- decls: 5 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: `UniversalGSTGeometricDeterminantGeneration G F : ∀ q, ∃ programs : Fin (finrank) → GradedCorrespondenceProgram V H 0 q, (nativeGSTProgramHodgeMatrix G programs).det ≠ 0` (def-Prop; docstring: "It remains to prove such programs exist for arbitrary V").
- main content: general linear algebra: right inverse of the coordinate matrix reconstructs any x from supplied vectors (proven, clean); determinant form via NonsingularInverse; **`exact_hodge_of_universal_GST_geometric_determinants`**: BigradedBettiHodgeStatement from one nonzero determinant per weight.
- name-vs-content: "UNIVERSAL GST HODGE ATTACK" = a correct reduction of Hodge to a scalar determinant nonvanishing; the geometry is future work.
- gaps: the determinant nonvanishing for genuine correspondence-program outputs on arbitrary V is precisely the unproven geometric challenge.

### GSTClassicalHodgeExplicitArsenalGeneration.lean (319 lines)
- decls: 15 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: on the finite pure window: forward matrix unit E_pq = normalized P_q∘L^(2(q−p))∘P_p (central-binomial scalar, exact receipts); backward unit by Poincaré-reversal conjugation; every matrix unit generated by the projector/Lefschetz/Poincaré algebra.
- name-vs-content: accurate for the finite formal model.
- gaps: "Lefschetz operator" here is the formal window operator, not a geometric cup-with-ample operator; no realization on a variety.

### GSTGraphV2CanonicalRenormalization.lean (309 lines)
- decls: 11 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none.
- main content: exact recurrences of `canonicalTail r a = (4^(3^r·a) − 1)/3^(r+1)`: block recurrence, power-block recurrence, two-unit square expansion, 3-adic phase strip (phase a recovered exactly, renormalized quotient = affine packet).
- name-vs-content: accurate (elementary 3-adic arithmetic of the 4-vs-3 quotient).
- gaps: none internally; supports the digit-arithmetic campaign only.

### GSTClassicalHodgeRankFreeLefschetzPoincareGeneration.lean (302 lines)
- decls: 11 theorems, 3 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: transport of the finite LP-word identity to arbitrary Hodge fibers (hodgeMatrixUnit = lifted two-slot L² word); **honest obstruction section**: L/Λ-words kill joint-primitive vectors, finite LP combinations stay in the source line, cannot hit an independent primitive direction; degree-trace Hankel matrix is identically zero on primitive sectors (degree factors through cup-L).
- name-vs-content: accurate, and unusually honest about its own negative results ("discriminates the missing geometric-source operator").
- gaps: the abstract two-slot operator is NOT realized by genuine cup-L words — exactly the missing link the file proves is nontrivial.

### GSTClassicalHodgeProjectiveSpectralCover.lean (296 lines)
- decls: 9 theorems, 1 def, 2 structures, 0 axioms, 0 sorry
- hypotheses: `ProjectiveWordSpectralFamily` fields: word (data), basisIndex (injective), eigenvalue (injective ℚ), **`eigenvector : ∀ i, (word.operatorPair G).cohomologyOperator (basis i).1 = eigenvalue i • (basis i).1`** — simple rational spectrum of a genuine projective word on selected Hodge sheets; `FiniteProjectiveSpectralCover` adds **`covers_live_support`** and **`visible : ∀ k, CoordinateVisible k`**.
- main content: projective words have native point lifts ⇒ atomic-span stability (derived); coordinatewise visibility ⇒ cyclic seed ⇒ selected sheets algebraic; **`bigradedBettiHodge_of_finite_projective_spectral_covers`**: one finite cover per nonzero class suffices for the full Hodge statement.
- name-vs-content: "ONE PROJECTIVE WORD / FINITE SPECTRAL COVER" describes the interface; existence of covers is the input.
- gaps: constructing the spectral word with distinct rational eigenvalues and per-sheet visibility for arbitrary V/Hodge classes is open.

### GSTClassicalHodgePiSpineTwoGeneratorUnboundedFinale.lean (286 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `D : SpineTowerConservedCharge G` (imported conserved-charge record) and **`R : ∀ p j, ProjectiveTwoGenerator (seed.sourceIndex) j`** (imported two-generator realization per target) as theorem binders.
- main content: canonical spine seed per weight; target cycles via two-generator words with `cycleClass = basis j`; three-sector omniverse + unbounded higher-causal certificates; **`bigradedBettiHodge_of_spine_projectiveTwoGenerator_omniverse`**.
- name-vs-content: "UNBOUNDED FINALE" is again a conditional crown; omniverse layers are decorative semantics.
- gaps: SpineTowerConservedCharge and ProjectiveTwoGenerator existences are the unproven inputs.

### GSTClassicalHodgeCoordinatewiseSeedAssembly.lean (278 lines)
- decls: 5 theorems, 1 def, 1 structure, 0 axioms, 0 sorry
- hypotheses: `CoordinatewiseVisibleLocalRealization` fields: spectral (data), spectral_basisIndex, **`visible : ∀ i : HodgeSupportIndex alpha, ∃ a, (∑ a_j • basis_j) ∈ pointCycleClassSpan ∧ a i ≠ 0`** — per-sheet atomic visibility.
- main content: genuine finite hyperplane avoidance over ℚ (Subspace.exists_eq_top_of_iUnion_eq_univ): coordinatewise visibility assembles one cyclic seed with all coefficients nonzero; criterion theorem `bigradedBettiHodge_of_coordinatewise_visible_realizations`.
- name-vs-content: accurate; the real math is the classical "vector space over infinite field is not a finite union of proper subspaces".
- gaps: visibility itself (a geometric statement about point-cycle spans) is not proven anywhere in this file.

### GSTClassicalHodgeDegreeCertifiedFullCorrespondenceCompiler.lean (275 lines)
- decls: 7 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `FullCorrespondenceSourceTargetProgram` fields: program (data) + **`source_action : program.cohomologyEval G S.hodge.1 = (repr S.hodge S.sourceIndex) • (basis j).1`**; degree-certified specialization needs imported `hlive : ProjectivelyLiveSource …` and **`hExact : Order.coheight (ambientSuccessorPoint …) = p + 1`**.
- main content: naturality turns the one-source action law into an exact target-basis cycle; weightwise crown `hodge_weight_of_degreeCertifiedFullCorrespondencePrograms`.
- name-vs-content: "COMPILER" is fair (interface builder); the geometric action law is an input.
- gaps: producing verified correspondence programs with prescribed action on a degree-certified source, plus liveness/coheight-exactness, is open.

### GSTClassicalHodgeNativeCycleCosmicShadow.lean (269 lines)
- decls: 13 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `hpoint : ∀ x : CodimensionPoint V.X p, successorMass V p x = limitlessLefschetzScalar p (p+1)` (uniform successor-mass law) inside the propagation theorem.
- main content: `nativeCycleMass` (sum of point-presentation coefficients; unit point = 1) and the "cosmic shadow" linear map into a formal ℕ-indexed basis; matrix-unit read/write moves mass between weights; propagation of mass along the cut tower conditional on the uniform point-mass law.
- name-vs-content: "direct artery from genuine projective cycles into the limitless GST address universe" — the universe is a Finsupp basis; content is bookkeeping.
- gaps: well-definedness of "mass" leans on the imported point normal form; the uniform successor-mass hypothesis is unproven.

### GSTFourPowerAffineChannelAutomaton.lean (261 lines)
- decls: 12 theorems + 1 lemma, 8 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: ternary-digit automaton for pairs (x, 4x+c): exact one-trit splits, master recursion `PairCommonTwo x (4x+c) ⟺ lowSuccess ∨ PairCommonTwo(tail3 x, 4·tail3 x + next)`, four-state channel transition tables, channel closure under all iterates.
- name-vs-content: accurate (finite automaton arithmetic).
- gaps: none internally; feeds the 4x+c ternary digit program.

### GSTMultiChannelHodgeCosmology.lean (257 lines)
- decls: 11 theorems, 5 defs, 0 axioms, 0 sorry
- hypotheses: none ("No algebraic variety, cycle class, or Hodge-conjecture conclusion is assumed here").
- main content: Wave-II channel model: Fin S.holes → ℚ with Kronecker basis; arbitrary same-weight rank; rectangular rational diagonal classification with unique coefficients and finite cycle expansion.
- name-vs-content: "HODGE COSMOLOGY" is a coordinate model — the word "Hodge" is a label on a ℚ-vector-space combinatorics.
- gaps: no geometry; "materialization of channel generators is handled by the next layer".

### GSTClassicalHodgeUniversalTwoSlotNativeClosure.lean (253 lines)
- decls: 4 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `PrimitiveNativeTwoSlot` fields: **source / lefschetz / target : `HasNativePointLifts`** for the ambient source projector, the rationalized L² primitive, and the ambient target projector — three primitive geometric point-transition laws.
- main content: ambient extension of Hodge endomorphisms; the ambient two-slot word equals the rank-free matrix unit on the Hodge fiber (long computational identity); native point-lift closure under composition/scaling ⇒ atomic-span stability of the universal word.
- name-vs-content: accurate — "reduces the unrestricted arsenal externalization to three primitive geometric point-transition laws".
- gaps: the three HasNativePointLifts laws (geometric realization of projectors and L² by native cycles) are unproven.

### GSTHodgeChannelMaterialization.lean (248 lines)
- decls: 9 theorems, 1 def, 1 structure, 0 axioms, 0 sorry
- hypotheses: `ChannelHodgeRealization` fields: shape (data), coordinates (linear equiv hodge ≃ channel coords), channelCycle (data), **`channelCycle_mem : cycleClass (channelCycle i) ∈ hodge`** and **`channelCycle_coordinate : coordinates ⟨cycleClass (channelCycle i), _⟩ = channelBasis i`** — materialization of the canonical channel generators; `Stage2GChannelMaterializationObligation : ∀ p, Nonempty (Stage2GChannelMaterialization V H p)` (def-Prop).
- main content: channel superposition materializes every Hodge class (`channelCycleWitness_spec`); **`hodge_channel_materialization_crown`**: obligation ⇒ BigradedBettiHodgeStatement.
- name-vs-content: accurate ("generator algebraicity implies Hodge-surjectivity") — clearly flagged as conditional.
- gaps: constructing the channel basis (equivalently a Hodge basis of algebraic classes) per weight is the open obligation.

### GSTClassicalHodgePiStrictKernelCyclicOmniverseFinale.lean (242 lines)
- decls: 8 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `StrictKernelCyclicPacket` (the "geometry-first" bundle): topology `RationalBettiIntersectionPrimitives` (imported data-with-laws), correspondence `SchemeBiFiniteClosedCorrespondence`, kernel `MiddleBettiCorrespondenceKernel`, **`pointClass_eq : ∀ x, H.cycleClass p (codimensionPointCycle x) = pointClass x`**, `incidence : GeometricIncidencePrimitives …`, **eigenvalue/eigenvector** (simple spectrum of kernelAction on live basis), nonzero coefficients, **`seed_class`** (cyclic native seed).
- main content: kernel action preserves the cycle-class range (derived from the packet); spectral operator + cyclic seed ⇒ every live sheet algebraic ⇒ **`bigradedBettiHodge_of_strictKernelCyclicPackets`** (every nonzero target admits a packet).
- name-vs-content: "OMNIVERSE FINALE" — the load is entirely in the packet's unproven fields.
- gaps: existence of the bi-finite closed correspondence with the stated kernel action, the point-class synchronization, and simple spectrum is the whole geometric problem.

### GSTClassicalHodgeNativeWordFromArbitrarySeed.lean (237 lines)
- decls: 7 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `NativeHodgeSeed` (cycle + class_is_hodge + class_ne_zero — mild); the heavy binder is imported **`R : ∀ p j, GeometryFirstTwoGenerator (seed.sourceIndex) j`**.
- main content: arbitrary nonzero algebraic Hodge seed + native GST matrix-unit word ⇒ normalized target cycle hits each basis vector; **`bigradedBettiHodge_of_active_nativeHodgeSeeds`** (active-weight version avoids demanding seeds at dead weights).
- name-vs-content: accurate description of the interface ("geometry only has to supply one nonzero Hodge cycle class in each weight").
- gaps: GeometryFirstTwoGenerator (the two primitive realizations per ordered pair) is imported and unproven here.

### GSTClassicalHodgeLiveSheetIntertwining.lean (231 lines)
- decls: 7 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none.
- main content: tethering of live Hodge-support indices to finite GST sheet indices; sheet coefficient = original Hodge basis coefficient; denominator clearing preserves nonzero sheets; the tethered integer projector is an explicit integer polynomial with nonzero scalar.
- name-vs-content: accurate (index bookkeeping).
- gaps: none internal; purely combinatorial bridge.

### GSTGeometricRealizationStage2B.lean (227 lines)
- decls: 7 theorems, 3 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `HodgeSubspaceRealization` fields: hodge submodule + cycleClass (data), encode (injective linear chart), **`hodge_supported`**, and **`basisCycle_address : ∀ i ∈ hodgeSupport, encode (cycleClass (basisCycle i)) = addressBasis i`** — algebraic realization of the support basis coordinates; `FiberRealizationObligation` (def-Prop) names the remaining data.
- main content: Stage-2A→2B upgrade: submodule form of the target `hodge ≤ range(cycleClass)`; variable-rank family theorem; obligation ⇒ fiber theorem.
- name-vs-content: honest — "A literal proof of the classical Hodge conjecture still requires a native instantiation…".
- gaps: the realization data (basis cycles hitting address basis vectors) is exactly the unproven per-fiber obligation.

### GSTClassicalHodgeOmniverseStrictEventStability.lean (223 lines)
- decls: 5 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: `StrictlyMaterializedBranch` (def-Prop): ∃ d, P (Betti intersection primitives), K (bi-finite closed correspondence), κ (kernel), pt (point classes) with **`∀ z, H.cycleClass p (pointCycle z) = pt z`**, incidence primitives I, and **`y.state.1 = kernelAction … x.state.1`** — each GST branch event is literally the cup/Gysin action of a genuine correspondence; plus imported hlive/hExact for the degree-certified source.
- main content: strictly materialized events preserve the algebraic range (derived); event-stability + one nonzero algebraic source + reachability ⇒ every basis sheet algebraic ⇒ **`hodge_weight_of_strictOmniverse`** / `hodge_weight_succ_of_degreeCertified_strictOmniverse`.
- name-vs-content: accurate; the "omniverse" graph reachability is imported combinatory semantics.
- gaps: strict materialization of every primitive branch event (the correspondence/kernel/incidence packet) is unproven.

### GSTClimbTruthValue.lean (218 lines)
- decls: 14 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: binders `hB : erdos_even_conjecture_iff_tailF`, `hOdd : erdos_ternary_2_conjecture_odd` (imported, proven elsewhere in repo), `hClimb : GSTInfiniteFourPowerNavigation.four_power_happy_climb` (imported unproven climb law).
- main content: the conditionality certificate: climb ⇒ full Erdős ternary statement (∀ n ≥ 9, 2^n owns a ternary digit 2); verified instances K=5,6,7; floor witness (conjecture holds at K=7 while climb fails — the climb is the strictly stronger pair-demand); explicit Happy rows at K=8,9,10; exact floor iff under the climb.
- name-vs-content: honest and important — states plainly that hTailF's single hypothesis "carries the entire remaining content of the conjecture".
- gaps: `four_power_happy_climb` (∀ K ≥ 8, ∃ p ≥ 3, digit3(4^K)p = 2 ∧ carry ∈ {0,3}) is open; machine-checked only on [8,5000].

### GSTGraphV2PerfectPowerBlockCollision.lean (214 lines)
- decls: 7 theorems, 3 defs, 0 axioms, 0 sorry
- hypotheses: none (conditional hypotheses hChild/hRightBad are per-theorem inputs describing a Happy cell + bad right strip).
- main content: pure x4/base-3 divergence density: Happy ⟺ positive blockDensity (12-cell decide table); exact vertical telescope; terminal N-wave packet transfer; terminal right-boundary density nonpositivity.
- name-vs-content: accurate (combinatorial density bookkeeping).
- gaps: "deliberately does not assert that the shifted Happy/bad packet is contradictory" — no contradiction/termination result here.

### GSTGraphV2FourPowerResidueObstruction.lean (209 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: row-p digit of 4^K is periodic in K with period 3^p (LTE); row-2 overlap (consecutive digit-2 pairs in 4^K, 4^(K+1)) ⟺ K ≡ 5,6 (mod 9); no-common-two forbids those classes; relocated Happy classification.
- name-vs-content: accurate (exact residue classification).
- gaps: none internal.

### GSTClassicalHodgeConstructiveCyclicLanding.lean (205 lines)
- decls: 7 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `LocalCycleSpectralRealization` fields: `spectral : SpectralCycleOperator V H p (HodgeSupportIndex alpha)` (imported data-with-laws), `spectral_basisIndex`, `seed : spectral.CyclicSeed` (imported).
- main content: finite-support recombination of extracted live-basis cycles gives `cycleClass (reconstructedCycle) = alpha.1`; point-presentation form; crown `bigradedBettiHodge_of_local_cycle_spectral_realizations`.
- name-vs-content: "fully constructive local landing theorem" is accurate *given* the local spectral realization.
- gaps: SpectralCycleOperator + CyclicSeed existences are imported hypotheses (in other files of the campaign).

### GSTLefschetzCrownV2.lean (202 lines)
- decls: 16 theorems, 3 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: exact ℤ-arithmetic of the Lefschetz operator on the 12-cell wave lattice: degree-by-degree maps with exact matrices; complementary powers L⁵ = ×10 (det 10), L³ = [[3,3],[1,3]] (det 6), middle unimodular (det 1) with explicit integral section; injectivity; non-surjectivity at unit scale (1 not in 10·ℤ).
- name-vs-content: accurate — "EXACT COMPLEMENTARY-POWER ARITHMETIC" of a finite combinatorial lattice (a hard-Lefschetz analogue for the GST model).
- gaps: model-only; no variety, no (1,1)-theorem content.

### GSTClassicalHodgeCanonicalPointIncidenceTransfer.lean (199 lines)
- decls: 6 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: `SuppliedPointDirectIncidenceLaw` (def-Prop): for P (Betti cup/Gysin primitives), K (bi-finite closed correspondence), κ (kernel): **∀ x, P.gysinTheory.sndGysin (2p) (P.cupTheory.cup (2d) (2p) κ.kernelClass (fstCohomologyPullback (cycleClass (pointCycle x)))) = H.cycleClass p (K.nativePointImage p x)** — the single pointwise incidence equation.
- main content: canonical point class (cycle class of the point atom) makes the old point-class parameter definitional; the direct law manufactures the full incidence packet; global transfer `cycleClass (nativeOperator Z) = kernelAction (cycleClass Z)` from the one point law.
- name-vs-content: honest — "does NOT claim that the supplied Stage-2G map has already been identified with an independently constructed geometric fundamental-class theory".
- gaps: the direct incidence law itself (a genuine intersection-theory computation) is not proven here; semantic rigidity (ruling out the zero-map copy) is explicitly still required.

### GSTClassicalHodgeLimitlessProjectiveLefschetzTower.lean (197 lines)
- decls: 11 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: `hstep : ∀ p Z, cl (p+1) (successorNativeOperator V p Z) = L p (cl p Z)` (single-step comparison law) in the tower-identification theorem.
- main content: projective cut tower (recursive principal-cut successor from the fundamental cycle); cosmic Lefschetz tower with exact central-binomial coefficients C(2p,p) ≠ 0; one-step law identifies all tower levels.
- name-vs-content: accurate (parallel tower packaging).
- gaps: the single-step comparison (geometric cut step = cosmic Lefschetz step) is the unproven identification.

### GSTClassicalHodgeVerticalRayMassFactorization.lean (195 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: imported binders: `F : NativeMassCohomologyFactorization` (native mass factors through genuine cycle class), **`vertical : ∀ p live, ExactVerticalCutRayCertificate V p`** (one exact vertical ray per live weight), `hclose : GhostWeightPrimitiveStrictClosure G`.
- main content: unit-degree trace manufactured from native-mass factorization; ray + factorization ⇒ cut-tower class nonzero ⇒ canonical synchronized seed on every live weight; ghost-weight survival derived; **`hodge_of_massFactorization_verticalRays_and_strictClosure`** ⇒ BigradedBettiHodgeStatement.
- name-vs-content: accurate chain, but every link's input is an imported unproven package.
- gaps: NativeMassCohomologyFactorization, ExactVerticalCutRayCertificate, and strict ghost closure are all open (defined in files outside this batch).

### GSTClassicalHodgeNativePointSeedSaturation.lean (192 lines)
- decls: 8 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `NativePointHodgeSeed` fields: point (data), **`class_is_hodge : cycleClass (pointCycle) ∈ rationalHodgeSubspace`**, **`class_ne_zero`** — one genuine point with nonzero (p,p) class; plus imported `R : ∀ i j, GeometryFirstTwoGenerator i j`.
- main content: one point seed ⇒ algebraic Hodge subspace ≠ ⊥; with two-generator realization ⇒ algebraic subspace = ⊤ ⇒ every (p,p) class has a native cycle; active-weight crown.
- name-vs-content: accurate ("keep the remaining geometric construction literal").
- gaps: existence of a point with nonzero Hodge class in each weight and the GeometryFirstTwoGenerator family are the unproven geometric inputs.

### GSTClassicalHodgeTotalSheetMatrixUnit.lean (187 lines)
- decls: 7 theorems, 4 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: Poincaré-dual reflection on square-world coefficients (involutive, preserves pure diagonal support); backward sheet matrix unit via mirror-forward-dual; total matrix unit exact for every ordered pair; nonzero source sheets survive transport.
- name-vs-content: accurate (finite combinatorial matrix units).
- gaps: model-level; no geometry.

### GSTClassicalHodgeCycleClassIntersectionPrimitives.lean (186 lines)
- decls: 3 theorems, 0 defs, 4 structures, 0 axioms, 0 sorry
- hypotheses: the three "standard facts" as data: `PointCylinderPullbackLaw` (**class_eq_fstPullback**: cylinder class = p₁* point class), `KernelFiberIntersectionLaw` (**class_eq_kernel_cup_cylinder**: [C] ∪ cylinder class = fiber intersection class), `ProperProjectionFiberLaw` (**gysin_class**: p₂! of the intersection class = geometric cycle class of the native point image); bundled as `GeometricIncidencePrimitives`.
- main content: derives `kernelAction (pt x) = GeometricCycleClass (nativePointImage x)` from the three laws (the point transfer theorem is *proved* from the packet, not stored).
- name-vs-content: accurate decomposition of the point-incidence calculation.
- gaps: the three standard intersection-theory laws themselves are inputs (structures with propositional fields) — no Künneth/cup/proper-pushforward theorem is proven here.

### GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra.lean (185 lines)
- decls: 4 theorems, 1 def (inductive), 0 axioms, 0 sorry
- hypotheses: none (HasGeometricIdentity is defined as an explicit capability, not assumed).
- main content: free noncommutative expression algebra over realized finite closed correspondences (zero/atom/smul/add/comp); operatorPair evaluation; exact native/cohomology commuting square for every expression; range and atomic-span stability; positive iteration (no zero-th power by design).
- name-vs-content: accurate (syntax layer with preserved naturality).
- gaps: `HasGeometricIdentity` (a geometric identity correspondence) is stated as a capability Prop and left open — though the diagonal correspondence is built elsewhere (GSTClassicalHodgeDiagonalIdentityCorrespondence).

### GSTClassicalHodgeOntologicalWindowReverseExistence.lean (178 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: contrapositive reverse-existence: an all-bad row/window has nonpositive reverse/weighted ontological current; hence every strictly positive finite GST window contains at least one genuine Happy cell; graph specialization with explicit live witness.
- name-vs-content: accurate; explicitly replaces a rejected "reverse-window postulate" with a proven weaker form.
- gaps: positivity of the relevant windows is not established here.

### GSTClassicalHodgeTwoSlotLefschetzPoincareGeneration.lean (178 lines)
- decls: 5 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: exact 2-slot identity `twoSlotCode = (1/2)·L²∘P` (Poincaré reversal), proven from pure-diagonal Lefschetz receipts (L²e₀ = 2e₁, L²e₁ = 0); source projector = id − (1/2)L²P; lift to every ordered Hodge basis pair.
- name-vs-content: accurate ("the code/projector language is derived polynomial/composite syntax").
- gaps: "does not assume native classical externalization of Poincaré" — i.e., the geometric realization of P is still missing.

### GSTGraphV2PowerThreeWaveObservation.lean (174 lines)
- decls: 3 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: per-theorem inputs hChild (one Happy cell on a power sheet) and hRightBad (all-depth bad boundary).
- main content: width-three wave observation packet: positive left phase window, nonpositive right window, exact strip equation `64·digit + wideCarry = digit' + 3·wideCarry'`, strictly positive coupled-U derivative; quantized form (U-derivative ≥ 1).
- name-vs-content: accurate (a combinatorial observation, not a contradiction).
- gaps: explicitly "the information is not discarded or turned into a one-step contradiction".

### GSTWorldCrownBridge.lean (172 lines)
- decls: 9 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: the old 12-cell cup operators are native axis transports under the chart equivalence: cup commutation and 3/4-boundary nilpotence (cupDigit³ = 0, cupCarry⁴ = 0) absorbed from the dimension-free world laws.
- name-vs-content: accurate (chart theorem).
- gaps: none internal.

### GSTK3TranscendentalHodgeCompleteness.lean (169 lines)
- decls: 3 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: **`hKunnethKernel : ker(transcendentalReadout) ≤ genuineDivisorWordHodgeSubspace`** (Künneth/divisor-word kernel containment) and **`hScalarEndomorphisms : ∀ u ∈ E, ∃ c : ℚ, u = c • readout(diagonal)`** (scalar End_HS(T(S)) — valid for very general K3, NOT all K3s).
- main content: classical K3 structure argument: under (1)+(2), every rational (2,2) class on S×S is a divisor word + scalar diagonal ⇒ **all_middle_hodge_classes_from_scalar_K3_geometry**: every rational (2,2) Hodge class on the product is algebraic.
- name-vs-content: honest — "not a restatement of full Hodge surjectivity"; assumptions flagged as independently geometric.
- gaps: the two K3 facts are assumed, not proven; they fail for K3s with non-scalar transcendental endomorphisms.

### GSTClassicalHodgeProjectiveCorrespondenceCosmicRealization.lean (164 lines)
- decls: 4 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `ProjectiveCosmicRealization` fields: kernel (data) + **`acts_as_cosmic : ∀ alpha, (projectiveCorrespondencePair G kernel).cohomologyOperator alpha.1 = canonicalCosmicAmbient i j alpha.1`**.
- main content: correspondence algebra pairs have exact cycle-class squares; a realization for every ordered pair ⇒ CanonicalCosmicNaturality ⇒ (with nonzero algebraic seed) the weight-p Hodge fiber is algebraic.
- name-vs-content: accurate interface file ("represent the single canonical two-sheet GST read/write word inside the projective correspondence algebra" is named as the remaining target).
- gaps: the acts_as_cosmic realization is unproven; seed nonzeroness is a separate input.

### GSTClassicalHodgePrimitiveArsenalIrreducibility.lean (160 lines)
- decls: 11 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none.
- main content: PrimitiveArsenalInvariant (stability under projector/Lefschetz/Poincaré alone) ⇒ FullArsenalInvariant ⇒ zero-or-top irreducibility; one nonzero primitive-stable seed generates every basis vector.
- name-vs-content: accurate (finite-dimensional linear algebra).
- gaps: model-level; the "externalization" (naturality of these operators on real cohomology) is the missing layer.

### GSTClassicalHodgeCanonicalNaturalityEquivalence.lean (157 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `hseed : AlgebraicFiber ≠ ⊥` (one nonzero algebraic Hodge seed).
- main content: **the key honest equivalence**: given a seed, `CanonicalCosmicNaturality p ⟺ AlgebraicFiber p = ⊤ ⟺ rationalHodgeSubspace ≤ range(cycleClass)`; base cosmic shadows cannot distinguish multiplicity sheets or points.
- name-vs-content: accurate and self-critical — "it is not legitimate to insert canonical cosmic naturality as an unexplained formal assumption and call the Hodge proof complete."
- gaps: the single naturality law (preservation of the algebraic range by the canonical read/write operator) is the entire remaining fixed-weight content.

### CardinalWorldsPrefixClassifier.lean (154 lines)
- decls: 8 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: exact arbitrary-depth classifier: hasTernaryTwo(4^K) ⟺ ∃ p, (digit3 (4^(exponentPrefix K p)) (p+1) + exponentTrit K p) % 3 = 2; signature-free ⟺ all prefixes avoid; old mod-9/27/81 certificates become shallow corollaries.
- name-vs-content: accurate (prefix classifier).
- gaps: none internal.

### GSTClassicalHodgeRelativeSuccessorExactStratum.lean (149 lines)
- decls: 5 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: `RelativeSuccessorAmbientExact V p x : ∀ y ∈ relativeCodimensionOneFinset, Order.coheight (ambientSuccessorPoint V x y) = p + 1` (ambient codimension additivity).
- main content: under exact grading, every selected successor contributes a unit atom; successor mass = cardinality of the relative cut; nonempty cut ⇒ nonzero successor cycle (crown).
- name-vs-content: accurate ("no Hodge class, Hodge basis, or cycle-class surjectivity occurs").
- gaps: ambient codimension additivity + nonemptiness in live positive dimension are stated as the two remaining pure scheme statements, unproven here.

### GSTClassicalHodgeBasisCycleBridge.lean (146 lines)
- decls: 4 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `HodgeBasisCycleBridge` fields: basisCycle (data) + **`basisCycle_spec : ∀ i, H.cycleClass p (basisCycle i) = (hodgeBasis V H p i).1`** — every Hodge basis vector has an algebraic representative (the irreducible datum).
- main content: basis lift linear map with exact spec; basis-wise algebraicity ⇒ arbitrary rational (p,p) class has a native cycle. Extracted from HodgeConjecture.lean to break a circular import.
- name-vs-content: accurate (the named bridge is exactly what it does).
- gaps: the bridge itself is the hypothesis; nothing constructs it.

### GSTCompactNativeCyclePresentation.lean (143 lines)
- decls: 5 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: real Mathlib infrastructure: on a compact scheme every locally finite algebraic cycle has finite support; ℙⁿ_ℂ is Zariski-compact (graded-ring finite-type argument); smooth projective complex schemes are compact; finite point presentation of native cycles.
- name-vs-content: accurate and genuinely useful.
- gaps: none — this is solid, reusable foundation.

### GSTClassicalHodgeClosedCorrespondenceCosmicRealization.lean (139 lines)
- decls: 2 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: imported **`hReach : ∀ i j, MatrixUnitReachableByClosedCorrespondences V H i j`** (a realized correspondence word acts as E_ij on the Hodge fiber) + `hseed : AlgebraicFiber ≠ ⊥`.
- main content: reachability ⇒ NativeCanonicalCosmicRealization family (agreement extends from the Hodge fiber to ALL algebraic cycle classes via the spine) ⇒ CanonicalCosmicNaturality ⇒ **`hodgeWeight_of_closedCorrespondence_cosmicRealization`**.
- name-vs-content: accurate architecture summary; the input is the whole geometric problem.
- gaps: MatrixUnitReachableByClosedCorrespondences is an imported unproven def-Prop.

### GSTCanonicalTailStateIso.lean (138 lines)
- decls: 8 theorems, 4 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: exact digit/carry slice isomorphisms through low prefixes (seed-zero cuts); `Navigation N := ∃ p, HappyCell (carry4 N p) (digit3 N p)`; canonical tail isomorphism for R = 1 + 3^b·Q.
- name-vs-content: accurate (state-isomorphism arithmetic).
- gaps: none internal.

### GSTUniversalProjectiveProductPrimitive.lean (133 lines)
- decls: 5 theorems, 3 defs, 0 axioms, 0 sorry
- hypotheses: none declared; the cohomology ring of X×P² (u^(d+1)=0, v³=0, Hard-Lefschetz multiplier) is hard-coded into the 3-coordinate model.
- main content: P_d = u² − (d−1)uv + (d(d−1)/2)v² is primitive (killed by L^(d−1)) and nonzero; the primitive part of the hyperplane subalgebra is exactly ℚ·P_d; uniform constructor.
- name-vs-content: honest — "does NOT claim to formalize the scheme-theoretic cohomology ring or the external classical ample intersection theorem".
- gaps: model-level verification only; primitive cohomology of X outside the hyperplane subalgebra untouched.

### GSTFourPowerDirectCreationMaster.lean (129 lines)
- decls: 5 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `hDirect : FourPowerDirectExistence` (imported def-Prop — direct common-two existence) in the master theorem.
- main content: exact equivalence `CommonTwo K ⟺ CreationCertificate (4^K)`; direct existence ⟺ historical creation master.
- name-vs-content: accurate (interface equivalence).
- gaps: FourPowerDirectExistence itself is the open surface (reduced elsewhere to Happy-row providers).

### GSTFourPowerDirectResidue81.lean (127 lines)
- decls: 4 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none.
- main content: row-four overlap classes modulo 81: fourteen explicit residues {8,20,41,42,51..58,66,76}; exact iff-classifier for consecutive digit-2 pairs at row 4 (exhaustive, not merely sufficient); no-common-two avoids them all.
- name-vs-content: accurate (pure arithmetic classifier).
- gaps: none internal.

### GSTClassicalHodgeStrictKernelRangeStability.lean (121 lines)
- decls: 3 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: per-theorem inputs: P/K/κ (data) + **`hpoint : ∀ x, cycleClass (pointCycle x) = pt x`** + **`I : GeometricIncidencePrimitives …`** (the three intersection laws).
- main content: a strict correspondence kernel and its factor-swapped transpose preserve the genuine cycle-class range (AlgebraicBettiRange).
- name-vs-content: accurate consequence layer.
- gaps: the hpoint synchronization and incidence packet are unproven inputs (see CycleClassIntersectionPrimitives).

### GSTK3GeometricSourceToArbitraryX.lean (116 lines)
- decls: 2 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: the K3 pair (hKunnethKernel + hScalarEndomorphisms as above) + imported **`R : NativeHodgeRetract Y X D H 2 p`** (a Hodge-preserving Chow retract from the K3 product to the arbitrary target X).
- main content: K3-source algebraicity transported to arbitrary X: every target (p,p) class gets a native codim-p cycle; fixed-weight fiber covered.
- name-vs-content: honest — "The existence of such a Hodge-preserving Chow-retract for every arbitrary X is not proved: the condition is meaningful, very restrictive geometry, not a hidden universal axiom."
- gaps: the retract is a very strong unproven condition; universal coverage would need sources of sufficient geometric rank.

### GSTFourPowerDirectExistenceNoAxiom.lean (110 lines)
- decls: 5 theorems, 0 defs, 0 axioms, 0 sorry (the single grep hit for "sorry" is the word "sorryAx" inside a comment about another file's audit)
- hypotheses: `happy_ge_three : ∀ K ≥ 8, ∃ p ≥ 3, HappyCell (carry4 (4^K) p) (digit3 (4^K) p)` (row-3 Happy provider) as the sufficient input.
- main content: Happy cell ⇒ same-row CommonTwo; direct base cases K=5,6; **`fourPowerDirectExistence_iff_physical_happy_positive`**: direct existence ⟺ positive-row physical Happy forcing on the exact production domain — the exact boundary identified.
- name-vs-content: accurate ("no-axiom bridge"; deliberately avoids the dirty navigation provider whose audit contains sorryAx).
- gaps: the Happy-row provider for K ≥ 8 remains open (this is the climb/shadow-wave input again).

### GSTClassicalHodgeCompactPresentationRoundtrip.lean (106 lines)
- decls: 2 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: exact roundtrip `realize (presentationOfNativeCycle Z) = Z` on smooth projective carriers; presentation map injective.
- name-vs-content: accurate (lossless finite presentation).
- gaps: none — solid infrastructure.

### GSTClassicalHodgeCMGaloisConjugateSpan.lean (101 lines)
- decls: 3 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: field automorphisms fixing ℚ preserve finite algebraic tensor expansions with the same rational generators; nonzero periods stay nonzero under conjugation; rational targets admit conjugated coefficients.
- name-vs-content: accurate small algebra lemma ("without asserting the geometric factor identifications themselves").
- gaps: the CM surface-switch geometric identifications are not formalized.

### GSTClassicalHodgeSeparatorAmbientPrimeInterval.lean (95 lines)
- decls: 2 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: genuine Mathlib commutative algebra: any prime between the source point-ideal and the separator ambient prime equals an endpoint; no ambient prime strictly between source and separator successor.
- name-vs-content: accurate (prime-order statement for height transport).
- gaps: none internal; supports the separator/height-one machinery.

### GST2DMixedEmergenceUpgrade.lean (91 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: universal (unbounded) versions of the micro/macro digit identities: finalMicroDigit = outDigit for all C,d; exact cell balance 3·nextCarry + outDigit = C + 4d; seven-kernel telescope cancels symbolically — the old twelve-cell physical theorems are absorbed.
- name-vs-content: accurate.
- gaps: none internal.

### GSTClassicalHodgeDiagonalIdentityCorrespondence.lean (89 lines)
- decls: 3 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: the graph of the identity endomorphism (diagonal correspondence) realizes `LinearMap.id` on point classes (residue degree one); packaged as a genuine realized correspondence with full native cycle-class naturality.
- name-vs-content: accurate; supplies the previously missing identity element of the correspondence algebra.
- gaps: none internal (small but genuine geometric lemma).

### GSTGeneralSpacePartialCharts.lean (81 lines)
- decls: 1 theorem, 5 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: none.
- main content: `PartialChart` (Coord type + domain + observe), pullback, reindex, overlap, overlap observations — trivial data plumbing for "General Space Theory".
- name-vs-content: accurate (no mathematics).
- gaps: pure scaffolding; nothing proven beyond rfl-level simp lemmas.

### GSTClassicalHodgePositiveDegreeNonunit.lean (74 lines)
- decls: 3 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: in a nontrivial ℕ-graded ring, positive-degree homogeneous elements are nonunits (degree-zero projection argument); nonzero positive homogeneous elements give genuine principal equations.
- name-vs-content: accurate (general graded-ring lemma).
- gaps: none internal.

### questions/deepmind_problem_406/Solution.lean (57 lines)
- decls: 2 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: **`hB : erdos_ternary_2_universal_of_tailF`** (imported monolith theorem) and **`hTailF : GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF`** — the open Erdős input rides as an explicit boundary hypothesis.
- main content: predicate bridge `noTernaryDigitTwo = noTernaryTwo` (proven in full); `erdos_ternary_2_of_boundaries`: ∀ n ≥ 9, 2^n has a ternary digit 2, conditional on the two boundary inputs.
- name-vs-content: "Solution for the comparator harness" — it is a conditional solution; the docstring admits the deep input "rides as the explicit boundary hypothesis".
- gaps: DeepMind problem 406 (Erdős ternary-2) is NOT proven: `four_power_omega_shadow_wave_tailF` is exactly the remaining open content.

### questions/deepmind_problem_406/Challenge.lean (25 lines)
- decls: 1 theorem, 1 def, 0 axioms, **1 sorry (intentional, challenge side)**
- hypotheses: the statement itself: `theorem erdos_ternary_2 : ∀ n : Nat, 9 ≤ n → noTernaryDigitTwo (2^n) = false := by sorry`.
- main content: the benchmark surface: recursive Boolean predicate "no ternary digit 2" and the Erdős statement for n ≥ 9.
- name-vs-content: accurate — this is the question side of the official comparator harness; the sorry is by design.
- gaps: the sorry is the open Erdős conjecture; the companion Solution.lean discharges it only conditionally.

---

## BATCH SUMMARY

**Totals.** 71 files, 19,379 LOC; 720 theorems + 1 lemma; 174 defs; 23 structures; **0 `axiom` declarations; 0 `opaque`**; 1 `sorry` (the intentional challenge-side statement of DeepMind problem 406); ~362 `#print axioms` receipts. Every file carries maximally inflated `maxHeartbeats` (up to 280,000,000) — CI-only compilation.

**The dominant idiom.** No custom axioms are used in this batch. Instead the corpus is organized as a cascade of *conditional reductions*: each "finale/crown/master" file proves `BigradedBettiHodgeStatement V H` (the Clay-shaped statement) from a `def : Prop` or structure-valued hypothesis that packages the actual geometric content. The unproven-assumption inventory:

*Hodge-line hypothesis inventory (each = the open input of one or more crowns):*
1. `UniversalGSTKrylovHankelNondegeneracy` / `UniversalProjectiveDegreeKrylovNondegeneracy` — one realized correspondence + seed + trace with nonvanishing Hankel determinant per weight (KrylovMomentDeterminant).
2. `UniversalGSTGeometricDeterminantGeneration` — GST correspondence programs with nonzero Hodge-coordinate determinant per weight (MatrixRankLanding).
3. `ClosedCorrespondenceWindowRealization.on_hodge` (+ `PointVisible`) — a closed-correspondence word acting as the zero-complement observable on the Hodge fiber (SpectralAmplifier).
4. `PointFiniteCorrespondenceWeightRealization.realizes` / `PiPointFiniteCorrespondenceRealization` — finite correspondences realizing GST matrix units on point cycles (PiPointFiniteCorrespondenceUltimateFinale).
5. `ProjectiveWordSpectralFamily.eigenvector` (+ injective eigenvalues) and `FiniteProjectiveSpectralCover` (covers_live_support, visible) (ProjectiveSpectralCover).
6. `CoordinatewiseVisibleLocalRealization.visible` — per-sheet atomic visibility (CoordinatewiseSeedAssembly).
7. `ChannelHodgeRealization` (channelCycle_mem, channelCycle_coordinate) / `Stage2GChannelMaterializationObligation` (HodgeChannelMaterialization).
8. `StrictKernelCyclicPacket` — topology/correspondence/kernel + `pointClass_eq` + `incidence` (GeometricIncidencePrimitives) + simple spectrum + cyclic seed (PiStrictKernelCyclicOmniverseFinale).
9. `PointCylinderPullbackLaw`, `KernelFiberIntersectionLaw`, `ProperProjectionFiberLaw` (bundled `GeometricIncidencePrimitives`) — the three standard intersection-theory laws (CycleClassIntersectionPrimitives); `SuppliedPointDirectIncidenceLaw` (CanonicalPointIncidenceTransfer); `hpoint` synchronization (StrictKernelRangeStability).
10. `FullCorrespondenceSourceTargetProgram.source_action` (+ `ProjectivelyLiveSource`, coheight-exactness) (DegreeCertifiedFullCorrespondenceCompiler).
11. `PrimitiveNativeTwoSlot` — three `HasNativePointLifts` laws (UniversalTwoSlotNativeClosure); imported `GeometryFirstTwoGenerator`, `ProjectiveTwoGenerator`, `SpineTowerConservedCharge`.
12. `StrictlyMaterializedBranch` per GST branch event + one nonzero algebraic seed (OmniverseStrictEventStability).
13. `NativeMassCohomologyFactorization` + `ExactVerticalCutRayCertificate` (per live weight) + `GhostWeightPrimitiveStrictClosure` (VerticalRayMassFactorization).
14. `MatrixUnitReachableByClosedCorrespondences` + seed (ClosedCorrespondenceCosmicRealization); `ProjectiveCosmicRealization.acts_as_cosmic` (ProjectiveCorrespondenceCosmicRealization).
15. `NativePointHodgeSeed` (point with nonzero (p,p) class) + `GeometryFirstTwoGenerator` family (NativePointSeedSaturation / NativeWordFromArbitrarySeed).
16. `LocalCycleSpectralRealization` (SpectralCycleOperator + CyclicSeed) (ConstructiveCyclicLanding).
17. `HodgeSubspaceRealization` / `FiberRealizationObligation` (Stage2B); `HodgeBasisCycleBridge.basisCycle_spec` (BasisCycleBridge).
18. K3-line: `hKunnethKernel` + `hScalarEndomorphisms` (End_HS(T(S)) scalar) (K3TranscendentalHodgeCompleteness); + `NativeHodgeRetract Y X` (K3GeometricSourceToArbitraryX).
19. `RelativeSuccessorAmbientExact` (codimension additivity of the principal cut) (RelativeSuccessorExactStratum).

*Arithmetic-line hypothesis inventory (Erdős ternary-2 program):*
20. `four_power_omega_shadow_wave` and its weakenings `_tail, _tail2.._tail5, _tailE, _tailF` — "every shadow/dust exponent owns a ternary digit 2 in 4^K" (OmegaWaveLaw); `four_power_happy_climb` (imported, ∀ K ≥ 8 ∃ Happy row); `erdos_even_conjecture_iff_tailF`, `erdos_ternary_2_conjecture_odd`, `erdos_ternary_2_universal_of_tailF` (imported bridge theorems); the Solution to DeepMind problem 406 is conditional on `hTailF`.

**Five most load-bearing files (why):**
1. **GSTGraphV2OmegaWaveLaw.lean** — defines the entire residual-input chain (`four_power_omega_shadow_wave_tailF` etc.) of the ternary-digit campaign; the DeepMind-406 "solution" and the one-lane receipt all terminate on these def-Props, which are equivalent to the open Erdős ternary-2 conjecture.
2. **GSTClassicalHodgePiPointFiniteCorrespondenceUltimateFinale.lean** — the cleanest Clay-level conditional (`BigradedBettiHodgeStatement` from `PiPointFiniteCorrespondenceRealization`); the reference shape of the whole Hodge-line reduction cascade.
3. **GSTClassicalHodgeGeometricKrylovMomentDeterminant.lean** — the "strongest compact numerical target" (per its own docstring): full Hodge from one Hankel determinant; also contains the honest degree-eigenfunctional obstruction that blocks naive routes.
4. **GSTClassicalHodgeCycleClassIntersectionPrimitives.lean (+ StrictKernelRangeStability, CanonicalPointIncidenceTransfer)** — the geometric bedrock: the three assumed intersection-theory laws (cylinder pullback, cup/intersection, proper pushforward) and the point-class synchronization on which every "strict/geometric" branch of the campaign silently rests.
5. **GSTK3TranscendentalHodgeCompleteness.lean (+ GSTK3PrimitiveGram.lean)** — the only place with recognizably classical Hodge-structure mathematics (End(T(S)) scalar + Künneth kernel ⇒ (2,2) algebraicity on K3×K3); the model into which all "K3" claims elsewhere should be read.

**Single biggest gap.** Not one file in this batch proves any *existence* half of its interface: for the Hodge line, the existence — for an arbitrary smooth projective V — of even one genuine finite closed correspondence / spectral packet / two-generator realization with the required action on the Hodge fiber (all 19 Hodge-line hypothesis packages above are restatements of this one missing fact, variously disguised); for the arithmetic line, `four_power_omega_shadow_wave_tailF` ≡ the Erdős ternary-2 conjecture, which leaves DeepMind problem 406 formally unsolved (its "Solution" is a conditional bridge). Everything actually proven in batch 1 is either (i) exact elementary number theory / finite-lattice combinatorics, (ii) honest linear-algebra reductions (matrix-inversion, Hankel, hyperplane-avoidance, irreducibility), (iii) Mathlib-grade infrastructure (compactness, presentations, graded rings), or (iv) conditional theorems whose hypotheses carry the entire remaining mathematical content.
