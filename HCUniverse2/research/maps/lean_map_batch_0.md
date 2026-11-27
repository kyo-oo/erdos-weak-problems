# Lean Batch 0 Map — research/gpt6-native-point-primitive-span-20261017 @ 6c20bb7

Mapper: lean-mapper batch 0 (Task 1-a). Files: 68, LOC 19,379, theorems 735, defs 198, structures 22, **axioms 0, sorry 0**. Every file read in full (only GSTUniversalCMArithmeticObstruction.lean, 5066 lines, was read via header + structure/theorem-statement sweep + targeted sections; it has no structures/classes and no axioms).

Key to the hypothesis inventory: this batch contains **zero `axiom` declarations and zero `sorry`**. All load-bearing unproven assumptions live as (a) `structure`-records whose fields are mathematical propositions (the "ForAllN hypothesis idiom"), or (b) named `def ... : Prop` obligations passed as theorem hypotheses. Both are catalogued below. Quoted fields are verbatim.

---

### GSTUniversalCMArithmeticObstruction.lean (5066 lines)
- decls: 189 theorems, 65 defs, 0 axioms, 0 sorry
- hypotheses: none as axioms/records. Load-bearing **theorem-level hypothesis bundles** in the `auxiliaryWeil*` family: `hTheta : coordinates (nativeToHodgeFiberLinear G thetaSquare) = (1, (0, 0))`, `hExtract : coordinates (nativeToHodgeFiberLinear G (extract Γ)) = (0, contractGraph tensor)`, `hCMFunctorial : ∀ Z, coordinates (nativeToHodgeFiberLinear G (cmPullback Z)) = ((((d+1)^2+d)^2) * ..., fourthPowerAction d (d+1) ...)`, `hProperGysinNaturality`, `hSecantCharacter : (bettiExtract fixedSixfoldBetti).2 = ((d+1)/(2*d), (0:ℚ))`, plus a Baire period-spread packet (`hclosed/hidentity/hlocal`).
- main content: adversarial audit file. (1) No-go lemmas: an imaginary-quadratic CM law `T²-2aT+(a²+b²)` is impossible on ℚ (rank-one); genuine cross-carrier transfers and their compositions can never output a non-algebraic target from an algebraic source. (2) Exact arithmetic of CM "Weil" operators (projectors idempotent, spectrum censuses, determinant dichotomies). (3) Large body of explicit graph/lattice combinatorics (Ext² counts, Koszul complexes, Gram lattices, incidence ranks, torsion-pair orbits) for specific candidate sixfold graph constructions. (4) The final `auxiliaryWeilEveryMiddleHodgeClass_from_secantCharacter` assembles a cycle for any rational (2,2) Hodge class on a Weil fourfold, conditional on the displayed geometric comparison hypotheses.
- name-vs-content: "Universal CM Arithmetic Obstruction" is accurate — it mostly proves obstructions/no-go results, not a universal Hodge theorem.
- gaps: every `auxiliaryWeil*` landing is conditional; the geometric leaves (semiregularity of the source, Hilbert period spread, cup/Gysin comparison, CM functoriality) are supplied, not proved, here.

### GSTGraphV2OntologicalFoldForAllN.lean (524 lines)
- decls: 26 theorems, 10 defs, 0 axioms, 0 sorry
- hypotheses: **`FoldProcessOn` (hypothesis-record)** — field `landing_cycle : ∀ v : PairWit, landing v → scale v ≠ 0 → ∃ Z : w.Cyc, w.cl Z = w.alpha` (the "committed landing chain (Theorem C + Serre + Thom-Porteous + GAGA)", i.e. the actual Hodge content, supplied as a field). `FoldPairCalculus` is abstract but genuinely instantiated by `P2PairCal` (line-sum pairs on P²), so it is not an unproven assumption.
- main content: PART A: exact ch-identity `2·expTr(1) − (expTr(1)+expTr(−1)) = 2h` and parity obstruction `x²≡x mod 2` ⇒ every pure line-sum pair on P² has even scale. PART B: scale-set is an additive subgroup; principality (least positive m* divides all scales) — proved. Determination m* = 2 *within the line-sum calculus instance*. PART C: `forAllN_landing` — if the universal bit fires on every input, landing holds for all inputs (pure logic packaging of the field).
- name-vs-content: "Ontological Fold For-All-N Certificate" overstates: the for-all-N reduction is a one-line field-application; the classical integrability/landing content is explicitly a labeled field.
- gaps: extension of the parity obstruction to all holomorphic pairs on P² (Chern-lattice integrality, "Theorem P(ii)") is derivation-level, NOT kernel-checked; no instance of `FoldProcessOn` is constructed.

### GSTClassicalHodgeTwoGeneratorLefschetzPoincareGeneration.lean (473 lines)
- decls: 11 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none.
- main content: on the abstract `RationalPureWindow N` model, the normalized Lefschetz operator U = (1/2)L² and Poincare reversal D = PUP generate every matrix unit (E_ij = Uʲ Π₀ Dⁱ), Π₀ = I − UD is exactly the bottom-sheet projector, and any nonzero submodule invariant under the two generators is everything (irreducibility).
- name-vs-content: accurate for the abstract model; the "Hodge" in the name refers to the combinatorial pure-diagonal model, not actual cohomology of varieties.
- gaps: `RationalPureWindow` is a finite-dimensional toy carrier; geometric externalization (cycle-class naturality of Lefschetz/Poincare on a real variety) is acknowledged as the remaining burden and is not here.

### GSTDimensionFreeHodgeDiagonal.lean (438 lines)
- decls: 20 theorems, 7 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: on an A×B rectangular index grid, "weight-p Hodge class" = function supported on the (p,p) cell; classification: such a class is uniquely z·(diagonal basis class); diagonal address = (B+1)p; rational version identical; outside depth ⇒ zero; cosmic (Finsupp ℕ×ℕ) version.
- name-vs-content: "DIRECT RATIONAL DIMENSION-FREE CLAY LAW" is a large name for: a function supported on a single cell is determined by its value there.
- gaps: pure index-grid combinatorics; no connection to actual Hodge structures beyond naming.

### GSTClassicalHodgeFiberedCycleClassDefect.lean (411 lines)
- decls: 16 theorems, 0 defs (several `noncomputable def`s), 0 axioms, 0 sorry
- hypotheses: none as records; the closing theorem is conditional on defect-zero states: `state : ∀ p i, FiberedNativeAddress V H p` with `hdefect : ∀ p i, fiberedCycleClassDefect ... (state p i) = 0`.
- main content: defines the fibered cycle-class defect (native cycle class minus reconstructed Hodge face) as a linear map; proves defect is insensitive to normalization/circulation corrections; **`bigradedBettiHodge_of_defectZero_basisStates`: if defect-zero fibered states exist for every Hodge basis sheet, then `BigradedBettiHodgeStatement V H` follows** (finite-support reconstruction).
- name-vs-content: accurate — it isolates the defect quantity; nothing is landed unconditionally.
- gaps: existence of defect-zero states (the actual geometric problem) is entirely open here; the mass-calibrated source construction is referenced to an external .tex derivation.

### GSTClassicalHodgeFullLimitlessCrown.lean (396 lines)
- decls: 19 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: **`LiveSpineMassSurvival` (hypothesis-record)** — fields verbatim: `kernel_mass_zero : ∀ p : Nat, ∀ Z : codimensionCycles V.X p, H.cycleClass p Z = 0 → nativeCycleMass V p Z = 0` and `live_tower_mass_ne_zero : ∀ p : Nat, rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥ → nativeCycleMass V p (spineNativeTower G p) ≠ 0`. Also `SpineTowerNonvanishing` (spine tower nonzero in live weights), `FullProjectiveCosmicExternalization G` (∀ p i j, ∃ ProjectiveNativeKernel K, AtomCosmicExternalization G i j K), and `SpineTowerConservedCharge` (imported).
- main content: **the crown file**: `bigradedBettiHodge` — BigradedBettiHodgeStatement V H (= every rational (p,p) class is a cycle class) from spine G + nonvanishing + full projective externalization; three variants (conserved charge / live-mass survival); elementwise "every Hodge class has a native cycle" forms.
- name-vs-content: "Full Limitless Crown" is the composition layer; the Hodge statement is genuinely derived but only from the three unproven geometric interfaces.
- gaps: no instance of SpineTowerNonvanishing / LiveSpineMassSurvival / FullProjectiveCosmicExternalization is constructed anywhere in this batch; these are the load-bearing unproven assumptions of the whole "limitless" route.

### GSTGr25PurePairLatticeCertificate.lean (383 lines)
- decls: 22 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: none (the generator Chern-character table is supplied as literal data, honestly labelled).
- main content: exact polynomial arithmetic in ℚ[h,s₂]/(h⁴−3h²s₂+s₂², h³s₂−2hs₂²) = H*(Gr(2,5)) presentation: period table (h⁶=5h²s₂² etc.), the naive Plücker assembly's grade-4 obstruction, and the **completed pure pair at scale 360**: E± with equal ranks 2231, equal ch₁, 2(ch₂(E+)−ch₂(E−)) = 144·alphaZ (=720α), and ch₃…ch₆ equal in the quotient (explicit combination of r₁, r₂).
- name-vs-content: accurate as a *polynomial-arithmetic* certificate; the scheme-level interpretation is explicitly out of scope.
- gaps: minimality of scale 360, the rank/ch values as statements about actual bundles, the two-center descent law [D+]−[D−] = −360α and the match with the Rees witness are proved only in the external .tex, not in Lean.

### GSTClassicalHodgeFiniteClosedCorrespondenceOperator.lean (351 lines)
- decls: 11 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: `RealizesAmbientOnPoints` (def-Prop, theorem hypothesis): a cohomological operator agreeing with the correspondence on genuine point-cycle classes.
- main content: promotes a finite closed correspondence's point action to a full native cycle-space operator via the compact presentation equivalence; graph consistency (graph correspondence = native pushforward of the endomorphism); pointwise-to-global upgrade: agreement on point atoms ⇒ exact cycle-class-naturality on all cycles; rational correspondence-cycle arena (Finsupp on correspondences).
- name-vs-content: accurate construction/packaging layer.
- gaps: the existence of correspondences realizing a given cohomological operator (the `RealizesAmbientOnPoints` input) is not addressed.

### GSTClassicalHodgeActualCommutatorRankGain.lean (344 lines)
- decls: 14 theorems, 4 defs, 0 axioms, 0 sorry
- hypotheses: `SpineTowerConservedCharge D` (imported record), nonzero commutator `hcomm : bettiGeometricCommutator G E F ≠ 0`, charge-eigenoperator laws hE/hF, rank hypothesis `hrank : finrank (ClassicalHodgeFiber V H p) = 2`.
- main content: if two charge-eigen correspondence expressions have a nonzero commutator, spine + commutator are linearly independent; **in a rank-two Hodge fiber this closes every Hodge class at that weight** (`every_rank_two_hodge_class_of_nonzero_geometric_commutator`). Plus an honest 4-dimensional rational countermodel (`FourCoordinateGSTGraphAudit`): two noncommuting charge-preserving operators whose graph closure never reaches the 4th coordinate — refuting abstract rank-completion from noncommutativity+charge alone.
- name-vs-content: "Actual Commutator Rank Gain" is honest: gain is conditional on the nonzero commutator and rank exactly 2.
- gaps: nonzero geometric commutator existence, and the rank-2 restriction, are unproven; the countermodel shows the method cannot work in higher rank without more geometry.

### GSTClassicalHodgeProjectivePointTransport.lean (338 lines)
- decls: 11 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none (uses Mathlib residue-degree pushforward of algebraic cycles).
- main content: genuine geometric construction: point pushforward with residue-degree weights along a scheme morphism, extended linearly to finite presentations and (via compact normal form) to all native codimension-p cycles on a smooth projective scheme; externalization criterion — the pushforward admits an ambient cohomological action iff it preserves finite point-class relations (`geometricPushforward_has_ambientAction_iff`).
- name-vs-content: accurate; pure transport construction, no Hodge conclusion claimed.
- gaps: this is infrastructure; the cohomological action existence for specific maps is deferred.

### GSTGeometricRealizationStage2C.lean (326 lines)
- decls: 7 theorems, 3 defs, 0 axioms, 0 sorry
- hypotheses: **`NativeSchemeHodgeRealization` (hypothesis-record)** — fields: `hodge`, `cycleSpace` (a ℚ-submodule of Mathlib `AlgebraicCycle X ℚ`), `cycleClass`, `encode : Coh →ₗ[ℚ] RatAddress N`, `encode_injective : Function.Injective encode`, `hodgeSupport : Finset (Fin N)`, `hodge_supported : ∀ alpha ∈ hodge, SupportedOn hodgeSupport (encode alpha)`, `basisCycle : Fin N → cycleSpace`, `basisCycle_address : ∀ i ∈ hodgeSupport, encode (cycleClass (basisCycle i)) = addressBasis i`. This is the "realization certificate": finite address encoding + basis cycles hitting address basis vectors.
- main content: rational ℚ-module structure on Mathlib AlgebraicCycle; native-scheme fiber theorem (every rational Hodge class in a supplied realization has a cycle witness in an actual Mathlib algebraic-cycle submodule); universal variable-rank family theorem; `NativeSchemeFiberRealizationObligation` — the exact remaining per-fiber obligation.
- name-vs-content: honest — docstring lists the six classical identifications (X smooth projective over ℂ, Coh = H^{2p}, genuine Hodge subspace, Chow construction, genuine cycle class, realization certificate) that are still required.
- gaps: the pinned Mathlib revision does not provide the classical Hodge/Chow/Betti cycle-class stack; `cycleSpace`, `hodge`, `cycleClass`, `encode` are all supplied data; no realization certificate is constructed.

### GSTClassicalHodgeCommonClassPlaneRealization.lean (314 lines)
- decls: 8 theorems, 3 defs, 0 axioms, 0 sorry
- hypotheses: **`CommonClassPlanePacket` (hypothesis-record)** — fields: `correspondence : SchemeBiFiniteClosedCorrespondence V`, `trace : RightFiniteBettiTrace ...`, `pointCompatibility`, `planeClass : CarrierCohomology ...`, `source_face : leftCohomologyPullback ... u.state.1 = planeClass`, `target_face : rightCohomologyPullback ... v.state.1 = planeClass` (the two unproven geometric face equalities l*(u)=ω=r*(v)). **`GhostCommonClassPlaneStrike`** (seed + plane). `GhostAdaptiveCommonClassPlaneCompleteness` / `GhostWeightPrimitiveCommonClassClosure` (def-Prop obligations).
- main content: derives the strict Betti relation by transitivity through the common carrier class; one common-class plane strike kills a hypothetical omniversal separator ghost; **`hodge_of_commonClassPlanes`: plane completeness ⇒ BigradedBettiHodgeStatement**; branch-level `hodge_of_survival_and_commonClassPlaneClosure`.
- name-vs-content: accurate "realization law" phrasing but everything geometric is in the packet fields.
- gaps: no `CommonClassPlanePacket` is ever constructed; the completeness predicate is (per file 47) exactly Hodge-equivalent.

### GSTInfiniteCollision.lean (309 lines)
- decls: 17 theorems, 6 defs, 0 axioms, 0 sorry
- hypotheses: none (`InfiniteCoupledControl` is a Prop-structure whose fields are all *proved* by `infinite_coupled_control`).
- main content: exact arithmetic of the x4/base-3 carry machine (`affineCarry`, `naturalCarry`), a `CoupledState` transition system with an invariant `parentSeed + 4·parentOffset = childResidue + A·childCarry`, orbit semigroup law, exact closed forms for childTail/parentWord/childCarry along the orbit.
- name-vs-content: "Infinite Collision" is Collatz-flavored digit arithmetic; the name does not announce a mathematical theorem beyond the transport layer.
- gaps: purely arithmetic transport; no termination/collision theorem is claimed.

### GSTClassicalHodgeLimitlessCosmicMatrixUnits.lean (298 lines)
- decls: 16 theorems, 3 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: "cosmic" diagonal matrix units E_ij on the Finsupp carrier CompactCosmos (read weight i by Poincare probe, write at j); exact matrix-unit composition laws; rational version on ℕ→₀ℚ; irreducibility: a nonzero submodule stable under all cosmic matrix units is ⊤.
- name-vs-content: "Limitless Cosmic … Artery" is Finsupp linear algebra; the grand name exceeds the elementary content.
- gaps: the carrier is a combinatorial shadow of Hodge theory, not cohomology of any variety.

### GSTFourPowerDirectExistenceProviderPipeline.lean (293 lines)
- decls: 19 theorems, 4 defs, 0 axioms, 0 sorry
- hypotheses: **`FourPowerProductionUniverse` (Prop-structure)** — fields: `directExistence : FourPowerDirectExistence`, `noBadAffineChannelOne : FourPowerDirectNoBadAffineChannelOne`, `noCounterexampleClosure : FourPowerDirectNoCounterexampleClosure`, `creationMaster : FourPowerCreationMaster`, `creationCertificate : ∀ K, 5 ≤ K → K ≠ 7 → CreationCertificate (4^K)`. These are all unproven arithmetic statements of the four-power program.
- main content: equivalence network: FourPowerDirectExistence ⟺ production universe ⟺ no-bad-affine-channel-1 ⟺ no-counterexample closure; provider gates (Happy-row provider, common-two ≥ 3 provider) that imply direct existence; obstruction bundle for hypothetical counterexamples (mod 9/27/81 classes and parametric trit obstructions).
- name-vs-content: "Provider Pipeline" accurate — it reorganizes proof obligations around the still-unproved `FourPowerDirectExistence`.
- gaps: `FourPowerDirectExistence` itself (a Collatz-like open arithmetic statement about ternary digits of consecutive powers of 4) is not proved here or anywhere in this batch; it is passed around as a hypothesis.

### GSTClassicalHodgeLimitlessArsenalConjugation.lean (284 lines)
- decls: 10 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: embeds finite integral pure squares into the compact cosmos and identifies the finite total-sheet matrix unit with the observation of the cosmic read/write matrix unit; denominator-cleared Hodge states read back exactly on live slots.
- name-vs-content: accurate identification of finite vs "limitless" shadows.
- gaps: all in the combinatorial shadow universe; no geometry.

### GSTClassicalHodgeTwoGeneratorPointKernelSaturation.lean (277 lines)
- decls: 6 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: **`TwoPrimitivePointTransitions` (hypothesis-record)** — fields: `code : NativePointTransition (ambientTwoSlotCode i j)` and `lefchetz : NativePointTransition (ambientTwoStepLefschetz i j)` (existence of native point lifts for the two fixed ambient observables). Also `hseed : AlgebraicHodgeSubspace V H p ≠ ⊥` and a full family `R : ∀ i j, TwoGeneratorNative`.
- main content: the two-generator ambient word equals the Hodge matrix unit on the Hodge fiber (pure GST calculation); native point lifts ⇒ matrix-unit orbit of algebraic vectors stays algebraic ⇒ one nonzero algebraic seed saturates the whole weight: **`hodge_weight_of_two_primitive_point_transitions`** lands the weight-p Hodge statement.
- name-vs-content: accurate "point-kernel saturation" reduction; the conclusion is conditional.
- gaps: constructing the NativePointTransitions (the actual geometry) is the open obligation; seed nonvanishing is assumed.

### GSTClassicalHodgePointwiseCosmicExternalization.lean (270 lines)
- decls: 7 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: **`FinitePointCosmicExternalization` / `PointAtomCosmicExternalization` (def-Props, theorem hypotheses)**: `∀ x, finitePointCycleClassMap p (H.cycleClass p) (transition V p K x) = canonicalCosmicAmbient i j (H.cycleClass p (codimensionPointCycle V.X p x))` — the finite transition class equals the cosmic matrix-unit action on point classes. Plus `SpineTowerNonvanishing`.
- main content: point-generator externalization suffices: equality on point atoms extends to the whole atomic span by linearity; finite point-transition equations ⇒ CanonicalCosmicNaturality ⇒ **`bigradedBettiHodge_of_spine_and_finitePointExternalization`** (full Stage-2G statement).
- name-vs-content: honest reduction of the externalization interface to pointwise equations.
- gaps: no kernel K satisfying the externalization equation is constructed; spine nonvanishing also assumed.

### GSTRadixWorldDynamics.lean (269 lines)
- decls: 16 theorems, 8 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: mixed-radix coordinate-change theorem: the transpose between the s-low and b-low charts of Fin s × Fin b is an equivalence; conservation, uniqueness, bijectivity, finite-world closure; the old x4/base-3 twelve-cell transition is the s=4,b=3 specialization; quotient/remainder characterization.
- name-vs-content: accurate arithmetic generalization of the 4×3 cell.
- gaps: none for its scope; irrelevant to Hodge content directly.

### GSTClassicalHodgeHandwrittenPiProgramLanding.lean (257 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `hne : (P0 q).cohomologyEval G (geometricOriginClass V H) ≠ 0` (nonzero program from the codimension-zero origin, per weight), `R : ∀ j, ProjectiveTwoGenerator ... sourceIndex j` (projective two-generator families, hypothesis-records imported), `hdiag` membership.
- main content: derives the orbit seed from a genuine graded program from the fundamental cycle; projective GST words put every Hodge basis vector in the geometric program orbit; localized L²-branches land; **`bigradedBettiHodge_of_handwritten_program_words`** — full Stage-2G statement from origin programs + projective words.
- name-vs-content: "Handwritten Pi Program Landing" reflects the manuscript construction; the landing is conditional on the program/word existence.
- gaps: nonzero origin programs and ProjectiveTwoGenerator realizations are unproven geometric inputs.

### GSTClassicalHodgeProperCutCodimensionOne.lean (254 lines)
- decls: 5 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none (topological hypotheses are Mathlib typeclasses).
- main content: **genuine point-set topology**: in a Noetherian quasi-sober irreducible T0 space, the ambient coheight-one points of a subset with proper closure form a finite set (they are generic points of irreducible components of the closed hull); applied to source-dependent principal cuts on smooth projective schemes: `finite_principal_cut_coheight_one`, plus packaging as a Finset of genuine codimension-one points.
- name-vs-content: accurate; this is real, Mathlib-adjacent mathematics.
- gaps: only the codimension-one step of the recursive cutting engine.

### GSTClassicalHodgeSingleCorrespondenceRankTwo.lean (252 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `hlive : ell (spineHodgeSeed G p) ≠ 0`, `htransverse : hodgeChargeWedge G ell E ≠ 0` (or nonproportionality `hnot`), `hrank : finrank = 2`.
- main content: charge-wedge construction Δ = ℓ(s)·T_native(Z) − ℓ(T_Betti(s))·Z; its class is automatically charge-zero; if nonzero it is independent of the spine; **rank-two closure**: one transverse realized correspondence ⇒ every Hodge class at that weight is algebraic; scalar-action no-go certificate.
- name-vs-content: honest "weight-local charge-wedge rank gain" — conditional.
- gaps: transversality/nonproportionality and rank exactly 2 are unproven geometric inputs (the file says so explicitly).

### GST2DMixedEmergence.lean (242 lines)
- decls: 9 theorems, 16 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: exact arithmetic of the physical x4/base-3 cell: two x2 layers reproduce the x4 output trit; seven-kernel telescoping; the mixed density 8·sevenKernel+7·U decomposes as horizontal BIG1-only boundary derivative + ternary carry derivative + positive SURVIVE incidence; row and rectangle divergence theorems (a discrete Stokes law for the cell system); Happy-chord dichotomy (NULL = 2→1→2, GST+ = 2→2→2).
- name-vs-content: "2D Mixed Emergence" is an arithmetic identity collection; the physics vocabulary is metaphorical.
- gaps: all statements are finite-table verification (norm_num/decide); no limiting/trajectory theorem.

### GSTClassicalHodgeZeroComplementSpectrum.lean (242 lines)
- decls: 10 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: chooses an algebraic complement of the rational Hodge subspace (exists over ℚ), builds the zero-complement ambient observable (diagonal on Hodge fiber, zero on complement); X·Lagrange isolator polynomial is an honest ambient sheet projector killing the whole complement; augmented isolator selects its sheet with nonzero normalization.
- name-vs-content: accurate linear algebra of spectral projectors.
- gaps: pure vector-space algebra; no algebraicity/geometry content.

### GSTClassicalHodgeGeneralSpaceOperatorCosmos.lean (231 lines)
- decls: 7 theorems, 5 defs, 0 axioms, 0 sorry
- hypotheses: `GeometryFirstTwoGenerator` (imported hypothesis-record) for the geometry-first paths.
- main content: builds a `GeneralSpace` (category-style structure) whose points are even Betti points and paths are operator pairs with commuting cycle-class squares; native locus is path-closed (trivially from the commuting square); geometry-first two-generator pairs give paths from any native seed to exact Hodge basis sheets; `basis_native_of_geometryFirst`.
- name-vs-content: "Operator Cosmos" is a thin category wrapper around linear maps.
- gaps: all geometric content sits in the imported `GeometryFirstTwoGenerator` records.

### GSTClassicalHodgeOntologicalTwelveChart.lean (231 lines)
- decls: 8 theorems, 5 defs, 0 axioms, 0 sorry
- hypotheses: `h12 : liveRank alpha = 12` (the only cardinality bridge).
- main content: transports a Hodge class with exactly twelve live multiplicity sheets into the physical 4×3 Graph-V2 chart by canonical code; every transported coefficient is nonzero; the positive-energy cells are exactly the two Happy cells (energy = Graph-V2 density × coefficient magnitude); two-sector gap (≤ 0 or ≥ 42).
- name-vs-content: honest about the liveRank = 12 restriction; "ontological" is Graph-V2 vocabulary.
- gaps: only applies when the Hodge support has exactly 12 sheets; the "ontology" is the arithmetic cell table.

### GSTClassicalHodgeCanonicalSpectralObservable.lean (224 lines)
- decls: 10 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none (structure `FiniteHodgeBasisWindow` is pure data + injectivity).
- main content: manufactures a spectral observable from any finite injective window of the genuine Hodge basis: distinct labels 1..N, diagonal endomorphism, extension to ambient cohomology by the vector-space extension theorem; selected basis vectors are exact eigenvectors; singleton windows exist unconditionally.
- name-vs-content: accurate — "no spectral datum is supplied: it is manufactured".
- gaps: the observable is pure linear algebra; cycle naturality of anything is not touched.

### GSTHodgeChannelQuotient.lean (223 lines)
- decls: 8 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: **`ChannelHodgeQuotient` (hypothesis-record)** — fields verbatim: `decode : FixedWeightChannelCoordinates shape p →ₗ[ℚ] hodge`, `decode_surjective : Function.Surjective decode`, `channelCycle : HodgeChannel shape → CycleQ`, `channelCycle_decodes : ∀ i : HodgeChannel shape, cycleClass (channelCycle i) = (decode (channelBasis shape p i)).1`. I.e. a surjective decoder from a channel universe onto the Hodge sector whose canonical generators decode to algebraic cycle classes. `Stage2GChannelQuotientObligation` = ∀ p, Nonempty (quotient).
- main content: quotient materialization theorem — superposing the algebraic channel generators with chosen channel coordinates gives an exact cycle witness; **`bigraded_betti_hodge_of_channel_quotient_obligation`**: the obligation ⇒ BigradedBettiHodgeStatement; a split retract canonically forgets to the quotient.
- name-vs-content: honest minimal-interface description.
- gaps: the entire Hodge content is the unproven existence of a surjective algebraic-generator decoder in every weight; nothing is instantiated.

### GSTFourPowerDirectFailedRelocationState.lean (214 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `hNoNext : ¬ CommonTwo (K+1)` (hypothetical failure states).
- main content: exact automaton analysis of failed relocations in the four-power program: forced binary carry = 1, physical carry = 3, equal non-two digits on consecutive sheets, two-step physical state (carry in {1,2}).
- name-vs-content: accurate local arithmetic lemmas.
- gaps: feeds the unproven FourPowerDirectExistence program; no global statement.

### GSTClassicalHodgeSpineNonzeroFiniteSupportOrbit.lean (212 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `N : ∀ q, rationalHodgeSubspace ≠ ⊥ → spineHodgeSeed G q ≠ 0` (weight-local spine nonvanishing) and `R : ∀ i, ProjectiveSpanLiveSourceTarget (spineOrbitSeed ...) i.1` (projective-span transports, imported hypothesis-record family).
- main content: turns one nonzero spine state into a synchronized orbit seed using only nonvanishing; **`bigradedBettiHodge_of_weight_spine_nonzero_finite_projectiveSpan`**: spine nonvanishing at live weights + projective-span transports on the finite support of each class ⇒ full Stage-2G statement; per-class variant weakens nonvanishing to nonzero-class weights.
- name-vs-content: honest "brute-force" reduction with clearly displayed remaining data.
- gaps: spine nonvanishing and ProjectiveSpanLiveSourceTarget instances are unproven.

### GSTGraphV2HandwrittenOmegaUBlock.lean (208 lines)
- decls: 10 theorems, 6 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: exact exponential identities: 4^(3^t·n) factors through one (and two) ternary origin cuts; residual child/parent energy factorizations; all graph observables (carry, digit, eventCode, uCharge, mixedCharge, crossingCharge, survive) at the residual parent boundary equal those of the canonical parent perfect power; Happy-cell transport.
- name-vs-content: "Handwritten Omega/U" is exponent arithmetic; honest about using "only its exact finite-natural core".
- gaps: arithmetic only; no termination/residual-Omega theorem claimed.

### GSTFourPowerDirectExistence.lean (202 lines)
- decls: 13 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: none (the target itself is a def-Prop, not an axiom).
- main content: defines **`CommonTwo K`** (∃ p ≥ 1, digit₃(4^K, p) = 2 ∧ digit₃(4^(K+1), p) = 2) and **`FourPowerDirectExistence`** (∀ K ≥ 5, K ≠ 7 → CommonTwo K); proves positive classes mod 9 (K≡5,6), mod 27 (14,18,19,25), mod 81 (RowFourClass); counterexample exclusion laws; killing-trit reformulation (CommonTwo ⟺ some scale hits its killing trit).
- name-vs-content: honest isolation of "the actual universal arithmetic target".
- gaps: `FourPowerDirectExistence` is an open Collatz-flavored conjecture — the partial residue-class coverage is tiny relative to all K ≥ 5, K ≠ 7.

### GSTClassicalHodgeAtomicSpan.lean (200 lines)
- decls: 8 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: **atomic range theorem** (genuine): on a compact scheme, the range of the native codimension-p cycle-class map equals the span of the classes of genuine codimension-p point cycles; hence `BigradedBettiHodgeStatement ⟺ rationalHodgeSubspace ≤ pointCycleClassSpan` in every weight (basis-free normal form); crown adds the cosmic-diagonal projection receipt.
- name-vs-content: accurate and genuinely useful reformulation.
- gaps: reformulation only — the inclusion is the Hodge conjecture itself.

### GSTClassicalHodgeClosedCorrespondenceGhostExtinction.lean (199 lines)
- decls: 6 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: `hHit : ClosedCorrespondenceHitsSheet j` (def-Prop: ∃ point x, word W, nonzero scalar c with W(cl[x]) = c·basis_j) or `MatrixUnitReachableByClosedCorrespondences`.
- main content: separators kill images of point atoms under realized words; one correspondence hit puts the target basis sheet in the atomic span and makes separators impossible; **`bigradedBettiHodge_of_closedCorrespondenceHits`**; reconnection to the GST matrix-unit arsenal (reachability + live coordinate ⇒ hit).
- name-vs-content: accurate "geometry-first reachability criterion".
- gaps: `ClosedCorrespondenceHitsSheet` is exactly the unproven geometric reachability statement for every sheet.

### GSTInfiniteBadTransport.lean (196 lines)
- decls: 10 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: `hbad : SeededBadTrace D X` (a def-Prop hypothesis: ∀ k, ¬ Happy(affineCarry D X k, digit X k)).
- main content: all-depth bad-language transport: carry semigroup law, suffix reindexing preserves complete badness, coupled controller carries exact child/parent realization and regenerated badness at every depth, closure under re-basing. `InfiniteBadCoupledControl` is a Prop-structure with all fields proved from `hbad`.
- name-vs-content: accurate arithmetic transport layer.
- gaps: conditional on the existence of an all-Nat bad trace; no contradiction/termination derived.

### GSTCMNumberManipulationTrace.lean (192 lines)
- decls: 13 theorems, 9 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: ℚ(i) as rational pairs with explicit mul/conj/norm/inv/trace; Tr(u⁻¹) = 2a/(a²+b²); conjugation commutes with the indexed NM/CM denominator x^(m+1) − y^(m+2); the indexed trace is rational and conjugation-invariant for every index; nonzero real part certifies nonzero trace (with the honest caveat that a purely imaginary denominator can have zero trace).
- name-vs-content: honest: "a genuine CM number-theoretic rational descent step … does NOT assume or prove that the coefficient is the period of a geometric Hodge cycle".
- gaps: period/cup/Gysin comparison and nonzero realization are explicitly future work.

### GSTClassicalHodgeOmniversalGhostBranchClosure.lean (192 lines)
- decls: 4 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: `GhostWeightNativeSeedSurvival G` (every hypothetical ghost weight has a nonzero synchronized native/Hodge seed) and `GhostWeightPrimitiveStrictClosure G` (strict-relation compiler at ghost weights) — both def-Prop obligations; `PrimitiveStrictRelationCompiler` imported.
- main content: normalizing the strict branch image constructs a native cycle with class exactly the ghost's detected basis sheet ⇒ contradiction; **`hodge_of_survival_and_strictBranchClosure`**: survival + strict closure ⇒ BigradedBettiHodgeStatement.
- name-vs-content: accurate conditional finale.
- gaps: survival and strict closure are the two unproven structural laws (and file 60 shows the ghost-indexed form of strict closure is Hodge-equivalent, i.e. a reformulation).

### GSTClassicalHodgeNativeTransferAddressIdentification.lean (185 lines)
- decls: 8 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: the diagonal weight map p ↦ cosmicAddressEquiv(p,p) is injective; after reindexing and rationalization, the cosmic shadow of every genuine codimension-p point cycle equals the established limitless transfer generator `compactClMono p`; arbitrary cycles = total point mass times the transfer direction; cut-tower shadows lie on the transfer ray.
- name-vs-content: accurate address bookkeeping.
- gaps: pure compatibility layer between two bookkeeping systems.

### GSTU2DEventTransport.lean (182 lines)
- decls: 9 theorems, 4 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: complete 12-cell event-density table; sign classification (positive density ⟺ Happy); positive spectrum exactly {2,3}; reverse-base-four event codes: a leading Happy cell forces code ≥ 8 after two or more cells (rigid no-erasure mechanism: Happy emits BIG2, worst event −8 vs ×4 accumulation).
- name-vs-content: accurate finite automaton analysis.
- gaps: local/horizontal only; no global trajectory theorem.

### GSTClassicalHodgeLimitlessFailureOrbit.lean (180 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none (uses imported `not_hodge_yields_nonzero_integralPureSquare_pairing`).
- main content: a nonzero pure-square pairing has a nonzero diagonal source; the cosmic matrix unit sends it to every natural Hodge weight nonzero; **failure-orbit theorem**: ¬BigradedBettiHodgeStatement ⇒ a finite integral pure witness whose single nonzero sheet generates nonzero cosmic states at every weight (address form: every transfer direction hit).
- name-vs-content: accurate contrapositive packaging.
- gaps: the interesting content (existence of the pure-square pairing witness) is imported; this file just moves it around the cosmos.

### GSTClassicalHodgeProjectiveApexSpokeCircularity.lean (177 lines)
- decls: 5 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: `MinimalGhostProjectiveSpokeClosure` (def-Prop: ghost-indexed family of ProjectiveApexL2Spokes) plus a seed selector.
- main content: a basis separator kills every native cycle class (via the atomic span theorem); a minimal ghost forbids any projective L² spoke into its sheet (naturality vs the spoke equation ⇒ contradiction); **`minimalGhostProjectiveSpokeClosure_iff_hodge`**: ghost-indexed spoke closure is exactly Hodge-strength.
- name-vs-content: "Circularity" is the point — the file proves the spoke law is a reformulation, not an independent theorem.
- gaps: no spoke is ever constructed; equivalence only.

### GSTNativeCodimensionCyclePresentation.lean (175 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: genuine construction on Mathlib `AlgebraicCycle`: codimension points as coheight-p points, unit point-cycles, finite rational presentations realized as native codimension-p cycles with codimension proved by construction; exact linearity and the image formula under any rational cycle-class map.
- name-vs-content: accurate infrastructure.
- gaps: no cycle-class surjectivity asserted (explicitly); infrastructure only.

### GSTK3TranscendentalProjector.lean (171 lines)
- decls: 6 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: `ExactDivisorIntersectionDuality` (def-Prop: ℓ_i(D_j) = δ_ij) — an intersection-dual finite system.
- main content: abstract linear algebra mirroring the K3 construction: the divisor correspondence projector ∑ ℓ_i(x)·D_i is idempotent for any finite rank; the transcendental complement kills divisors, fixes orthogonal classes, is idempotent, and survives nonzero orthogonal classes.
- name-vs-content: honest — "The K3 interpretation … remain[s] geometric input[s] not formalized in this algebra-only file".
- gaps: no K3 surface, no Néron-Severi lattice, no actual correspondence Π_tr = Δ − Π_alg − Π₀ − Π₄ appears; only its shadow in a vector space.

### GSTClassicalHodgeStrictCorrespondenceTransferFromPrimitives.lean (169 lines)
- decls: 3 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: **imported hypothesis-records**: `RationalBettiIntersectionPrimitives` (cup+Gysin theory packet), `MiddleBettiCorrespondenceKernel`, `PointBettiClass` with `hpoint : ∀ x, H.cycleClass p (codimensionPointCycle V.X p x) = pt x`, and `GeometricIncidencePrimitives` packets for K and K^t.
- main content: constructs the historical point-fiber intersection law from split low-level ingredients (cup, Gysin, point classes, cylinder pullback, pushforward, point rigidity); derives the global transfer equality cl(K_* Z) = T_C(cl Z) as a theorem from those primitives.
- name-vs-content: accurate — "the final transfer equality is a theorem, not a field".
- gaps: the cup/Gysin/point-class primitives themselves are interface records whose mathematical content (standard algebraic topology) is not constructed in Lean anywhere in this batch.

### GSTClassicalHodgeOmniversalGhostPlaneStrike.lean (164 lines)
- decls: 4 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: **`GhostStrictPlaneStrike` (hypothesis-record)** — fields: `seed : NativeHodgeOrbitSeed` and `relation : StrictRelationEdgePacket` (the raw strict Betti relation from seed to the ghost's sheet); `GhostAdaptiveStrictPlaneCompleteness` (def-Prop obligation).
- main content: executing the compiled correspondence expression on the seed's native cycle gives class exactly the detected sheet ⇒ ghost contradiction; **`hodge_of_ghostAdaptiveStrictPlanes`**: plane completeness ⇒ BigradedBettiHodgeStatement.
- name-vs-content: honest ghost-adaptive reduction.
- gaps: no strike is constructed; completeness is Hodge-equivalent (see files 47/60).

### GSTClassicalHodgeBettiCupGysinPrimitives.lean (160 lines)
- decls: 4 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: **`RationalProductCupTheory` (hypothesis-record)** — field `swap_natural : ∀ a b (u) (v), swapCohomologyPullback A (a+b) (cup a b u v) = cup a b (swapCohomologyPullback A a u) (swapCohomologyPullback A b v)`; **`RationalProjectionGysinTheory`** — fields `snd_swap`, `fst_swap` (Gysin along projections conjugated by factor swap); **`RationalBettiIntersectionPrimitives`** bundling both.
- main content: isolates the ordinary rational Betti operations (graded cup on H*(X_an×X_an), integration/Gysin along projections, swap functoriality) that the pinned Mathlib singular-cohomology API does not supply; derives the swap lemmas as consequences of the packet.
- name-vs-content: honest: "standard algebraic-topology primitives only".
- gaps: the cup and Gysin maps are *fields*, not constructions — the standard theorems of singular cohomology are unformalized here; every downstream use is conditional on these packets.

### GSTClassicalHodgeCommonClassPlaneEquivalence.lean (158 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none beyond the definitions audited.
- main content: **honesty audit**: `GhostAdaptiveCommonClassPlaneCompleteness ⟺ BigradedBettiHodgeStatement` (forward by the realization file; converse vacuous because Hodge empties the ghost type); same for the survival+closure package; plus a *counterinstance*: the zero cycle-class spine satisfies all spine compatibility laws yet plane completeness fails whenever a nonzero Hodge class exists (`not_universal_planeCompleteness_from_spine_laws`), so no proof from the current interface can be universal.
- name-vs-content: accurate — "prevents a conditional realization package from being mistaken for an unconditional derivation".
- gaps: this file is the repo's own disclosure that the ghost-adaptive plane route is a reformulation of Hodge, not progress toward it.

### GSTGraphV2OmniversalHyperEvents.lean (152 lines)
- decls: 8 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none (HyperEventSystem is pure data).
- main content: typed higher-arity inference rules over the omniversal graph; the generated closure satisfies the semantic-closure induction principle; monotonicity, idempotence of closure.
- name-vs-content: grand ontology name for an inductive closure principle (essentially structural induction).
- gaps: no mathematical content beyond abstract graph closure.

### GSTUniversalLefschetzCurveCycles.lean (151 lines)
- decls: 2 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: **`HyperplaneDivisorHardLefschetz` (hypothesis-record)** — fields: `nativeHyperplaneIntersect`, `hodgeLefschetz`, `hardLefschetz : Function.Surjective hodgeLefschetz` (Hard Lefschetz h^{d−2}: Hodge¹ → Hodge^{d−1}), `intersection_cycleClass : ∀ D, H.cycleClass (d-1) (nativeHyperplaneIntersect D) = (hodgeLefschetz ⟨H.cycleClass 1 D, _⟩).1`; plus `DivisorsRepresentHodge11 H` (def-Prop: Lefschetz (1,1)).
- main content: the classical codimension-(d−1) argument packaged constructively: `curveCycleOfHodgeClass` returns an actual native cycle H^{d−2}·D with class exactly α; **`all_codimension_d_minus_one_Hodge_classes_algebraic`** for any variety whose three standard external theorems are supplied.
- name-vs-content: honest — "NOT a proof for primitive middle Hodge classes 2 ≤ p ≤ d−2" is stated in the docstring.
- gaps: Hard Lefschetz, Lefschetz (1,1), and the cup/intersection compatibility are external inputs "not formalize[d] … in Lean" by the repo.

### GSTClassicalHodgeNativeCycleCorrespondenceGhostAttack.lean (144 lines)
- decls: 5 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: `NativeCycleCorrespondenceHitsSheet` (def-Prop: a realized word sends some native cycle's class to a nonzero multiple of basis_j), family form `hHit : ∀ p j, ...`.
- main content: separators kill images of *all* native cycles (not just points) under realized words; a source-specific hit puts the sheet in the atomic span; **`bigradedBettiHodge_of_nativeCycleCorrespondenceHits`**.
- name-vs-content: accurate generalization of file 34's criterion.
- gaps: the hits are unproven geometric reachability statements.

### GSTUniversalHodgeResidualProjection.lean (144 lines)
- decls: 6 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: **`GeometricDualCyclePacket` (hypothesis-record)** — field `dual : ∀ i j, detectors i (cycleClass (cycles j)) = if i = j then 1 else 0` (intersection-dual Kronecker system).
- main content: constructs Z(α) = ∑ ℓ_i(α)·z_i for every α; the residual r(α) = α − cl(Z(α)) is invisible to all geometric probes; exact decomposition; **explicitly does NOT assert residual zero** ("Residual zero for all alpha would amount to the original Hodge conjecture"); zero residual ⟺ exact representation; unrepresented targets have nonzero residual.
- name-vs-content: honest constructive projection with an exact residual.
- gaps: the packet (dual intersection system) is unproven to exist in relevant generality; residual vanishing is the open problem, correctly not assumed.

### GSTMathboxCMGeometricComplexStructure.lean (140 lines)
- decls: 4 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `hJ2 : ∀ z, J (J z) = -z` on the rational Hodge fiber (a rational complex structure), `hgeom : J (spineHodgeSeed G p) = movedSpine G E`, `hrank : finrank = 2`, spine nonzero.
- main content: pure algebra: a rational J with J² = −I has no eigenvectors (c² = −1 has no rational root); hence a realized correspondence whose spine action is such a J is nonproportional to the spine; a Hodge-basis coordinate provides the readout; **`rank_two_hodge_of_actual_CM_complex_structure`** closes rank-two weights.
- name-vs-content: honest: "The proof does NOT assert that such a J/E exists on every … variety; an odd-dimensional rational Hodge fiber cannot carry any J with J² = −I at all."
- gaps: existence of the CM complex structure on realized correspondences and the rank-2 hypothesis are open; odd-dimensional fibers are excluded outright.

### GSTClassicalHodgeAugmentedTargetMatrixUnit.lean (136 lines)
- decls: 4 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: augmented (support-plus-target) window transport: the total GST matrix unit moves a live source coefficient to an arbitrary adjoined target; after denominator normalization it equals the unrestricted rank-free Hodge matrix unit; existence of a live source with nonzero coefficient for every target.
- name-vs-content: accurate finite GST calculation.
- gaps: combinatorial shadow only (no algebraicity transfer).

### GSTClassicalHodgeArsenalOrbitSaturation.lean (135 lines)
- decls: 5 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none.
- main content: cyclicity: every nonzero Hodge class is a cyclic vector for the matrix-unit arsenal (E_{i,j}α = α_i·e_j; invert scalars over ℚ; basis reconstruction); every target is a finite rational combination of matrix-unit images of any fixed nonzero source.
- name-vs-content: accurate linear algebra.
- gaps: the "arsenal" is the abstract matrix-unit algebra on the Hodge fiber, not geometry.

### GSTClassicalHodgeClosedCorrespondenceIrreducibilityBridge.lean (128 lines)
- decls: 4 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `hReach : ∀ q i j, MatrixUnitReachableByClosedCorrespondences i j` (every GST matrix unit realizable by genuine correspondence words) and `hSeed : ∀ q, ZeroFiberOrAlgebraicSeed` (imported obligations).
- main content: correspondence-invariance ⇒ rank-free arsenal invariance; **`exactHodge_of_closedCorrespondenceMatrixUnits`**: reachability + seed condition ⇒ `EveryHodgeClassIsRationalAlgebraic H` (the exact Clay-facing statement); finite-combination form.
- name-vs-content: accurate bridge between the two routes.
- gaps: both obligations (matrix-unit reachability by genuine correspondences; zero-fiber-or-algebraic-seed) are unproven and are exactly Hodge-strength.

### GSTDivisorWordRealization.lean (127 lines)
- decls: 3 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: `hexpr : ∃ e, eval (fun i => cl (D i)) e = alpha` (the target is a divisor word in cohomology).
- main content: evaluation of finite rational expressions (add/neg/mul/scalar) commutes with any ℚ-algebra cycle-class morphism; hence any class expressible as a divisor word has an explicit native representative; honest scope note: applies to varieties with divisor-generated cohomology (tori, flags), "NOT the full Hodge conjecture", explicitly false for primitive middle classes.
- name-vs-content: honest and accurate.
- gaps: divisor-generation of cohomology is a strong, separately required premise.

### GSTClassicalHodgeProjectiveSeparatorHeightOne.lean (121 lines)
- decls: 5 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: **genuine commutative algebra**: a positive-degree homogeneous separator is a nonunit modulo any proper homogeneous prime; the separator class generates an ideal of exact height one in the point quotient; every minimal prime over it has prime height exactly one (monotonicity + Krull height theorem).
- name-vs-content: accurate unconditional local codimension-one receipt.
- gaps: local algebra only; feeds the cutting engine.

### GSTClassicalHodgeRelativeSuccessorLowerBound.lean (116 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: pure specialization-order geometry: relative-cut points are strict specializations of the source; ambient coheight ≥ p+1 for codimension-p sources (lower bound half of the successor grading).
- name-vs-content: accurate.
- gaps: the matching upper bound (local regularity) lives elsewhere.

### GSTClassicalHodgeLiveApexSpineFanFinale.lean (110 lines)
- decls: 2 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: `tower_live : ∀ p, HodgeWeightLive H p → H.cycleClass p (projectiveCutTower V p) ≠ 0` (canonical cut tower has nonzero class in live weights) and `fan : ∀ p live, RootedStrictRelationFan (canonicalCutOrbitSeed G p ...)` (imported hypothesis-record family).
- main content: single-program generation with sparse ontology (dead weights discharged by the zero program); **`exactHodge_of_live_apexSpineFans`**: tower liveness + rooted fans ⇒ `EveryHodgeClassIsRationalAlgebraic H`.
- name-vs-content: "Finale" is the composition; the geometric burden is displayed as two hypotheses.
- gaps: both hypotheses are unproven; this is the apex/spine/fan route's conditional landing.

### GSTClassicalHodgeHorizontalGhostClosureCircularity.lean (107 lines)
- decls: 4 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `NativeMassCohomologyFactorization F` (imported) and `vertical : ∀ p live, ExactVerticalCutRayCertificate V p` (imported obligation).
- main content: **circularity audit**: given the vertical/source side, ghost-indexed horizontal closure predicates (strict or common-class) are each *equivalent* to the Hodge conclusion; therefore the horizontal finale must be a non-ghost-indexed unconditional construction.
- name-vs-content: accurate self-audit of the horizontal route's status.
- gaps: the vertical side itself (mass factorization + exact vertical cut rays) is assumed, and the horizontal side is shown to be a reformulation.

### GSTClassicalHodgeSeparatorPrimeCover.lean (98 lines)
- decls: 3 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: the separator minimal prime is nonzero and covers the quotient origin: every prime below it is ⊥ or itself; no prime strictly between (height-one cover law).
- name-vs-content: accurate algebra.
- gaps: local step of the cutting engine only.

### GSTFourPowerOntologicalAdapter.lean (97 lines)
- decls: 4 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: `FourPowerCreationMaster` (def-Prop: ∀ K ≥ 5, K ≠ 7, CreationCertificate (4^K)) — unproven arithmetic statement, passed as hypothesis.
- main content: defines `CreationCertificate` (explicit ternary-digit existence pattern) and proves its exact equivalence with the `Navigation` statement on four-powers; conversion lemmas.
- name-vs-content: honest "adapter" — explicitly says FourPowerCreationMaster "is a dependency, not an axiom".
- gaps: the creation master statement is unproven (equivalent in strength to the four-power program).

### GSTMathlibFiniteBasis.lean (93 lines)
- decls: 5 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: thin adapter over `Module.Basis.equivFun`: coordinate/decode maps are inverse; Kronecker vectors decode to basis vectors.
- name-vs-content: accurate utility file.
- gaps: none for its scope.

### GSTClassicalHodgeCMCoefficientDescentCore.lean (85 lines)
- decls: 4 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: a ℚ-linear retraction ε of the unit exists in every ℚ-algebra K (even infinite); finite K-linear representations of rational vectors descend to rational coefficients (`finite_span_descends`).
- name-vs-content: honest "linear algebra theorem … does not assert existence of the geometric input cycles".
- gaps: header carries a process note "NEEDS CI RUN LATER"; the geometric input cycles are elsewhere.

### GSTClassicalHodgeSeparatorRelativeCutLanding.lean (85 lines)
- decls: 3 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `hlive : ProjectivelyLiveSource ...` (source is projectively live).
- main content: genuine scheme-level landing: the descended separator successor lies in the principal-section range; its point-closure lift lies in the actual scheme-theoretic relative principal cut (via Mathlib's pullback range formula); the landed point is non-generic.
- name-vs-content: accurate geometric step.
- gaps: one step of the recursive cutting machine.

### GSTGeneralSpaceManifoldTangentFamily.lean (72 lines)
- decls: 2 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none.
- main content: records the genuine Mathlib tangent bundle as a GST "local family"; fiber identification is rfl; every charted manifold has a native tangent family.
- name-vs-content: accurate small glue file; explicitly declines to assert path transport.
- gaps: no connection/transport; no Hodge content.

### InformationBadTraceScratch.lean (57 lines)
- decls: 2 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: `hbad : ∀ j, GSTBadPairS (gstAffineMulCarryS 4 D X j) (gstDigitS X j)` (a seed-retaining affine bad trace).
- main content: a bad trace cannot contain the universal "22" synchronizer; the LSB-first word 1,2,1,0,2 forces a Happy gate from any carry < 4.
- name-vs-content: accurate scratch file (chronological label #0214/1132, imported from a side branch).
- gaps: scratch consequences for the information-surgery program; no global result.

### GSTGraphV2CanonicalTransparentBridgeProbe.lean (25 lines)
- decls: 1 theorem, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: every positive canonical width 3^s (s ≥ 1) is an exact integer number of transparent width-three blocks.
- name-vs-content: accurate one-line probe.
- gaps: none for its scope.

---

## BATCH SUMMARY

**Totals**: 68 files, 19,379 LOC, 735 theorems, 198 defs, 22 structures, **0 `axiom` declarations, 0 `sorry`, 0 `opaque`** (366 `#print axioms` audit lines). The repo's discipline in this batch: no bare axioms; all unproven content is packaged as hypothesis-records / def-Prop obligations passed as theorem hypotheses, with `#print axioms` capstones.

### Inventory of ALL custom axioms / unproven hypothesis-records (the load-bearing assumptions)

Named `axiom` declarations: **none**. The unproven-assumption inventory (all as records/def-Props):

**A. Hodge-route geometric interfaces (the load-bearing unproven assumptions):**
1. `FoldProcessOn.landing_cycle` (GSTGraphV2OntologicalFoldForAllN): `∀ v : PairWit, landing v → scale v ≠ 0 → ∃ Z : w.Cyc, w.cl Z = w.alpha` — assumes an integrable pure pair at nonzero scale yields a cycle with class exactly α ("Theorem C + Serre + Thom-Porteous + GAGA chain" as a field).
2. `LiveSpineMassSurvival` (GSTClassicalHodgeFullLimitlessCrown): `kernel_mass_zero : ∀ p Z, H.cycleClass p Z = 0 → nativeCycleMass V p Z = 0` ∧ `live_tower_mass_ne_zero : ∀ p, rationalHodgeSubspace ≠ ⊥ → nativeCycleMass V p (spineNativeTower G p) ≠ 0`.
3. `SpineTowerNonvanishing` (same file): `∀ p, rationalHodgeSubspace ≠ ⊥ → spineHodgeSeed G p ≠ 0`.
4. `FullProjectiveCosmicExternalization` (same file): `∀ p i j, ∃ K : ProjectiveNativeKernel V p, AtomCosmicExternalization G i j K`.
5. `SpineTowerConservedCharge` (imported; consumed in files 6, 9): conserved charge with nonzero native read on the spine tower.
6. `NativeSchemeHodgeRealization` (GSTGeometricRealizationStage2C): supplied hodge/cycleSpace/cycleClass/encode with `encode_injective`, `hodge_supported`, `basisCycle_address` — the finite-address realization certificate.
7. `ChannelHodgeQuotient` (GSTHodgeChannelQuotient): `decode_surjective` + `channelCycle_decodes` (surjective channel decoder whose generators decode to algebraic cycle classes); obligation `Stage2GChannelQuotientObligation`.
8. `FinitePointCosmicExternalization` / `PointAtomCosmicExternalization` (GSTClassicalHodgePointwiseCosmicExternalization): finite transition class = cosmic E_ij action on point classes, ∀ i j.
9. `TwoPrimitivePointTransitions` (GSTClassicalHodgeTwoGeneratorPointKernelSaturation): `NativePointTransition` for the code observable and the two-step Lefschetz observable (native point-lift existence).
10. `GhostStrictPlaneStrike` / `GhostAdaptiveStrictPlaneCompleteness` (OmniversalGhostPlaneStrike): every ghost admits a strict-relation edge to its detected sheet.
11. `CommonClassPlanePacket` fields `source_face`/`target_face` (CommonClassPlaneRealization): `leftCohomologyPullback ... u.state.1 = planeClass`, `rightCohomologyPullback ... v.state.1 = planeClass`; `GhostAdaptiveCommonClassPlaneCompleteness`.
12. `GhostWeightNativeSeedSurvival` + `GhostWeightPrimitiveStrictClosure` (OmniversalGhostBranchClosure): surviving seed + strict-relation compiler at ghost weights.
13. `HyperplaneDivisorHardLefschetz` (GSTUniversalLefschetzCurveCycles): surjective `hodgeLefschetz` (Hard Lefschetz) + `intersection_cycleClass`; plus `DivisorsRepresentHodge11` (Lefschetz (1,1)).
14. `RationalBettiIntersectionPrimitives` = `RationalProductCupTheory.swap_natural` + `RationalProjectionGysinTheory.snd_swap/fst_swap` (GSTClassicalHodgeBettiCupGysinPrimitives): the standard cup/Gysin structure on singular cohomology, stored as fields — **Mathlib does not supply these; they are unformalized standard theorems**.
15. `GeometricIncidencePrimitives` / `MiddleBettiCorrespondenceKernel` / `PointBettiClass` + `hpoint` (StrictCorrespondenceTransferFromPrimitives): the low-level incidence/Gysin comparison packets.
16. `ClosedCorrespondenceHitsSheet` / `NativeCycleCorrespondenceHitsSheet` (GhostExtinction, GhostAttack): a realized correspondence word sends a point/native cycle class to a nonzero multiple of a basis sheet, ∀ p j.
17. `MatrixUnitReachableByClosedCorrespondences` + `ZeroFiberOrAlgebraicSeed` (ClosedCorrespondenceIrreducibilityBridge): every GST matrix unit realizable by genuine correspondences + per-weight seed condition.
18. `tower_live` + `RootedStrictRelationFan` (LiveApexSpineFanFinale): cut-tower nonzero class in live weights + rooted strict-relation fans.
19. `ProjectiveSpanLiveSourceTarget` families + spine nonvanishing (SpineNonzeroFiniteSupportOrbit); `ProjectiveTwoGenerator` families + nonzero origin programs (HandwrittenPiProgramLanding); `GeometryFirstTwoGenerator` (OperatorCosmos); `ProjectiveApexL2Spoke` family (ApexSpokeCircularity); `NativeMassCohomologyFactorization` + `ExactVerticalCutRayCertificate` (HorizontalGhostClosureCircularity) — all imported record/obligation families, none instantiated in this batch.
20. `GeometricDualCyclePacket.dual` (GSTUniversalHodgeResidualProjection): `∀ i j, detectors i (cycleClass (cycles j)) = if i = j then 1 else 0` (intersection-dual Kronecker system).
21. Rank-two conditionals: nonzero geometric commutator / transversality / nonproportionality / CM complex structure J with `J² = −I` + `finrank = 2` (ActualCommutatorRankGain, SingleCorrespondenceRankTwo, MathboxCMGeometricComplexStructure).
22. Theorem-hypothesis bundles in GSTUniversalCMArithmeticObstruction: `hTheta/hExtract/hCMFunctorial/hProperGysinNaturality/hSecantCharacter` + Baire period-spread packets (the Weil-fourfold landing's geometric comparisons).

**B. Arithmetic (four-power/Graph-V2) unproven statements** (def-Props, never assumed as axioms): `FourPowerDirectExistence` (∀ K ≥ 5, K ≠ 7 → CommonTwo K — consecutive powers of 4 share a ternary digit 2; Collatz-flavored open problem), `FourPowerCreationMaster`/`CreationCertificate`, `FourPowerProductionUniverse` fields, `FourPowerHappyGeThreeProvider`, `FourPowerCommonTwoGeThreeProvider`, `FourPowerDirectNoCounterexampleClosure`, `FourPowerDirectNoBadAffineChannelOne`, `SeededBadTrace` (all-Nat bad trace existence). These drive the Graph-V2 "ontology" but are open.

### The 5 most load-bearing files and why
1. **GSTClassicalHodgeFullLimitlessCrown.lean** — the composition crown: `bigradedBettiHodge` derives the repo's Hodge statement (BigradedBettiHodgeStatement) from exactly the three unproven interfaces (SpineTowerNonvanishing / LiveSpineMassSurvival / FullProjectiveCosmicExternalization). Everything in the "limitless" route funnels through here.
2. **GSTClassicalHodgeBettiCupGysinPrimitives.lean** — the floor of the geometric stack: cup product and projection Gysin on singular cohomology exist only as record fields. Since Mathlib does not provide them, *every* correspondence-transfer theorem above (files 44, 12, 34, 50, …) is conditional on unformalized standard algebraic topology.
3. **GSTGeometricRealizationStage2C.lean** — defines what a "realization certificate" means (NativeSchemeHodgeRealization): the bridge between actual Mathlib schemes/cycles and the Hodge statement; its obligation (`NativeSchemeFiberRealizationObligation`) is precisely the unmet classical input (genuine H^{2p}, genuine (p,p) subspace, genuine cycle class).
4. **GSTUniversalCMArithmeticObstruction.lean** (5066 lines, 189 theorems) — the largest file; both the honest no-go layer (CM law impossible on ℚ; transfers preserve non-algebraicity) and the most developed positive conditional route (auxiliaryWeil fourfold/sixfold assembly with explicit hypothesis bundles). It sets the epistemic tone: naming conditional transfers does not discharge the implication.
5. **GSTClassicalHodgeCommonClassPlaneEquivalence.lean** — the honesty audit that proves the ghost-adaptive plane/closure predicates are *equivalent* to the Hodge statement (reformulations, not theorems), including a counterinstance (zero spine) showing the current interface cannot be universally closed. It caps how much of the surrounding "crown/finale" architecture is logical packaging.

### The single biggest gap
**No instance of any load-bearing geometric interface exists anywhere in this batch.** Concretely: the crown (`BigradedBettiHodgeStatement`) is proved only from records like `LiveSpineMassSurvival` / `FullProjectiveCosmicExternalization` / `FoldProcessOn.landing_cycle`, and the repo's own equivalence audits (files 47, 60, 41) prove these ghost-adaptive formulations are exactly Hodge-equivalent reformulations — i.e., the entire "limitless/ghost/plane" architecture reduces the Hodge conjecture to *itself*. The genuinely new mathematical content in the batch is real but bounded: no-go/obstruction theorems (file 1), exact Gr(2,5) pure-pair arithmetic (file 7), genuine point-set/commutative-algebra steps for the principal-cut engine (files 21, 57, 58, 61, 65), the atomic-span reformulation (file 33), and the conditional codimension-(d−1) Lefschetz closure (file 49). The missing piece — constructing even one defect-zero state, one externalization kernel, or one strict-relation plane on an actual variety — is untouched. Secondary but also total: the four-power arithmetic program (`FourPowerDirectExistence`) is an open Collatz-like conjecture treated as an explicit unproven dependency, and the standard cup/Gysin singular-cohomology API does not exist in Lean here at all.
