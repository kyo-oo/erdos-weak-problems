# Lean Batch 2 Map (Task 1-c)

Repo: /tmp/hc-clone-23 @ branch research/gpt6-native-point-primitive-span-20261017.
Batch: /tmp/lean_batch_2.txt — 70 files, 19,365 LOC, 740 theorems, 134 defs, 30 structures, **0 custom `axiom` declarations** (the single regex hit for `^\s*axiom\b` in GSTClassicalHodgeGradedOntologicalFanFinale.lean:37 is the docstring word "axiom, or arbitrary basis-cycle family is used."), **0 `sorry`**, 361 `#print axioms` receipt commands (outputs not stored in files; toolchain is CI-only). Every unproven assumption in this batch is carried by **hypothesis-records (structures with unproven mathematical fields)** or by theorem hypotheses — never by custom axioms.

### GSTUniversalResolvedSupportHodge.lean (2993 lines)
- decls: 93 theorems, 26 defs, 0 axioms, 0 sorry
- hypotheses: 3 hypothesis-records. (1) `ResolvedSupportGysin (c : ℕ)` fields: `rationalHodgeLift : ∀ alpha, alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading (c+1)) → alpha ∈ LinearMap.range bettiGysin → ∃ beta : ClassicalHodgeFiber Y HY 1, bettiGysin beta.1 = alpha` (rational Hodge strictness/surjectivity of the Gysin map onto supported Hodge classes) and `cycleClass_gysin : ∀ D, HX.cycleClass (c+1) (nativeGysin D) = bettiGysin (HY.cycleClass 1 D)` (cycle-class/Gysin naturality). (2) `AffineCodimensionTwoLocalization` field `localization_exact : ∀ delta, restrictBetti delta = 0 → delta ∈ LinearMap.range G.bettiGysin` (localization exactness of the pair (X,U)). (3) `AffineSuccessorHodgeLocalization` fields `boundary_localization_exact` (same at successor codimension) and `boundary_rational_hodge_lift : ∀ delta ∈ rationalHodgeSubspace → delta ∈ range boundaryBettiPush → ∃ beta : ClassicalHodgeFiber Y HY q, boundaryBettiPush beta.1 = delta` (Hodge lift through the boundary push). All are the docstring's "two geometric source obligations".
- main content: Gate 3 source-production: given the records + `DivisorsRepresentHodge11 HY` (Lefschetz (1,1), imported), constructs `nativeCycle` (divisor on resolved support pushed forward) with `HX.cycleClass (c+1) (nativeCycle) = alpha`; affine-open closure+boundary-divisor reconstruction of codim-2 classes; successor-induction for all p; source-free affine-vanishing variant; middle-primitive affine restriction injectivity. Then ~2300 lines of fully verified algebra over abstract commutative rings: quadric Bott projector idempotents, Jacobian-kernel projectors, Adams/degree-d projector algebra, finite nilpotent inverses (adjugate identities), target-coupled virtual sources with exact Gram/period laws, Todd-defect identities chow = K0 + Todd, Chow graded convolutions, Koszul primitives on abelian fourfolds (Gram det 12, exact target cycle with prescribed periods (a²-ab+b²)/3), all-even-dimension Koszul P/Q sources, paired-divisor Koszul annihilation, diagonal-sheaf correspondence extraction, blowup mixed push, incidence/nodal top-Chern polynomials, one/two-center Chern-character detection with exact factorial-multiple period laws.
- name-vs-content: name matches the resolved-support half of Gate 3, but the support condition is exactly the unproven half — the file itself says imposing it on all Hodge classes "would restate the missing universal source-production task".
- gaps: no instance of `ResolvedSupportGysin`/localization records is ever constructed (Gysin strictness + cycleClass naturality are assumed); the ring-level algebra (Gram tables, Chern polynomials) is verified combinatorics, not geometry of actual varieties; `DivisorsRepresentHodge11` comes from another file (unproven there).

### GSTPolarizedHodgeResidualEnergy.lean (941 lines)
- decls: 23 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: none as records; theorem hypotheses only: `hPositive : ∀ v ≠ 0, 0 < (Q v) v` (Hodge–Riemann positive-definiteness on the primitive fiber), `hPair`/`hGramDual` (detectors are genuine polarization/Gram-dual readouts), `hSchur`/`hIntegral`/`hSmall` (integer lattice gap inputs for the quantized exactness certificates).
- main content: exact polarized Pythagoras `Q(α,α)=Q(cl Z,cl Z)+Q(r,r)`; residual orthogonality to the algebraic projection; Gram-surplus / target-residual coupling force strict native rank birth (`span < span ∪ {fresh}`); optimal-step energy descent identity `Q(r,r) − Q(r,z)²/Q(z,z)`; quantized integer and Schur-determinant energy-gap exactness certificates (one sub-gap construction ⇒ exact representative); one-direction rank-one residual sector saturation; signed antideck source pairing = 2Σ|period|.
- name-vs-content: accurate — this really is polarized residual energy arithmetic; it does not claim Hodge.
- gaps: all positivity/energy/Gram-duality and lattice-gap inputs are hypotheses; existence of a coupled fresh native cycle per target remains open (stated in-file).

### GSTCMQuadraticNativeRankForcing.lean (636 lines)
- decls: 20 theorems, 11 defs, 0 axioms, 0 sorry
- hypotheses: no hypothesis-records (CMGraphDivisorCoordinates is a plain ℚ⁴ coordinate record). Theorem hypotheses: `hMin` (imaginary quadratic CM polynomial T²−2aT+(a²+b²) satisfied by the realized correspondence's Hodge operator), `hrank : finrank = 2`, `hPeriod/hReal/hImag` (canonical period comparisons of the spine seed with CM number-traces), `hR : HodgeCompatible`.
- main content: imaginary-CM has no rational eigenline (real content); CM correspondence transversality ⇒ rank-2 native Hodge realization (`∃ Z, cycleClass Z = alpha` in rank-2 fibers); CM number-trace (single & dual channel) forces nonzero seed; exact skew-adjoint CM orbit Gram `Q(v,v)Q(Tv,Tv)−Q(v,Tv)² = b²Q(v,v)²`; E×E CM elliptic divisor/graph sources have signed Gram 2I₃; tensor words give 3^m orthogonal sources with Gram 2^m I and trivial kernel; target-period compiler with exact readout recovery.
- name-vs-content: "rank forcing" is honest about the rank-2 limitation, stated explicitly in-file.
- gaps: rank-two-only; CM polynomial on arbitrary (p,p) fibers and geometric period comparisons are unproved inputs (stated in-file: "CM on H¹ of abelian varieties does not automatically yield this polynomial on all rational (p,p) fibers").

### GSTUniversalLefschetzKernel.lean (575 lines)
- decls: 22 theorems, 5 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: closed-form transition kernel for powers of the "universal Lefschetz" L = digit+carry shift on every A×B GST world: coefficient = binomial at the unique causal (Manhattan) time, 0 elsewhere; nonzero/positive iff classifiers; causal semigroup composition; sharp nilpotency index A+B−1; cosmic (unbounded ℤ² grid) kernel, non-nilpotence; historical 4×3 coefficient 10 absorbed.
- name-vs-content: "Lefschetz" is GST terminology for a lattice shift operator — no relation to the Hard Lefschetz theorem; otherwise accurate for finite worlds.
- gaps: purely combinatorial linear algebra over the digit/carry lattice; zero contact with cohomology of varieties (the analogy is never instantiated).

### GSTWorldRecoordinationGroupoid.lean (522 lines)
- decls: 24 theorems, 10 defs, 0 axioms, 0 sorry
- hypotheses: none (GSTWorldShape is data: rows, cols, area_eq).
- main content: equal-cardinality rectangular worlds form a recoordination groupoid through Fin N; code-preserving transport is unique; spectral code-sector projectors are idempotent/orthogonal/complete, natural under transport, and each is an integer spectral polynomial; complete classification of code-spectral intertwiners (any linear map intertwining all code projectors is pointwise multiplication by the image of 1); mixed-radix transpose absorbed; global recharting of the cosmic grid.
- name-vs-content: accurate for the finite-world combinatorics; "groupoid" is legitimate.
- gaps: pure ℤ-valued finite-index bookkeeping — no mathematical content beyond Fin N manipulations.

### GSTUniversalLefschetzCosmology.lean (473 lines)
- decls: 38 theorems, 3 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: H (digit) and V (carry) as Module.End of the world coefficient module; H^B = 0, V^A = 0, [H,V]=0, binomial calculus for L^n; grading/sector and Poincaré interface re-exports; cosmic endomorphism algebra (no extinction); compact (finitely-supported) evolution equals cosmic evolution observed in windows; exact recovery at each time.
- name-vs-content: same caveat as the kernel file — "Lefschetz/Poincare" here name lattice-shift and dual-pairing analogues, not the theorems.
- gaps: combinatorial only; the "Poincaré duality" is a perfect pairing on a finite index set.

### GSTGeometricRealizationStage2G.lean (429 lines)
- decls: 15 theorems, 5 defs, 0 axioms, 0 sorry
- hypotheses: two interface/hypothesis-records. (1) `HodgeBigrading` fields: `component : Fin (n+1) → Submodule ℂ (Complexification VQ)`, `independent : iSupIndep component`, `spans : (⨆ a, component a) = ⊤` — a **supplied** Hodge decomposition; the docstring admits "it does not yet construct the decomposition analytically" and conjugation symmetry is deliberately not assumed. (2) `HodgeBigradedBettiData` fields: `analytification`, `hodgeBigrading : ∀ p, HodgeBigrading … (2p)`, `cycleClass : ∀ p, codimensionCycles V.X p →ₗ[ℚ] RationalSingularCohomology …` — an **arbitrary** linear cycle-class map (proven under-constrained by the zero-map countermodel in GSTClassicalHodgeStage2GSemanticRigidity).
- main content: rationalHodgeSubspace defined as pullback of H^(p,p) along ℚ→ℂ complexification; explicit-witness normal form of the target; equivalence of the Stage-2G obligation with Stage-2F/2E obligations (Iff.rfl); landing theorems `bigraded_betti_hodge_of_stage2g_family/_obligation` and rank-free compact versions.
- name-vs-content: "realization" is semantic bookkeeping — nothing is realized; the file defines the target statement and reduces obligations across stages.
- gaps: the entire Hodge-theory interface (bigrading + cycleClass) is unproven input; no analytic construction, no instance for any actual variety.

### GSTClassicalHodgeOmniversalNativeOrbitSeparation.lean (406 lines)
- decls: 18 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: the load-bearing Prop `GeometricGSTPlaneCompleteness G : ∀ q j, ∃ P : GradedGeometricProgram V 0 q, P.cohomologyEval G (geometricOriginClass V H) = (classicalHodgeBasis V H q j).1` (every Hodge basis sheet is the output of one verified graded geometric program) — supplied, never constructed.
- main content: three-way exact identification: plane completeness ⇔ graded native-orbit cyclicity ⇔ completed-probe pairing totality; each implies `IsEmpty (OmniversalSeparatorGhost G)` and `BigradedBettiHodgeStatement V H` and the Clay-style `EveryHodgeClassIsRationalAlgebraic/FiniteRationalCombination`; weak-spine no-go: fields of the spine alone cannot force pairing totality (zero-cycle-class spine countermodel).
- name-vs-content: honest — the "separation" theorems are equivalences, and the file never claims the premise holds.
- gaps: `GeometricGSTPlaneCompleteness` is precisely the missing universal source-production task (the whole Hodge problem renamed into program-orbit language).

### GSTClassicalHodgeExactVerticalCutRay.lean (387 lines)
- decls: 17 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: theorem hypotheses `vertical : ∀ p, HodgeWeightLive H p → ExactVerticalCutRayCertificate V p` (a surviving exact vertical ray for every live weight) and `fan : ∀ p, RootedStrictRelationFan …` (rooted fans) in the finale; also `D : ProjectiveDegreeTraceSemantics V H` (degree-trace interface, imported).
- main content: nonnegativity of all successor-presentation transition coefficients; inductive `ExactVerticalCutRay` whose endpoint has strictly positive coefficient in the canonical cut presentation; one ray ⇒ positive projective trace ⇒ `cycleClass (projectiveCutTower V p) ≠ 0`; finale: vertical rays + rooted fans ⇒ `EveryHodgeClassIsRationalAlgebraic`.
- name-vs-content: accurate description of the ray mechanism.
- gaps: ray existence per live weight and fan existence are hypotheses; ProjectiveDegreeTraceSemantics is an interface whose geometric instantiation is elsewhere/undone.

### GSTClassicalHodgeSheetSpectralExtraction.lean (369 lines)
- decls: 10 theorems, 4 defs, 0 axioms, 0 sorry
- hypotheses: none (works from `¬ BigradedBettiHodgeStatement V H`).
- main content: on pure integral squares the code-sector projectors isolate single diagonal sheet atoms; sheet decomposition f = Σ sheetDiagonalAtom; complementary-mirror sheet pairing; `not_hodge_yields_single_sheet_spectral_witness`: failure of Stage-2G produces a finite integral pure square, a separator probe, and one spectrally isolated sheet pair with nonzero projected pairing.
- name-vs-content: accurate — a failure-witness reduction inside the combinatorial square model.
- gaps: the "integral pure square model" reduction lives in the GST combinatorial universe; translation from a genuine cohomological separator to the square model relies on imported constructions (canonicalIntegralPureSquareModel etc.).

### GSTClassicalHodgeHandwrittenPiCorrespondenceProgramLanding.lean (349 lines)
- decls: 9 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: hypothesis-record `SourceTargetCorrespondenceExpressions` with field `source_action : ∀ j, (expr j).cohomologyOperator (seed).hodge.1 = (basis repr coefficient) • (classicalHodgeBasis V H p j).1` — assumes a realized correspondence expression hitting every target basis sheet from the derived source; the strict specialization assumes `StrictlyMaterializedBranch` for every source→sheet branch (imported Prop).
- main content: from one nonzero full-correspondence program P0 (hne : output ≠ 0), the derived seed generates the full correspondence orbit; composed programs put c•e_j in the orbit, so each basis sheet and then every handwritten GST branch lies in the orbit; finite branch collapse ⇒ `∃ Z, H.cycleClass p Z = alpha.1`; global version: per-weight nonzero programs + source-specific strict branch materializations ⇒ `BigradedBettiHodgeStatement V H`.
- name-vs-content: "landing" overstates — it is a conditional reconstruction whose premises are exactly the missing geometry.
- gaps: strict materialization of the required branches and nonzero program outputs are unproven; no global omniverse materialization is used (deliberately), but nothing replaces it.

### GSTClassicalHodgeGeometricSpineKernelReduction.lean (341 lines)
- decls: 10 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: hypothesis-records `PrincipalCutKernelRealization` (fields `kernelStable : ∀ p, GradedKernelStable (successorNativeOperator V p)` and `hodge : ∀ p, … gradedAmbientOperator … ∈ rationalHodgeSubspace (p+1)` — kernel stability and Hodge preservation of the principal-cut operator) and `KernelReducedGeometricCycleClassSpine` (fields `algebraic_is_hodge`, `pushforward_kernelStable : ∀ p f, KernelStable (smoothProjectiveNativePushforward V f p)`, `principalCut`).
- main content: exact iff theorems: pushforward cohomological naturality exists ⇔ cycle-class kernel stability ⇔ preservation of finite point-class relations; principal-cut operator pair exists ⇔ graded kernel stability; the full spine is manufactured from the reduced kernel semantics (operator pairs become theorems, not stored data).
- name-vs-content: accurate — a genuine interface reduction.
- gaps: the kernel-stability and Hodge-preservation fields are unproven geometric laws; the file reduces packaging, not the mathematics.

### GSTGraphV2HandwrittenAnchoredCocycle.lean (329 lines)
- decls: 12 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: exact U-potential cocycle on the infinite Graph-V2 sheet (reverse-base-4 word concatenation); shifted "Equation III" identity and its weighted telescope; two-dimensional horizontal/vertical bicocycle; Happy ⇔ negative U-jump on the 12 physical cells; positive derivative at child-Happy/right-bad configurations; canonical recoordination of full-energy sheets onto tail-energy sheets at phase shifts.
- name-vs-content: accurate for the elementary arithmetic it does.
- gaps: pure base-3/base-4 integer arithmetic; no mathematical content beyond divisibility identities.

### GSTClassicalHodgePlaneGroundPoint.lean (321 lines)
- decls: 13 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none beyond `HodgeBigradedBettiData`/`GeometricCycleClassSpine` interfaces; the central Prop `PointSemanticGround H p pt` (point cycle classes equal an assigned geometric Betti class per point) is the local ground datum.
- main content: point-assignment ⇔ linear cycle-class map (equivalence `pointGeometryCycleClassEquiv`); PointSemanticGround ⇔ equality of the whole Stage-2G map with the point-generated map; unique global extension; zero-cycle-class world violates any nonzero point ground; full GST plane can coexist with ground failure (intrinsic plane algebra cannot synthesize semantics); ghost-adaptive plane packages are iff Hodge, hence barred as premises.
- name-vs-content: accurate — a semantic descent endpoint for the plane audit.
- gaps: no geometric point assignment is ever constructed; the file's own conclusion is that Stage-2G semantic freedom is exactly its (unconstrained) point coordinates.

### GSTGraphV2InfiniteControl.lean (310 lines)
- decls: 17 theorems, 3 defs, 0 axioms, 0 sorry
- hypotheses: none (InfiniteCell is data).
- main content: the infinite enriched V2 graph as a function on all (t,p); exact lattice law per cell; crossing-charge conservation on every rectangle; prefix-slice projection laws (digit/carry of P + 3^b·tail slices); physicality of prefix-generated seeds (carry < 4); Happy ⇔ seeded predicate of the exposed tail.
- name-vs-content: accurate arithmetic.
- gaps: elementary number theory; "infinite control" is an ℕ×ℕ lattice.

### GSTHodgePoincareStrands.lean (303 lines)
- decls: 13 theorems, 5 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: signed Hodge charge q = C−d strands on rectangular worlds; Poincaré complement reflects q ↦ (A−B)−q with strand-cardinality symmetry; strand projectors idempotent/orthogonal; digit/carry shifts shift charge exactly; pure diagonal ⇔ zero-charge strand; pairing of strands vanishes unless charges are complementary; pure diagonal Poincaré-stable iff square world.
- name-vs-content: "Hodge-Poincaré" is by analogy (charge = difference of lattice indices); content is honest combinatorics.
- gaps: no connection to Hodge theory beyond naming.

### GSTUniversalLefschetzCausalGeometry.lean (298 lines)
- decls: 16 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: the kernel's nonzero entries define a partial order (refl/trans/antisymm); exact degree advance, unique transition time, no positive-time return, bidirectional transitions trivial; composition of nonzero causal propagations is nonzero; every intermediate leg of a forward factorization is live; time bounded by remaining depth.
- name-vs-content: accurate for the lattice; "causal geometry" is order-theoretic bookkeeping.
- gaps: combinatorial only.

### GSTClayOfficial.lean (287 lines)
- decls: 9 theorems, 3 defs, 0 axioms, 0 sorry
- hypotheses: none (works inside the finite WaveCell model).
- main content: the Clay wording translated into the finite GST wave world: `clay_hodge_conjecture` (every Hodge class of the 12-cell lattice is a ℚ-multiple of the codim-p cycle class, for p < 3), constructive diagonal-coordinate witness, coefficient uniqueness, Hodge-type monomial classification (3C+d=4p ⇒ (C,d)=(p,p)), ℤ-dominates-ℚ, capstone `the_official_clay_landing`. The file itself adds the audit note: "It is a theorem about WaveCoef and RatCoef, not yet about arbitrary smooth projective complex varieties."
- name-vs-content: **largest gap in the batch**: `clay_hodge_conjecture` / `the_official_clay_landing` are names of a finite 4×3-lattice statement, not the Clay problem; the docstring's table maps "projective non-singular variety over C" to "the twelve-cell lattice".
- gaps: no varieties, no cohomology, no cycles beyond lattice cells; p restricted to p < 3.

### GSTGraphV2SixAdicSynchronizedShadows.lean (279 lines)
- decls: 14 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: CRT synchronization: 6-adic resolution = simultaneous dyadic+triadic resolution at equal depth; multiplication by 4^t is an isometry of triadic shadows and shifts dyadic depth by 2t (truncated); saturation phase transition; boxed divisibility law 6^k ∣ 4^t(x−y) ⇔ 3^k ∣ x−y ∧ 2^(k−2t) ∣ x−y.
- name-vs-content: accurate elementary number theory.
- gaps: none mathematically; no Hodge content.

### GSTFourPowerHappyProvider.lean (277 lines)
- decls: 14 theorems, 3 defs, 0 axioms, 0 sorry
- hypotheses: provider gates as theorem hypotheses (`hProvider : ∀ K ≥ 8, CommonTwoGeThree K`, `PrefixHitGeThree`); the roadmap target `FourPowerHappyGeThreeFromMonolith` is stated as a named Prop, not proved.
- main content: row ≥ 3 common-two ternary digits of 4^K transport to the physical HappyCell predicate; mod-27 row-three and mod-81 row-four residue classes give genuine witnesses; exact equivalence `CommonTwoGeThree K ↔ PrefixHitGeThree K` (prefix equality + killing trit).
- name-vs-content: "provider" is accurate — it converts one arithmetic witness form into another, not into a theorem.
- gaps: the actual universal existence (`∀ K ≥ 8, …`) is unproved; all content is ternary-digit arithmetic.

### GSTFourPowerExponentTritObstruction.lean (270 lines)
- decls: 11 theorems, 3 defs, 0 axioms, 0 sorry
- hypotheses: none (obstruction theorems assume `¬ ∃ common-two row` as hypothesis by design).
- main content: base-3 decomposition of the exponent K; the p-th exponent trit shifts both consecutive-power row digits equally; row p+1 is common-two ⇔ prefix rows agree AND the trit equals the unique killing trit 2−d; uniqueness of the killing phase; recursive restriction on K's ternary expansion if no common-two row exists.
- name-vs-content: accurate.
- gaps: elementary; the "obstruction" constrains hypothetical counterexamples only.

### GSTClassicalHodgeGSTDegreeCertifiedSource.lean (268 lines)
- decls: 5 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: theorem hypothesis `hstable : SameWeightGSTStable p (nativeAlgebraicWeightAddressSpan G p)` (GST sheet units preserve the algebraic Chow address span — explicitly flagged as "the precise remaining unproved universal condition"); `hlive`/`hExact` (exact successor survival at a point); `D : ProjectiveDegreeTraceSemantics`.
- main content: degree-certified saturation: any codim-p point cycle is nonzero because its projective degree is positive, so the GST sheet span saturates under hstable; degree-certified successor seed, source sheet, nonzero probe; per-target programs R : DegreeCertifiedGSTProgram give basis-sheet cycles, separator extinction, and `hodge_weight_of_degreeCertifiedPrograms`.
- name-vs-content: "source" is accurate — a starting seed, conditional.
- gaps: hstable and the synchronized source-target programs are unproven; the file says native-operator realization "is NOT inferred from a formal Hodge basis matrix unit".

### GSTInfiniteWorldClassification.lean (258 lines)
- decls: 16 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: complete classification `WindowTower ≃ (ℕ → Fin 3)` (coherent GST infinity = ternary stream space); level-K equality ⇔ first-K-trit equality; two-current trace is a complete injective observable; topological upgrade to a homeomorphism; continuity detected by finite windows.
- name-vs-content: accurate.
- gaps: pure combinatorics/topology of Cantor-like stream space.

### GSTClassicalHodgeStrictCorrespondenceAnalyticSpan.lean (254 lines)
- decls: 1 theorem, 5 defs, 0 axioms, 0 sorry
- hypotheses: none (IntrinsicBettiSpan fields are the constructed pullbacks, not assumed propositions).
- main content: for a strict bi-finite closed correspondence K → X×X: intrinsic analytic carrier = image of carrier complex points in X^an×X^an with subspace topology; continuous projections; genuine Mathlib singular chain/cochain functors; canonical left/right cohomology pullbacks on the FULL Betti carrier; `BettiRelated` relation cut out by the span.
- name-vs-content: accurate — real construction, no Hodge claims.
- gaps: no transfer/pushforward operator yet (next file); no example correspondence beyond graphs.

### GSTUniversalLefschetzDynamics.lean (251 lines)
- decls: 14 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none.
- main content: dimension-free degree descent (L^k vanishes below degree k); L raises pure degree sectors exactly; L^(A+B−1)=0 for positive worlds; the historical 12-cell L^6 theorem recovered via the chart lift.
- name-vs-content: accurate within the lattice model.
- gaps: combinatorial only.

### GSTUniversalCodimensionTwoPrimitiveExtraction.lean (246 lines)
- decls: 8 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: hypothesis-record `GeometricHigherLefschetzData G d` with field `hardLefschetz : Function.Surjective cupH2` (Hard Lefschetz surjectivity of cup-with-h^(d−2) from H¹ to H^(d−1) — the load-bearing unproven geometric input), plus `twoStepCompatibility`, `nativeNaturality`, and cup/primitiveTest data; also uses imported `DivisorsRepresentHodge11 H` (Lefschetz (1,1)).
- main content: given the data, constructs an ACTUAL algebraic codim-2 correction cycle h·D for any (2,2) class α; exact decomposition α = primitive remainder + native cycle; primitive projector kills cup-h for any Hodge α; threefold specialization (primitiveTest = id ⇒ primitive remainder zero ⇒ every (2,2) class on a threefold has a native cycle).
- name-vs-content: honest — "extraction" of the nonprimitive part only; the primitive remainder is exactly what remains.
- gaps: Hard Lefschetz surjectivity and Lefschetz (1,1) are hypothesis fields/imports; the primitive remainder's algebraicity is the open problem (stated in-file).

### GSTClassicalHodgeGradedProgramSpectralSaturation.lean (237 lines)
- decls: 8 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: hypothesis-records `GradedProgramSpectralFamily` (fields: program, injective basis indices, injective eigenvalues, `eigenvector : ∀ i, program.cohomologyEval G (basis i) = eigenvalue i • (basis i)` — assumes one horizontal program diagonalizes a finite basis family with distinct rational eigenvalues) and `FiniteGradedProgramSpectralCover` (fields: `covers_live_support`, `visible` — assumes each live sheet is orbit-visible).
- main content: orbit-spectral saturation: coordinatewise visibility + hyperplane avoidance assembles one cyclic seed; Lagrange interpolation isolates each selected basis vector inside the graded program orbit; per-class finite covers ⇒ native cycle for α; per-class covers in all weights ⇒ `BigradedBettiHodgeStatement`.
- name-vs-content: accurate mechanism description; "saturation" is conditional on the covers.
- gaps: existence of a diagonalizing program with distinct rational eigenvalues and of covers/visibility is not addressed.

### GSTClassicalHodgeCodimensionPointTower.lean (234 lines)
- decls: 8 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: the Prop `NativePointSuccessorNonvanishing V : ∀ p x, successorNativeOperator V p (codimensionPointCycle V.X p x) ≠ 0` — "The uniform survival law remains a hypothesis; induction does not prove it" (verbatim); structures NativeCutReached/NativeCutStop carry (derived) certificates.
- main content: conditional codimension-point tower from the degree apex; unconditional cut search returning reached-or-stopped with a stop certificate proving the native cut is zero; no-go: uniform survival cannot be inferred from an unbounded address space (empty next stratum refutes it).
- name-vs-content: accurate and unusually candid about the hypothesis.
- gaps: uniform principal-cut survival for all varieties/points is open and structurally necessary.

### GSTClassicalHodgePlanePrimitiveCircularity.lean (231 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: theorem hypotheses `hseed : AlgebraicHodgeSubspace ≠ ⊥` / conserved spine `SpineTowerConservedCharge` for the equivalences.
- main content: circularity firewall: with a live algebraic seed, all-pairs native realizations of the two universal two-slot GST primitives ⇔ the fixed-weight Hodge conclusion; likewise the explicit chosen point-transition kernel package; hence these families cannot be promoted to lower axioms.
- name-vs-content: accurate — an audit, not a proof of Hodge.
- gaps: only firewall value; everything is an equivalence with Hodge itself.

### GSTFourPowerDirectChat2Application.lean (224 lines)
- decls: 14 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: closure gates as hypotheses (`hClosed : ∀ K ≥ 5, K ≠ 7 → ¬¬ CommonTwo K`).
- main content: the direct problem = affine channel 1; counterexample = bad state B₁; first-trit split; mod-9 killing classes; obstruction bundle (mod-9, mod-27, mod-81, exponent-trit laws) for any counterexample; exact equivalences `FourPowerDirectExistence ↔ ∀ K ≥ 5, K ≠ 7 → ¬ BadChannel 1 (affineOrbit K)` and creation-master equivalence.
- name-vs-content: accurate interface algebra between arithmetic languages.
- gaps: the bad channel is never killed — `FourPowerDirectExistence` remains unproved (the monolith/Happy program's open core).

### GSTResearchGeometricOrbitSynthesis.lean (221 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: imported Prop `ActualHodgeCorrespondenceIrreducible (V,H,p)` (the actual correspondence representation has no nontrivial invariant subspace) — supplied as theorem hypothesis `hirred`; plus `hnz` (nonzero seed class).
- main content: inductive geometric orbit words (seed + realized Hodge-compatible correspondences); orbit span is invariant under all actual correspondences (proved, not assumed); irreducibility + nonzero seed ⇒ orbit span = ⊤ ⇒ every rational Hodge class has a native cycle (`every_hodge_class_of_constructed_actual_orbit`).
- name-vs-content: honest — the docstring states it "does NOT prove that arbitrary smooth projective varieties possess an irreducible correspondence action. That strong assertion would include the central unresolved algebraicity problem."
- gaps: geometric existence of irreducible correspondence families is open and equivalent-strength to the algebraicity problem.

### GSTClassicalHodgeProjectiveSelfCorrespondences.lean (217 lines)
- decls: 8 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: genuine Mathlib scheme geometry: self-product X×_{Spec ℂ}X; diagonal and graphs of ℂ-endomorphisms as closed immersions (via separatedness of Proj over ℂ, base change of the diagonal along the twist); graph universal property; crown theorem.
- name-vs-content: accurate — real algebraic geometry, no Hodge content claimed.
- gaps: no cohomological action of these correspondences here (deferred to later files).

### GSTClassicalHodgeGradedOntologicalFanFinale.lean (209 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry (the `axiom` regex hit at line 37 is a docstring word, not a declaration)
- hypotheses: hypothesis-record `GradedOntologicalFan G D` with fields `vertical : SeedPropagationFamily V H` (a vertical propagation family through genuine graded transports), `zero_eq : vertical.seed 0 = (codimensionZeroDegreeApex G D).hodge`, `horizontal : ∀ p, RootedStrictRelationFan (propagatedOrbitSeed …)` (a rooted strict-relation fan in every weight) — the complete unproven fan package.
- main content: constructs propagated nonzero algebraic orbit seeds at every weight from the degree apex; from any GradedOntologicalFan: `bigradedBettiHodge`, `everyHodgeClassIsRationalAlgebraic`, `everyHodgeClassIsFiniteRationalCombination`, elementwise `hodgeClass_has_nativeCycle` — i.e., the full Clay-style statement conditional on the fan.
- name-vs-content: "finale" is conditional — nothing here proves the fan exists.
- gaps: SeedPropagationFamily existence and per-weight RootedStrictRelationFan existence are the entire remaining burden (one vertical Lefschetz transport + one materialized strict ray per target direction, per the docstring).

### GSTClassicalHodgeAtomicAnnihilator.lean (208 lines)
- decls: 5 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none.
- main content: pure linear algebra: a separating functional exists for any point outside a submodule; Hodge weight ≤ atomic span ⇔ every detector annihilating all codim-p point-cycle classes annihilates the Hodge subspace; Stage-2G statement ⇔ no atomic separator; contrapositive witness form (weight + class + detector).
- name-vs-content: accurate dualization of the target.
- gaps: none internally; it is a reformulation, not progress toward truth of the statement.

### GSTClassicalHodgeAtomicOperatorAlgebra.lean (203 lines)
- decls: 13 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none (closure under ops given atomic stability of generators).
- main content: AtomicSpanStable is closed under 0, id, scalar, +, −, comp, powers, polynomials; native point lifts likewise; Lefschetz-assembly form (polynomials in A+B).
- name-vs-content: accurate operator closure algebra.
- gaps: closure only; stability of any interesting generator is external.

### GSTClassicalHodgeFiberedDefectProjectiveCocycle.lean (200 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `N : GeometricPushforwardNaturality V H p f` (pushforward cohomological naturality interface, imported), `hcod` (codimension preservation of the point).
- main content: point-class pushforward = residue-weighted target point class; exact relabelled-transport defect cocycle `defect(f·(i,x) relabelled j) = f_*^H(defect(i,x)) + (f_*^H e_i − deg_x(f) e_j)`; defect-zero transport ⇔ genuine sheet-action equation.
- name-vs-content: accurate cocycle calculus.
- gaps: GeometricPushforwardNaturality instances are the (unproven) interface; no geometric construction of the required sheet actions.

### GSTClassicalHodgeStrictCorrespondenceBettiObstruction.lean (199 lines)
- decls: 6 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: theorem hypotheses `htotal` (obstruction vanishes identically) and `hright` (right pullback injective) for the canonical operator.
- main content: transfer obstruction = left pullback followed by quotient by right-pullback range; obstruction zero on α ⇔ ∃β with l*α = r*β; totality ⇔ obstruction = 0; injectivity ⇒ unique targets; canonical full-Betti correspondence operator exists and is unique under totality+injectivity.
- name-vs-content: accurate — the precise push-pull interface.
- gaps: totality and injectivity of the pullbacks are exactly the unproved analytic input for correspondence operators.

### GSTClassicalHodgeBareLefschetzNonCircularity.lean (195 lines)
- decls: 5 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: theorem hypotheses `haAlg` (algebraic source), `hi` (nonzero coordinate), `hL` (native point lifts) inside the equivalence; `MinimalGhostLocalSeed` for the ghost specialization.
- main content: native point lifts for the compressed two-slot L² operator ⇔ algebraicity of the target basis sheet (given one live algebraic source with nonzero coordinate); minimal-ghost specialization: the bare-L² premise is literally the algebraicity of the detected ghost sheet; a genuine minimal separator forbids the lifts.
- name-vs-content: accurate non-circularity audit.
- gaps: audit only — shows the premise is Hodge-equivalent, not true.

### GSTClassicalHodgeFiniteSupportArsenalConjugation.lean (194 lines)
- decls: 8 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none.
- main content: every Hodge class has finite live support; conjugated matrix units reproduce the full matrix-unit pattern on the live support; Lefschetz tomography detects any nonzero class; conjugation receipts and crown.
- name-vs-content: accurate bookkeeping.
- gaps: linear-algebra identities inside the chosen basis; no geometry.

### GSTGraphV2CanonicalPhaseWaveProbe.lean (190 lines)
- decls: 10 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: canonical tail arithmetic: block recurrence; 4^(n·3^r) ≡ 1 mod 9; canonicalTail r n ≡ 7n mod 9; LTE coefficient ≡ 16 mod 27; prefix offset ≡ 5 mod 9; parent-tail phase (5+7n) mod 9; Happy parent gates for residues 3,4 mod 9; global parent badness forbids residues 3,4.
- name-vs-content: accurate modular arithmetic.
- gaps: elementary only.

### GSTClassicalHodgeGradedNativeCohomologyRealization.lean (185 lines)
- decls: 5 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: `GradedKernelStable A` (kernel-preservation Prop) as the single congruence condition (theorem hypothesis `hA`).
- main content: class congruence; descent of a graded native transport to the cycle-class range; extension to the whole ambient cohomology via LinearMap.exists_extend; automatic graded cycle-class naturality; the graded operator pair is generated, not stored.
- name-vs-content: accurate descent construction.
- gaps: kernel stability of any particular geometric transport is external; extension is a choice (Classical.choose) agreeing only on the range.

### GSTClassicalHodgeFiberedSeparatorDefect.lean (183 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `S : BasisAtomicSeparator V H p i` (imported separator record with annihilates_atoms/detects_basis fields); structure `FiberedDefectEvent` packages separator+point+derived nonzero detector reading (fields proven by the constructor, not assumed).
- main content: a separator reads the fibered defect of every common atom as minus its nonzero basis value; hence atom defects are nonzero; normalized spectral atoms likewise; Stage-2G failure + one native point ⇒ a nonzero fibered defect event.
- name-vs-content: accurate microscopic failure packaging.
- gaps: `choosePoint : ∀ p i, Nonempty (CodimensionPoint V.X p)` is itself a nontrivial existence hypothesis in the final theorem (points at every codimension).

### GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall.lean (180 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none (structures package genuine Mathlib finiteness predicates).
- main content: strict correspondence layer: SchemeFiniteClosedCorrespondence (closed into self-product + IsFinite left projection) and bi-finite version; one-way forgetting into the older point-finite API; factor-swap transpose preserves strict bi-finiteness.
- name-vs-content: accurate — a genuine upgrade firewall from point-finiteness to scheme-finiteness.
- gaps: no cohomology yet; existence of interesting correspondences (beyond graphs) external.

### GSTClassicalHodgeRankFreePrimitiveGeneration.lean (177 lines)
- decls: 7 theorems, 3 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: finite read/write conjugation between any finite list of genuine Hodge basis directions and the rational GST pure window; the finite matrix unit is definitionally the lifted rank-free Hodge matrix unit; every global matrix unit = lift of one fixed 2×2 GST projector/Lefschetz word after recoordination.
- name-vs-content: accurate.
- gaps: pure linear algebra; "GST arsenal generation" of the 2×2 word is imported combinatorics.

### GSTGraphV2RecursiveStateCausality.lean (174 lines)
- decls: 6 theorems, 7 defs, 0 axioms, 0 sorry
- hypotheses: `TransportRespectsGeneration` Prop as theorem hypothesis (cross-world transport stays in the generated cosmos).
- main content: packed states (Σ-world); primitive local/transport steps; finite composable histories; reachability/closure; stable semantics propagate through histories; generated-world closure under generation-respecting transport.
- name-vs-content: accurate type-theoretic causality scaffolding.
- gaps: abstract ontology layer; no mathematical content beyond inductive-path bookkeeping.

### waves/GSTWaveCohomologyV2.lean (172 lines)
- decls: 9 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: source-free ⇔ exact (two-form = horizontal+vertical coboundary) on WaveCells; exact matter locus = three cells; row-class cocycle over concatenated windows; finite transport law; translated row Gauss law and translated 2D Gauss law (exact boundary/source decompositions from any horizontal phase); crown.
- name-vs-content: "cohomology" is a 12-cell coboundary identity; content is honest finite arithmetic.
- gaps: no relation to singular or sheaf cohomology.

### waves/CardinalWorldsPostulateLawV2.lean (168 lines)
- decls: 11 theorems, 3 defs, 0 axioms, 0 sorry
- hypotheses: `ControlledTowerV2` is a data structure (level/bridge/admissible with invariant laws `level_admissible`, `ledger`, `control_preserved` — an interface, not an unproven mathematical proposition).
- main content: legacy controlled tower degenerates (stationary); V2 separates control from transition: exact finite transport, composition, reconstruction from level 0, admissibility propagation, extensionality, a non-stationary example tower; crown.
- name-vs-content: accurate; "Postulate III" is internal GST nomenclature.
- gaps: discrete dynamics bookkeeping only.

### waves/GSTVortexSingularityV2.lean (166 lines)
- decls: 12 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: fixed points of the vortex core rotation = two axial cells; spiral BIG2 exactness; arbitrary-sheet stability of cascade windows mod 3^k; exact ignition witness: HappyCell fires at the LTE cut row a+1 for cores ≡ 2 mod 3; absorbed singularity theorem; N-shape channel cut signatures and global cut-row selectors.
- name-vs-content: accurate arithmetic; "vortex/singularity" are internal names for digit configurations.
- gaps: elementary number theory only.

### GSTTactic.lean (160 lines)
- decls: 14 theorems, 3 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: small arithmetic helper lemmas (case splits for carries/digits, GST+/ALT−/NULL space predicates, bridge contradictions); custom tactics `gst_omega` (deliberately Aesop-free residual arithmetic solver), `gst_carry_cases`/`gst_digit_cases`/etc. macros, and `gst_end` final closing tactic for the "RED incision".
- name-vs-content: accurate utility file.
- gaps: none (infrastructure).

### GSTClassicalHodgeProjectiveSeparatorCarrierDescent.lean (155 lines)
- decls: 7 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `hlive : ProjectivelyLiveSource n x` (live-source condition, imported).
- main content: the projective separator successor lies in the closure of the source point (prime containment), hence in the closed image of the carrier's projective immersion; descent to a genuine carrier point, distinct from the source, vanishing on the chosen separator equation, in the support of the principal section.
- name-vs-content: accurate genuine topology/geometry.
- gaps: no Hodge content; live-source condition is external.

### GSTGraphV2ArithmeticOmniversalRealization.lean (155 lines)
- decls: 9 theorems, 4 defs, 0 axioms, 0 sorry
- hypotheses: none (ArithmeticNode is data).
- main content: the legacy x4/base3 lattice realized as one `OmniversalGraph` (carrier-agnostic event ontology); horizontal/vertical updates are events; the exact digit/carry laws are preserved; reachability embedding; crown.
- name-vs-content: accurate glue layer.
- gaps: definitional plumbing only.

### GSTClassicalHodgeTransferSeedUniverse.lean (149 lines)
- decls: 7 theorems, 1 def, 0 axioms, 0 sorry
- hypotheses: none.
- main content: canonical cosmic transfer seed = single-point Finsupp at the diagonal address (nonzero, "Hodge" in the ℚ-address support sense); every multiplicity sheet projects to that seed; every nonzero Hodge state has a live sheet tethered to the canonical seed; crown.
- name-vs-content: accurate internal GST bookkeeping.
- gaps: "Hodge" here is a support condition on addresses, not cohomological Hodge theory.

### GSTClassicalHodgeCodimensionZeroFundamentalCycle.lean (146 lines)
- decls: 5 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: coheight-zero points of a smooth projective carrier are exactly the generic points of the finitely many irreducible components (sober + Noetherian argument); canonical codimension-zero fundamental cycle = sum of unit point cycles over all components, with the cycle-class formula under any linear class map; crown.
- name-vs-content: accurate genuine construction.
- gaps: none for weight zero (one of the few unconditional geometric constructions in the batch).

### GSTFourPowerDirectNo22.lean (143 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `hNo : ¬ ∃ q ≥ 1, digit3 (4^K) q = 2 ∧ digit3 (4^(K+1)) q = 2` (assumed counterexample) by design.
- main content: under a global no-common-two trace, every source digit 2 forces the next binary carry to 1 and forbids an adjacent 2 (no "22" blocks anywhere in 4^K); exact isolation packet for every source digit two.
- name-vs-content: accurate obstruction arithmetic.
- gaps: conditional on the counterexample hypothesis; elementary.

### GSTClassicalHodgeCyclicRealizedCorrespondenceAttack.lean (139 lines)
- decls: 5 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: the Prop `IsCyclicAlgebraicSeed seed : seed ∈ AlgebraicHodgeSubspace ∧ ∀ alpha, ∃ W : RealizedCorrespondenceWord, (realizedWordPair W).cohomologyOperator seed.1 = alpha.1` — a cyclic algebraic seed under actual correspondence words (supplied, never constructed).
- main content: realized words preserve the cycle-class range; one cyclic seed per weight ⇒ `BigradedBettiHodgeStatement`; ⇒ literal `EveryHodgeClassIsRationalAlgebraic` and finite-rational-combination forms.
- name-vs-content: honest — "attack" is the right word; the file frames the remainder as one representation statement (construct a cyclic algebraic seed).
- gaps: cyclicity of any seed for the actual correspondence algebra is open and is Hodge-equivalent strength.

### GSTClassicalHodgeStage2GSemanticRigidity.lean (138 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none (it builds the countermodel).
- main content: `zeroCycleClassData H` keeps the analytification and bigrading but sets cycleClass := 0 — accepted by the Stage-2G structure; any nonzero (p,p) class then falsifies `BigradedBettiHodgeStatement`; hence no theorem quantified over arbitrary `HodgeBigradedBettiData` can be the classical Hodge theorem unless the cycle-class field is geometrically constrained.
- name-vs-content: accurate and crucial — the honest self-audit of the interface.
- gaps: demonstrates the gap rather than closing it: the corpus's own interface admits degenerate models.

### GSTClassicalHodgePrincipalCutNativeCycle.lean (132 lines)
- decls: 4 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `[IrreducibleSpace V.X]` instance assumption.
- main content: principalCutCycle: finite sum of unit cycles over the coheight-one points of the selected positive-degree principal section — a literal native codimension-1 algebraic cycle, independent of Hodge semantics; cycle-class formula under any linear map; crown.
- name-vs-content: accurate unconditional geometry.
- gaps: irreducibility assumed; nonvanishing/class of the cut not addressed here.

### GSTResearchFiniteWeightGeometricDegree.lean (132 lines)
- decls: 4 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: hypothesis-record `BoundedGeometricDegreeCharge G d` fields: `class_degree : ∀ p ≤ d, bettiDegree p (H.cycleClass p Z) = nativeDegree p Z` (degree/cycle-class compatibility), `base_degree_ne_zero : nativeDegree 0 (codimensionZeroFundamentalCycle V) ≠ 0`, `successor_degree : ∀ p < d, nativeDegree (p+1) (successorNativeOperator V p Z) = successorScalar p * nativeDegree p Z` (principal-cut degree transport).
- main content: degree of the native spine tower is constant in the window p ≤ d; nonzero native degree derived; cohomological spine class nonzero; nonzero algebraic Hodge seed at each p ≤ d. Explicitly dimension-bounded (no p > d claims).
- name-vs-content: accurate; the header says "without ANY assertion that its structural hypotheses have been proved for all varieties".
- gaps: the degree-charge fields (cup/Gysin/projective intersection verification) are "a substantive next obligation" (verbatim).

### GSTSeedOneShift.lean (125 lines)
- decls: 8 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: exact digit/carry stripping for the prefixed-one chart 1+3X; Navigation of 1+3X ⇔ seed-one witness on X; physicality (seed-one carry < 4, four-state cases).
- name-vs-content: accurate arithmetic.
- gaps: elementary only.

### GSTClassicalHodgeFiniteSpineMomentCompatibility.lean (120 lines)
- decls: 2 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `D : SpineTowerConservedCharge` (imported conserved-charge record) / `M : NativeMassCycleClassBridge` (imported mass-bridge record) — the inputs whose compatibility is being proved.
- main content: any unbounded conserved charge restricts to a finite moment chain at every horizon; the finite detector recovers the same seed nonvanishing; the older native-mass bridge factors through the finite detector.
- name-vs-content: accurate backward-compatibility layer.
- gaps: both input records are themselves unproven geometric interfaces defined elsewhere.

### GSTClassicalHodgeAmbientIntersectionFromPrimitives.lean (118 lines)
- decls: 5 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `P : RationalBettiIntersectionPrimitives A d` (imported cup/Gysin primitive theories) and `kappa : MiddleBettiCorrespondenceKernel` (kernel class data).
- main content: the historical bundled AmbientBettiIntersectionCalculus is a definitional repackaging of cup + projection Gysin; correspondence kernel action and transpose action written directly from the two primitives.
- name-vs-content: accurate interface flattening.
- gaps: the primitive theories (rational cup product, Gysin maps on singular cohomology) are imported interfaces, not constructed here.

### GSTK3DirectGraphOrbitDifference.lean (110 lines)
- decls: 2 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: theorem hypotheses `hShared : ∀ i, P.primitiveTest (nativeToHodgeFiberLinear G (graphs i)) = common` (all four graph classes have the SAME Lefschetz test value — the geometric input) and measure values (2,0)/(0,2) supplied for the independence detector; `P : GeometricHigherLefschetzData` (Hard Lefschetz record) throughout.
- main content: even/odd graph differences Γ_id−Γ_g², Γ_g−Γ_g³ are directly primitive (primitiveTest = 0) under the shared-test hypothesis; rank-two independence via the (2,0)/(0,2) measurement (Fermat quartic K3 with g: z₀↦i z₀ is the motivating example; Gram diag(8,8) is docstring arithmetic, not a Lean theorem).
- name-vs-content: accurate; the K3/Fermat specifics are prose motivation — the Lean is generic conditional algebra.
- gaps: no Kunneth comparison between scheme graphs and Betti endomorphisms (stated in-file as "the remaining analytic instantiation"); Gram values not proven in Lean.

### GSTClassicalHodgeCorrespondenceSemanticFirewall.lean (104 lines)
- decls: 2 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none (constructs the countermodel).
- main content: with the zero cycle-class map, EVERY linear endomorphism satisfies the pointwise realization law of `RealizedFiniteClosedCorrespondence` for the SAME geometric correspondence K; hence zero and identity package as two distinct "realized" Betti actions on identical geometry — the off-image cohomological action is not pinned by pointwise laws.
- name-vs-content: accurate countermodel audit of the correspondence interface.
- gaps: identifies the missing geometric input (canonical full-Betti correspondence action) without providing it.

### GSTClassicalHodgePointClosureIntegral.lean (104 lines)
- decls: 2 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: the point-closure subscheme (vanishing ideal of closure {x}) is reduced (radical vanishing ideals on affine charts), irreducible (imported), hence integral; every stalk is a domain; crown.
- name-vs-content: accurate genuine commutative algebra.
- gaps: none internally; feeds the principal-cut dimension engine.

### GSTClassicalHodgeKrullPrincipalCut.lean (94 lines)
- decls: 6 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: nonzero element of a domain is a non-zero-divisor; in a Noetherian domain a nonzero nonunit principal ideal has height exactly 1; Krull upper bound ≤ 1 in general Noetherian rings; minimal primes over principal ideals; stability under associates.
- name-vs-content: accurate — Mathlib's Krull PIT correctly invoked and specialized.
- gaps: none; genuine, unconditional commutative algebra.

### GSTGraphV2BlockScratch.lean (91 lines)
- decls: 2 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none (hD/hA are definitional equations for block parameters).
- main content: affine carry sampled across k-trit blocks: exact block-step recurrence; block echo law S_(q+k) = 4cU_q + (S_q+4U_q)/D.
- name-vs-content: accurate; "Scratch" in the name is honest.
- gaps: elementary arithmetic; carries a git-history banner (branch sol_physical-phase-crossing-surgery, 2 commits).

### GSTMathboxCorrectedZetaInfinite.lean (88 lines)
- decls: 4 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: none.
- main content: exact infinite sum of the corrected Equation (3) kernels: Σ_{m≥0} indexedKernel 2 2 m = −1 (genuine `tsum` over ℝ); summability; nonzero amplitude under a nonzero scalar (e.g., a zeta value); explicit disclaimers that a zeta value alone creates no algebraic cycle.
- name-vs-content: accurate; "Mathbox" signals a numerical-audit module.
- gaps: a geometric series evaluation — mathematically trivial content in campaign vocabulary.

### GSTGeneralSpace.lean (77 lines)
- decls: 0 theorems, 2 defs, 0 axioms, 0 sorry
- hypotheses: none (GeneralSpace/Chart/etc. are data structures: points + typed composable paths with category laws proven by rfl in `discrete`).
- main content: the ontological root of GST: carrier-independent GeneralSpace (no metric/dimension/chart built in); charts as observations; optional incidence/grading; every type is a discrete General Space.
- name-vs-content: accurate minimal ontology.
- gaps: pure scaffolding; no theorems, no mathematical content.

### GSTGraphV2FourPowerCanonicalParentObstruction.lean (75 lines)
- decls: 3 theorems, 0 defs, 0 axioms, 0 sorry
- hypotheses: `hNo : ¬ ∃ q ≥ 1, HappyCell …` (global no-Happy on the unit-energy power column) by design.
- main content: global no-Happy on right-edge exponents 3^(s+1)n+3^s transports to all-depth seeded badness on the canonical parent tail; hence origin residues 3,4 mod 9 are forbidden; surviving origin phase sector is the 7-class complement.
- name-vs-content: accurate obstruction transport.
- gaps: conditional arithmetic; the no-Happy premise is the unproved monolith assumption.

### GSTResearchLocalCyclicityHodge.lean (71 lines)
- decls: 1 theorem, 0 defs, 0 axioms, 0 sorry
- hypotheses: theorem hypothesis `hcyclic : ∀ p, (∃ a ≠ 0) → ∃ Z, SeedCyclicForActualGeometry G Z` — a native algebraic cycle cyclic under the actual finite-closed Hodge-compatible correspondence operators at every nonzero weight (imported Prop).
- main content: `full_hodge_of_all_active_native_geometric_cyclicities`: local per-weight cyclicity (weaker than global irreducibility, no zeta scalar, no matrix-unit assumptions) ⇒ `BigradedBettiHodgeStatement V H`; zero fibers handled trivially.
- name-vs-content: honest — the docstring says "an all-varieties, all-weights CONDITIONAL reconstruction result (not the unconditional classical Hodge conjecture)".
- gaps: the local cyclicity premise is unproven and is exactly the orbit-generation burden.

---

## BATCH SUMMARY

**Totals.** 70 files; 19,365 LOC; 740 theorems; 134 defs; 30 structures; **0 custom `axiom` declarations**; **0 `sorry`**; 361 `#print axioms` receipt commands. The corpus discipline is: never `axiom`/`sorry` — instead package unproven mathematics into **hypothesis-records** (structures whose fields are propositions) and conditional theorems.

**Unproven-assumption inventory (hypothesis-records and named premise-Props found in this batch):**

1. `HodgeBigradedBettiData` (GSTGeometricRealizationStage2G) — the master interface: assumes a full Hodge bigrading (`component`/`independent`/`spans`) per weight on the rational singular cohomology of an analytification, AND an arbitrary rational-linear `cycleClass` map. Not analytically constructed anywhere; the zero-cycle-class countermodel (GSTClassicalHodgeStage2GSemanticRigidity) shows the type is degenerate-compatible.
2. `ResolvedSupportGysin` (GSTUniversalResolvedSupportHodge) — assumes `rationalHodgeLift` (Gysin strictness/surjectivity onto supported Hodge classes) + `cycleClass_gysin` (naturality).
3. `AffineCodimensionTwoLocalization` / `AffineSuccessorHodgeLocalization` (same file) — assume localization exactness and boundary Hodge-lift through the Gysin push.
4. `GeometricHigherLefschetzData` (GSTUniversalCodimensionTwoPrimitiveExtraction) — assumes `hardLefschetz : Function.Surjective cupH2` (Hard Lefschetz), plus compatibility/naturality fields; reused in GSTK3DirectGraphOrbitDifference.
5. `DivisorsRepresentHodge11` (imported, used in files 1 and 26) — Lefschetz (1,1) as an interface; not constructed in this batch.
6. `GeometricGSTPlaneCompleteness` (GSTClassicalHodgeOmniversalNativeOrbitSeparation) — "every Hodge basis sheet is the output of one graded geometric program"; proven ⇔ orbit cyclicity ⇔ pairing totality, and ⇒ full Stage-2G Hodge + Clay forms.
7. `GradedOntologicalFan` (GSTClassicalHodgeGradedOntologicalFanFinale) — vertical `SeedPropagationFamily` + per-weight `RootedStrictRelationFan`; ⇒ `EveryHodgeClassIsRationalAlgebraic`.
8. `SourceTargetCorrespondenceExpressions` + `StrictlyMaterializedBranch` premises (GSTClassicalHodgeHandwrittenPiCorrespondenceProgramLanding) — realized correspondence expressions hitting every basis sheet from one derived source.
9. `GradedProgramSpectralFamily` / `FiniteGradedProgramSpectralCover` (GSTClassicalHodgeGradedProgramSpectralSaturation) — a diagonalizing program with distinct rational eigenvalues + orbit visibility/cover per class.
10. `IsCyclicAlgebraicSeed` (GSTClassicalHodgeCyclicRealizedCorrespondenceAttack) and `SeedCyclicForActualGeometry` (GSTResearchLocalCyclicityHodge) — cyclicity of an algebraic seed under actual correspondence words, per weight.
11. `ActualHodgeCorrespondenceIrreducible` (imported, used in GSTResearchGeometricOrbitSynthesis) — irreducibility of the correspondence action; the file states this "would include the central unresolved algebraicity problem".
12. `PrincipalCutKernelRealization` / `KernelReducedGeometricCycleClassSpine` (GSTClassicalHodgeGeometricSpineKernelReduction) — kernel stability + Hodge preservation of the principal-cut operator; pushforward kernel stability; `algebraic_is_hodge`.
13. `BoundedGeometricDegreeCharge` (GSTResearchFiniteWeightGeometricDegree) — degree/cycle-class compatibility, nonzero base degree, successor degree transport.
14. `NativePointSuccessorNonvanishing` (GSTClassicalHodgeCodimensionPointTower) — uniform principal-cut survival ("a hypothesis; induction does not prove it", verbatim).
15. `SameWeightGSTStable` / `DegreeCertifiedGSTProgram` (GSTClassicalHodgeGSTDegreeCertifiedSource) — GST-sheet stability of the algebraic Chow address span; synchronized source-target programs.
16. Imported interface/hypothesis records consumed throughout: `ProjectiveDegreeTraceSemantics`, `GeometricPushforwardNaturality`, `RationalBettiIntersectionPrimitives`, `MiddleBettiCorrespondenceKernel`, `SpineTowerConservedCharge`, `NativeMassCycleClassBridge`, `BasisAtomicSeparator`, `MinimalGhostLocalSeed`, `SeedPropagationFamily` (defined in other batches).
17. Theorem-level premise families flagged as Hodge-equivalent by the circularity audits: `TwoGeneratorNative`, `TwoPrimitivePointTransitions`, `HasNativePointLifts` (for bare L²), ghost-adaptive plane packages — all proven ⇔ the Hodge conclusion, hence barred as premises (GSTClassicalHodgePlanePrimitiveCircularity, GSTClassicalHodgeBareLefschetzNonCircularity, GSTClassicalHodgePlaneGroundPoint).

**The 5 most load-bearing files:**
1. **GSTUniversalResolvedSupportHodge.lean** (2993 lines) — the Gate 3 engine: the resolved-support/affine-localization hypothesis-records are the exact form in which the missing universal source-production is stored; also the largest body of verified projector/Koszul/Chern algebra feeding all later "source" claims.
2. **GSTGeometricRealizationStage2G.lean** — defines `HodgeBigrading`, `rationalHodgeSubspace`, `HodgeBigradedBettiData` and the target `BigradedBettiHodgeStatement`; every classical-Hodge file in the batch is typed over this unproven interface.
3. **GSTClassicalHodgeOmniversalNativeOrbitSeparation.lean** — proves the three-way completeness equivalence and the implication (completeness ⇒ Hodge ⇒ Clay forms), i.e., the single named hypothesis (`GeometricGSTPlaneCompleteness`) that carries the whole program, plus the weak-spine no-go that blocks fake derivations of it.
4. **GSTClassicalHodgeGradedOntologicalFanFinale.lean** — the most "final-looking" conditional landing: one fan record ⇒ `EveryHodgeClassIsRationalAlgebraic`; it packages the entire remaining burden into two existence fields.
5. **GSTClayOfficial.lean** — the official-Clay-worded headline; proving those words only inside the finite 12-cell wave model, it defines the name-vs-content ceiling of the campaign (its own audit note admits this).

**The single biggest gap.** No unconditional mathematics toward the Hodge conjecture exists in this batch: every "Hodge" theorem is of the form *(unproven hypothesis-record) ⇒ BigradedBettiHodgeStatement*, and the two semantic-rigidity/firewall files prove inside Lean that the underlying interfaces (`HodgeBigradedBettiData` with arbitrary cycleClass; `RealizedFiniteClosedCorrespondence` with unpinned off-image action) admit degenerate countermodels. Concretely: there is no analytic construction of a Hodge bigrading, no geometric construction of a genuine cycle-class map, no instance of any completeness/cyclicity/irreducibility premise, and no Hard Lefschetz / Lefschetz (1,1) theorem — while `GSTClayOfficial.clay_hodge_conjecture`, the file named after the prize problem, is a statement about a 4×3 lattice of twelve cells. The gap between the campaign's names and its verified content is the batch's defining feature; the honest content is: genuine scheme-theoretic constructions (graphs, diagonals, finite correspondences, point closures, Krull PIT, fundamental cycles), genuine linear-algebra reductions and circularity audits, a large volume of verified arithmetic (lattice "worlds", base-3/4 digit laws), and a fully conditional Hodge-implication network awaiting a single real instance.
