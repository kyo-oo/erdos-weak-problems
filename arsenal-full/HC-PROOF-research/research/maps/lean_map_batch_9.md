# LEAN BATCH 9 MAP (Task 1-j)

Repo: /tmp/hc-clone-23 @ 6c20bb7, branch research/gpt6-native-point-primitive-span-20261017.
Files: 71, total 19,361 LOC. Totals: 700 `theorem`, 166 `def`, ~41 real `structure` declarations, **0 `axiom`, 0 `opaque`, 0 `sorry`, 0 `native_decide`** (the single textual "sorry" hit is inside a docstring of GSTPairChannelWallsCertificate asserting its absence). Every file carries `#print axioms` receipts for its main results (about 270 receipt lines total). All files raise `set_option maxHeartbeats`/`maxRecDepth` (1e6 up to 2.6e8).

Batch-wide finding: this branch NEVER smuggles mathematics in as `axiom` or `sorry`. The unproven content lives entirely in **hypothesis-records (structures whose fields are unproven mathematical propositions, taken as theorem parameters)** and in **supplied semantic data** (fields of `BettiHodgeData` etc.). The crowns are honest conditionals: "IF a record with field X is inhabited THEN the Hodge statement holds". Below, "hypotheses" quotes those fields.

---

### GSTLefschetzCrown.lean (1413 lines)
- decls: 59 theorems, 18 defs, 0 structures (2 docstring lines matched), 0 axioms, 0 sorry
- hypotheses: none (self-contained finite model). Imports GSTCanonicalSevenAxisBridge + waves.GSTWaveCohomology (outside batch).
- main content: Full "absorption" of the classical Lefschetz arsenal for the **12-cell finite lattice** `WaveCoef` (functions on 12 cells, i.e. Z^12): `divisor_generation` (every wave = sum coeff*cellClass -- plain basis decomposition), Hard-Lefschetz injectivity/surjectivity with explicit sections for the index-shift operators cupDigit/cupCarry, `L^6=0`, unimodular Poincare pairing (Kronecker complement), `kunneth_projector_polynomial` (sector projectors are integer polynomials in the degree operator), `hodge_locus_residue_algebraic` (hodgeLocus at height p is a union of residue classes mod 3^(p+1) -- trivial since digit3/carry4 depend only on residues). `the_lefschetz_crown` packs all five.
- name-vs-content: announces "the full Hodge conjecture of the absorbed world", "standard conjecture as a theorem", "Cattani-Deligne-Kaplan absorbed" -- actual content is exact finite combinatorics on a rank-12 free abelian group with cup operators defined as index shifts.
- gaps: no connection to actual algebraic varieties, Chow rings, or analytic Hodge theory; the "dictionary" (classical theorem -> 12-cell statement) is narrative only.

### GSTWorldtraceArithmetic.lean (1347 lines)
- decls: 52 theorems, 1 def, 0 structures, 0 axioms, 0 sorry
- hypotheses: none.
- main content: exact modular arithmetic of ternary digits of 4^K: binomial expansion 4^(1+3m)=4*64^m, "blades" (quadratic mod 729, cubic mod 6561, quartic mod 19683 congruences), kill sets (explicit 32/64-element residue lists mod 2187/6561 forcing digit3(4^K)7=2 / =8), survivor maps for `CantorianPower` (level 6: 64 survivors mod 2187; level 7: 128 survivors mod 6561), pair-read fire formulas, top-split/window descent lemmas, `worldtraceWindowClass` filtration laws. Receipts `the_worldtrace_receipt` / `_seven` are giant explicit residue tables.
- name-vs-content: "the boss's transformation, landed" -- correct kernel-proven arithmetic, but the "GAP-A2 transformation" is 3-adic digit analysis of powers of 4, not Hodge-adjacent geometry.
- gaps: the underlying Collatz-adjacent target (noTernaryTwo(4^K), CantorianPower tree) is pursued via ever-deeper residue cascades; no closing argument (survivors keep doubling 32->64->128...).

### GSTPrimitiveProductTowerStabilization.lean (971 lines)
- decls: 41 theorems, 21 defs, 1 structure (`EllipticPairNativeDivisor` -- pure Q^3 data: left/right/diagonal coordinates; NOT a hypothesis-record), 0 axioms, 0 sorry
- hypotheses: none as assumptions. `EllipticPairNativeDivisor` fields are just `left right diagonal : Q`.
- main content: (i) universal commutative-ring identities: `primitive_source_binomial_collapse` ((Lx+h)^k*z = h^k*z when Lx*z=0), `unseeded_two_polarization_factorization` ((u+v)*P_m = u^(m+1) - (-v)^(m+1)), rank/self-intersection formulas; (ii) explicit Q-coordinate intersection tables for divisor classes on E x E (Koszul P = x1-x2, graph D = delta-x1-x2; primitive w.r.t. h=x1+x2; Gram = diag(2,2); tensor products give 2^m orthogonal primitive sources of energy 2^m); (iii) arbitrary-genus curve-pair versions, K0/Todd normalization, tautological vs internal-graph period separation.
- name-vs-content: "primitive algebraic product stabilization in every dimension" -- proven content is ring identities + norm_num-checked 3x3 divisor coordinate algebra; the geometric instantiation on X=E^(2m) is narrative ("this is a source family on a substantial variety class, not arbitrary-X Hodge algebraicity" -- honest).
- gaps: no Lean-side scheme/Chow instantiation; cycle-class/GRR comparison "is the geometric specialization" outside the file.

### GSTClassicalHodgeGeometryFirstGlobalPropagation.lean (704 lines)
- decls: 23 theorems, 0 defs, 4 structures, 0 axioms, 0 sorry
- hypotheses (load-bearing, quoted):
  - `GeometryFirstLefschetzStep.transport_formula`: `cohomologyOperator source.1 = limitlessLefschetzScalar p q * target.1` (plus `cycleClass_natural`, nonzero source/target Hodge fibers) -- i.e. one assumed Lefschetz transport step between Hodge fibers.
  - `GeometryFirstSeedPropagation`: `seed : forall p, ClassicalHodgeFiber V H p`, `seed_ne_zero`, `step : forall p : Nat, GeometryFirstLefschetzStep V H p (p+1)` -- a transport step at EVERY weight with nonzero seed.
  - `GeometryFirstGlobalPropagation.fixedWeight`: `forall p, forall i j, GeometryFirstTwoGenerator (V:=V) (H:=H) i j` -- two-generator saturation for every Hodge-basis pair in every weight.
  - `GeometryFirstLivePathCosmos.livePath`: every live weight-p fiber is reached by a finite `GeometryFirstNativePath` from a weight-zero `NativePointHodgeSeed`.
- main content: given those records, algebraicity propagates: `target_mem_algebraic_of_source`, `geometryFirstNativePath_constructs_target` (inductive construction of target cycles along paths), culminating in `bigradedBettiHodge` (the Stage-2G Hodge statement) and `every_hodge_class_has_native_cycle` for the Global-Propagation record.
- name-vs-content: "global propagation" is real logic, but all propagation steps are inputs, not conclusions.
- gaps: inhabitation of every one of these records is open; also relies on imported `smoothProjective_cycleClass_range_eq_atomic_span`.

### GSTClassicalHodgePointClosureRelativeCut.lean (584 lines)
- decls: 21 theorems, 1 def, 0 structures, 0 axioms, 0 sorry
- hypotheses: none (genuine Mathlib scheme topology).
- main content: for `V : SmoothProjectiveComplexScheme`, the relative principal cut of the reduced closure of a point is closed and proper; the coheight-one locus of the cut is finite (`finite_relative_coheight_one`, via Noetherian-space combinatorics); target-directed cuts from strict specialization of homogeneous prime ideals; every relative coheight-one point has a directed-cut component; `every_ambient_successor_point_has_directed_cut_component` and `every_ambient_point_has_exact_coheight_flag` (exact flags of length = coheight).
- name-vs-content: matches content -- honest scheme-level topology.
- gaps: "No assertion that this is an effective Cartier divisor is needed or made. No Hodge data, cycle-class map, or Hodge-direction preimage enters the cut" -- i.e. pure Krull-dimension infrastructure for the cut spine.

### GSTPairChannelWallsCertificate.lean (547 lines)
- decls: 20 theorems, 32 defs, 1 structure (`ChPair` -- pure data: r, g1..g4 coefficient lists), 0 axioms, 0 sorry (docstring asserts none)
- hypotheses: none as axioms; "universal table laws in hypothesis form" are trivial Q-implications (e.g. `pair_charge_split_universal (m iWR2 qP qM : Q) (hi : iWR2 = 8) (hp : qP - qM = -m*iWR2) : qP - qM = -8*m`).
- main content: bitmask exterior-algebra model of the "discriminator's" rational cohomology ring on a Weil fourfold: kernel-decided integer certificates for W0 annihilation (theta^j wedge W = 0, j=1,2,3), period constants (theta^4=24, W_R^2=W_I^2=8, W_R*W_I=0, Omega OmegaBar=16), Fourier-Mukai normalization fm(W_R)=W_R, fm(W_I)=W_I with identity round-trips, and the W6 pair Chern table on 6 synthetic instances (grade purity, charge split -8m, 24-scaled mixed-End identities, carrier q=0 slice, detector).
- name-vs-content: "certificate" is accurate -- explicit scope box: "This certificate DETERMINES NO BIT: no decision of S = 0 versus S = W_Q ... the dichotomy bit remains the campaign's forcing vertex."
- gaps: scheme-level leaves explicitly NOT certified here: HRR, Chern-character multiplicativity, GAGA, Serre duality, derived FM toolkit (E13 Phi-hat Phi ~ (-1)*[-8]), dual-world axioms, K^0 presentation, pair-form equivalence (W2), integrality of Weil charges.

### GSTWorldCosmology.lean (479 lines)
- decls: 25 theorems, 18 defs, 1 structure (`CosmicObservations` -- data + coherence law `restrictWindow hA hB (window C D) = window A B`, not an unproven math proposition), 0 axioms, 0 sorry
- hypotheses: none.
- main content: dimension-free Z-valued carrier on NxN: finite windows WorldCoef A B, observe/extendWindow/restrictWindow exactness, `observations_separate`, CompletedCosmos = CosmicObservations (`cosmicObservationEquiv`), compact (finite support) vs completed fields separated (`constant_one_not_compact`), shift operators digitShiftN/carryShiftN with additivity, axis commutation, boundary extinction, the 12-cell model as one exact chart (`twelve_cell_is_native_chart`), translation embedding.
- name-vs-content: "WORLD COSMOLOGY" is grandiose for functions NxN -> Z with window bookkeeping, but content is honest.
- gaps: no geometric interpretation assumed or built (by design -- "No geometric interpretation is assumed").

### GSTClassicalHodgePlaneSemanticIndependence.lean (456 lines)
- decls: 13 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none -- this is a **countermodel/independence theorem**.
- main content: replace the Stage-2G cycle-class map by zero (`zeroCycleClassData`), keeping analytification and Hodge bigrading. Then the full intrinsic GST plane completeness survives (`zeroCycleClass_full_GST_plane`) while the Hodge landing fails (`zeroCycleClass_plane_complete_and_hodge_false`), and native-plane completion fails. Therefore no intrinsic-plane theorem can imply the geometric Hodge statement; likewise for full-correspondence plane, native orbit pairing totality, geometric program plane, reduced core -> native executable plane (`no_bareStage2G_plane_to_hodge_implication` etc.).
- name-vs-content: accurate and valuable -- a real separation result inside the GST universe.
- gaps: it rules out whole proof routes; it does not advance the positive program.

### GSTClassicalHodgeGradedGeometricProgramOrbit.lean (411 lines)
- decls: 12 theorems, 2 defs, 0 structures (inductive `GradedGeometricProgram`), 0 axioms, 0 sorry
- hypotheses: `GradedGeometricOrbitCyclic G : Prop := forall q, rationalHodgeSubspace (H.hodgeBigrading q) <= geometricProgramOrbitSubspace G q` -- the **compressed open reachability statement** (taken as parameter `hcyclic`).
- main content: noncommutative program algebra (id, projective words, principal cut, +, scalar, composition) with cycle-class-naturality invariant proven by induction (`GradedGeometricProgram.cycleClass_cycleEval`); orbit lies in cycle-class range and in Hodge sector; `bigradedBettiHodge_of_gradedGeometricOrbitCyclic`; old normalized spine compiles into the new orbit (`normalizedSpineProgram`).
- name-vs-content: "the whole Hodge problem is compressed to one pure reachability statement" -- stated honestly in the header.
- gaps: cyclicity (`GradedGeometricOrbitCyclic`) is not proven anywhere in this file; it is the load-bearing hypothesis.

### GSTClassicalHodgeNativePointRelationDescent.lean (394 lines)
- decls: 13 theorems, 9 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: `NativeClassKernelStable cl A : forall Z, cl Z = 0 -> cl (A Z) = 0` (kernel preservation -- a defined Prop, always an explicit hypothesis of the descent theorems); `PreservesFiniteClassRelations` (equivalent form).
- main content: linear algebra of descending an endomorphism along `LinearMap.range cl`: well-defined `nativeClassRangeAction`/`nativeClassRangeEnd`, naturality forced on the geometric image, composition law, retraction criteria, `exists_nativeAmbientAction_iff`, derivation of `PointClassTransitionKernel` from a raw native operator (`rawTransition_has_ambientAction_iff`, `derivedPointClassTransitionKernel`).
- name-vs-content: accurate -- "native-first finite-relation descent" is exactly what is proven.
- gaps: ambient extension uniqueness only on the actual cycle-class range ("no uniqueness claim outside it").

### GSTClassicalHodgePiPointRationalCorrespondenceUnboundedFinale.lean (383 lines)
- decls: 7 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses (crown inputs, quoted): `hpoint : forall p, rationalHodgeSubspace ... != bot -> Nonempty (CodimensionPoint V.X p)`; `A : forall p hp j, RationalClosedCorrespondenceCycle V`; `hT : ... K.RealizesAmbientOnPoints (T p hp j K)`; and the load-bearing `hA : (rationalPair (A p hp j) ...).cohomologyOperator (pointHodgeSource G p x).1 = (classicalHodgeBasis V H p).repr (pointHodgeSource G p x) (pointSourceIndex G D p x) * (classicalHodgeBasis V H p j).1` for EVERY j -- i.e. **the correspondence action performs the rank-one matrix-unit hit on every basis vector**.
- main content: under hA, normalized native images give basis cycles (`pointTargetCycleOfRationalCorrespondence_spec`), the collapse cycle represents any Hodge class (`correspondenceCollapseCycle_spec`), hence `bigradedBettiHodge_of_point_rationalCorrespondence_omniverse` and the Clay finite-sum form.
- name-vs-content: "UnboundedFinale" suggests closure; it is another conditional whose premise (hA) is essentially the algebraicity of all matrix units on the Hodge fiber.
- gaps: no construction of the correspondences A or the realizing operators T; hA is exactly the unproven "GST source hit".

### GSTClassicalHodgeOmniversalConstructorGraph.lean (353 lines)
- decls: 11 theorems, 6 defs, 0 structures (two inductives `ConstructorNode`, `ConstructorEvent`), 0 axioms, 0 sorry
- hypotheses: none -- events are constructive; the `cycleHodge` event requires a *proof* that the class is Hodge.
- main content: a typed event graph over real geometry (point -> codim point -> cycle -> Betti -> Hodge, principal cut, projective pushforward). Key theorem `hodge_constructorClosure_iff_genuine_native_representation`: reaching a Hodge state from a native cycle seed iff existence of a native representative; `constructorCompleteClosure_iff_exactHodge`: total event reachability iff the literal Hodge statement ("completeness firewall": "This theorem is NOT used as a new Hodge premise").
- name-vs-content: accurate and epistemically clean ("No event sends an arbitrary Hodge class to a cycle. Therefore total Hodge reachability remains a real theorem to be proved, not an encoded assumption").
- gaps: nothing proven toward inhabiting the closure; it is a classification/firewall.

### GSTGraphV2SixAdicOntologicalGeometryLaws.lean (344 lines)
- decls: 31 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none.
- main content: elementary laws of the base-6 congruence `SixAdicIsoAt k x y := exists q, x - y = 6^k*q`: reflexivity/symmetry/transitivity, translation/negation/scaling, `six_iso_scale_six`, weakening, nested balls, six-way refinement centers, dyadic/triadic shadows, compatibility with the seven-axis ontology and the x4 chart.
- name-vs-content: "Ontological Geometry Laws" is inflated; content is exact integer congruence algebra.
- gaps: "No analytic completion is assumed: all statements are finite, exact" -- no 6-adic topology.

### GSTGeometricRealizationStage2F.lean (338 lines)
- decls: 10 theorems, 3 defs, 2 structures, 0 axioms, 0 sorry
- hypotheses (the **supplied semantic data**, quoted): `BettiHodgeData` fields `hodgePP : forall p, Submodule Q (RationalSingularCohomology analytification (2*p))` (the rational (p,p) Hodge subspace -- supplied, not constructed) and `cycleClass : forall p, codimensionCycles V.X p ->_L[Q] RationalSingularCohomology analytification (2*p)` (the genuine cycle-class map -- supplied). `AnalytificationData` = a TopCat with `pointsEquiv : ComplexPoint V =~ space`.
- main content: the Betti carrier is made non-arbitrary: Mathlib's singular chain complex of the analytification, its Q-dual cochain complex, homology objects; `BettiHodgeStatement V H := forall p, H.hodgePP p <= LinearMap.range (H.cycleClass p)` -- the working Hodge-conjecture statement of the whole ClassicalHodge family; equivalence with the Stage-2E target; realization certificates.
- name-vs-content: accurate: "The two remaining fields are exactly the still-missing classical geometry: the rational (p,p) subspace and the genuine cycle-class map. No surjectivity/algebraicity assumption is included."
- gaps: analytification topology, Hodge bigrading, and cycle-class map remain supplied data throughout the family (the actual classical input).

### GSTClassicalHodgeStrictCorrespondenceChainTransfer.lean (323 lines)
- decls: 5 theorems, 0 defs, 2 structures, 0 axioms, 0 sorry
- hypotheses: `RightFiniteChainTransfer` fields: `transfer`, `degree != 0`, and `transfer_right : transfer >> rightChainMap A K = degree * 1` (an honest finite-degree transfer; constructible from a section via `ofRightSection`); `BiFiniteChainTransfer` (both legs).
- main content: chain-level transfer descent: normalize to a section, dualize to a cochain trace, functoriality gives `cohomologyTrace_rightPullback` (trace after rightPullback = degree * id), `toRightFiniteBettiTrace`, `pushPull`, graph-transpose chain transfer.
- name-vs-content: accurate module/homological bookkeeping over Mathlib singular chains.
- gaps: the transfer records themselves are inputs (constructible only when the analytic right leg splits).

### GSTClassicalHodgeProjectiveTwoGeneratorExternalization.lean (317 lines)
- decls: 9 theorems, 0 defs, 2 structures, 0 axioms, 0 sorry
- hypotheses (quoted): `ProjectivePrimitiveRealization` for an operator T: `map : V.X -> V.X`, `naturality : GeometricPushforwardNaturality V H p map`, and `restricts_to_hodge : forall alpha, naturality.cohomologyPushforward alpha.1 = (T alpha).1` -- **an actual projective self-map whose Betti action restricts to a prescribed Hodge-fiber operator**. `ProjectiveTwoGenerator` = two such realizations (for `twoSlotCodeHodge i j` and `twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2)`).
- main content: given realizations, `normalized_word_on_hodge` (the word acts as the matrix unit i->j on every Hodge state), and crowns: `bigradedBettiHodge_of_projective_limitless_arsenal` (needs `ProjectiveTowerHodgeIntertwining` + two-generators for every p,j), conserved-spine and native-mass variants requiring only one live source per weight.
- name-vs-content: "Externalization" = converting assumed cohomological generators into assumed projective ones; the geometry is still an input.
- gaps: existence of such projective endomorphisms realizing matrix units is untouched (a standard-conjecture-grade input).

### GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy.lean (305 lines)
- decls: 11 theorems, 1 def, 1 structure, 0 axioms, 0 sorry
- hypotheses: `LimitlessCosmicEscape` is a witness-definition (source/target/alpha + `escapes : liftCosmicWindowOperator ... alpha notin AlgebraicFiber`), i.e. failure data, not an assumed truth.
- main content: embedding finite rational pure-Hodge windows into Nat ->_0 Q with exact readback (`readWindow_embedWindow`), intertwining finite matrix units with limitless cosmic matrix units, reformulating the concrete two-slot failure as a limitless cosmic escape (`TwoSlotEscape.toLimitlessCosmicEscape`), and dichotomies: `proper_algebraicFiber_zero_or_limitlessCosmicEscape`, `algebraicFiber_eq_top_of_seed_and_limitlessCosmicStable`.
- name-vs-content: accurate reframing file.
- gaps: none of the disjuncts is discharged -- the escape/or-stability dichotomy is the open vertex.

### GSTClassicalHodgeHandwrittenPiEquationDerivation.lean (301 lines)
- decls: 9 theorems, 2 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: `LiveLocalizedL2BranchesLandInOrbit G alpha : Prop` (exists live source i with forall j in supp, the localized normalized-L2 branch lies in `geometricProgramOrbitModule G p`) and its global form `HandwrittenPiGeometricLanding`.
- main content: `localizedNormalizedL2_eq_hodgeMatrixUnit` (the branch operator E_ij IS the matrix unit -- imported rank-free result), `branch_collapse_localizedL2_at` (alpha = sum_j (alpha_j/c) * E_ij alpha over a chosen live coordinate -- exact basis algebra), omniverse reachability of branches, and the landing: branches-in-orbit => alpha in orbit => native cycle => `bigradedBettiHodge_of_handwritten_pi_geometric_landing`.
- name-vs-content: "derivation" is honest: the two-page handwritten route, with the one geometric equation isolated as `HandwrittenPiGeometricLanding`.
- gaps: `HandwrittenPiGeometricLanding` (every live branch lands in the orbit) is open.

### GSTClassicalHodgeLefschetzTomography.lean (294 lines)
- decls: 11 theorems, 3 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none.
- main content: finite "tomography": `multiplicityLefschetzKernel i j = choose(2(j-i), j-i)` for i <= j else 0 (central binomials), identified with the GST world action `worldAct` on pure diagonal states; the transform is unit-triangular (`lefschetzTomography_triangular`), injective, moments determine coordinates; nonzero vectors have nonzero moments.
- name-vs-content: accurate finite Q linear algebra over the GST world model.
- gaps: kernel identification relies on imported `pure_diagonal_lefschetz_forward_exact` (GST world calculus, not classical geometry).

### InformationDescentScratch.lean (284 lines)
- decls: 18 theorems, 4 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none ("only exact arithmetic mechanics; no universal Erdos claim").
- main content: exact ternary carry/digit recurrences for the GST step arithmetic (`gstCarryS_forward_exact_all` including the p=0 seam), NULL/GST+ regeneration laws, affine carry semigroup law, digit reindexing, child-carry seeding, affine block memory invariant, conserved shared-information carry equation, multiplier bounds, GST quarter geometry and the 22-synchronizer.
- name-vs-content: "Scratch" is accurate -- kernel-check arithmetic for the information-descent surgery.
- gaps: nothing universal; no Erdos claim (explicitly disclaimed).

### GSTGraphV2CanonicalDescentOntology.lean (276 lines)
- decls: 14 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none.
- main content: exact 3-adic/4-power arithmetic of the canonical descent tree: `canonicalEnergy_cut_decomposition` (prefix 1 at the production cut), right-edge cut decomposition with exposed descent, seed-one parent carry (`canonical_right_low_prefix_seed_one`: 4(1+3^(s+1))/3^(s+2) = 1 for s >= 1), child carry zero at the cut, child tail = next-scale canonical tail, canonical descent graph laws.
- name-vs-content: "Ontology" inflated; content is verified Nat arithmetic of exponent prefixes.
- gaps: part of the Collatz-adjacent four-power program; no termination/descent closure.

### GSTClassicalHodgeStrictCorrespondenceGeometricTransferFinale.lean (271 lines)
- decls: 7 theorems, 0 defs, 2 structures, 0 axioms, 0 sorry
- hypotheses (quoted): `GeometricPointFiberLaw` fields -- `kernel_cup_pointFundamental : forall x, P.cup (2*d) (2*p) kappa.kernelClass (fstCohomologyPullback ... (pt x)) = fiberIntersectionClass x` and `gysin_fiberIntersection : forall x, P.sndGysin (2*p) (fiberIntersectionClass x) = GeometricCycleClass pt (...nativePointImage p x)` -- **the cup-with-kernel = fiber-intersection-class and Gysin-pushforward = incidence-cycle-class laws** (the intersection-theory calculation). `BiGeometricPointFiberLaw` adds the transpose law.
- main content: given the fiber law, `geometric_action_on_point` (kernel action on point classes = geometric class of the incidence image), point-naturality of the geometrically generated cycle class, `supplied_cycleClass_eq_geometric` / `supplied_cycleClass_nativeOperator` (the Stage-2G supplied map identified with the constructed one by point rigidity -- "the final commuting square is a theorem, not a field"), forward+transpose transfer, factor-swap incidence.
- name-vs-content: "Finale" = removing a circularity in interface order, not proving the fiber law.
- gaps: `GeometricPointFiberLaw`/`BiGeometricPointFiberLaw` (the actual cup/Gysin/projection calculation) are unproven geometric inputs.

### GSTClassicalHodgeOmniversalFailurePacket.lean (265 lines)
- decls: 8 theorems, 1 def, 0 structures, 0 axioms, 0 sorry
- hypotheses: none (structural propagation of a hypothetical failure witness).
- main content: a nonzero integral pure square keeps: nonzero rationalized diagonal, nonzero tomography moments, truncated cohomology-ring realization of coefficients, projector/Lefschetz/Poincare orbit to every sheet, nonzero limitless-cosmos embedding, identification of total-sheet transfers with cosmic matrix-unit shadows -- "a classical failure cannot hide in an abstract separator".
- name-vs-content: accurate packaging of the failure dichotomy across the model worlds.
- gaps: propagation only; the failure is not excluded.

### GSTClassicalHodgeFiberedNativeSpectralProjectors.lean (260 lines)
- decls: 9 theorems, 1 def, 0 structures, 0 axioms, 0 sorry
- hypotheses: none.
- main content: invariant-code projectors on shaped fields: `fiberedNativeCodeProj` natural under recoordination (`transportFiberedNative_codeProj`), isolation of single shaped states, summing the isolated field, three-face agreement (classical = live coefficient x Hodge sheet; native = x point cycle; limitless = x transfer generator).
- name-vs-content: "Spectral Projectors" = code-keyed indicator projectors in the GST shape language; content matches.
- gaps: purely internal GST bookkeeping; no spectral theory of operators.

### GSTHodgeChannelFiniteBasis.lean (255 lines)
- decls: 7 theorems, 1 def, 3 real structures, 0 axioms, 0 sorry
- hypotheses (quoted): `FiniteBasisAlgebraization.basisCycle_class : forall i, cycleClass (basisCycle i) = (basis i).1` -- **each Hodge basis vector is assumed to be the cycle class of an actual cycle**; `Stage2GFiniteBasisAlgebraization` same at scheme level; `CanonicalBasisCycleSupply.basisCycle_class` for Mathlib's finBasis. Also the declared open Prop `Stage2GFiniteBasisAlgebraizationObligation := forall p, Nonempty (Stage2GFiniteBasisAlgebraization V H p)`.
- main content: from basis algebraization, channel quotients are canonical (`toChannelQuotient`), `finite_basis_hodge_le_cycleClass_range`, constructive cycle witnesses, and `bigraded_betti_hodge_of_finite_basis_obligation`.
- name-vs-content: honest: "the only algebraic input that remains is one codimension-p cycle whose cycle class equals each basis vector" -- the input is the Hodge conjecture on a basis.
- gaps: the obligation (basis cycles per p) is exactly the reduced open problem; also finiteness of Hodge sectors is used via chosen bases.

### GSTClassicalHodgeHandwrittenPiExplicitNativeCollapse.lean (248 lines)
- decls: 7 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: `SourceTargetCorrespondenceExpressions G P0 hne` (imported record supplying realized correspondence programs hitting every basis sheet) with nonzero origin program value.
- main content: `targetBasisCycle` = normalized native execution of the program on the codimension-zero fundamental cycle, `targetBasisCycle_spec` (its class IS the basis vector e_j), branch cycles B_ij(alpha) = alpha_i * Z_j with class exactly the localized L2 branch, and the final collapse `Z_alpha = sum_j (alpha_j/alpha_i) * B_ij` with cl(Z_alpha) = alpha.
- name-vs-content: the "explicit native collapse" is real linear algebra once the expression family is given.
- gaps: the geometric input is the imported realized-correspondence expression family (not constructed here).

### GSTClassicalHodgeCycleLanding.lean (247 lines)
- decls: 8 theorems, 1 def, 1 real structure, 0 axioms, 0 sorry
- hypotheses (quoted): `FiberedBasisCycleBridge.basisCycle_spec : forall i, H.cycleClass p (basisCycle i) = (classicalHodgeBasis V H p i).1` -- "the irreducible classical geometric datum after the limitless GST coordinate side has been constructed".
- main content: linear lift of basis cycles to every Hodge class (`fiberedBasisCycleLift_spec`), `hodge_class_has_cycle_of_fibered_basis_bridge`, `bigraded_hodge_of_fibered_basis_cycle_family` (bridge per p => Stage-2G Hodge), and the reverse extraction showing the bridge is equivalent to the target.
- name-vs-content: accurate; "No cycle-class surjectivity, Hodge conclusion, realization obligation, or custom mathematical axiom is assumed below."
- gaps: inhabitation of the bridge family = the Hodge conjecture itself (by the reverse direction).

### GSTFourPowerThirdWave.lean (240 lines)
- decls: 10 theorems, 3 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none; the open boundary is DOCUMENTED, not asserted: "Closing the final step -- that no natural exponent K >= 8 follows a gate-dodging walk forever -- is the open boundary ... deliberately NOT asserted here."
- main content: band reformulation of the four-power direct-existence law: multiplication-by-4 row carry laws (`digit3_four_mul_of_lt/ge`), gate predicate `thirdWave` (digit two + outer quarter band), and the unconditional EQUIVALENCE of the direct existence law with "every K >= 5, K != 7 has a firing gate row".
- name-vs-content: accurate; exemplary scope honesty (records the six-agent strike's unformalized results: trie bijection, growth rate ~2.48, exception set {0,...,4,7}).
- gaps: the gate-dodging-walk closure is open; research-record facts are outside Lean.

### GSTGraphV2CoupledUFlux.lean (232 lines)
- decls: 8 theorems, 11 defs, 1 structure (`State` -- pure data), 0 axioms, 0 sorry
- hypotheses: none ("Nothing terminates here. K is always an observation coordinate").
- main content: exact coupled U-flux identity `coupled_u_flux_step_exact`: parentJump - A*childJump = 3*delta-potential for the potential `charge(parentSeed) - A*charge(childCarry) + 24*parentOffset` -- a telescoping invariant identity for the GST carry dynamics; orbit versions and bounded-carry consequences.
- name-vs-content: accurate exact arithmetic; no termination claim.
- gaps: no universal claim (Erdos-type statements absent by design).

### GSTClassicalHodgePiStrictOmniverseCompiler.lean (231 lines)
- decls: 6 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: `StrictlyMaterializedBranch` (imported: branch materialized by actual bi-finite correspondence + cup/Gysin/incidence primitives) -- per-edge geometric input.
- main content: splice theorem `strictBranch_has_realizedExpression` (a strictly materialized branch supplies a `RealizedFiniteClosedCorrespondence` whose naturality was derived from the primitive packet, not assumed), hence the omniverse needs no separate `PrimitiveBranchCompiler`; chain into the handwritten Pi route (source -> branch -> correspondence -> program -> native target cycles -> collapse).
- name-vs-content: "Compiler" = interface-glue file; accurate.
- gaps: strict materialization of branches (the geometry) is imported and open.

### GSTClassicalHodgeOpenAIGeometricPeriodCertificates.lean (224 lines)
- decls: 7 theorems, 1 def, 2 structures, 0 axioms, 0 sorry
- hypotheses (quoted): `GeometricSourcePeriodCertificate` fields: `source : SmoothProjectiveComplexScheme`, `geometricTransfer : CrossCarrierTransfer ...`, `sourceNativeCycle`, `period : Q`, `nonzero_period : period != 0`, `exact_period_formula : geometricTransfer.betti ...` (transfer of the source cycle class = period * basis vector) -- a **per-sheet nonzero rational period identity**.
- main content: transfer outputs are always algebraic (`geometricTransferOutputSet_algebraic`), the output span lies in the cycle-class range; certificates + basis support construct target native cycles by rational normalization. Header: "The FINAL implication to the Hodge conjecture remains CONDITIONAL on real geometric certificates for every target sheet"; distinguishes itself from the OpenAI CM/Qbar period case ("not misrepresented as a full formalization of the Qbar/CM geometric case"). Flagged "NEEDS CI RUN LATER".
- name-vs-content: "OpenAI" names the upstream paper route; content is a conditional certificate algebra.
- gaps: no real certificates constructed; Qbar/CM descent indispensable upstream, absent here; CI status unverified.

### GSTClassicalHodgePiUnboundedOmniverseCrown.lean (221 lines)
- decls: 5 theorems, 2 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none (cosmos constructions trivially inhabited by PUnit states).
- main content: promotes the Hodge branch graph to a `SelfExpandingCosmos` and `HigherCausalCosmos` where worlds stay literally the same projective branch nodes at every causal dimension (`branchWorld_has_unbounded_higher_tower`), i.e. the unbounded GST tower expands around the fixed V,H,p.
- name-vs-content: "Unbounded Omniverse Crown" is structural bookkeeping (identity towers), not new mathematics.
- gaps: the heavy lifting (branch events, materialization) lives in imported files.

### GSTClassicalHodgeConcreteArsenalConjugation.lean (217 lines)
- decls: 7 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none.
- main content: injectivity of live-slot -> integral-square-sheet (`squareSheetOfLiveSlot_injective`), `readLiveSquare` readback, and the conjugation theorem identifying the rank-free `hodgeMatrixUnit` action with the concrete projector/Lefschetz/Poincare total-sheet matrix-unit word read through the genuine classical basis and divided by the denominator-clearing scale.
- name-vs-content: accurate coordinate-conjugation file ("the complete local matrix-unit pattern is ... the coordinate conjugate of the existing GST operator arsenal").
- gaps: internal to the GST/world model pair.

### GSTGraphV2InfiniteBigNDichotomyScratch.lean (211 lines)
- decls: 10 theorems, 1 def, 1 structure (`GSTInfiniteBridgePathS` : Prop-record with `bridge_step : forall j, gstBinaryBridgeOutputS (a j) (d j) = d (j+1)` -- a path hypothesis), 0 axioms, 0 sorry
- hypotheses: `GSTInfiniteBridgePathS` (an actual infinite bridge path -- input); the dichotomy theorems are elementary logic (`gst_infinite_bigN_or_notBig1S`).
- main content: first-BIG1 analysis: before the first `d N = 1` all digits are 2 (`gst_before_first_big1_all_big2S`) and edges survive with mass 5 / event 8; the BIG-N vs never-BIG1 dichotomy for infinite paths.
- name-vs-content: "Scratch" accurate; dichotomy is elementary logic applied to the bridge automaton.
- gaps: neither branch discharged; feeds the Erdos-ternary program.

### GSTClassicalHodgeOmniverseStrictRelationRayCompiler.lean (206 lines)
- decls: 7 theorems, 1 def, 1 structure, 0 axioms, 0 sorry
- hypotheses (quoted): `StrictRelationEdgePacket` fields: `correspondence : SchemeBiFiniteClosedCorrespondence V`, `trace : RightFiniteBettiTrace ...`, `pointCompatibility : PointCycleCompatibility ...`, `related : BettiRelated H.analytification correspondence (2*p) u.state.1 v.state.1` -- the **raw pullback relation** leftPullback(source) = rightPullback(target) per edge.
- main content: uniqueness `pushPull_eq_of_related` (nonzero right trace makes the target the push-pull of the source), compilation of a raw relation into a realized correspondence expression (`expression_materializes`), ray propagation of genuine algebraicity along strict-relation rays.
- name-vs-content: accurate; explicitly "does not assert that every causal edge already has such a strict relation ... constructing those geometric relations is the exact remaining edge-level burden".
- gaps: per-edge strict relations (the geometry) are the open burden.

### GSTClassicalHodgeDegreeCertifiedOmniverseCausalCompiler.lean (204 lines)
- decls: 2 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry (dense glue file)
- hypotheses: `ProjectivelyLiveSource` + exact coheight-stratum identity (for the successor seed), primitive realized-expression compiler (imported), plus G/D spine semantics.
- main content: the degree-certified live source index is an honest live support index; `degreeCertified_causal_event_to_target` fires the augmented GST causal event from the degree-certified source to any target basis direction; `degreeCertifiedProgramOfPrimitiveCompiler` turns a primitive realized-expression compiler into the full source-specific correspondence program.
- name-vs-content: "Causal Compiler" = glue between degree-certified sources and the correspondence program layer; accurate.
- gaps: materialization of primitive events (realized expressions per branch) remains imported/open.

### GSTClassicalHodgeGradedPointKernelLift.lean (200 lines)
- decls: 5 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses (quoted): `GradedPointClassTransitionKernel.transition_spec : forall x, (finitePointCycleClassMap q clQ) (transition x) = T (clP (codimensionPointCycle X p x))` -- the pointwise class formula.
- main content: free linear extension of point kernels (`presentationOperator`), `finitePointClass_natural` (intertwining by linearity), conjugation through cycle/presentation normal forms on compact carriers (`nativeCycleOperator`), naturality squares.
- name-vs-content: accurate module-level reduction ("a future projective hyperplane-section construction only has to prove its formula on genuine point generators").
- gaps: the pointwise formula itself is the input.

### GSTClassicalHodgeProjectiveCorrespondenceAlgebra.lean (198 lines)
- decls: 8 theorems, 1 def, 0 structures, 0 axioms, 0 sorry
- hypotheses: none.
- main content: the native operator sector generated by actual scheme endomorphisms: `geometricGenerator f = smoothProjectiveNativePushforward V f p`, its rational span `projectiveCorrespondenceSpan`, closure under +, scalar, finite sums, representation on finite point presentations.
- name-vs-content: accurate construction ("No cohomology action is assumed here").
- gaps: which cohomological operators are induced is deferred to the external-realization layer.

### GSTClassicalHodgeOneSidedFiniteCorrespondenceKrylovFinale.lean (196 lines)
- decls: 6 theorems, 1 def, 1 structure, 0 axioms, 0 sorry
- hypotheses (quoted): `OneSidedKrylovCertificate` fields: `correspondence : FiniteClosedCorrespondence V` (finite over SOURCE only), `cohomologyOperator`, `realizesOnPoints : correspondence.RealizesAmbientOnPoints (H:=H) cohomologyOperator`, `preservesHodge : forall alpha, cohomologyOperator alpha.1 in rationalHodgeSubspace (H.hodgeBigrading p)`, `seedCycle`, `seedHodge : H.cycleClass p seedCycle in rationalHodgeSubspace ...`.
- main content: Krylov orbit synchronization `nativeOrbit_cycleClass` (native iterate classes = cohomological iterates, by induction from pointwise naturality), and (with the imported cyclic criterion) cyclicity of the T-orbit of cl(Z) gives the weight-p Hodge range.
- name-vs-content: "Finale" = weakening the carrier requirement to one-sided finiteness; accurate.
- gaps: realizesOnPoints/preservesHodge/cyclicity all inputs.

### GSTFourPowerDirectExistenceFromHappy.lean (193 lines)
- decls: 6 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `DirectBadDossier K : Prop` -- a *derived* dossier (built FROM not-CommonTwo K), fields: exact exponent period law, mod-9/27/81 residue filters, `noSource22`, `sourceNo22MagnitudeBound : forall m, 4^K < 9^m -> 8*4^K <= 7*(9^m - 1)`, exponent-trit obstruction law, affine low-trit branch.
- main content: `noCommonTwo_builds_direct_bad_dossier` (not-CommonTwo K => the full simultaneous obstruction dossier), `happy_row_to_commonTwo` (a direct physical Happy row on 4^K is already a common-two row, via the exact x4 carry formula).
- name-vs-content: accurate: reducing the four-power direct existence law to the Happy/common-two interface.
- gaps: `CommonTwo`/`FourPowerDirectExistence` themselves unproven (the dossier is the contradiction target).

### GSTClassicalHodgeRankFreeLimitlessAssembly.lean (190 lines)
- decls: 8 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: `hcert : forall i, Nonempty (BasisProjectorCertificate V H p i)` (imported per-sheet projector certificate -- assumed input).
- main content: removes the Nat-chart: `genuineHodgeAddress` = Basis.repr into basis-index finsupps; fibered coordinates = embDomain of the genuine address; `basisCycle`/`basisCycle_spec` from certificates; finite-support reconstruction gives every Hodge class a cycle.
- name-vs-content: accurate ("Microscopic projector certificates produce native algebraic cycles at those exact basis addresses").
- gaps: the per-sheet `BasisProjectorCertificate` family is the unproven geometric input.

### GSTClassicalHodgeGSTSpineGlobalSource.lean (185 lines)
- decls: 6 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: `NativeMassCycleClassBridge V H` (imported, 3 substantive geometric premises -- flagged elsewhere as NOT universally valid).
- main content: lifts the limitless spine into the total (weight,sheet) cosmos: `globalSpineOrbitSeed` (manufactured from spine + native-mass bridge), global source sheet/probe = the selected basis coefficient, global source nonvanishing in every weight (native mass + spine conservation), matrix units send the source address to nonzero multiples of arbitrary sheets.
- name-vs-content: accurate orbit bookkeeping; "no target algebraicity ... assumed here".
- gaps: inherits the NativeMassCycleClassBridge premises, which the repo's own audit refutes in general.

### GSTClassicalHodgeCyclicRealizationEquivalence.lean (184 lines)
- decls: 6 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: `LocalCycleSpectralRealization` / `LocalCyclicRealization` (imported cyclic-spectral records -- inputs of the equivalence).
- main content: equivalence of the cohomological local-cyclic engine and the native-cycle formulation: forward lifts a spectral observable to native cycles via projectivity over Q; reverse extracts native cycles per live direction and exhibits the unit-sum atomic seed (`live_basis_mem_atomic`, `unit_seed_mem_atomic`, `toLocalCyclicRealization`).
- name-vs-content: accurate equivalence file ("no independent native-operator hypothesis is present").
- gaps: both realizations remain hypotheses of the local criterion.

### GSTClassicalHodgeProjectivePointOmniverseSource.lean (179 lines)
- decls: 6 theorems, 0 defs, 0 structures (3 docstring lines matched), 0 axioms, 0 sorry
- hypotheses: `hgeom : forall {u v}, (hodgeBranchGraph ...).Event u v -> StrictlyMaterializedBranch u v` -- **every** primitive GST branch event strictly materialized (the geometric input of the crown).
- main content: `pointCycle_cycleClass_ne_zero` (point classes never vanish, by strictly positive projective degree trace); `pointHodgeSource` (any codim-p point is a nonzero algebraic Hodge source); `hodge_weight_of_projectivePoint_strictOmniverse` (point source + strict materialization of ALL branch events => the whole weight-p Hodge sector is in the cycle-class range).
- name-vs-content: honest: the seed is now cheap (a point), but the cost moved to materializing every branch event.
- gaps: `StrictlyMaterializedBranch` for all events is open (per-edge correspondence geometry).

### GSTClassicalHodgeGradedGeometricOrbitAlgebra.lean (177 lines)
- decls: 8 theorems, 1 def, 0 structures, 0 axioms, 0 sorry
- hypotheses: none.
- main content: `geometricProgramOrbitModule` -- the reachable set is already a Q-submodule (addition/scaling are program constructors); `geometricProgramOrbitSubspace_eq_module`; graded module law `program_maps_geometricProgramOrbitModule` (every program p->q maps the orbit module at p into the orbit module at q, by post-composition); spine seeds internal to the orbit.
- name-vs-content: accurate ("genuine graded module over the whole mixed noncommutative program algebra").
- gaps: pure syntax-level algebra; no reachability progress.

### GSTClassicalHodgeVerticalRayProjectiveApexFinale.lean (175 lines)
- decls: 4 theorems, 0 defs, 0 structures (1 docstring line matched), 0 axioms, 0 sorry
- hypotheses: `ExactVerticalCutRayCertificate V p` (per live weight -- imported) and `ApexLocalizedL2Realization ...` (realized localized-L2 expressions from the canonical apex to each basis sheet -- imported).
- main content: dead weights discharged by zero; live weight: vertical ray => canonical cut seed nonzero => apex-localized L2 expressions place the whole (p,p) sector in the range (`live_weight_range_of_verticalRay_and_apexLocalizedL2`, `exactHodge_of_verticalRays_and_apexLocalizedL2`).
- name-vs-content: "Finale" = minimal-input interface compression ("no rooted fan, arbitrary omniverse compiler, all-edge materialization ... is an input").
- gaps: both certificates (vertical rays, apex-localized L2 realizations) are open geometric inputs.

### GSTClassicalHodgeNativeArsenalRepresentation.lean (171 lines)
- decls: 5 theorems, 0 defs, 2 structures, 0 axioms, 0 sorry
- hypotheses (quoted): `NativeArsenalRepresentation.hodge_action : forall i j alpha, (operator i j).cohomologyOperator alpha.1 = (hodgeMatrixUnit i j alpha).1` with `operator i j : CycleClassOperatorPair` -- **a cycle-class-natural native operator pair realizing EVERY rank-free Hodge matrix unit**; `GlobalNativeArsenalRepresentation` = one per weight plus a seed.
- main content: from such a representation: range/atomic-span stability, `algebraicHodgeSubspace_invariant`, one seed satisfies the whole orbit law, and the global crown gives every Hodge class a native cycle.
- name-vs-content: honest about being a representation hypothesis ("No separate orbit_algebraic assumption remains" -- because it is derived from a STRONGER assumption).
- gaps: inhabitation of the representation = algebraicity of all matrix units (standard-conjecture-grade input), open.

### GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer.lean (169 lines)
- decls: 6 theorems, 2 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none beyond the imported analytic-span structure of a strict correspondence.
- main content: canonical maximal transfer: `transferableSubspace = ker Omega_K`, `targetAmbiguity = ker r*`, `transferableRangeMap`, quotient identification `ker Omega_K -> H^n(X)/ker r*` -- the largest choice-free action determined by the relation itself.
- name-vs-content: accurate ("No Hodge basis, algebraic cycle selector, arbitrary linear extension, or choice of target representative occurs").
- gaps: `Omega_K = 0` and injectivity of r* are not addressed here (that is the BettiObstruction layer).

### GSTClassicalHodgeCrossCarrierObstruction.lean (164 lines)
- decls: 7 theorems, 0 defs, 0 structures (1 docstring line matched), 0 axioms, 0 sorry
- hypotheses: `CrossCarrierTransfer` records (imported; supply naturality `R.naturality` and range preservation `R.native_range_preserved`).
- main content: conservation laws: transfers preserve the cycle-class kernel and the already-algebraic range; detectors killing target algebraic classes kill all transported images; `nonzero_detector_forbids_period_hit` -- a nonzero detector forbids normalizing an algebraic source onto a nonalgebraic target (the ghost obstruction). Header: "NEEDS CI RUN LATER. No Lean compilation is performed in this session."
- name-vs-content: accurate; explicitly "a new constraint on GST geometric-program construction rather than a surjectivity assumption".
- gaps: CI status unverified; obstruction-only (no positive construction).

### GSTPrefixOneSeedCore.lean (161 lines)
- decls: 9 theorems, 2 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none.
- main content: exact arithmetic of the unit canonical tail: `unitTail_eq_lteCoeff` (canonical quotient = LTE coefficient via 4^(3^s) = 1 + 3^(s+1)*c_s), `unitTail_prefix_one`, `canonical_prefix_recurrence` (Q_s(1+3n) = c_s + 3*4^(3^s)*Q_(s+1)(n)), prefix-one seed laws.
- name-vs-content: accurate arithmetic core for the prefix-one escape analysis.
- gaps: feeds the Erdos/four-power branch; no universal claim here.

### GSTClassicalHodgeNormalizedFiberedSpectralAtom.lean (155 lines)
- decls: 5 theorems, 0 defs, 0 structures (1 docstring line matched), 0 axioms, 0 sorry
- hypotheses: none.
- main content: divides out the nonzero live coefficient once: `normalizedSpectralAtom` = (liveSpectralCoefficient)^-1 * isolated state, with exact coefficient-one faces (`normalized_hodgeFace_exact`, native face, limitless face).
- name-vs-content: accurate normalization file.
- gaps: internal GST shape bookkeeping.

### GSTGeneralSpaceFiberedCosmology.lean (155 lines)
- decls: 1 theorem, 7 defs, 3 structures, 0 axioms, 0 sorry
- hypotheses: none -- structures are pure type-theoretic data (`LocalFamily.Fiber`, `FiberedTransport.transport` with functorial laws `transport_id`/`transport_comp`, `FiberedHom.map` + naturality).
- main content: dependent local families over a GeneralSpace, pullback, product, sections, parallel transport systems, parallel sections (`isParallel_pullback`), natural maps with id/comp.
- name-vs-content: "Cosmology" = a category of dependent types with connection-like structure; content honest and elementary.
- gaps: no geometry; "Transport is a separate capability: a varying family does NOT automatically possess a connection" (honest).

### GSTClassicalHodgeOmniversalNativeOrbitClosure.lean (149 lines)
- decls: 5 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: `OmniversalSeparatorGhost G` (a hypothetical failure ghost -- witness data) + `OneSourceCompositionalCorrespondenceRealization` (imported per-sheet correspondence packet).
- main content: `hodgeWeightLive_of_omniversalGhost` (a detected sheet certifies liveness); `false_of_omniversalGhost_and_oneSourceRealization` -- the ghost is impossible once correspondence geometry constructs the exact native cycle of the detected sheet (identity-program collision).
- name-vs-content: accurate contradiction packaging.
- gaps: the one-source compositional realization is the open input.

### GSTClassicalHodgeGeneralSpaceGSTCompiler.lean (147 lines)
- decls: 6 theorems, 2 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: `GSTSourceTargetProgram G S j` (imported source-target program record with `source_action`).
- main content: source/basis points of the General Space realization are native; `normalizedProgram_source_action` (normalize by inverse source scalar: source maps to the exact basis vector); `sourceProgram_generalSpacePath` -- every synchronization certificate becomes an actual General Space path from the native source to the exact Hodge basis state.
- name-vs-content: accurate interface compiler GST -> General Space.
- gaps: the program records are inputs.

### GSTClassicalHodgePolynomialTransitionClosure.lean (141 lines)
- decls: 4 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: `PointClassTransitionKernel` / `AtomicSpanStable` (operator-stability hypothesis on T).
- main content: atomic stability propagates through the full rational polynomial calculus: `atomicSpanStable_linearPolyEval`, `finitePointTransitions_linearPolyEval`, chosen kernels for P(T), native cycles for polynomially extracted point classes.
- name-vs-content: accurate closure lemma.
- gaps: generatorwise stability of the base observable is the input.

### GSTClassicalHodgeUniversalTwoSlotSaturation.lean (141 lines)
- decls: 6 theorems, 1 def, 0 structures, 0 axioms, 0 sorry
- hypotheses: `UniversalTwoSlotInvariant S` (stability under the single word `forwardArsenalWord 0 1` after every recoordination) -- defined Prop, taken as hypothesis.
- main content: `universalTwoSlotInvariant_rankFree` (one universal 2x2 word generates full rank-free matrix-unit invariance), `universalTwoSlotInvariant_eq_top`, `algebraicHodgeSubspace_eq_top_of_twoSlot`, defect-vanishing corollaries.
- name-vs-content: accurate compression ("the only operator whose geometric externalization remains is forwardArsenalWord 0 1 = P_1 L^2 P_0").
- gaps: the two-slot invariance of the algebraic subspace is the (open) geometric input.

### InformationStateScratch.lean (137 lines)
- decls: 5 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none.
- main content: exact shared-information-state identities: `gst_shared_information_state_exactS` (the bottom decomposition D+4Z is one seeded affine carry with multiplier 4A), the ternary vertical recurrence, quotient-seam normalizations.
- name-vs-content: accurate scratch arithmetic.
- gaps: none claimed.

### GSTClassicalHodgeGlobalArsenalPropagationCrown.lean (133 lines)
- decls: 5 theorems, 0 defs, 2 structures, 0 axioms, 0 sorry
- hypotheses (quoted): `WeightArsenalRealization.orbit_algebraic : forall i j, hodgeMatrixUnit i j seed in AlgebraicHodgeSubspace V H p`; `GlobalArsenalPropagation` = `propagation : SeedPropagationFamily V H` + `zero_seed_algebraic` + arsenal per weight.
- main content: composes cross-weight propagation with fixed-weight saturation: `seed_algebraic`, `algebraicHodgeSubspace_eq_top` in every weight, `every_hodge_class_has_native_cycle`, basis-free native cycle for every Hodge class.
- name-vs-content: accurate conditional crown.
- gaps: the whole GlobalArsenalPropagation record (propagation family + arsenal realization per weight) is the unproven input.

### GSTClassicalHodgeCMConstructiveSurfaceDescent.lean (130 lines)
- decls: 2 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses (quoted): `hIncidence : RealizesFinitePointKernelOnBetti pointKernel betti` and `hBettiExpansion : forall i, algebraMap Q K ((b.repr target) i) = sum over j in s of coeff j * algebraMap Q K ((b.repr (betti (D.cycleClass p (sourceCycles j)))) i)` -- **a finite K-coefficient Betti expansion of the target through source cycle classes**.
- main content: `rational_target_of_finite_surface_kernel` -- given the incidence kernel and the K-expansion, the target is an actual Q-cycle class (`exists Z, H.cycleClass q Z = target`); the Hodge-target variant. Coefficient field K arbitrary over Q (Qbar allowed).
- name-vs-content: honest ("The one geometric obligation is the pointwise Betti action ... not equivalent to the claim that every Hodge class is algebraic unless sufficient geometric source data is supplied"). "NEEDS CI RUN LATER."
- gaps: real incidence kernels + expansions for actual CM/Gale sources are not constructed; CI unverified.

### GSTFourPowerExactExponentPeriod.lean (126 lines)
- decls: 3 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none.
- main content: `pow4_mod_one_iff_three_pow_dvd : 4^n % 3^(p+1) = 1 iff 3^p | n` -- exactness of the exponent period 3^p at modulus 3^(p+1) (no smaller precision disappears), by 3-adic induction with digit-period and trit-lift lemmas.
- name-vs-content: accurate, genuinely nontrivial arithmetic lemma.
- gaps: none internally; feeds the four-power program.

### GSTResearchGeometricMassSemanticAudit.lean (122 lines)
- decls: 4 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none -- this is an **adversarial audit**: it REFUTES an over-strong hypothesis used elsewhere.
- main content: `mass_collision_forbids_nativeMassCycleClassBridge` (equal classes with different raw masses refute the native-mass bridge); `zero_class_semantics_refutes_mass_bridge` (zero-cycle-class semantics + one point contradict kernel_mass_zero, since point mass = 1); the repaired universally-safe degree readout `homologicalDegree` (any Q-linear cohomology functional) with correct kernel properties. Header explains the P2 conic-vs-2-lines counterexample (mass -1 vs class 0) and states "A formal P2 cycle-class model is needed to certify this particular geometric example in Lean. We Do NOT claim that instance is formalized."
- name-vs-content: accurate self-audit; mathematically the most sober file of the batch.
- gaps: the conic counterexample itself is not formalized; the audit only proves the implication "mass collision => not-bridge".

### HodgeDeRhamBridgeV2.lean (114 lines)
- decls: 10 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none ("does not assume ReverseOntologicalWindow").
- main content: `signature_current_exact` (HappyCell iff ontDensity = 84 or 42 -- interval-cases on the 12 cells), `positive_current_exact`, period rebasing `4^(r+3m) = 4^r * 64^m`, composed finite twists (SixAdicIsoAt iff dyadic and triadic shadows), de Rham twist invariance, mixed-period layer factorization, `absorption_v2_crown`.
- name-vs-content: "HC ABSORPTION V2" -- content is finite GST arithmetic laws; no Hodge conjecture content.
- gaps: the "bridge" is internal to the GST finite model (imports HodgeDeRhamBridge, outside batch).

### GSTHodgeChannelAddressBridge.lean (112 lines)
- decls: 5 theorems, 1 def, 0 structures, 0 axioms, 0 sorry
- hypotheses: none.
- main content: faithful embedding of fixed-weight Wave-II channel vectors into Nat -> Q via physical channel addresses (`channelAddressLift_at`, `_injective`), Kronecker behavior of channel basis vectors, `channel_address_bridge_crown`. "No Hodge conclusion and no algebraic-cycle statement occurs here."
- name-vs-content: accurate pure address geometry.
- gaps: none claimed.

### GSTResearchOriginalEquationNames.lean (105 lines)
- decls: 4 theorems, 3 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none; attribution record for the user's three "original GST equations" (GSTGCCF, GSTOSR, GSTIZHCF).
- main content: GSTGCCF squaring identity (third independent geometric coordinate interpretation); GSTOSR defined as a scalar inequality with an explicit zero-maps counterexample showing it "is not universally true without additional actual geometric hypotheses"; GSTIZHCF infinite series `sum' m, indexedKernel 2 2 m = -1` and nonzero zeta amplification.
- name-vs-content: honest -- "Only their currently TYPED mathematical components are Lean definitions and theorems here ... No meanings are silently invented."
- gaps: the user's index-set R, H x Q operation, and T(Non-Zero N) lack original geometric definitions; the three "equations" are not established as mathematical laws.

### GSTClassicalHodgeGeneralSpaceSynchronization.lean (102 lines)
- decls: 3 theorems, 0 defs, 1 structure, 0 axioms, 0 sorry
- hypotheses: `SynchronizedPathExecution` fields: `program`, `reaches : program.cohomologyEval G x.2 = y.2`, `sourceCycle`, `source_sync : H.cycleClass x.1 sourceCycle = x.2` -- synchronization data (constructible from a path + native witness via `synchronizePath`).
- main content: `target_sync` (native and Betti execution of the same General Space path land at the same state -- the "cosmic synchronization square"), `target_native`, `synchronized_path_native`.
- name-vs-content: accurate.
- gaps: paths come from the General Space realization whose Path type is existentially defined over programs (reachability still open).

### GSTResearchUniversalMassZetaSource.lean (95 lines)
- decls: 1 theorem, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses (quoted from header): "CAUTION: NativeMassCycleClassBridge is a STRUCTURE WITH THREE substantive geometric premises; its universal inhabitance has not been proved in HC-PROOF. This theorem is valid for any such certified bridge but is NOT an unconditional proof of the Hodge conjecture or the bridge's existence." The theorem takes `(M : NativeMassCycleClassBridge V H)` as parameter.
- main content: `fixed_corrected_zeta_source_every_weight` -- from a certified mass bridge, a Q-linear Hodge-fiber readout normalized to 1/2 on the genuine native spine at EVERY weight (using the corrected indexed series value -1 at x=y=2), with nonzero spine seed.
- name-vs-content: "Universal Mass Zeta Source" -- content is one conditional measurement lemma; the name suggests more.
- gaps: bridge inhabitance open AND the repo's own audit (GeometricMassSemanticAudit) shows the bridge fails in general (mass collisions); the zeta scalar is decorative (fixed -1/2).

### GSTClassicalHodgeGhostIndexedCriterionCircularity.lean (91 lines)
- decls: 4 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none -- meta-theorem.
- main content: `ghostIndexedCriterion_iff_hodge` (and witness/relation variants): any criterion indexed only by hypothetical Hodge-failure ghosts, if strong enough to imply Hodge, is EQUIVALENT to Hodge -- "It cannot be used as a logically weaker foundation for a noncircular proof." Prevents renaming the conclusion as ghost survival/fan/closure/plane/materialization packages.
- name-vs-content: accurate and important anti-circularity guardrail.
- gaps: none (it is a barrier theorem, by design).

### GSTGraphV2FourPowerForcingBridge.lean (88 lines)
- decls: 5 theorems, 1 def, 0 structures, 0 axioms, 0 sorry
- hypotheses: `FourPowerDirectExistence` / `FourPowerCreationMaster` (unproven Props, imported -- the open arithmetic target).
- main content: `FourPowerGraphForcing := forall K >= 5, K != 7, exists p >= 1, HappyCell (carry4 (4^K) p) (digit3 (4^K) p)`; interface equivalences: graph forcing iff creation master iff direct existence.
- name-vs-content: accurate equivalence bridge.
- gaps: the forcing law itself is open (the four-power program's target).

### GSTClassicalHodgeGeneralSpaceExactOperatorFinale.lean (82 lines)
- decls: 3 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses (quoted): `seed : forall p, NativeHodgeSeed (V:=V) (H:=H) (p:=p)` and `R : forall p, forall j, GeometryFirstTwoGenerator (V:=V) (H:=H) (seed p).sourceIndex j` -- a native seed at every weight plus two-generators from its live source to every sheet.
- main content: `everyHodgeClassIsRationalAlgebraic_of_operatorCosmos`, `everyHodgeClassIsFiniteRationalCombination_of_operatorCosmos` (the Clay finite-sum form), `all_basis_points_native` (pointwise General Space statement).
- name-vs-content: "Exact Operator Finale" -- another conditional assembly ("does not package Hodge surjectivity; it assembles the already constructed native GST words").
- gaps: the seed/two-generator inputs are the standing open hypotheses.

### GSTClassicalHodgeRadicalPrincipalCutDimension.lean (72 lines)
- decls: 3 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none.
- main content: `ringKrullDim_quotient_radical` (quotient by I or sqrt(I) has the same Krull dimension -- via order-isomorphic prime spectra/zero loci); `ringKrullDim_quotient_radical_span_singleton_succ`: in a Noetherian local domain, the REDUCED one-equation cut still drops dimension exactly by one for f != 0 nonunit.
- name-vs-content: accurate commutative algebra (Krull principal ideal theorem form, radical-stable).
- gaps: none internally; supports the separator's radial one-sheet move.

### GSTGeneralSpaceSchemeDimensionObservation.lean (66 lines)
- decls: 3 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry
- hypotheses: none.
- main content: `ringKrullDim (stalk) = coheight` packaged as a GeneralSpace Chart; `codimensionPoint_observed_exactly` (a codim-p point is seen at value p); `codimension_observation_crown` -- "the codimension label is completely recovered from local geometry and is absent from the ontological core".
- name-vs-content: accurate small architectural lemma.
- gaps: none.

---

## BATCH SUMMARY

**Totals**: 71 files, 19,361 LOC, 700 theorems, 166 defs, ~41 structures, 0 axioms, 0 opaque, 0 sorry, 0 native_decide. ~270 `#print axioms` receipt lines. Every crown theorem is a `#print axioms`-receipted conditional.

**Inventory of ALL custom axioms / unproven hypotheses found (the load-bearing assumption inventory).** There are NO `axiom` declarations. The unproven content is carried by hypothesis-records (structure fields) and supplied-data fields, all taken as theorem parameters:

1. `BettiHodgeData.hodgePP` + `BettiHodgeData.cycleClass` (GSTGeometricRealizationStage2F, used by ~30 files): the genuine rational (p,p) Hodge subspace and the genuine cycle-class map are SUPPLIED DATA (honestly: "the still-missing classical geometry"). No algebraicity/surjectivity asserted.
2. `GeometryFirstLefschetzStep.transport_formula` (GeometryFirstGlobalPropagation): `cohomologyOperator source.1 = limitlessLefschetzScalar p q * target.1` -- assumed Lefschetz transport between Hodge fibers; `GeometryFirstSeedPropagation.step : forall p, GeometryFirstLefschetzStep V H p (p+1)` (one per weight); `GeometryFirstGlobalPropagation.fixedWeight` (two-generator per basis pair); `GeometryFirstLivePathCosmos.livePath` (every live fiber reachable from a weight-0 point seed).
3. `ProjectivePrimitiveRealization.restricts_to_hodge` (ProjectiveTwoGeneratorExternalization): a projective self-map whose Betti pushforward equals a prescribed Hodge-fiber operator; `ProjectiveTwoGenerator` = two per basis pair.
4. `NativeArsenalRepresentation.hodge_action` (NativeArsenalRepresentation): cycle-class-natural operator pairs realizing EVERY rank-free Hodge matrix unit E_ij (standard-conjecture-grade).
5. `FiniteBasisAlgebraization.basisCycle_class` / `FiberedBasisCycleBridge.basisCycle_spec` / `CanonicalBasisCycleSupply.basisCycle_class` (HodgeChannelFiniteBasis, CycleLanding): every Hodge basis vector has an actual cycle representative -- literally the Hodge conjecture on a basis; declared open Prop `Stage2GFiniteBasisAlgebraizationObligation`.
6. `GradedGeometricOrbitCyclic` (GradedGeometricProgramOrbit) / `HandwrittenPiGeometricLanding` + `LiveLocalizedL2BranchesLandInOrbit` (HandwrittenPiEquationDerivation): the reachability/orbit-landing statements into which "the whole Hodge problem is compressed".
7. `hA` of `bigradedBettiHodge_of_point_rationalCorrespondence_omniverse` (PiPointRationalCorrespondenceUnboundedFinale): rational closed correspondences whose action performs the rank-one source hit on every basis vector.
8. `GeometricPointFiberLaw.kernel_cup_pointFundamental` + `.gysin_fiberIntersection` (StrictCorrespondenceGeometricTransferFinale): the cup/Gysin fiber-intersection calculation (classical intersection theory, unproven).
9. `StrictRelationEdgePacket.related` etc. (OmniverseStrictRelationRayCompiler): per-edge raw Betti relation leftPullback(source)=rightPullback(target) with nonzero right trace + point compatibility.
10. `OneSidedKrylovCertificate.realizesOnPoints/preservesHodge` (OneSidedFiniteCorrespondenceKrylovFinale): independently realized Hodge-preserving correspondence action + algebraic seed.
11. `GeometricSourcePeriodCertificate.exact_period_formula` + `nonzero_period` (OpenAIGeometricPeriodCertificates): per-sheet nonzero rational period identities via cross-carrier transfers (CM/Kuga-Satake/Gale route) -- "CONDITIONAL on real geometric certificates".
12. `hBettiExpansion` of CMConstructiveSurfaceDescent: finite K-coefficient Betti expansion of the target through source cycles (with `RealizesFinitePointKernelOnBetti`).
13. `ExactVerticalCutRayCertificate` + `ApexLocalizedL2Realization` (VerticalRayProjectiveApexFinale, imported): vertical ray nonvanishing + apex-localized L2 expressions per sheet.
14. `WeightArsenalRealization.orbit_algebraic` + `GlobalArsenalPropagation` (GlobalArsenalPropagationCrown): matrix-unit orbit algebraicity per weight + cross-weight seed propagation family.
15. `NativeMassCycleClassBridge V H` (input to GSTSpineGlobalSource, UniversalMassZetaSource): three substantive geometric premises; **universal inhabitance NOT proved -- and the repo's own audit (GeometricMassSemanticAudit) proves mass collisions and the zero-class semantics each REFUTE it in general**.
16. `UniversalTwoSlotInvariant` (UniversalTwoSlotSaturation): stability under the single word forwardArsenalWord 0 1.
17. Arithmetic-branch open targets (defined Props, never asserted): `FourPowerDirectExistence`/`FourPowerCreationMaster`/`FourPowerGraphForcing` (four-power program), `CommonTwo`, `CantorianPower`, the gate-dodging-walk closure of GSTFourPowerThirdWave, `GSTInfiniteBridgePathS` dichotomy branches.
18. Modular input records feeding the crowns: `SynchronizedPathExecution` (GeneralSpaceSynchronization), `GradedPointClassTransitionKernel.transition_spec` (GradedPointKernelLift), `RightFiniteChainTransfer.transfer_right` (ChainTransfer), `GSTSourceTargetProgram` (GeneralSpaceGSTCompiler), `SourceTargetCorrespondenceExpressions` (HandwrittenPiExplicitNativeCollapse), `BasisProjectorCertificate` family (RankFreeLimitlessAssembly), `SeedPropagationFamily` + `ProjectiveTowerHodgeIntertwining` + `SpineTowerConservedCharge` (imported).

**The 5 most load-bearing files and why:**
1. **GSTGeometricRealizationStage2F.lean** -- defines the working Hodge statement `BettiHodgeStatement` (`forall p, hodgePP p <= range (cycleClass p)`) and fixes the Betti carrier to Mathlib singular cohomology; nearly every ClassicalHodge file in the batch is typed against its `BettiHodgeData`. Its two supplied fields (Hodge subspace, cycle-class map) are where all classical geometry enters.
2. **GSTClassicalHodgeGeometryFirstGlobalPropagation.lean** -- the central propagation engine: its hypothesis-records (Lefschetz steps per weight, two-generators per pair, live paths) are the standing open inputs that every later "crown" (GlobalArsenalPropagationCrown, GeneralSpaceExactOperatorFinale, ProjectiveTwoGeneratorExternalization...) re-packages; it states the honest reduction of Hodge to these records.
3. **GSTHodgeChannelFiniteBasis.lean + GSTClassicalHodgeCycleLanding.lean** -- the cleanest statement of the irreducible remaining obligation (`basisCycle_class` per basis vector; `Stage2GFiniteBasisAlgebraizationObligation`), i.e. the exact normal form of the Hodge conjecture inside this framework, with the reverse implication showing the bridge is EQUIVALENT to the target.
4. **GSTLefschetzCrown.lean** -- the largest self-contained verified artifact (59 theorems, 0 inputs): the finite 12-cell "absorption" of Hard Lefschetz/Poincare/Kunneth/CDK. Load-bearing because it is the flagship "we own the human arsenal" claim, and its scope (a rank-12 lattice) defines the gap between the campaign's narrative and its verified mathematics.
5. **GSTResearchGeometricMassSemanticAudit.lean + GSTClassicalHodgeGhostIndexedCriterionCircularity.lean** (one guardrail pair) -- the audit refutes the NativeMassCycleClassBridge in general (the input of GSTSpineGlobalSource/UniversalMassZetaSource), and the circularity barrier proves any ghost-indexed criterion is equivalent to Hodge. Together they fence off the two easiest ways to fake progress.

**The single biggest gap:** the entire ClassicalHodge edifice is a chain of honest conditionals whose endpoints never touch ground: every "Hodge crown" in this batch (GeometryFirstGlobalPropagation, GlobalArsenalPropagationCrown, GeneralSpaceExactOperatorFinale, PiPointRationalCorrespondenceUnboundedFinale, VerticalRayProjectiveApexFinale, NativeArsenalRepresentation...) derives `BigradedBettiHodgeStatement` from records whose fields ARE the Hodge conjecture in disguise (cycles per basis vector, matrix-unit realizations, Lefschetz transports per weight, per-sheet correspondence/period certificates). No file in batch 9 constructs, for any actual smooth projective variety and any p, a single one of these inputs; moreover the repo's own audit shows one favored input (the native-mass bridge) is refuted in general. Compounding this, the two genuine finite-model files (GSTLefschetzCrown, GSTWorldCosmology) prove their "classical arsenal" statements only on a 12-cell Z-lattice, and the arithmetic branch (Worldtrace/FourPower/PrefixOne, ~5,000 LOC of the batch) addresses a Collatz-adjacent ternary-digit problem with no proved bridge to the Hodge program at all. Batch 9 contains zero unconditional progress toward Hodge; its value is interface engineering, honest scope statements, countermodels, and anti-circularity guardrails.
