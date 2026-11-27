### GSTUniversalChowRetractToTarget.lean (1420 lines)
- decls: 29 theorems, 5 defs, 8 structures (hypothesis-records), 0 axioms, 0 sorry, 18 #print axioms
- hypotheses (structure-fields, all unproven geometric input packets; quoted field content):
  - NativeHodgeRetract (Y X D H q p): native/betti linear maps, hodgeSection with section_is_hodge (Hodge-preservation), betti_retract: `∀ alpha, betti (hodgeSection alpha) = alpha`, cycleClass_natural: `∀ Z, H.cycleClass p (native Z) = betti (D.cycleClass q Z)`. Assumes a full Chow/Betti correspondence retract pair between source and target cohomology.
  - GeometricMultiSourceChowBirth: finite source schemes/codims with native/betti maps, naturality, and hodgeSpan: `∀ alpha ∈ rationalHodgeSubspace …, ∃ beta, (∀ i, beta i ∈ rationalHodgeSubspace …) ∧ ∑ i, betti i (beta i) = alpha` — assumes every target Hodge class splits as a sum of source Hodge classes through the given Betti maps.
  - GeometricSplitGysinPacket: same + readout maps with readout_hodge (Hodge preservation) and reconstruct: `∑ i, betti i (readout i alpha) = alpha` — assumes an exact cohomological reconstruction identity (bundle/blowup formula).
  - SchemeProjectiveBundleGysin: degree-indexed xi^j*pi^* maps, cycleClass_natural, readout_hodge, reconstruct `∑ j : Fin r, bettiXiPull j (hodgeReadout j alpha) = alpha` — assumes the projective-bundle formula.
  - SchemeBlowupGysin: exceptional Gysin maps over Option (Fin (c-1)) with the same naturality/readout/reconstruct laws — assumes the blowup Chow/Hodge formula.
  - SchemeFiniteDominantTwoTransfer: degree ≠ 0, nativePush/bettiPush/bettiPull with pull_preserves_hodge, native_betti_natural, push_pull_degree: `bettiPush (bettiPull alpha) = degree • alpha` — assumes f_* f^* = d·id for a generically finite morphism.
  - SchemeExceptionalCenterRetract: exceptionalNative/exceptionalBetti + centerRecover maps with exceptionalCycleClass, recoveryCycleClass, centerLeftInverseBetti (`centerRecoverBetti (exceptionalBetti alpha) = alpha`), exceptionalPreservesHodge — assumes the exceptional Gysin embedding with a cohomological left inverse.
  - SchemeProjectiveMiddleStabilization: nativeStabilize/nativeRecover + betti maps with stabilizeNaturality, recoverNaturality, bettiLeftInverse, preserveHodge — assumes pr_Y^*(-)·h^r / pr_{P^r,*} stabilization identities.
- main content: purely conditional derivations, honestly labeled: (1) target cycle construction from a solved source via a retract (calc chains on cycleClass); (2) scheme-typed multi-source "birth" laws assembling ∑ native i (Z i) with H.cycleClass p (∑ …) = alpha; (3) inductive towers SchemeTypedGSTCodimensionTwoBlowupTower / SchemeTypedGSTGeometricTower with structural induction showing HodgeAtWeight/BigradedBettiHodgeStatement propagates; (4) all-varieties reductions: algebraic_center_iff_exceptional_blowup_class (per-class iff), algebraic_iff_rational_blowup_middle_class, arbitrary_variety_hodge_from_rational_middle_world (Hodge on X ← Hodge in middle degree on rational M=Y×P^r); (5) defect-persistence: NativeDefectIndependent families survive blowup+stabilization.
- name-vs-content: name promises "universal Chow retract to target" but every theorem is conditional on unproven Gysin/blowup/retract packets; the file explicitly says the geometric maps "are separate scheme-level instances to be proved".
- gaps: no geometric instantiation of any packet exists here (projective-bundle/blowup/finite-morphism Gysin maps are external obligations); BigradedBettiHodgeStatement (full Hodge conjecture) on seeds is assumed; the middle-degree reduction only shifts the conjecture to rational M.

### CardinalWorlds.lean (1251 lines)
- decls: 92 theorems, 20 defs, 0 structures, 0 axioms, 0 sorry, 15 #print axioms
- hypotheses: none (no axiom, no hypothesis-record; header explicitly: "NO postulate in this universe is assumed as an axiom"; the open fragment lives in MonolithBoundary.lean, not here)
- main content: "the Cardinal Worlds" — elementary ℕ arithmetic copied verbatim from the source monolith `kyo-oo/erdosternary2`: ternary-digit readers noTernaryTwo/hasTernaryTwo, carryAtPos bounds, modular periodicity of 4^a mod 9/27/81, digit-2 witnesses for 4^a in specific residue classes, exceptions n=0,2,8; the "bridge 3=1+2" identities (2^(j+2)·d j = 3^(2^j)−1, bridge signatures); verdict/witness equivalence `erdos_even_verdict_iff_digit_witness` ((∀K≥8, noTernaryTwo(4^K)=false) ↔ (∀K≥8, ∃p, 4^K/3^p%3=2)); three-world collapse 5·Σ_{j<K}2^j3^j = 6^K−1.
- name-vs-content: name suggests deep "cardinal worlds" cosmology; content is honest elementary number theory (mostly mod-9/27/81 periodicity + one geometric series identity), with the actual Erdős-type claim unproven.
- gaps: the even-world conjecture ∀K≥8, noTernaryTwo(4^K)=false is only checked on a≤500 (modular_check_base); file is UNCOMPILED locally (CI is verifier of record); imports all of Mathlib.

### GSTGraphV2UnboundedHigherCausality.lean (1012 lines)
- decls: 39 theorems, 27 defs, 5 structures, 0 axioms, 0 sorry, 20 #print axioms
- hypotheses (interface/hypothesis-records, not Hodge content):
  - HigherCausalCosmos: globular ω-category data over SelfExpandingCosmos — assumes source/target/identity operations with globular laws (source (identity x) = x, source (source x) = source (target x) etc.) — an assumed interface, no concrete instance in this file.
  - AnchoredCausalLoops (W,g): g distinct non-identity 1-cells all anchored at W (injective edge, genuine_edges).
  - AnchoredCausalTwoFillings: 2-cells filling anchored loops with prescribed boundary faces.
  - TwoSkeleton (vertices edges faces): finite ℤ-linear chain complex — assumes `boundaryOne (boundaryTwo z) = 0` (i.e. ∂₁∘∂₂ = 0).
  - RationalEllipticFoldForm: plain ℚ⁶ data record (no proposition).
- main content: (1) globular tower bookkeeping (identityTower, boundary_crown, causalTwoBoundary_zero); (2) finite linear algebra: TwoSkeleton ⇒ range ∂₂ ≤ ker ∂₁; logarithmicShiftPower nilpotency/kernel exactness/dimension counts on Fin n → ℚ; monodromy fixed-point characterizations; (3) "CausalHodgeAlignment" on ℚ⁶ fold-forms: explicit compiler ellipticAlignedDivisorCompiler with exact reconstruction theorem under the aligned condition b=e ∧ c=−d; diagonal form is (1,1) at equal moduli and NOT at incommensurable moduli; (4) incidence matrix identity A² = s·A and tr A = s for A_ij = x_i·ell_j (Jouanolou-style numerator check, all n).
- name-vs-content: "Unbounded higher causality" is honest as an abstract globular interface, but the Hodge-flavored parts are small explicit ℚ⁶/ℚ^{n×n} computations, not geometry.
- gaps: no instance of HigherCausalCosmos from actual geometry; the elliptic/Hodge interpretation of RationalEllipticFoldForm rests on "geometry established separately"; the Jouanolou scheme-level construction lives only in a research/ .tex, not in Lean.

### GSTTransferBridge.lean (716 lines)
- decls: 31 theorems, 10 defs, 0 structures, 0 axioms, 0 sorry, 28 #print axioms
- hypotheses: none in-file (0 axioms; relies on GSTHodgeAssault's `hodge_conjecture` for the finite WaveCoef carrier — itself a finite combinatorial statement, other file/batch)
- main content: "Layer 12 transfer bridge": ClRing := Fin 12 → ℤ presented as degree basis of ℤ[H,V]/(H³,V⁴); dictionary addr : WaveCoef ≅ ClRing proven bijective/additive; cup operators clCupD/clCupV proven equal to multiplication by H and V; ring laws H³=0, V⁴=0, HV=VH; addr transports cupDigit/cupCarry and cycleClass (addr (cycleClass p) = clMono (4p)); then `transferred_hodge_conjecture` / `transferred_clay_hodge_conjecture` / `transferred_clay_witness`: every isClHodge p φ (degree-4p supported class) is a rational multiple of the monomial H^p V^p, coefficient = the degree-4p coordinate (p < 3).
- name-vs-content: "THE HODGE CONJECTURE AND THE OFFICIAL CLAY STATEMENT TRANSFER" is a transfer of a 12-dimensional free ℤ-module computation, not of the Clay problem about cohomology of varieties.
- gaps: header concedes the classical instantiation problem: actual rational cohomology, genuine (p,p) Hodge subspace, cycle-class map, smooth-projective eligibility and the basis-cycle realization family are all still to be supplied; the 12-cell carrier does not supply them.

### GSTGraphV2ScaleEquivariance.lean (609 lines)
- decls: 33 theorems, 1 def, 0 structures, 0 axioms, 0 sorry, 18 #print axioms
- hypotheses: none (all statements are unconditional ℕ identities)
- main content: compositional laws for the Graph-V2 "U-cut": originSuffix n (K+L) = originSuffix (originSuffix n K) L, prefix/phase/tail-energy additivity; u_cut_plane_equivariance: the physical packet field (fun x p => physicalPacket (4^(3^t·n)) x p) equals the field of the cut packet (uTailEnergy, uPhaseShift-shifted); semigroup coherence K-cut ∘ L-cut = (K+L)-cut; crowns scale_equivariance_crown / scale_ontological_invariance_crown bundling observable/predicate/binary-relation invariance and HappyCell/ontDensity invariance under cuts.
- name-vs-content: "SCALE EQUIVARIANCE CROWN" is elementary arithmetic equivariance of a Nat-indexed data table — no geometry.
- gaps: none mathematically (self-contained arithmetic), but entirely internal to the GST graph cosmology; no link to the Hodge program beyond naming.

### HCProof.lean (557 lines)
- decls: 0 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry, 3 #print axioms (of imported theorems)
- hypotheses: none (pure import/receipt file)
- main content: the universe's entry face: ~80 imports assembling the whole corpus (CardinalWorlds, MonolithBoundary, GraphV2 layers, Lefschetz crown, HodgeAssault, ClayOfficial, TransferBridge, GeometricRealizationStage2–2G, waves/*) and ~250 `#check` receipts enumerating the headline theorems of each module; ends with 3 `#print axioms` (polynomialCompletion_injective, compactEvolution_completed, compactEvolution_never_extinguishes).
- name-vs-content: "HC PROOF" names the whole campaign, but this file proves nothing — it is a comparator one-screen index.
- gaps: everything; the actual mathematical status is determined by the imported modules (many of which are conditional or finite-carrier).

### GSTTruncatedWorldCohomologyRing.lean (488 lines)
- decls: 29 theorems, 1 def (+1 instance), 0 structures, 0 axioms, 0 sorry, 6 #print axioms
- hypotheses: none (unconditional finite algebra)
- main content: constructs the operator algebra of the two GST axis shifts on WorldCoef A B: H, V commute with H^B = 0, V^A = 0, so ℤ[H,V] acts through the quotient by truncIdeal; worldOperatorHom, worldAct module laws (zero/one/add/mul/H/V/monomial), worldAct_L boundary (L = H+V Lefschetz operator), hc_H_cube/hc_V_fourth/hc_L_six_acts_zero, truncated_world_ring_crown; a "FormalCoordinateCosmos" type + polynomialCompletion_injective (completion into MvPolynomial injective) and quotientRestriction transitivity.
- name-vs-content: "truncated world cohomology ring" is accurate as algebra of a finite free ℤ-module; "cohomology" is by analogy only.
- gaps: no topology/geometry — the ring is the operator algebra of a digit/carry shift table; connection to actual cohomology is only via the (external) transfer-bridge naming.

### GSTClassicalHodgeGlobalSheetSaturation.lean (444 lines)
- decls: 14 theorems, 2 defs, 0 in-file structures, 0 axioms, 0 sorry, 6 #print axioms
- hypotheses: no in-file axiom; theorem hypotheses are (a) imported hypothesis-records `G : GeometricCycleClassSpine V H` and `M : NativeMassCycleClassBridge V H` (unproven spine/bridge packets from other files), (b) `SameWeightGSTStable p W : ∀ i j phi ∈ W, sheetMatrixUnit ⟨p,i⟩ ⟨p,j⟩ phi ∈ W` (stability of the native algebraic address span under same-weight GST matrix units — a geometric unproven condition), (c) `hNonzero : H.cycleClass p Z ≠ 0`.
- main content: linear algebra on FiberedHodgeAddress: FixedWeightSheetSubspace p = exact rational span of the weight-p Hodge sheet generators (fixedWeight_eq_generatorSpan); every_sheet_mem_of_spine_and_stable (one nonzero spine address + GST stability ⇒ all sheet generators in W); globalMatrixUnit_eq_LPWord_on_hodge / _twoSlotLefschetz_on_hodge (matrix units are localizations of Lefschetz/Poincare words on the Hodge fiber); nativeAlgebraicWeightAddress_saturates_of_GST_stability(+_and_source) (FixedWeightSheetSubspace ≤ nativeAlgebraicWeightAddressSpan under stability); missing_native_sheet_forces_unrealized_GST_move (obstruction certificate: a missing sheet cannot be reached by a GST move preserving the native algebraic image).
- name-vs-content: "global sheet saturation" is accurate as a subspace-inclusion result, but it is conditional on the spine/bridge records and the stability hypothesis — not an unconditional Hodge result.
- gaps: GeometricCycleClassSpine / NativeMassCycleClassBridge fields are unproven imports; SameWeightGSTStability of the native span is exactly the missing "synchronize GST words with native-cycle programs" step admitted in the header.

### GSTU2DPureDivergence83.lean (413 lines)
- decls: 15 theorems, 6 defs, 0 structures, 0 axioms, 0 sorry, 5 #print axioms
- hypotheses: none (all finite checks; potentials are explicit constants 15/−48/−132 and 0/140/252/420)
- main content: a discrete "pure divergence" law on the 8×3 (carry×digit) cell table: density83 C d = digitPotential(outDigit) − 8·digitPotential(d) + carryPotential(C) − 3·carryPotential(nextCarry); full 12-entry value table by `decide`; happy_iff_density83_positive (positivity ⇔ the two HappyCell orientations), positive spectrum ∈ {84,168}, lower bound −105; reverse density and weighted rectangle prefix versions with exact telescoping identities (reverseDensity83_exact, density83_rectangle_exact, weightedRectanglePrefix83_positive_of_top_leading_happy, graph_density83_rectangle_exact).
- name-vs-content: honest — it is exactly a finite divergence/superharmonic-type computation on the GST graph tables; "Poincaré lemma"-style naming only by analogy.
- gaps: none as arithmetic; no mathematical content beyond a 12-cell table and prefix-sum telescoping; no link to Hodge theory beyond naming.

### GSTGraphV2Production.lean (399 lines)
- decls: 4 theorems, 23 defs, 10 structures (all pure data records: Cell, Edge, Lattice, Neighborhood, Rectangle, OriginCoordinates, OriginFrame, ResidualFrame, ResidualGateFrame, CanonicalCutFrame — no proposition fields), 0 axioms, 0 sorry, 0 #print axioms
- hypotheses: none (data-only assembly)
- main content: assembles the single "production graph object" from previously green coordinates: cell/lattice/edges on GSTGraphV2InfiniteControl.graph E t p, rectangle with carryWord/physical state/uPotential, origin/residual/canonical-cut frames; the 4 theorems are inheritance wrappers (rectangle_physicalInvariant via simpa of an imported lemma, rectangle_uPotential_exact by rfl, canonical/residual variants).
- name-vs-content: honest by its own admission ("deliberately introduces no closing theorem").
- gaps: no mathematical content of its own; correctness rests entirely on imported modules (UnifiedPowerRectangle, HandwrittenAnchoredCocycle, etc.).

### GSTClassicalHodgeRationalCorrespondenceOperatorSynthesis.lean (371 lines)
- decls: 6 theorems, 0 defs of its own (several `noncomputable def` counted under defs earlier are Pair constructors), 0 structures, 0 axioms, 0 sorry, 1 #print axioms
- hypotheses: no in-file axioms; theorem hypotheses: `T : ∀ K : FiniteClosedCorrespondence V, … →ₗ[ℚ] …` together with `hT : ∀ K, K.RealizesAmbientOnPoints (H := H) (T K)` — each primitive finite closed correspondence must independently realize its cohomological operator on point cycles (imported unproven realization condition).
- main content: the space of CycleClassOperatorPair (cycle operator + cohomology operator agreeing through cycleClass) is closed under zero/add/rational smul (ext_data, module-law checks); for a finitely-supported rational combination A of finite closed correspondences, rationalPair's operators are the native correspondence operator and ∑ q_K • T_K, and rational_cycleClass_natural: H.cycleClass p (correspondenceCycleNativeOperator A p Z) = (∑ q • T K) (H.cycleClass p Z) — derived purely by Finsupp induction/linearity.
- name-vs-content: "operator synthesis" is accurate — it is a linearity lemma, conditional on per-correspondence point-realization.
- gaps: no geometric realization for any FiniteClosedCorrespondence is established here; RealizesAmbientOnPoints hypotheses are external obligations.

### GSTU2DExactCrossingCharge.lean (369 lines)
- decls: 15 theorems, 6 defs, 0 structures, 0 axioms, 0 sorry, 8 #print axioms
- hypotheses: none (explicit constants 19/56/21, −19/−56/0, coefficient 84)
- main content: discrete crossing-charge law on the x4 transition table: crossDensity C d = digitPotential(outDigit) − 4·digitPotential(d) + carryPotentialX(C) − 3·carryPotentialX(nextCarry) + 84·surviveI; complete 12-cell table by `decide`; happy cells have charge exactly 105, non-happy ≤ 0 (happy_iff_crossDensity_eq_105, rigidity/dichotomy); reverse codes and rectangle telescoping (reverseCrossCode_exact, reverseCrossRectangle_exact), lower bounds −111 and ≥105/≥2^K under leading-happy hypotheses; exact_crossing_charge_classification_crown bundles the classification.
- name-vs-content: honest finite-arithmetic content; "crossing charge" is a potential-theory analogue on the digit-carry table.
- gaps: none as arithmetic; zero contact with algebraic geometry.

### GSTClassicalHodgeIntegralSquareLocalization.lean (342 lines)
- decls: 13 theorems, 3 defs, 1 structure (IntegralPureSquareModel — data + proven predicate fields, constructed canonically, not an assumption), 0 axioms, 0 sorry, 7 #print axioms
- hypotheses: none assumed in-file (fields scale_pos/world_pure/scaled_eq are discharged by the canonical construction canonicalIntegralPureSquareModel from `ha : IsRationalPureHodge a`)
- main content: uniform denominator clearing for finite rational families: commonDenominator (product of reduced denominators, positive, divides everything), finite_rational_clear_denominators; clearedIntegralWorld is pure-Hodge, diagonal-supported, and pointwise = scale·a; nonzero_rationalPairing_yields_nonzero_integralPairing (pairing scales by the positive product of denominators); not_hodge_yields_nonzero_integralPureSquare_pairing / _Coordinates (a rational separator witness transfers to a nonzero integral pure-vs-pure GST witness).
- name-vs-content: accurate — an integrality/denominator-clearing lemma in the GST square algebra.
- gaps: purely coefficient-level; "classical Hodge" here is the GST finite-square analogue (IsRationalPureHodge on RationalWorldCoef), not cohomology of varieties.

### GSTClassicalHodgeSuccessorGroundFloor.lean (333 lines)
- decls: 13 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry, 6 #print axioms
- hypotheses: only `[IrreducibleSpace V.X]` (geometric instance); header's AUTHORITY 005 audit states no Hodge/cycle-class/ghost/seed/closure law is assumed
- main content: unconditional p=0 case of the successor-coheight additivity law L1 (RelativeSuccessorAmbientExact): a coheight-zero point of an irreducible quasi-sober carrier is the generic point (closure = univ); the point-closure inclusion is a surjective order embedding preserving/reflecting specialization; LTSeries chains transport both ways so ambient and closure coheights agree; every successor candidate has coheight 1 = 0+1. Corollaries: successorMass_eq_relativeCard, successorMass_ne_zero, successorNativeOperator_point_ne_zero, relative_successor_exact_stratum_crown at the ground weight with NO exactness hypothesis (first discharged hExact in repo).
- name-vs-content: accurate and modest — order theory only.
- gaps: p ≥ 1 rungs remain open (catenarity localization unpaid — Mathlib lacks catenarity/height_add); this is only the ground floor of the Route S siege.

### GSTU2DCanonicalPhaseDensity.lean (324 lines)
- decls: 13 theorems, 4 defs, 0 structures, 0 axioms, 0 sorry, 5 #print axioms
- hypotheses: none (explicit potentials d−1 and 2/1/0)
- main content: third variant of the discrete density law: phaseDensity C d = (outDigit−1) − (d−1) + phaseCarryPotential(C) − 3·phaseCarryPotential(nextCarry) + surviveI; twelve-state table by `decide` (Happy cells +2, floor −4); happy ⇔ positive ⇔ = 2, spectral gap; weighted column prefix bounds; horizontal digit / vertical carry telescoping lemmas; phaseColumn_exact and phaseRectangle_exact identities.
- name-vs-content: honest finite arithmetic on the x4/base3 transition table.
- gaps: none as arithmetic; no mathematical substance beyond the 12-cell table and telescoping.

### GSTGraphV2FourPowerRelocation.lean (317 lines)
- decls: 14 theorems, 4 defs, 0 structures, 0 axioms, 0 sorry, 13 #print axioms
- hypotheses: none assumed; NAMED OPEN PROP `FourPowerHappyPropagation : ∀ K p, 8 ≤ K → 1 ≤ p → HappyCell (graph 1 K p) → ∃ q ≥ 1, HappyCell (graph 1 (K+1) q)` — the file's stated goal, left as a definition (unproven); also `FourPowerCanonicalHappyTarget`, `FourPowerDigitOverlap` (equivalent reformulations).
- main content: reduction chain around the happy-propagation problem: graph_happy_iff_consecutive_digit_two (Happy ⇔ digit 2 present and survives the x4 step); four_power_canonical_target_iff_digit_overlap / iff_direct_existence (the canonical target ⇔ digit overlap ⇔ direct existence of a happy cell on the next sheet); digit-overlap verified at bases 5, 6, 8; support cutoff 4^(K+2)+1 lemmas (digit zero / graph neutral at cutoff); latent_vertical_future_packet and future_bad_of_no_relocated_happy (if no relocated happy exists the future is bad).
- name-vs-content: "relocation" accurate — it relocates the open propagation problem, it does not solve it.
- gaps: FourPowerHappyPropagation itself is NOT proven here (it is the Erdős-type propagation on 4^K ternary digits); only equivalences and small-base checks.

### GSTGeometricRealizationStage2E.lean (304 lines)
- decls: 9 theorems, 4 defs (+2 structures counted: RationalVectorSpace, ClassicalHodgeData, Stage2EClassRealization, Stage2ECompactRealization), 0 axioms, 0 sorry, 6 #print axioms
- hypotheses (hypothesis-records, all unproven input packets):
  - ClassicalHodgeData V: `cohomology : Nat → RationalVectorSpace`, `hodgePP : ∀ p, Submodule ℚ (cohomology p)`, `cycleClass : ∀ p, codimensionCycles V.X p →ₗ[ℚ] cohomology p` — the intended rational cohomology, (p,p)-Hodge subspace and cycle-class map as abstract data (no surjectivity field, deliberately).
  - Stage2EClassRealization V H p N: `realization : CodimensionHodgeRealization N p V.X (H.cohomology p)`, `hodge_eq : realization.hodge = H.hodgePP p`, `cycleClass_eq : realization.cycleClass = H.cycleClass p` — assumes the Stage-2D finite-coordinate realization matches the intended classical semantics.
  - Stage2ECompactRealization: rank-free analogue with `hodge_iff : realization.isHodge alpha ↔ alpha ∈ H.hodgePP p`.
- main content: reduction architecture — ClassicalHodgeStatement V H := ∀ p, H.hodgePP p ≤ range (H.cycleClass p); hodge_class_has_classical_cycle (certificate ⇒ witness); classicalCycleSelector (choice-based right inverse) + spec; classical_hodge_of_stage2e_family / _obligation; UniversalClassicalHodgeStatement and its family theorem; Stage2ERealizationObligation / Stage2ECompactRealizationObligation record the remaining obligation as named Props.
- name-vs-content: honest — file is explicitly a plug-in socket, not a proof of the classical statement.
- gaps: no ClassicalHodgeData instance for a real variety exists; the realization certificates/obligations are exactly the unproven geometric content (the whole Hodge conjecture reduced to them).

### GSTGraphV2PerfectPowerBlockProbe.lean (302 lines)
- decls: 14 theorems, 3 defs, 0 structures, 0 axioms, 0 sorry, 4 #print axioms
- hypotheses: none (unconditional arithmetic on the graph tables)
- main content: probe laws for perfect-power blocks: graph_phase_prefix_positive_of_happy / nonpositive_of_bad (Happy cell ⇒ positive base-3 weighted phase pressure below that row; bad column ⇒ nonpositive); weightedPhaseColumnPrefix_eq_sum; digit3 weighted prefix exact identities (nat/int); graph_phase_column_exact / graph_phase_window_exact / graph_phase_digit_window_boundary_exact (exact window sums of digit/carry/phase); canonical_power_origin_happy_iff (canonical block origin Happy characterization).
- name-vs-content: honest arithmetic "probe"; no geometric content.
- gaps: none internally; relevance to Hodge is only via the GST narrative.

### GSTClassicalHodgePiOneWordCyclicSeedOmniverseFinale.lean (289 lines)
- decls: 9 theorems, 0 defs, 1 structure (hypothesis-record), 0 axioms, 0 sorry, 5 #print axioms
- hypotheses: CanonicalOneWordCyclicSeedPacket G alpha — fields: `spectral : ProjectiveWordSpectralFamily G (Fin (liveRank alpha))` (imported hypothesis-record), `coefficient_ne_zero : ∀ i, coefficient i ≠ 0`, and the load-bearing `seed_class : H.cycleClass p seedCycle = ∑ i, coefficient i • (classicalHodgeBasis V H p (liveBasisIndex alpha i)).1` — ASSUMES a native codimension-p cycle whose class is the all-nonzero-coefficient combination of alpha's live Hodge basis sheets (an algebraicity assumption of Hodge-conjecture strength for that combination); capstone hypothesis `packet : ∀ q, ∀ alpha ≠ 0, Nonempty (CanonicalOneWordCyclicSeedPacket G alpha)`.
- main content: from the cyclic seed: cyclic_seed_atomic (the combination lies in the point cycle-class span), live_basis_algebraic / support_basis_algebraic (spectral operator's cyclic-seed extraction ⇒ each live Hodge basis sheet is algebraic), target_cycle (∃ Z, H.cycleClass p Z = alpha.1); oneWordCyclicSeed_pi_fullOmniverse_crown bundles the cycle witness with N-cohomology basis existence, sector/branch-graph/higher-causal certificates, recoordination naturality, and the limitless transfer address; bigradedBettiHodge_of_oneWordCyclicSeedPackets: the packet family for all q ⇒ BigradedBettiHodgeStatement V H.
- name-vs-content: "OMNIVERSE FINALE" is a crown-of-crowns name for what is a conditional derivation whose main hypothesis is essentially the Hodge conjecture restated through a cyclic seed.
- gaps: no instance of CanonicalOneWordCyclicSeedPacket is ever constructed from geometry (seed_class is exactly the missing algebraicity); also relies on imported GeometricCycleClassSpine and ProjectiveWordSpectralFamily records.

### GSTClassicalHodgePrincipalCutSpectralFusion.lean (285 lines)
- decls: 8 theorems, 1 def, 0 in-file structures, 0 axioms, 0 sorry, 6 #print axioms
- hypotheses: imported hypothesis-records `G : GeometricCycleClassSpine V H`, `R : ClosedCorrespondenceWindowRealization G W` (a realized spectral correspondence word), `S : NativeHodgeOrbitSeed` (synchronized algebraic seed cycle); explicit conditions `hCoh : (G.principalCutPair q).cohomologyOperator (H.cycleClass q (codimensionPointCycle …)) ≠ 0` and `hcover : ∀ j with nonzero coordinate, ∃ i, W.basisIndex i = j ∧ SeedVisible R (…) i` (the seed covers alpha's finite live support with nonzero coordinates).
- main content: spectral extraction by polynomial functional calculus: extractedBasisCycleFromSeed = (s·c)⁻¹ • linearPolyEval (realizedWordPair R.word).cycleOperator (W.augmentedIsolatorPolynomial i) S.cycle with exactness theorem extractedBasisCycleFromSeed_spec (extracts the exact requested Hodge basis sheet from a visible synchronized algebraic seed); visibleSeed_basis_mem_cycleClass_range / visibleSeed_window_algebraic; target_mem_cycleClass_range_of_supported_basis_algebraic / of_seed_spectral_coverage and target_cycle_of_seed_spectral_coverage (finite-support linearity reconstructs the target class); principalCut_nonzero_spectral_basis_cycle / _target_cycle (nonzero principal-cut action + coverage ⇒ actual codimension-(q+1) cycle representing alpha).
- name-vs-content: "fusion" accurate — it fuses the principal-cut seed route with the spectral amplifier, all conditional.
- gaps: ClosedCorrespondenceWindowRealization and the nonzero principal-cut cohomology action are unproven inputs; the coverage condition hcover is a strong unverified geometric hypothesis.

### GSTClassicalHodgeGradedFiniteClosedCorrespondence.lean (278 lines)
- decls: 8 theorems, 0 defs, 1 structure (hypothesis-record), 0 axioms, 0 sorry, 3 #print axioms
- hypotheses: GradedCorrespondencePointNaturality K H p q — fields: `cohomologyOperator : H^(2p) →ₗ H^(2q)` and `point_natural : ∀ x : CodimensionPoint V.X p, H.cycleClass q (K.gradedNativePointImage q x) = cohomologyOperator (H.cycleClass p (codimensionPointCycle V.X p x))` — assumes the cohomological action of a finite closed correspondence is cycle-class natural ON POINT GENERATORS only.
- main content: unlocks the graded (source codimension p → target codimension q) structure of FiniteClosedCorrespondence: gradedTransition_self, gradedNativePointImage_self; constructs gradedPresentationOperator / gradedNativeCycleOperator from finite left-fiber enumeration + right-image codimension-q filtering + linear extension through the compact cycle/presentation equivalence; gradedNativeCycleOperator_has_finite_target; cycleClass_natural upgrades the pointwise law to the full commuting square (compact point normal form), manufacturing a GradedCycleClassOperatorPair.
- name-vs-content: accurate — a genuine construction with one pointwise-naturality hypothesis.
- gaps: the pointwise naturality packet is unproven geometry; no instance of FiniteClosedCorrespondence with the required cohomological action is constructed.

### GSTClassicalHodgeLocalCyclicCriterion.lean (275 lines)
- decls: 9 theorems, 2 defs, 1 structure (hypothesis-record), 0 axioms, 0 sorry, 4 #print axioms
- hypotheses: LocalCyclicRealization V H p alpha — fields: `spectral : ClassicalHodgeSpectralOperator V H p (HodgeSupportIndex alpha)`, `spectral_basisIndex : spectral.basisIndex = HodgeSupportIndex.include`, and the load-bearing `seed_mem_atomic : (∑ i : HodgeSupportIndex alpha, (classicalHodgeBasis V H p i.1).1) ∈ pointCycleClassSpan p (H.cycleClass p)` — ASSUMES the sum of alpha's live Hodge basis directions is algebraic; equivalently SupportAlgebraicityCertificate per support.
- main content: rank-free local cyclic criterion: hodgeClass_eq_support_sum (alpha = finite combination of its live basis vectors); live_basis_mem_atomic (Lagrange projectors of a spectral observable with distinct eigenvalues on live directions extract each live basis vector from the algebraic seed); class_mem_atomic ⇒ alpha algebraic; bigradedBettiHodge_of_local_cyclic_realizations (packet per alpha ⇒ BigradedBettiHodgeStatement); bigradedBettiHodgeStatement_iff_supportCertificates (exact iff reformulation).
- name-vs-content: accurate as a criterion — but the criterion's seed algebraicity is precisely the unproven Hodge content.
- gaps: no LocalCyclicRealization is ever constructed; the file explicitly removes finite-dimensionality hypotheses but not the algebraicity assumption.

### GSTInfiniteFourPowerNavigation.lean (263 lines)
- decls: 15 theorems, 1 def, 0 structures, 0 axioms, 0 sorry, 12 #print axioms
- hypotheses: NAMED OPEN PROP `four_power_happy_climb : ∀ K ≥ 8, ∃ p ≥ 3, HappyCell (carry4 (4^K) p) (digit3 (4^K) p)` — unproven; every headline theorem takes it as hypothesis `hClimb`.
- main content: divisibility bridges (6^k ∣ 4^t(x−y) ↔ 3^k ∣ (x−y) ∧ 2^(k−2t) ∣ (x−y), dyadic/triadic shadow versions); power_width_three_exact_conservation; u-jump sign dichotomy (negative iff happy local, nonnegative iff not); climbFireRow characterization theorems (ge three, happy, minimal, before-climb not happy); happy_to_creation_certificate; gst_four_power_navigation_universal (hClimb ⇒ ∀ k ≥ 5, k ≠ 7, an explicit digit-2 witness p with the creation dichotomy — cases 5,6 by norm_num); a root-level compatibility export to CreationCertificate.
- name-vs-content: "navigation universal" is conditional on the unproven climb — the Erdős-type digit problem remains the input.
- gaps: four_power_happy_climb is exactly the open ternary-digit propagation; k = 7 is excluded by hypothesis.

### GSTGraphV2HandwrittenExponentialCascade.lean (259 lines)
- decls: 18 theorems, 6 defs, 0 structures, 0 axioms (the grep hit "axiom" at line 154 is the tail of a doc-comment: "…not a terminal-space axiom. -/"), 0 sorry, 6 #print axioms
- hypotheses: none
- main content: the handwritten exponential cascade as a finite family indexed by K: originPrefix/originSuffix (n % 3^K, n / 3^K), uPhaseShift = 3^t·prefix, uTailEnergy = 4^(3^(t+K)·suffix); exact block split (n = 3^K·suffix + prefix ⇒ 4^(3^t·n) = (phase-shifted energy)·tail energy); perfect_power_u_block_exact / u_absolute_energy_exact; graph observable/horizontal-axis transport exactness; navigationNullspace flux identity (4·(R % 3^p) = nullspace + 3^p·carry); eventual-zero laws (originSuffix_eventually_zero, uTailEnergy_eventually_one, suffix zero / energy one for large cut); additivity of all five coordinates.
- name-vs-content: honest arithmetic; "exponential cascade" = iterated 3-adic digit-block factorization of 4^(3^t·n).
- gaps: none internally; pure ℕ identities feeding the GST graph narrative.

### GSTClayOfficialV2.lean (255 lines)
- decls: 11 theorems, 1 def, 0 structures, 0 axioms, 0 sorry, 7 #print axioms
- hypotheses: none in-file (builds on GSTHodgeAssault(V2)/GSTClayOfficial finite-carrier theorems)
- main content: rationalized finite GST classification: ratCycleClass p = 0 for p ≥ 3; rational_hodge_all_weights (every integral GST Hodge class f is a rational multiple of the weight-p cycle class for ALL p — zero-sector above weight 2); on live weights p < 3 the coefficient is exactly the diagonal coordinate (exact/unique); IsRationalHodgeClass on RatCoef with off-diagonal vanishing, direct coefficient theorems; rational_v2_crown bundling the classification.
- name-vs-content: "RATIONAL HODGE LAYER V2" continues the Clay-flavored naming, but the statement is the ℚ-ification of the 12-cell GST lattice classification (WaveCoef/RatCoef), not the Clay conjecture.
- gaps: same as all finite-carrier layers — no cohomology of varieties appears; the Clay-shaped statement is about a finite free module.

### GSTGraphV2InfiniteControllerBridge.lean (249 lines)
- decls: 11 theorems, 1 def, 0 structures, 0 axioms, 0 sorry, 1 #print axioms
- hypotheses: none (unconditional arithmetic transport)
- main content: transplants the all-Nat controller state (GSTV2.CoupledState) from a physical width-N rectangle of the infinite graph: graphCoupledState field-exactness theorems (childTail % 3 = left-edge digit, parent digit, invariant, step exactness, orbit exactness ∀K, rebase/add-action laws); control-flow results graph_right_bad_to_seededBadTrace, graph_infinite_bad_control, graph_child_happy_to_controller, graph_child_happy_latent_transfer.
- name-vs-content: honest bridge arithmetic between two GST graph modules.
- gaps: none internally; no mathematical content beyond ℕ identities.

### GSTInfiniteCoupledLedger.lean (247 lines)
- decls: 9 theorems, 3 defs, 1 structure (InfiniteCoupledLedger — a Prop-record DISCHARGED by infinite_coupled_ledger from CoupledInvariant, not an assumption), 0 axioms, 0 sorry, 0 #print axioms
- hypotheses: none assumed (hA : 0 < A, h0 : CoupledInvariant A initial are the construction's premises; the ledger structure itself is proven)
- main content: past/future information ledger for the seeded x4 stream: seededPast; seeded_mass_past_future (D + 4X = seededPast + 3^K·(affineCarry + 4·(X/3^K)) at every depth); coupledOrbit_childCarry_affine_exact; coupled_state_full_future_equation; parent/child ledger synchronization (coupledOrbit_past_synchronization, past_residue_exact, past_reconstruct_exact); coupled_ledger_reconstruction_crown; infinite_coupled_ledger (every exact coupled controller carries the ledger).
- name-vs-content: honest conservation arithmetic of ternary digit streams.
- gaps: none internally; "information ledger" is ℕ bookkeeping, not information theory.

### GSTClassicalHodgeCMGSTNativeBasisCompiler.lean (237 lines)
- decls: 6 theorems, 0 defs, 1 structure (large hypothesis-record), 0 axioms, 0 sorry, 1 #print axioms; header note "NEEDS CI RUN LATER"
- hypotheses: CMGSTNativeSheetProgram G q j — one packet per target basis sheet with fields: source scheme + sourceData, pointKernel : FiniteCrossCarrierPointKernel source V …, betti map, `geometricPointLaw : RealizesFinitePointKernelOnBetti pointKernel betti`, gstProgram : GradedCorrespondenceProgram V H entryCodim q, active : Finset Nat, sourceCycle, coefficient : Nat → K, and the load-bearing `basisPeriodExpansion`: coordinates of the target classical Hodge basis tensor (in the chosen ℚ-basis) EQUAL `∑ a ∈ active, coefficient a •` coordinates of `gstProgram.cohomologyEval G (betti (sourceData.cycleClass sourceCodim (sourceCycle a)))` — a finite period-expansion of each target Hodge basis sheet through the GST program evaluated on actual source cycles, with coefficients in an extension K/ℚ. Capstone supply hypothesis: `CMGSTNativeBasisProgramSupply : ∀ q j, Nonempty (CMGSTNativeSheetProgram G q j)`.
- main content: nativeTerm/nativeBasisCycle (finite rational combination of GST program outputs, coefficients descended from K); nativeTerm_cycleClass (naturality DERIVED from point-kernel + program calculus); nativeBasisCycle_spec (constructed cycle has EXACTLY the classical Hodge basis class); one_basis_sheet_is_algebraic; basisCycleSupply_of_CM_GST_programs (supply ⇒ HodgeBasisCycleSupply); bigradedBettiHodge_of_CM_GST_programs (supply ⇒ BigradedBettiHodgeStatement via the Stage-2G landing).
- name-vs-content: accurate as a compiler; the name suggests CM/Kuga-Satake/Gale inputs which exist only as the packet's unproven fields.
- gaps: no CM surface / Clifford / Gale packet is ever constructed — "the existence of suitable packets … is a mathematical construction task, not a postulate added in this module"; the basisPeriodExpansion field is exactly the unproven arithmetic input.

### GSTFourPowerDirectAdditionCarry.lean (235 lines)
- decls: 17 theorems, 3 defs, 0 structures, 0 axioms, 0 sorry, 8 #print axioms
- hypotheses: none
- main content: elementary ternary-carry arithmetic for multiplication by 4: directCarry4 (R p) = (4·(R % 3^p))/3^p < 4; exact forward recurrence directCarry4 R (p+1) = (directCarry4 R p + 4·digit3 R p)/3; decomposition directCarry4 = previous digit + binaryCarry (< 2); digit of 4R in terms of digit + carry; forbidden-edge characterizations (two_shift_eq_two_iff_forbidden_edges, common_two_row_iff_forbidden_edges); binary state machine (binaryState, next_exact, initial states for 4^K).
- name-vs-content: honest — pure ℕ division/modulo recurrences.
- gaps: none internally.

### GSTClassicalHodgeIntegralLefschetzTransport.lean (227 lines)
- decls: 7 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry, 5 #print axioms
- hypotheses: none in-file (finite ℤ-square linear algebra)
- main content: integral Lefschetz sheet transport on the finite GST square: sheetDiagonalAtom_eq_smul_basis; sheetAtom_lefschetz_forward_exact (source sheet r → target sheet s at unique live time 2(s−r), target coefficient = source × central binomial choose(2(s−r), s−r)); forward scalar ≠ 0 and result ≠ 0; wrong times vanish; backward_request_reflects_forward (Poincaré reflection); squarePureDual_sheetAtom.
- name-vs-content: accurate — concrete integer movement stage of the matrix-unit arsenal, i.e., binomial-coefficient algebra in a finite module.
- gaps: purely GST-square content; "classical Hodge"/"Lefschetz" refer to the finite lattice analogue, not geometry.

### GSTClassicalHodgeConcreteRankFreeGeneration.lean (226 lines)
- decls: 7 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry, 5 #print axioms
- hypotheses: none beyond `alpha ≠ 0` (cohomological linear algebra)
- main content: rank-free generation of arbitrary target Hodge basis directions from one live source coordinate of a nonzero Hodge class: chosenLiveSource (a live coordinate with nonzero coefficient); augmented window; denominator clearing; GST total projector/Lefschetz/Poincare matrix unit from live slot to target slot; arbitraryTargetGSTOutput_exact + read-back + normalization; concreteBasisGenerator_eq_basis (the normalized output is EXACTLY the target basis vector); hodgeClass_eq_sum_concreteGenerators; concrete_rank_free_generation_crown.
- name-vs-content: accurate — "generation" happens in cohomology/address space via finite operator words; it does NOT produce algebraic cycles.
- gaps: the GST word moves cohomology vectors; algebraicity of the moved vectors is NOT established here (that requires the seed/realization hypotheses in other modules).

### GSTClassicalHodgePrimitiveArsenalRationalization.lean (223 lines)
- decls: 6 theorems, 2 defs, 0 structures, 0 axioms, 0 sorry, 4 #print axioms
- hypotheses: none (finite matrix identifications)
- main content: rationalization of the finite primitive arsenal: spectralProjectorMatrixCoeff = the integer code-sector projector's matrix coefficient (sheetSpectralProj_basis_atom, spectralProjectorMatrixCoeff_eq, rationalizedSheetSpectralProj_eq); poincareMatrixCoeff / rationalizedWorldPoincare_eq (rational coordinate transport of the native Poincaré involution); diagonalLefschetzQ_basis (from native worldAct L^t coefficients); primitive_arsenal_rationalization_crown.
- name-vs-content: accurate — every rational operator is the ℚ-extension of an already-constructed integer GST world operator.
- gaps: internal to the finite GST square universe; no geometry.

### GSTClassicalHodgeOmniversePointStrictRelationFinale.lean (214 lines)
- decls: 3 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry, 3 #print axioms
- hypotheses (all unproven imported packets + one raw relation): `G : GeometricCycleClassSpine V H`, `D : ProjectiveDegreeTraceSemantics V H`, and per target sheet j: `K : SchemeBiFiniteClosedCorrespondence V` (an actual bi-finite closed correspondence), `T : RightFiniteBettiTrace H.analytification K (2p)`, `C : PointCycleCompatibility K T`, plus the load-bearing raw strict relation `hrel : BettiRelated H.analytification K (2p) (pointApexSeed G D p x).hodge.1 (sourceCoefficient • targetBasis)` — i.e. leftPullback(apex) = rightPullback(sourceCoefficient·targetBasis) for each requested target sheet.
- main content: targetCycle_ofPointStrictRelation (from one actual codimension-p projective point apex + raw bi-finite Betti relation, constructs the target basis cycle through the synchronized native operator); pointStrictRelationTargetCycle_spec (exact cycle-class specification); hodge_weight_of_pointStrictRelations (family over j ⇒ the weight-p Hodge statement).
- name-vs-content: honest about its reduced frontier ("one actual point + one raw relation per sheet") but "OMNIVERSE FINALE" overstates a conditional transfer theorem.
- gaps: the bi-finite correspondences K with their Betti traces, point-cycle compatibility and the raw BettiRelated relations are all unproven geometric inputs; the apex seed machinery (pointApexSeed) rests on the spine record.

### GSTGraphV2UnifiedVerticalTelescope.lean (213 lines)
- decls: 8 theorems, 1 def, 0 structures, 0 axioms, 0 sorry, 3 #print axioms
- hypotheses: none
- main content: vertical telescope arithmetic: carryWord_vertical_balance (macro x4/base3 balance: carryWord + 4^N·digit(start) = digit(start+N) + 3·carryWord(p+1)); unifiedState parent-offset/core step exactness; unified_equationIII_graph_closed and unified_equationIII_vertical_telescope (telescoping closure of Equation III); verticalFluxWindow closed/add-exact/one.
- name-vs-content: honest ℕ telescope identities.
- gaps: none internally.

### GSTClassicalHodgeGSTRationalCorrespondenceExactFinale.lean (206 lines)
- decls: 4 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry, 3 #print axioms
- hypotheses: `G : GeometricCycleClassSpine V H`, `M : NativeMassCycleClassBridge V H`, families `A p j : RationalClosedCorrespondenceCycle V`, `T p j K` operators with `hT : ∀ K, K.RealizesAmbientOnPoints (T p j K)` (per-correspondence point realization), and the load-bearing transfer relation `hA : (rationalPair (A p j) …).cohomologyOperator (globalSpineOrbitSeed G M p).hodge.1 = (target basis class combination)` — assumes the rational correspondence's cohomological action carries the canonical spine seed to each requested target basis sheet.
- main content: canonicalSpineTargetCycleOfRationalCorrespondence (apply the native rational-correspondence operator to the canonical nonzero projective-spine cycle, divide by the nonzero source coordinate) + _spec (exact target class); every_basis_mem_cycleClassRange_of_rationalCorrespondences; bigradedBettiHodge_of_rationalCorrespondences (family ⇒ BigradedBettiHodgeStatement); everyHodgeClassIsFiniteRationalCombination_of_rationalCorrespondences.
- name-vs-content: "EXACT FINALE" is a conditional transfer through rational correspondence cycles; the geometric realization (hA/hT) is assumed.
- gaps: RealizesAmbientOnPoints and the hA transfer equations are unproven; the spine/bridge records are unproven imports.

### waves/GSTNCohomologyV2.lean (205 lines)
- decls: 11 theorems, 5 defs, 0 structures, 0 axioms, 0 sorry, 5 #print axioms
- hypotheses: none (unconditional combinatorics on digit-tower lists)
- main content: N-cohomology V2: towerWindow nil/nonempty iff depth zero/positive; canonicalNCohoBasis; ncoho_rank_unconditional (rank = holes without ignition/nonemptiness hypotheses); weightedInterference/Horizontal/Vertical/Source with weighted_interference_decomposition (interference = horizontal + vertical − source); interference_is_weighted / decomposition_absorbed; shape_signature_exact_cut; digit_two_mode_classification; two_wave_frame_refines_absorbed; wave_II_v2_crown.
- name-vs-content: "cohomology" here is a rank/counting theory of digit-tower windows — finite combinatorics, no topology.
- gaps: none internally; naming suggests more than the combinatorial content.

### GSTFourPowerDirectHappyBridge.lean (200 lines)
- decls: 10 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry, 10 #print axioms
- hypotheses: imported named Prop `FourPowerDirectExistence` (from GSTFourPowerDirectExistence, other file) taken as hypothesis `hDirect` in the propagation/forcing theorems; affine-branch hypotheses in the branch lemmas.
- main content: bridges arithmetic witnesses to physical Happy rows: commonTwo_to_physical_happy_row (a CommonTwo K witness — digit 2 in both 4^K and 4·4^K — IS a physical Happy row at the same q, carry forced to 0 or 3); affine branch versions (0,2 and 2,1 branches force relocated physical happy); four_power_happy_propagates (hDirect ⇒ happy propagation K → K+1); commonTwo_iff_physical_happy_row (exact equivalence CommonTwo K ↔ ∃ physical Happy row); directExistence_iff_physical_happy_forcing (FourPowerDirectExistence ↔ ∀ K ≥ 5, K ≠ 7, ∃ positive-row Happy).
- name-vs-content: honest bridging/arithmetic; propagation remains conditional on the unproven FourPowerDirectExistence.
- gaps: FourPowerDirectExistence itself is the open Erdős-type statement (not proven in this batch).

### GSTClassicalHodgeIntegralLiveSupport.lean (197 lines)
- decls: 10 theorems, 1 def, 0 structures, 0 axioms, 0 sorry, 5 #print axioms
- hypotheses: none (finite-support ℚ-arithmetic)
- main content: commonDenominator (product of reduced denominators on a Finsupp's support) with positivity, divisibility, integrality of scaled coordinates; integralize_spec (scaling converts the live support to integer coefficients); recover_from_integralize / integralHodgeAddress_recovers / _ne_zero (division by the same nonzero integer recovers the original rational state exactly, nonzero preserved); integral_live_support_crown.
- name-vs-content: accurate — the ℤ/ℚ interface between rational Hodge states and the integer GST cosmology.
- gaps: none internally; purely coefficient bookkeeping.

### GSTClassicalHodgeConcreteSheetMatrixUnit.lean (196 lines)
- decls: 7 theorems, 5 defs, 0 structures, 0 axioms, 0 sorry, 4 #print axioms
- hypotheses: none (finite square algebra)
- main content: realizes abstract rational matrix units by concrete GST operator words: rationalizeWorld, rationalSheetProjector, forwardSheetWord (projector → unique Lefschetz power → projector), forwardNormalizeScalar (central binomial), forwardSheetMatrixUnit with _ne_zero, _target, _off_target, _exact (result = source coefficient on the target sheet, zero elsewhere), _nonzero.
- name-vs-content: accurate — concrete word realization of matrix units in the finite GST operator calculus.
- gaps: internal to the GST square universe.

### GSTClassicalHodgePresentationLanding.lean (193 lines)
- decls: 6 theorems, 0 defs, 1 structure (hypothesis-record), 0 axioms, 0 sorry, 6 #print axioms
- hypotheses: FiberedBasisPresentationBridge V H p — fields: `basisPresentation : ClassicalHodgeBasisIndex V H p → FiniteCodimensionPresentation V.X p` and `basisPresentation_spec : ∀ i, H.cycleClass p (realizeFiniteCodimensionPresentation V.X p (basisPresentation i)) = (classicalHodgeBasis V H p i).1` — ASSUMES each Hodge basis direction is the class of an explicit finite rational combination of codimension-p scheme points.
- main content: hodge_class_has_cycle_of_finite_presentations (bridge ⇒ cycle witness for every (p,p) class); bigraded_hodge_of_finite_presentation_family (bridge ∀p ⇒ BigradedBettiHodgeStatement); basisPresentation_spec_iff_point_class_sum (spec = concrete finite ∑ q • cycleClass(point) equation); fiberedBasisPresentationBridge_iff_point_class_sums (bridge Nonempty ⇔ family of point-class equations — "removes the last abstract codimensionCycles existential"); bigraded_hodge_of_point_class_sum_family; finite_presentation_projects_to_limitless_cosmos.
- name-vs-content: accurate — the landing of finite presentations into the fibered basis; the honest quote "the concrete equation that remains to be established geometrically".
- gaps: no FiberedBasisPresentationBridge instance exists — the point-class equations are exactly the unproven geometric content (equivalent strength to the target statement).

### GSTClassicalHodgeNativeGeneratorNaturality.lean (190 lines)
- decls: 7 theorems, 0 defs (HasNativePointLifts is a def), 1 structure (NativePointTransition — hypothesis-record: `imageCycle : CodimensionPoint X p → codimensionCycles X p` with `imageCycle_spec : ∀ x, cl (imageCycle x) = T (cl (codimensionPointCycle X p x))`), 0 axioms, 0 sorry, 6 #print axioms
- hypotheses: NativePointTransition packet (a native cycle for each point whose class is the transformed point class) — but used as an equivalent reformulation, with the three-way equivalence below; no unconditional instance.
- main content: equivalence machinery on smooth projective carriers: HasNativePointLifts T (every T(cl[x]) is a cycle class); nativePointLifts_of_atomicSpanStable / finitePointTransitions_of_nativePointLifts / atomicSpanStable_iff_nativePointLifts; hasNativePointLifts/atomicSpanStable from a NativePointTransition; smoothProjective_atomicStable_iff_nativePointLifts (global invariance of the atomic cycle-class span ⇔ generatorwise native algebraic-cycle lifts — compactness converts native cycles to finite rational point presentations).
- name-vs-content: accurate — a genuine equivalence-of-interfaces lemma.
- gaps: neither side is instantiated for actual cohomology operators; the equivalence is the content, not the stability itself.

### GSTCanonicalSevenAxisBridge.lean (185 lines)
- decls: 11 theorems, 5 defs, 1 structure (Vertex — pure data record: 8 Nat fields), 0 axioms, 0 sorry, 5 #print axioms
- hypotheses: none
- main content: the base seven-axis arithmetic state layer: Space (null/altMinus/gstPlus), spaceOfCarry, digit3 R p = R/3^p % 3, carry4 R p = (4·(R % 3^p))/3^p; carry4_forward_exact and digit3_mul_four_exact recurrences; canonical_cell_exact (cell = event + 3·carry update balance); bounds carry < 4, digit < 3; event = d + 3·outDigit with event_balance_exact; the equivalence crown: HappyCell ⇔ event = 8 ⇔ crossDensity = 105.
- name-vs-content: honest arithmetic layer ("non-Euclidean seven-axis vertex" is a data bundling of digit/carry/descent coordinates).
- gaps: none internally; foundation for all GST graph files.

### GSTClassicalHodgeActualNoncommutativeNativeFrame.lean (184 lines)
- decls: 7 theorems, 0 defs (several noncomputable defs in body), 0 structures, 0 axioms, 0 sorry, 3 #print axioms
- hypotheses: `G : GeometricCycleClassSpine V H` (imported unproven spine record), `E/F : RealizedCorrespondenceExpr V H p` (realized correspondence expressions — imported packets), `[FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]`, and `hdet : (geometricWordFrameMatrix G words).det ≠ 0` (full-rank frame of genuine noncommutative words).
- main content: nativeWord/nativeFiniteWordFrame with nativeWord_cycleClass (exact Betti realization: H.cycleClass p (nativeWord G E) = bettiWord G E); bettiFiniteWordFrame_has_native_cycle / _is_hodge; nativeGeometricCommutator (E∘F − F∘E) with exact cycle class and Hodge type; native_cycle_of_nonzero_geometric_word_frame (nonzero determinant ⇒ every class alpha is the cycle class of an explicit matrix-inverted native combination).
- name-vs-content: accurate and honest — "its existence for arbitrary varieties is not assumed or established by this file".
- gaps: full-rank geometric word frames for arbitrary varieties neither assumed nor constructed; the spine and realized-expression packets are unproven imports.

### GSTClassicalHodgeFiberedNativeDescentSeparation.lean (179 lines)
- decls: 7 theorems, 1 def, 0 structures, 0 axioms, 0 sorry, 4 #print axioms
- hypotheses: none beyond context records (uses the fibered native pullback machinery)
- main content: descent separation principle: NativeDescends T := ∃ native endomorphism A with toNativeCycle (T Φ) = A (toNativeCycle Φ); liftNativeOperator_descends (lifted native operators descend tautologically); nativeDescends_preserves_nativeKernel; codimensionPointCycle_ne_zero; atom_sub_atom_nativeFace_zero; multiplicityMatrixUnit_kernelWitness and multiplicityMatrixUnit_not_nativeDescends (a bare multiplicity matrix unit FAILS to descend when two multiplicity labels lie over the same nonzero native point atom); tensorWord_not_nativeDescends_of_nonzero.
- name-vs-content: accurate — an obstruction/no-go lemma preventing forgetting the native coordinate.
- gaps: purely structural; no Hodge content claimed.

### GSTClassicalHodgeConcreteFailureDichotomy.lean (177 lines)
- decls: 6 theorems, 0 defs, 1 structure (TwoSlotEscape — a witness record for the dichotomy's second branch: source/target basis indices, `alpha_algebraic : alpha ∈ AlgebraicFiber`, `escapes : liftFiniteHodgeOperator … (forwardArsenalWord …) alpha ∉ AlgebraicFiber` — an OUTPUT of the dichotomy, not an input assumption), 0 axioms, 0 sorry, 4 #print axioms
- hypotheses: none assumed (the dichotomy is proven); saturation theorems take explicit stability/seed premises
- main content: twoSlotWord_apply_eq_matrixUnit (the fixed 2-slot GST projector/Lefschetz word IS the corresponding rank-free matrix unit pointwise); twoSlotStable_iff_rankFreeInvariant; proper_algebraicFiber_zero_or_twoSlotEscape (if the algebraic fiber A_p ⊊ Hodge fiber then A_p = 0 OR an explicit TwoSlotEscape exists — failure reduced to two concrete modes); algebraicFiber_eq_top_of_seed_and_twoSlotStable (one algebraic seed + stability under the single two-slot word ⇒ A_p = whole fiber).
- name-vs-content: accurate — a genuine dichotomy reducing the closing task to ruling out two explicit failure modes.
- gaps: ruling out the two failure modes (zero algebraic fiber / escape) for actual varieties is exactly the remaining unproven geometric work.

### GSTGraphV2FluxScratch.lean (176 lines)
- decls: 10 theorems, 4 defs, 0 structures, 0 axioms, 0 sorry, 0 #print axioms; carries a chronological git-history header (branch sol_physical-phase-crossing-surgery, 2 commits)
- hypotheses: none
- main content: local information flux: gstCellMassV2S = C + 4d ∈ {0..11}, output = mass % 3, next carry = mass / 3; exact cell conservation (mass = output + 3·nextCarry); survive/create/destroy event types = exact disjoint mass sectors; parent mass from shared child state; mod-11 rotation law (gst_local_rotate_mass_mod11V2S); GSTBig2MassSpeciesV2S (mod-11 species invariant) closed under rotation and hitting survive within four steps.
- name-vs-content: honest "scratch" arithmetic (mod 3 / mod 11 event-sector classification).
- gaps: none internally; a scratch/experimental file by its own label.

### GSTClassicalHodgeCrossCarrierExplicitPointKernel.lean (170 lines)
- decls: 5 theorems, 1 def, 0 structures, 0 axioms, 0 sorry, 1 #print axioms; "NEEDS CI RUN LATER"
- hypotheses: the geometric law is the pointwise identity `RealizesFinitePointKernelOnBetti K B : ∀ x : CodimensionPoint V.X p, J.cycleClass q (realizeFiniteCodimensionPresentation W.X q (K x)) = B (H.cycleClass p (codimensionPointCycle V.X p x))` — cohomological push/pull agrees with the finite native target incidence cycle ON POINTS (used downstream as the `geometricPointLaw` packet field); the kernel K itself (FiniteCrossCarrierPointKernel) is imported point-incidence data.
- main content: CONSTRUCTS the cross-carrier native cycle map nativeOfFinitePointKernel by rational-linear extension of finite point incidence through the compact presentation equivalence; nativeOfFinitePointKernel_point (source atom ↦ finite target algebraic cycle); finitePointKernel_finite_sum (every action is a finite rational sum of assigned point cycles); pointKernel_realizes_iff_point_incidence (pointwise Betti identity ⇔ old global interface criterion); finitePointKernel_naturality (global naturality DERIVED from the finite kernel + one-point identities); finitePointKernel_normalized_period.
- name-vs-content: honest — the map is constructed, but the header concedes a finite point-incidence assignment "is not on its own a scheme-theoretic correspondence".
- gaps: Gysin/push-pull interpretation requires proving K comes from a genuine geometric incidence construction — unpaid; the pointwise Betti law is an unproven input.

### GSTClassicalHodgeSeparatorRelativeCoheightOne.lean (169 lines)
- decls: 3 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry, 3 #print axioms
- hypotheses: `hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)` (imported liveness condition for the point in projective space)
- main content: pure order lemma coheight_le_one_of_unique_strictAbove (element with exactly one strict point above has coheight ≤ 1); separatorSuccessor_lt_generic (the separator successor is strictly below the canonical generic point of the closure); pointClosureSeparatorSuccessor_coheight_one (Order.coheight of the separator successor = 1 exactly).
- name-vs-content: accurate — order theory applied to the point-closure lattice.
- gaps: rests on the ProjectivelyLiveSource hypothesis (unproven liveness input from another module).

### GSTFourPowerDirectResidue27.lean (165 lines)
- decls: 3 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry, 3 #print axioms
- hypotheses: none (residue-class hypotheses in the statements)
- main content: mod-27 (3³) classification of the row-three digit-two overlap: row_three_overlap_of_mod27_classes (K ≡ 14, 18, 19, 25 mod 27 ⇒ digit3 (4^K) 3 = 2 ∧ digit3 (4^(K+1)) 3 = 2, by periodicity pow4_digit_period); no_common_two_forbids_mod27_classes (converse exclusion); row_three_overlap_iff_mod27_classes (exact iff).
- name-vs-content: honest finite residue classification.
- gaps: covers only row three; the general Erdős-type overlap problem remains open.

### GSTResearchUniversalOrbitClosureLaw.lean (160 lines)
- decls: 4 theorems, 1 def, 0 structures, 0 axioms, 0 sorry, 3 #print axioms
- hypotheses: `G : GeometricCycleClassSpine V H` (imported unproven spine record); the local cyclicity criterion `SeedCyclicForActualGeometry` is a NAMED unproven target (deliberately not assumed); no Hodge algebraicity is postulated.
- main content: universal minimal geometric orbit law: native_orbit_minimal_among_actual_geometric_invariants (any Hodge subspace stable under all realized Hodge-compatible correspondences and containing the seed contains every constructible correspondence-word class); def SeedCyclicForActualGeometry; native_orbit_top_iff_seed_geometrically_cyclic (the constructed orbit = whole Hodge fiber ⇔ every invariant subspace containing the seed is everything — a LOCAL cyclicity target weaker than global irreducibility); hodge_cycles_from_one_geometrically_cyclic_native_seed (one geometrically cyclic native seed ⇒ the weight-p Hodge statement); local_cyclicity_of_global_geometric_irreducibility.
- name-vs-content: honest — header explicitly refuses to assert the cyclicity criterion ("doing so would assume the still-unproved Hodge algebraicity target").
- gaps: existence of a geometrically cyclic seed is exactly the open content; the spine record remains unproven.

### GSTClassicalHodgeCanonicalLimitlessNaturalityCrown.lean (155 lines)
- decls: 5 theorems, 1 def, 0 structures, 0 axioms, 0 sorry, 4 #print axioms
- hypotheses: (a) `CanonicalCosmicNaturality p : ∀ i j alpha, alpha ∈ AlgebraicFiber → liftCosmicWindowOperator (pairBasisIndex i j) (rationalCosmicMatrixUnit …) alpha ∈ AlgebraicFiber` — the single canonical limitless operator is compatible with the algebraic Hodge span (unproven operator law); (b) `hseed : AlgebraicFiber p ≠ ⊥` (one nonzero algebraic Hodge state); (c) for the full statement: `F : SeedPropagationFamily V H` with `h0 : F.seed 0 ∈ AlgebraicHodgeSubspace V H 0` and `h0ne : F.seed 0 ≠ 0`, plus naturality at every p.
- main content: not_limitlessCosmicEscape (naturality rules out the escape branch of the rank-free failure dichotomy); algebraicFiber_eq_top (nonzero seed + naturality ⇒ whole fiber algebraic); hodge_weight (the fixed-weight Stage-2G range statement rationalHodgeSubspace ≤ range cycleClass); propagatedSeed_ne_bot (cross-weight propagation of the base seed); bigradedBettiHodge (seed family + per-weight naturality ⇒ BigradedBettiHodgeStatement).
- name-vs-content: honest about being operator-compatibility laws, not surjectivity postulates; "CROWN" = capstone conditional.
- gaps: CanonicalCosmicNaturality and the weight-zero algebraic seed are the two unproven inputs; neither is constructed anywhere in this batch.

### GSTClassicalHodgeShiftedCyclePushforward.lean (155 lines)
- decls: 5 theorems, 1 def, 0 structures, 0 axioms, 0 sorry, 1 #print axioms
- hypotheses: none (uses Mathlib's AlgebraicCycle.map / pushforward support theorem; "no Hodge, cycle-class, intersection, or correspondence-realization premise is used")
- main content: the genuine projection half of the correspondence action Z ↦ p₂*(C · p₁*Z): relativeCodimensionWeight d x = coheight x − d as source weight, ordinary coheight as target weight; shiftedPushforwardRaw_support (support proof via Mathlib's locally-finite pushforward support theorem); shiftedPushforward_apply / _support — a codimension-(d+p) → codimension-p native pushforward on X×X → X.
- name-vs-content: accurate — a real Mathlib-based construction of the proper projection primitive.
- gaps: intersection/pullback half of the correspondence action remains a separate geometric construction.

### GSTClassicalHodgePrincipalCutGradedOperator.lean (150 lines)
- decls: 3 theorems, 0 defs (several noncomputable defs in body), 0 structures, 0 axioms, 0 sorry, 3 #print axioms
- hypotheses: `[IrreducibleSpace V.X]` only
- main content: linearizes the projective principal cut into a genuine native graded operator: zeroToOnePointKernel (codim-0 point ↦ finite codim-1 presentation from its point-specific positive-degree projective separator); zeroToOnePresentationOperator_single (linear extension on Finsupp); zeroToOneNativeOperator_point / generator_crown (on each codimension-0 point cycle it outputs principalCutCycle — an ACTUAL geometry-built codimension 0 → 1 native cycle operator, independent of Hodge semantics).
- name-vs-content: accurate — a real construction.
- gaps: the cohomological side (comparison with Lefschetz transport) is deferred to later naturality modules.

### GSTClassicalHodgeActualGeometricIrreducibility.lean (144 lines)
- decls: 3 theorems, 2 defs, 0 structures, 0 axioms, 0 sorry, 3 #print axioms
- hypotheses: named unproven Prop `ActualHodgeCorrespondenceIrreducible` (the genuine realized Hodge-compatible closed correspondences have NO nonzero proper invariant Hodge subspace); plus a nonzero genuinely algebraic Hodge seed in the saturation theorems; G spine record in context.
- main content: InvariantUnderActualHodgeCorrespondences (subspace stable under genuine finite closed correspondences certified to preserve Hodge type); algebraicHodgeSubspace_actual_correspondence_invariant (the actual algebraic Hodge subspace IS invariant — proven); all_hodge_classes_of_actual_geometric_irreducibility and full_hodge_of_actual_geometric_irreducibility (irreducibility + one nonzero algebraic seed ⇒ the whole Hodge fiber is algebraic / the Stage-2G statement).
- name-vs-content: honest — header states global irreducibility "must still be derived from actual geometry; arbitrary smooth projective varieties do not automatically provide it".
- gaps: no instance of the irreducibility criterion; the abstract-GST-matrix-unit ↔ finite-correspondence identification is explicitly NOT made.

### GSTClassicalHodgeStrictCorrespondenceAnalyticTranspose.lean (144 lines)
- decls: 5 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry, 2 #print axioms
- hypotheses: none beyond A : AnalytificationData V (imported data record)
- main content: transposeCarrierPointEquiv (carrier complex-point types of K and its factor-swap transpose Kᵗ are canonically equivalent); transpose_leftComplexPoint / _rightComplexPoint / _carrierPointPair (the analytic pair of Kᵗ is the coordinate swap of the analytic pair of K); mem_analyticLocus_transpose_iff; analyticLocus_transpose.
- name-vs-content: accurate — an orientation/transpose law at the level of actual complex points, explicitly independent of transfer/Gysin/Hodge content.
- gaps: none claimed; a small geometric bookkeeping lemma.

### GSTFourPowerAffineClassifierBridge.lean (140 lines)
- decls: 11 theorems, 1 def, 0 structures, 0 axioms, 0 sorry, 2 #print axioms
- hypotheses: none (bridge arithmetic between the direct-existence and affine-automaton layers)
- main content: affineOrbit_mod_three (least ternary digit of the affine orbit = least trit of K); commonTwo_iff_channel_one (direct common-two target ⇔ channel 1 of the affine orbit); noCommonTwo_iff_badChannel_one (a counterexample is literally bad state B₁ of the four-state channel automaton); low-trit branch classification (noCommonTwo_mod_three_zero/one/two); counterexampleNextChannel spectrum/laws (next-channel dynamics < 4).
- name-vs-content: honest classifier bridging.
- gaps: none internally; the affine route's open content lives in the imported automaton/existence files.

### GSTSmoothProjectiveNoetherian.lean (137 lines)
- decls: 2 theorems (+ several noncomputable instance defs), 0 structures, 0 axioms, 0 sorry, 5 #print axioms
- hypotheses: none (Mathlib-based)
- main content: Noetherian finiteness front: complexBase (Spec ℂ) locally Noetherian; smoothProjectiveIsLocallyNoetherian (smoothness over a Noetherian base, locally of finite type ⇒ locally Noetherian); smoothProjectiveIsNoetherian (+ compactness of the Zariski space from projectivity); smoothProjectiveNoetherianSpace; finite_irreducibleComponents and finite_hyperplaneSection_irreducibleComponents (finiteness for irreducible-component/generic-point constructions downstream).
- name-vs-content: accurate — genuine Mathlib derivations.
- gaps: none; this is one of the few files whose content is honest standard algebraic geometry.

### GSTClassicalHodgeCrossCarrierPointIncidence.lean (133 lines)
- decls: 3 theorems, 1 def, 0 structures, 0 axioms, 0 sorry, 1 #print axioms; "NEEDS CI RUN LATER"
- hypotheses: the pointwise incidence law `HasCrossCarrierPointIncidence` — native map N and Betti map B between different smooth projective varieties commute ON EACH ACTUAL codimension-p irreducible point cycle (an explicit geometric equation to be proven from the chosen correspondence's geometry); no universal existence claim for either operator.
- main content: global_naturality_of_point_incidence (compact native-cycle presentation upgrades the exact point law to full cycle-class naturality for every finite rational combination — eliminating any global naturality axiom); sourceCycle_image_from_point_incidence; normalized_target_from_point_incidence; outputs a fully constructed CrossCarrierTransfer record.
- name-vs-content: honest — "the substantive task is to construct these maps and prove its geometric point equation" (Kuga–Satake / Gale incidences named as future work).
- gaps: the point incidence equation itself is unproven geometry; no instance constructed.

### GSTClassicalHodgeProjectiveSeparatorKrull.lean (131 lines)
- decls: 4 theorems, 0 defs (abbrevs/defs in body), 0 structures, 0 axioms, 0 sorry, 4 #print axioms
- hypotheses: none (Noetherian domain + Krull PIT are Mathlib theorems)
- main content: pointQuotient (projective coordinate ring modulo the homogeneous prime of a Proj point); separatorClass (image of the canonical positive homogeneous separator); separatorClass_ne_zero (the relevance-selected separator lies outside the homogeneous prime, so its class is nonzero in the Noetherian domain); separator_unit_or_height_one (Krull principal ideal theorem dichotomy: unit ⇒ local principal zero locus disappears at that component, otherwise height exactly one); separator_height_one_of_nonunit; separator_minimalPrime_height_one.
- name-vs-content: accurate — unconditional commutative algebra, no Hodge data.
- gaps: none; a genuine local-algebra bridge.

### GSTGeneralSpaceManifold.lean (125 lines)
- decls: 2 theorems, 3 defs, 1 structure (ManifoldCapability — a certificate record with single field `manifold : IsManifold I n M`, discharged by manifoldCapability from an actual instance; not an assumption), 0 axioms, 0 sorry, 0 #print axioms
- hypotheses: none
- main content: GST↔Mathlib manifold plumbing: manifoldGeneralSpace (underlying GeneralSpace of a topological manifold carrier); ManifoldCapability + manifoldCapability (every actual Mathlib C^n manifold produces the capability certificate); every_manifold_admits_generalSpace (ALL-MANIFOLD ADMISSION LAW); contMDiffHom (C^n maps become GeneralSpace morphisms); contMDiff_preserves_generalSpace_reachability; manifoldCarrierChart.
- name-vs-content: accurate — an admission/interop layer, no geometry proven.
- gaps: none claimed; purely interface.

### GSTK3ScalarEndGhostExtinction.lean (122 lines)
- decls: 3 theorems, 1 def, 0 structures, 0 axioms, 0 sorry, 1 #print axioms
- hypotheses: `AllNonMiddleWeightsGeometricallyAlgebraic Y H : ∀ p ≠ 2, ∀ alpha ∈ rationalHodgeSubspace, ∃ Z, H.cycleClass p Z = alpha` — ASSUMES all outer weights (p=0,1,3,4 of the fourfold) are algebraically represented (justified classically but not proven here); plus the imported K3 scalar-End input (End_HS(T(S)) = ℚ·id from GSTK3TranscendentalHodgeCompleteness).
- main content: all_hodge_of_scalar_K3_geometry (outer-weight algebraicity + the K3 self-product p=2 native diagonal/divisor formula ⇒ the full BigradedBettiHodgeStatement on S×S); no_omniversal_ghost_on_scalar_K3_selfproduct (feeding this into the original omniversal ghost separator crown: an actual no-ghost theorem in the existing ghost universe, not a renamed assumption).
- name-vs-content: honest — header: "No theorem here pretends the scalar End condition holds on ALL K3 surfaces or that all arbitrary projective varieties are K3 sources."
- gaps: scalar End(T(S)) = ℚ·id is verified only for special K3s (elsewhere); outer-weight algebraicity is assumed, not derived; the result covers K3 self-products only.

### GSTUniversalSelfProductHodgeEquivalence.lean (115 lines)
- decls: 2 theorems, 0 defs, 1 structure (hypothesis-record), 0 axioms (the "axiom" grep hit is a docstring sentence "not replaced by an assumed surjectivity axiom"), 0 sorry, 2 #print axioms
- hypotheses: NativeProductSection R — fields: `nativeSection : codimensionCycles X.X p →ₗ[ℚ] codimensionCycles Y.X q` with `cycleClass_section_natural : ∀ Z, D.cycleClass q (nativeSection Z) = R.hodgeSection (H.cycleClass p Z)` — assumes the external-product-with-ample-top-power section satisfies the Künneth/projection-formula class identity; inherits the NativeHodgeRetract packet from the import.
- main content: representable_on_X_iff_marked_product_section_representable (per-class iff: alpha algebraic on X ⇔ sigma(alpha) = R.hodgeSection alpha algebraic on Y=X×X, with explicit cycle constructors both directions); every_Hodge_on_X_iff_every_marked_product_section_algebraic (the full weight-p Hodge statement on X ⇔ algebraicity of ONLY the geometrically marked Künneth-section subspace of Y — a non-circular exact product reduction).
- name-vs-content: honest — explicitly "NOT a proof of algebraicity of sigma(alpha) for arbitrary alpha".
- gaps: the NativeProductSection naturality identity (true pr1^*/pr2_* Gysin formulas) is an unproven geometric obligation.

### GSTClassicalHodgePrincipalSectionDescent.lean (105 lines)
- decls: 6 theorems, 2 defs, 0 structures, 0 axioms, 0 sorry, 5 #print axioms
- hypotheses: none (no Hodge theory or cycle-class statement used)
- main content: closed-set descent mechanism for recursive support cutting: cutSupport (support of the positive-degree principal section selected by x); source_not_mem_cutSupport (the source point avoids its own cut); descendSet (C ∩ cutSupport); descendSet_subset / _ssource / _isClosed; strict_closed_descent and univ_strict_descent (genuine strict closed descent inside any closed region containing the source).
- name-vs-content: accurate — pure topological/scheme-support bookkeeping.
- gaps: none claimed; an enabling lemma for the successor machinery.

### GSTNumberManipulationExactKernel.lean (111 lines)
- decls: 4 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry, 3 #print axioms
- hypotheses: none (a ≠ 0, a ≠ b as premises; safe-domain from imported verified law)
- main content: exact "Number Manipulation" algebra: nm_order_two_exact (1/(a−b) = 1/a + b/a² + b²/(a²(a−b)) — an EQUALITY with zero truncated-series error, by field_simp/ring); nm_indexed_kernel_exact (with a = x^(m+1), b = y^(m+2) every indexed term of the corrected Equation (3) has the exact 2nd-order decomposition); nm_safe_domain_all_indices (on y ≥ 1, x > y² no assumed nonzero denominators — they follow from the safe-domain geometric-series law); nm_exact_finite_sum.
- name-vs-content: honest exact rational identities; header states the open task is a genuine period comparison linking NM to a geometric readout — not done here.
- gaps: no contact with algebraic geometry or Hodge theory; purely a candidate identity package.

### GSTClassicalHodgeStrictPlaneCircularityAudit.lean (103 lines)
- decls: 5 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry, 4 #print axioms
- hypotheses: G spine record only
- main content: circularity audit of the ghost-adaptive strict-plane predicate: ghostStrictPlaneStrike_isEmpty (for each ghost E the strike type is empty — an inhabitant already derives False); ghostAdaptiveStrictPlanes_iff_noGhost (requiring every ghost to carry a nonempty strike ⇔ no ghosts at all); ghostAdaptiveStrictPlanes_iff_hodge / _of_hodge; all_ghostAdaptiveStrict_plane_packages_iff_hodge — proving the strict-plane predicate is a downstream consequence-normal form EQUIVALENT to the Hodge conclusion, not a lower geometric axiom.
- name-vs-content: accurate — an explicit anti-circularity certificate.
- gaps: purely logical hygiene; the Hodge conclusion itself remains unproven (the predicate's equivalence to it is the point).

### GSTUniversalSurfaceGraphAugmentation.lean (95 lines)
- decls: 1 theorem, 1 def, 0 structures, 0 axioms, 0 sorry, 1 #print axioms
- hypotheses: `G : GeometricCycleClassSpine V H`, `P : GeometricHigherLefschetzData G 4` (imported Lefschetz/primitive-test record), and the load-bearing shared-Lefschetz hypothesis `hShared : ∀ i, P.primitiveTest (nativeToHodgeFiberLinear G (graphs i)) = common` (all graphs in the automorphism orbit have the SAME primitive-test image — the verified shared-Lefschetz identity, e.g. on K3 self-products with H¹=0), plus augmentation-zero `hAug : ∑ a i = 0`.
- main content: all_augmentation_zero_graph_cycles_primitive — every augmentation-zero rational combination of genuine graph cycles Γ_g is an ACTUAL primitive algebraic codimension-two cycle (proof: linearity of the primitive test + ∑ a i • common = (∑ a i) • common = 0).
- name-vs-content: honest — "implements exactly the verified shared-Lefschetz hypothesis, without treating polarization preservation alone as the general shared-Lefschetz theorem".
- gaps: irregular surfaces (H¹ ≠ 0) need the H¹-moment cancellation from a separate file; the shared-Lefschetz identity is an input, not proven here.

### GSTClassicalHodgePrincipalCutKernelSheaf.lean (90 lines)
- decls: 2 theorems, 0 defs (noncomputable defs in body), 0 structures, 0 axioms, 0 sorry, 2 #print axioms
- hypotheses: none
- main content: exact kernel sheaf of the relative principal cut via Mathlib's IdealSheafData functoriality: relativePrincipalCutIdeal = comap of the generator-specific principal-section ideal along the point-closure immersion; closurePrincipalCut_kernel_eq_relativePrincipalCutIdeal (kernel of the closure-principal cut IS the pullback of the principal-section kernel sheaf); relativePrincipalCutIsoPullbackSubscheme (canonical pullback presentation).
- name-vs-content: accurate — a genuine Mathlib-based kernel computation.
- gaps: none claimed.

### GSTClassicalHodgeLocalRegularCutDimension.lean (88 lines)
- decls: 5 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry, 4 #print axioms
- hypotheses: none (pure commutative algebra)
- main content: exact one-step local dimension law: ringKrullDim_quotient_regular_succ (quotient by one regular element in the maximal ideal lowers ringKrullDim by exactly 1 — Mathlib regular-sequence Krull-dimension theorem); regular_of_nonzero_domain; ringKrullDim_quotient_nonzero_nonunit_succ; principal_height_one_of_local_domain; local_regular_cut_crown.
- name-vs-content: accurate — isolated pure-commutative-algebra lemma for later scheme-stalk use.
- gaps: none claimed.

### GSTCMAllIndexedNonzeroForcing.lean (82 lines)
- decls: 3 theorems, 0 defs, 0 structures, 0 axioms, 0 sorry, 1 #print axioms
- hypotheses: none
- main content: Gaussian-integer kernel for CM Number Manipulation: cmNormSq_mul / _pow (multiplicativity of the exact rational Gaussian norm); cmIndexedDenominator_nonzero_every_index — for x = 1+i, y = i the corrected-Equation-(3) denominator u_n = (1+i)^n − i^(n+1) is NONZERO for every positive index (norm argument: N(1+i)=2 vs N(i)=1, so the powers cannot coincide).
- name-vs-content: honest — and explicitly demarcates what is NOT claimed: the stronger imaginary-part-nonzero fact is "mathematically derived in the manuscript but NOT asserted to be Lean-verified by this module" (first attempt failed elaboration); the scheme/cohomology CM-isogeny realization is not a kernel theorem here.
- gaps: the CM isogeny/correspondence realization of u_n on E = ℂ/(ℤ+iℤ) is not formalized; the imaginary-part lemma is unproven in Lean.

### GSTGeneralSpaceReversiblePartialCharts.lean (74 lines)
- decls: 2 theorems, 3 defs, 1 structure (ReversiblePartialChart — interface record: Coord/domain/target + `coordEquiv : {x // x ∈ domain} ≃ {c // c ∈ target}`, reversible by construction; no unproven proposition), 0 axioms, 0 sorry, 0 #print axioms
- hypotheses: none (interface layer)
- main content: reversible local coordinatization of a General Space: toPartialChart (forget reversibility), observeAt / recoverAt with the inverse laws recover_observe and observe_recover (chart round-trips on the valid domain).
- name-vs-content: accurate GST abstraction plumbing.
- gaps: no instances beyond topological carriers; no geometry.

### GSTGeneralSpaceTransport.lean (45 lines)
- decls: 1 theorem, 0 defs, 3 structures (TransportGeometry — interface record assuming `transport_id : transport (G.idPath x) s = s` and `transport_comp : transport (G.compPath α β) s = transport β (transport α s)` (functorial path transport); InvariantObservable / InvariantPredicate — observation/predicate invariance records), 0 axioms, 0 sorry, 0 #print axioms
- hypotheses: the TransportGeometry functor laws (interface assumptions, not mathematical conjectures)
- main content: transport_assoc (transport along three composable paths is parenthesization-independent, derived from the two interface laws); invariant observable/predicate definitions.
- name-vs-content: accurate small abstraction layer.
- gaps: interface only; no mathematical content.

### GSTGeneralSpacePartialRealization.lean (43 lines)
- decls: 1 theorem, 2 defs, 1 structure (PartialRealization — interface record: Domain : G.Point → Prop, State, realize : ∀ x, Domain x → State; header: "algebraicity is a domain predicate, not a totality axiom"), 0 axioms, 0 sorry, 0 #print axioms
- hypotheses: none (interface)
- main content: PathClosed (paths preserve the domain); ofTotal (restrict a total realization to any predicate locus); domain_of_path (reachable points stay in the geometric locus of a path-closed partial realization).
- name-vs-content: accurate abstraction for locus-restricted realizations.
- gaps: interface only.


---

## BATCH 8 SUMMARY

**Totals:** 72 files, 19,385 LOC, 724 theorems, 0 lemmas, 268 defs, 44 structures, **0 `axiom` declarations, 0 `sorry`, 0 `opaque`**, 355 `#print axioms` receipts. (Two grep hits for the string "axiom" are doc-comment sentences: GSTGraphV2HandwrittenExponentialCascade.lean:154 and GSTUniversalSelfProductHodgeEquivalence.lean:34.)

**Corpus character:** batch 8 = the *scheme-typed conditional architecture* of the Hodge campaign (Stage-2E/2G sockets, CM/GST compilers, omniverse finales, transfer bridges) + the *Cardinal Worlds / Graph-V2 arithmetic engine* (ternary digit/carry/density tables, telescoping, Erdős-type open props) + three small GSTGeneralSpace interface files. No file claims an unconditional Hodge theorem; every "landing" is conditional on hypothesis-records.

### Unproven-assumption inventory

**(a) `axiom`/`sorry`: NONE.** All unproven mathematics enters as (i) structure fields of hypothesis-records ("packet idiom") and (ii) named `def … : Prop` open targets taken as theorem premises.

**(b) Load-bearing hypothesis-records (structure fields quoted in the per-file sections).** The strongest (Hodge-conjecture-strength) fields:
1. `CanonicalOneWordCyclicSeedPacket.seed_class` (PiOneWordCyclicSeedOmniverseFinale): `H.cycleClass p seedCycle = ∑ i, coefficient i • (classicalHodgeBasis V H p (liveBasisIndex alpha i)).1` with all coefficients nonzero — assumes the live Hodge-basis combination of every nonzero class is represented by a native cycle; capstone `packet : ∀ q, ∀ alpha ≠ 0, Nonempty (…)` ⇒ `BigradedBettiHodgeStatement`.
2. `CMGSTNativeSheetProgram.basisPeriodExpansion` (CMGSTNativeBasisCompiler): each target Hodge basis tensor equals `∑ a ∈ active, coefficient a •` the GST-program cohomology evaluation of actual source cycles — the CM/Kuga-Satake/Gale period expansion; supply `CMGSTNativeBasisProgramSupply` ⇒ `BigradedBettiHodgeStatement`.
3. `FiberedBasisPresentationBridge.basisPresentation_spec` (PresentationLanding): each Hodge basis direction = cycle class of an explicit finite rational combination of codimension-p points — equivalent to the point-class equations.
4. `LocalCyclicRealization.seed_mem_atomic` (LocalCyclicCriterion): the sum of alpha's live Hodge basis vectors lies in the point cycle-class span.
5. The eight Gysin/retract packets of GSTUniversalChowRetractToTarget (NativeHodgeRetract, GeometricMultiSourceChowBirth + hodgeSpan, GeometricSplitGysinPacket + reconstruct, SchemeProjectiveBundleGysin, SchemeBlowupGysin, SchemeFiniteDominantTwoTransfer + push_pull_degree, SchemeExceptionalCenterRetract + centerLeftInverseBetti, SchemeProjectiveMiddleStabilization) — each assumes the genuine Chow/Betti Gysin comparison identities.
6. `Stage2EClassRealization` / `Stage2ECompactRealization` (Stage2E): Stage-2D realization matches the intended classical semantics (`hodge_eq`, `cycleClass_eq`, `hodge_iff`); `ClassicalHodgeData` itself is abstract (no surjectivity field — by design).
7. Correspondence-realization laws used across the Graded/Finite/Rational-correspondence chain: `RealizesAmbientOnPoints`, `RealizesFinitePointKernelOnBetti`, `HasCrossCarrierPointIncidence`, `GradedCorrespondencePointNaturality.point_natural`, `BettiRelated` + `RightFiniteBettiTrace` + `PointCycleCompatibility` (OmniversePointStrictRelationFinale), `hA` transfer equations (GSTRationalCorrespondenceExactFinale), `hcover` coverage (PrincipalCutSpectralFusion).
8. Pervasive imported records (defined in other batches, assumed in ~15 files here): `GeometricCycleClassSpine V H`, `NativeMassCycleClassBridge V H`, `ProjectiveDegreeTraceSemantics`, `SchemeBiFiniteClosedCorrespondence`, `FiniteClosedCorrespondence`, `RealizedCorrespondenceExpr`, `ProjectiveWordSpectralFamily`, `GeometricHigherLefschetzData`, `AnalytificationData`, `ProjectivelyLiveSource`.
9. Interface/hypothesis records of the GST graph layer (not Hodge content): `HigherCausalCosmos` (globular laws), `TwoSkeleton` (∂₁∂₂ = 0), `TransportGeometry` (functorial transport), `AnchoredCausalLoops/TwoFillings`; data-only records: GSTGraphV2Production's 10, Vertex, RationalEllipticFoldForm, IntegralPureSquareModel (discharged), ManifoldCapability (discharged), InfiniteCoupledLedger (discharged).

**(c) Named open Props (conjecture-strength premises):**
- `FourPowerHappyPropagation` (FourPowerRelocation), `four_power_happy_climb` (InfiniteFourPowerNavigation), imported `FourPowerDirectExistence` (HappyBridge) — the Erdős-type ternary-digit problem for 4^K; all navigation/creation theorems conditional on them; only bounded residue classes (mod 9/27, K ≤ 500, rows 2-3, bases 5/6/8) are verified.
- `SeedCyclicForActualGeometry` (ResearchUniversalOrbitClosureLaw), `ActualHodgeCorrespondenceIrreducible` (ActualGeometricIrreducibility), `CanonicalCosmicNaturality` + nonzero weight-zero algebraic seed (CanonicalLimitlessNaturalityCrown), `SameWeightGSTStable` (GlobalSheetSaturation), `AllNonMiddleWeightsGeometricallyAlgebraic` + scalar End(T(S)) = ℚ·id (K3ScalarEndGhostExtinction), `Stage2ERealizationObligation`/`Stage2ECompactRealizationObligation`, `HodgeBasisCycleSupply`, `SeedPropagationFamily`.

**The five most load-bearing files**
1. **GSTUniversalChowRetractToTarget.lean** (1420 LOC) — the scheme-typed conditional skeleton of the whole campaign: 8 Gysin/retract packets, blowup-tower and geometric-tower inductions, the all-varieties ⇔ rational-middle-world reduction, and the defect-rank persistence theorems; imported by GSTUniversalSelfProductHodgeEquivalence and conceptually upstream of all Classical-Hodge landings.
2. **GSTGeometricRealizationStage2E.lean** — defines the actual semantic surface: `ClassicalHodgeData` (cohomology/hodgePP/cycleClass as abstract data), `ClassicalHodgeStatement` (the Hodge conjecture's shape: `HodgePP p ≤ range (cycleClass p)`), and the realization-obligation Props; the declared "plug-in socket" for a genuine Betti/Hodge implementation.
3. **GSTClassicalHodgeCMGSTNativeBasisCompiler.lean** — the strongest *supply route*: `bigradedBettiHodge_of_CM_GST_programs` derives the full statement from CM/Kuga-Satake/Gale packets whose `basisPeriodExpansion` field is exactly the unproven arithmetic-geometric input.
4. **GSTClassicalHodgePiOneWordCyclicSeedOmniverseFinale.lean** — the cyclic-seed compression whose `seed_class` field assumes the algebraicity it appears to derive; the cleanest single illustration of the packet idiom's circularity risk.
5. **GSTTransferBridge.lean** — the headline "Clay statement transfer": bijective dictionary WaveCoef ≅ (Fin 12 → ℤ) with `transferred_clay_hodge_conjecture`; this finite 12-cell result is what the campaign's claims rest on for their "official" flavor, while the header concedes the classical instantiation problem.

(Honorable mentions: GSTClassicalHodgePresentationLanding — reduces Hodge to explicit point-class equations; GSTClassicalHodgeGlobalSheetSaturation — the stability/saturation interface; CardinalWorlds.lean — the honest arithmetic core.)

**The single biggest gap:** no `ClassicalHodgeData` instance for any actual variety exists — genuine rational cohomology, its (p,p) Hodge subspace, and the true cycle-class map are never constructed — so every `BigradedBettiHodgeStatement` landing in this batch is a conditional theorem whose hypothesis-records (spine, realization certificates, CM supplies, cyclic seeds, Gysin packets) assume precisely the geometric content the Hodge conjecture requires; meanwhile the only unconditional "Hodge" results (TransferBridge/ClayOfficial layers) live on a 12-cell free ℤ-module. Secondarily, the Erdős-type open props (FourPowerHappyPropagation / four_power_happy_climb / FourPowerDirectExistence) gate the entire GST graph ontology layer.
