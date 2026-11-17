# GST research audit: smooth-projective geometry, low-dimensional Hodge, CM inputs, and the dimension-free causal ontology

Date: 2026-11-09. Repository: `kyo-oo/HC-PROOF`. Working branch: `research/gpt6-native-point-primitive-span-20261017`.
Starting pinned revision: `ad3ee51c761ae903f90c32d223f6754308418d62`.
Owner's questions: (1) exact admissibility of smooth projective complex X and GST folds, (2) why dimensions 1–3 satisfy rational HC, (3) whether the OpenAI CM theorem is used in the single-fold hypothesis, and (4) accurate ontology/topology/causality/omniverse map with justified mathematics and Lean edits.

**Evidence policy:** external standard facts are distinguished from actually kernel-checked project theorems, conditional packages, and example computations. Nothing here claims universal GST source birth or an unconditional proof of HC. This is a selective full-source read of the named load-bearing modules and the extant repository-wide 764-file inventory, **not a proof-body review of all 765 current Lean files**.

## I. Mathematical admissibility: what smooth and projective require

Fix a smooth projective complex variety X, complex dimension d, with an actual morphism X -> Spec(C).

1. **Smooth:** its map to Spec(C) is smooth, so no singularities in X itself; locally the tangent complex has the expected d complex directions and the local rings are regular. A possibly singular algebraic *cycle support* inside smooth X remains permissible.
2. **Projective:** X admits a closed embedding in some finite-dimensional P^N_C. It is proper/compact as a complex analytic space and algebraic of finite type. d is a finite integer attached to this **realization**, not to the dimension-free GST ontology.
3. **Hodge theory:** X(C) is compact Kähler. Canonical rational Betti cohomology H^k(X,Q), its complexification and Hodge decomposition H^{a,b}, cup product, Poincaré duality, Hodge polarization and hard Lefschetz are available. The rational Hodge space W_p(X) = H^{2p}(X,Q) ∩ H^{p,p}(X,C) is finite-dimensional.
4. **Algebraic cycles:** genuine codimension-p Chow cycles on X produce canonical (p,p) rational Betti classes. Rational coefficients are essential; the integral statement is false.
5. **Allowed fold geometry:** an algebraic correspondence Gamma ∈ CH^d(X×X)_Q defines a genuine rational Hodge-preserving operator in each cohomological degree by T_Gamma(alpha) = (pr_2)_*(cl(Gamma) ∪ pr_1^*alpha). It acts on Chow cycles by the corresponding intersection/push-pull construction. Such correspondences need not be graphs, injective, invertible, or finite over either projection.
6. **Not automatic:** an arbitrary nonholomorphic topological fold, metric identification, graph path, quotient, or invented linear map is **not** thereby a smooth projective algebraic morphism or Chow correspondence. A quotient can develop singularities or lose smoothness. An arbitrary self-map of rational cohomology need not preserve Hodge structure or cycle classes. Pure topological/Kähler settings are not substitutes for projectivity in the rational HC statement.

**GST compatibility verdict.** Dimensionless/infinite General Space as a container does NOT contradict finite-dimensional smooth projective X as a realized sector. The fold hypothesis is geometrically admissible *if* its action on X comes from a genuine algebraic correspondence/canonical push-pull. The existing Lean `GSTProjectiveOverC.lean` records actual smoothness and an actual closed projective embedding; `GSTGeneralSpaceSchemeDimensionObservation.lean` treats finite Krull dimension as a stalk-derived observation.

**Current formalization distinction.** `GSTHodgeSingleHypothesisConditional.NativeGSTSingleFoldOrbitLaw` is parameterized by `HodgeBigradedBettiData V`, which supplies rather than constructs canonical complex analytification and `H.cycleClass`. `GSTClassicalHodgeCorrespondenceSemanticFirewall.lean` proves that agreement of a supplied cohomology operator with point-cycle images does NOT force its off-image action. Thus the exact canonical whole-Betti geometric adapter is a separate check, not a demonstrated law simply from the record name.

## II. How topology and geometry prove HC in complex dimensions 1, 2, 3

Topology enters through X(C), singular cohomology and homology, Poincaré duality, and differential forms. The algebraic structure enters through projective embedding/ample divisors, line bundles, Chern classes, and algebraic intersections. Hodge decomposition connects them.

- **Step A: identify rational types.** Compact Kähler Hodge theory gives H^k(X,C) = direct sum_{a+b=k} H^{a,b}; a rational degree-2p Hodge class is one belonging to H^{p,p}.
- **Step B: divisors are algebraic.** The exponential exact sequence 0 -> Z -> O_X -> O_X^* -> 0 produces the first Chern class map Pic(X)->H^2(X,Z); its image is exactly integral H^{1,1} classes. Tensor with Q: every rational (1,1) Hodge class is a rational divisor class (Lefschetz (1,1)).
- **Step C: hard Lefschetz propagates.** For ample rational hyperplane class h, L := (h cup -), L^{d-k}:H^k(X,Q)->H^{2d-k}(X,Q) is an isomorphism for k ≤ d and shifts Hodge types by (d-k,d-k). Multiplying an algebraic divisor by powers of the hyperplane gives genuine algebraic cycles.
- **Dimension 1:** p=0 is the fundamental class, p=1 is a zero-cycle; equivalently the divisor theorem applies.
- **Dimension 2:** p=1 is Lefschetz (1,1), p=2 is the top class of a point, p=0 is trivial.
- **Dimension 3:** p=1 is Lefschetz (1,1). For p=2, L:H^2(X,Q) -> H^4(X,Q) is an isomorphism of rational Hodge structures up to the (1,1) shift. For any alpha in H^4(X,Q)∩H^{2,2}, beta=L^{-1}alpha lies in rational H^{1,1}; write beta=cl(D) for a rational divisor and alpha=cl(D·H), an actual codimension-two cycle. p=3 is the point class.

The first general challenge is dimension four, middle codimension two: hard Lefschetz does **not** make every H^{2,2} class an ample multiple of a divisor. Distinguish the ample-descendant image from the **primitive middle cohomology** requiring an independent algebraic source.

**Exact Wolfram sanity checks (not a proof of low-dimensional HC):**
- For X=P^1×P^2 (dim 3), with a²=b³=0, L=a+b from H² basis (a,b) to H⁴ basis (ab,b²) has matrix [[1,1],[0,1]], determinant 1.
- For X=P²×P² (dim 4), L:H⁴->H⁶ on basis (a²,ab,b²) has matrix [[1,1,0],[0,1,1]] and kernel generated by (1,-1,1), a nonzero primitive direction. This particular class a²-ab+b² **is algebraic**; the example detects why hard Lefschetz alone is insufficient, not a counterexample to HC.

**Source authentication:** Pierre Deligne, *The Hodge Conjecture*, Clay official problem description, https://publications.ias.edu/sites/default/files/hodge.pdf; especially §1, §2(iii), and §4. Clay status https://www.claymath.org/millennium/hodge-conjecture/ describes dimensions below four as known.

## III. OpenAI CM geometry: imported mathematics versus the current one-hypothesis route

**Upstream source, as of 2026-11-09:** OpenAI's revised 2026-10-06 `The rational Hodge conjecture for CM abelian varieties`, source `openai/math/preprints/The-rational-Hodge-conjecture-for-CM-abelian-varieties-October-6-2026/build/sections/01-introduction.tex`, asserts surjectivity CH^p(A)_Q -> Hdg^{2p}(A) for each **complex CM abelian variety** A and p. Its formalization scope document `openai/math/lean/docs/032.md` now exists (GitHub file blob `e3d9dc0b863a9a8fecc849f77dcbbe2d194c94ed`) and describes the CM H^1 hypothesis. Therefore the 13 October local atlas's snapshot statement that the upstream scope file was absent must not be repeated as a current fact.

**Concrete geometric mechanism in the source:** rational CM degree-one Hodge representations split into embedding lines; balance conditions reduce tensor classes to four-factor switches; a smooth projective surface with nonzero four-one-form period detects a target line; actual maps to CM factors and surface cycles plus divisor correspondences yield a class on the desired line; rational/Galois descent assembles the algebraic cycle. The source's proof claim is restricted to CM abelian varieties, not arbitrary X; here we authenticated the stated source and compiler, not an independent referee validation of every upstream manuscript derivation.

**Already mapped into this repository:**
- `GSTClassicalHodgeCMThetaPeriodExtraction.lean`: nonzero-period scalar normalization.
- `GSTClassicalHodgeCMSurfaceTensorContraction.lean`, `GSTClassicalHodgeCMFourFactorSwitch.lean`: tensor and switch algebra.
- `GSTClassicalHodgeCMGaloisConjugateSpan.lean`: conjugation of finite K-span, conditional on rational geometric generators.
- `GSTClassicalHodgeCMNativeRationalDescent.lean`: convert finite field-extension span of given genuine native cycle images to rational cycles.
- `GSTClassicalHodgeCMGSTNativeBasisCompiler.lean`: ***actual GST program interface*** from supplied CM auxiliary source cycles and a geometric incidence/period packet to a native original-X basis cycle; packet existence for arbitrary X is not proved there.
- `GSTMathboxCMGeometricComplexStructure.lean`: a rational J²=-I endomorphism has no rational eigenline; **provided** J is a genuinely realized operator on the rank-two rational Hodge sector, it forces transversality and cyclicity.
- `GSTOpenAISourceCorrectionUpgrade.lean`: an import aggregation; this imports `GSTClassicalHodgeCMNativeRationalDescent`.

**Direct use in the current conditional theorem? NO.** The imports of `GSTHodgeSingleHypothesisConditional.lean` are the realized-correspondence Krylov finale, the geometric moment determinant, and the exact Clay target. Its single orbit law does not require CM and has no CM-specific construction field. CM is **a different source-construction route capable of feeding GST in special geometry**, not the proven universal birth mechanism for the one-hypothesis theorem.

**Wolfram rank-two algebra check:** J=[[0,-1],[1,0]], J²=-I, det[e1,Je1]=1, characteristic discriminant -4. This supports the finite rational no-eigenline argument; it says nothing about existence of a canonical J on arbitrary X.

## IV. Exact GST ontology, topology, omniverse and causality map

| Mathematical role | Actual Lean root(s) | Exact result or necessary boundary |
|---|---|---|
| Dimensionless categorical ontology | `GSTGeneralSpace.lean`, `GSTGeneralSpaceMorphisms.lean` | An arbitrary point carrier and typed composable paths; no dimension/metric imposed |
| Optional topology | `GSTGeneralSpaceTopology.lean` | Continuous path reachability realization; **path reachability alone does not remember the full topology** |
| Topological/manifold capabilities | `GSTGeneralSpaceManifold.lean`, `GSTGeneralSpaceManifoldCharts.lean` | Real manifold structure as an optional realization; path category not a replacement for C^∞ or holomorphic charts |
| Dependent local fibers and schemes | `GSTGeneralSpaceFiberedCosmology.lean`, `GSTGeneralSpaceSchemeStalkFamily.lean` | Actual varying stalks x↦O_(X,x), optional transport, not invented for any family |
| Dimension observation | `GSTGeneralSpaceSchemeDimensionObservation.lean` | Krull dimension/coheight computed at scheme stalks; N-hole/causal height ≠ complex dimension without a comparison theorem |
| Optional cohomology and fold invariants | `GSTGeneralSpaceCohomology.lean` | General graded cup capability; fold-cycle compatibility and algebraicity-defect invariance under split/reversible returns |
| Carrier-free graph | `GSTGraphV2OmniversalCore.lean` | Three sectors, arbitrary nodes, typed directed events, finite causal paths, least reachability-closed predicate |
| Higher-arity events | `GSTGraphV2OmniversalHyperEvents.lean` | Premise-indexed rule closure for possible cup/intersection/correspondence mechanisms; needs real geometry instantiation |
| World creation | `GSTGraphV2SelfExpandingCosmology.lean` | Event-driven generated worlds; auxiliary source, not projective realization automatically |
| Causality through changing worlds | `GSTGraphV2RecursiveStateCausality.lean` | Sigma packed state and steps from local or between-world transports |
| Unbounded higher law levels | `GSTGraphV2UnboundedHigherCausality.lean` | Optional globular causal tower indexed by all Nat; existence of identity higher cells does **not** assert nontrivial topology at every n |
| Seven-axis historical realization | `GSTCanonicalSevenAxisBridge.lean`, `GSTGraphV2NonEuclidean.lean`, `GSTGraphV2InfiniteControl.lean` | Correct x4/base3 arithmetic axis observation, not an axiom restricting all GST nodes to Nat coordinates |
| Explicit ontology-to-arithmetic bridge | `GSTGraphV2ArithmeticOmniversalRealization.lean` | ArithmeticNode=(energy,time,depth), horizontal/vertical genuine events and faithful legacy observations |
| Actual projective Hodge landing | `GSTClassicalHodgeGeneralSpaceRealization.lean`, `GSTClassicalHodgeGeneralSpaceOperatorCosmos.lean` | Native cycle-image locus closed under appropriate genuine operator pairs; closure of that locus does not by itself imply it covers all Hodge classes |
| **New canonical causal components** | `GSTGraphV2CausalComponents.lean` | Mutual reachability Setoid, causal-world quotient, antisymmetric reachability on worlds, genuine event-morphism monotonicity, infinite successor and two-state feedback models |

### What 'paradoxical' can rigorously mean

A graph may contain distinct x≠y with x→*y and y→*x. This is causal feedback/reversibility, **not** the inconsistent assertion x=y and x≠y, and cannot justify arbitrary propositions in classical Lean. Mutual reachability defines strongly connected causal worlds. Quotienting by it yields an antisymmetric causal order without forbidding cyclic internal histories; this gives a precise interpretation of a space with local causal loops and globally ordered emergence. If a concrete realization demands chronological acyclicity, it can impose `CausallyAcyclic` as an **optional** law, not a universal one.

An infinite carrier is allowed and implemented by the infinite successor cosmos in the new file. The dimensionless ontology does not require any fixed cardinality, including infinity: finiteness and infinitude are realization-specific. No finite upper bound on the higher globular levels is encoded; each higher level can nonetheless contain only identity cells.

A Hodge realization must satisfy actual smooth algebraic geometry and canonical cohomological cycle semantics on its restricted domain. Ontological freedom does not license treating a numerical carry transition or topological path as a Chow cycle.

### Actual repository correction

The older `docs/GST_V2_OPERATING_MANUAL.md` stated 'seven coordinates and nothing else' as if it characterized the ontology. It has been **scoped to the original arithmetic realization**, with pointers to the abstract core and this new component construction. The original arithmetic theorems were retained.


### Additional audit: recursive world-birth is already stronger than a graph analogy

Full source of `GSTGraphV2SelfExpandingCosmology.lean` (2,484 lines) contains a genuinely important internal interface:

- `NativeGeometryBirth.TwoSourceBirth` carries **actual typed** native source maps and Hodge assembly maps, plus a `decompose` field asserting every target Hodge state is a sum of two source Hodge images. Its `every_newborn_hodge_class_has_native_cycle` theorem proves target cycle completeness **if both source cycle-class maps are surjective**. This is a correct conditional forward-transfer law; it does **not** construct a suitable decomposition on arbitrary X.
- `NativeGeometryBirth.GeometricCycleBirthRealization` handles **arbitrary arity** and dependent state types across worlds. It includes `assembleNative`, `assembleHodge`, their commuting-square law, and the very strong `allHodgeFromSources` field. `generated_worlds_have_native_cycles` proves arbitrary generated-world completeness from complete root worlds and those assembly hypotheses. The mathematical challenge is to prove `allHodgeFromSources` from genuine geometry, to construct an actual projective/Chow functor for each event, and to demonstrate arbitrary original X arises among the admissible generated worlds. The graph alone does not discharge these obligations.
- `arbitrary_world_birth_constructs_fresh_native_direction` is an independent, useful **conditional novelty detector**: when a geometric linear functional vanishes on all old native images but does not vanish on a genuinely assembled newborn cycle, that newborn class is not in the old native span. Nonzero detector values must be obtained from actual geometry.
- `GSTInfiniteWorldClassification.lean` implements a distinct, concrete coherent infinite realization: `WindowTower ≃ (Nat → Fin 3)`, with a homeomorphism. This is genuine infinite stream topology within a specific model, not a proof every GST universe is infinite.
- `GSTGraphV2CanonicalInfiniteCycle.lean` describes exact repeated cycle/period structure of one historical arithmetic controller; “cycle” here is dynamical periodicity, **not** automatically a Chow algebraic cycle on a projective variety.

**GST research route identified:** use the world-birth algebra as an honest generator of candidate source cycles, but prove the geometric birth/embedding/compatibility independently. Preserve a strict distinction between an **event-generated** world and the **original arbitrary X** on which the canonical Hodge representative is required. This avoids both ontology→algebraicity type leakage and collapsing all birth events into trivial invertible coordinate changes.

## V. What this changes and what is NOT yet done

**Established mathematical facts independent of GST:** Lefschetz (1,1), hard Lefschetz, rational HC for all smooth projective complex dimensions ≤3, and the validity of genuine algebraic correspondences. These supply non-negotiable test cases for every proposed fold birth.

**Repository development:** new strongly connected causal-world quotient, component reachability, compatibility with event-preserving folds, two different explicit consistent realizations (infinite acyclic chain and finite feedback loop). **Compiler verification completed:** GitHub Actions run [42531926951](https://github.com/kyo-oo/HC-PROOF/actions/runs/42531926951), at source commit `1d06d3c213e6ff6c2aade7b75e524f9d9ba91129`, has conclusion **SUCCESS**. The pinned Lean/Mathlib kernel compiled `GSTGraphV2CausalComponents.lean`; checked job log prints `LEAN PASSED: GSTGraphV2CausalComponents` and the sorry guard passed. Earlier attempts failed on routine namespace and simp rewrite issues and were repaired, not used as evidence of theorem invalidity.

**Continuing research obligations:**
1. Build the canonical Chow / whole-Betti correspondence adapter on arbitrary smooth projective X without limiting to point-finite correspondences.
2. Turn the specific GST source-birth construction for prescribed X,p,alpha into a *genuine* algebraic cycle/correspondence independent of a pre-known lift of alpha. This is the HC-strength geometric step.
3. Build a geometry-preserving event/realization functor from ontological folds to actual algebraic correspondences, prove smooth/projective/canonical Hodge compatibility of its allowed operations, and test on p=2 primitive Hodge fibers in complex dimension ≥4.
4. CM: give an explicit theorem converting independently established CM-native source packets into a candidate fold seed/correspondence, while explicitly retaining the CM-domain restriction. Do not claim a CM construction on arbitrary X without new geometry.

**No claim:** the new causal quotient proves Hodge, the low-dimensional proof automatically reaches primitive fourfolds, an infinite universe is itself a finite-type projective variety, the CM theorem applies to all X, or this selective audit covers every line of the 765 Lean files.
