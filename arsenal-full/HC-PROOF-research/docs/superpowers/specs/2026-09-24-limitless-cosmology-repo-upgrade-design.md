# Limitless Cosmology — Repository-Wide Lean Upgrade Design

Date: 2026-09-24
Repository: `kyo-oo/HC-PROOF`
Baseline observed at design time: `88a0d1f1cc3bb8c1a3e31ef7a59b136d48a66084`
Status: design specification before source implementation

## 1. Intent

This upgrade turns the existing HC-PROOF mathematical universe from an arbitrarily extensible collection of finite worlds into a genuinely unbounded cosmology in which finite worlds, finite addresses, finite Hodge ranges, truncated operator algebras, finite wave windows, and finite geometric charts are exact observations, quotients, compact sectors, or specializations of stronger limitless structures.

The objective is not to decorate existing theorems with generic parameters. The objective is to change the deepest mathematical direction of the repository so that finite ceilings cease to be global laws whenever they are artifacts of a chosen chart or observation window.

The upgrade is repository-wide. It covers:

- Cardinal Worlds and GST Graph V2 foundations;
- world geometry and recoordination;
- address spaces and reconstruction;
- mixed-radix dynamics;
- operators and operator algebras;
- wave, Omega, TailF, and coherent cosmology;
- topology-facing observation structures;
- cochain, cohomology, and related homological structures;
- Hodge diagonal, pure Hodge sectors, Lefschetz dynamics, and duality;
- graded algebra and truncated world cohomology rings;
- abstract algebraic geometry and coordinate geometry;
- analytic/de Rham/Hodge absorption layers;
- finite GST Hodge/Clay/transfer layers;
- Stage 2 geometric realization interfaces over actual Mathlib schemes.

The result must remain explainable: the mathematics may become structurally deep, but every new abstraction must have an explicit operational interpretation and exact recovery theorem for the structures it replaces.

## 2. Terminology

The architecture uses these terms consistently:

- **limitless universe**: the total unbounded mathematical cosmos;
- **unbounded cosmology**: its global world/operator/wave/Hodge structure;
- **universal layer**: a theorem or construction that does not depend on a terminal finite wall;
- **finite window**: an `A x B` observation of the unbounded world;
- **compact algebraic sector**: finite-support data in the unbounded universe;
- **completed observational sector**: data determined by a coherent family of all finite observations;
- **finite specialization**: an existing theorem recovered exactly from a stronger theorem by restriction, quotient, evaluation, or finite support.

Finite boundaries that express real local geometry are retained as finite-window facts. They are not erased or declared false; they stop being global ceilings.

## 3. Non-negotiable invariants

### 3.1 No weakening

No existing theorem may be weakened simply to fit the new architecture. If a theorem currently proves an exact finite result, that exact result must remain available with the same or a compatibility-preserving public interface unless a strictly stronger replacement subsumes it and migration is mechanically safe.

### 3.2 No fake infinity

Replacing `4 x 3` by arbitrary `A x B` is not sufficient. Arbitrarily large finite objects are still finite. A theorem is considered genuinely upgraded only if its strongest formulation no longer depends on a global terminal row, column, degree, address count, or fixed truncation when such dependence is not mathematically essential.

### 3.3 No false equivalences

The algebraic finite-support cosmos and the completed observation cosmos are related but generally not identical.

For a coefficient ring `R`, the algebraic unbounded world should be modeled by finite-support functions, morally

`(Nat x Nat) ->₀ R`,

while a compatible inverse system of all finite rectangular observations corresponds to an unrestricted/completed field, morally

`Nat x Nat -> R`.

The first is the direct-limit/compact-support side; the second is the inverse-limit/completion side. The repository must formalize the canonical embedding and the relevant reconstruction principles rather than asserting an invalid equivalence.

### 3.4 No invented geometric conclusion

The finite GST Hodge classification and Stage 2 realization machinery remain formally distinguished from the classical Hodge conjecture for arbitrary smooth projective complex schemes. Stronger GST geometry may reduce or solve explicit realization obligations only when Lean proves the required maps and identities. Names or documentation must never silently identify an internal finite classification with arbitrary classical cohomology.

### 3.5 No meaningless file churn

Every production Lean file is in scope for audit and migration. A file is changed when its mathematics, imports, interfaces, or strongest theorem genuinely participate in the limitless architecture. A theorem that is already maximally generic is not cosmetically rewritten merely to create a diff. Comparator fixtures and workflow smoke files are changed only when required by API migration or verification.

## 4. Two infinite faces of the cosmology

### 4.1 Compact algebraic universe

Introduce an unbounded cell space morally equivalent to

`CosmicCell := Nat x Nat`.

For coefficient ring/module `R`, introduce a compact algebraic field based on finite support, morally

`CosmicCoef R := CosmicCell ->₀ R`.

This universe has no upper row or column. Every element occupies a finite region, but the region is not fixed globally. This is the correct domain for exact algebraic operations, finite sums, polynomial operator actions, compact support pairings, and direct-limit theorems.

Every finite world `WorldCoef A B` receives canonical extension into the unbounded field, and every unbounded compact field whose support lies inside an `A x B` rectangle restricts back exactly. The migration must prove round-trip and support-detection theorems.

### 4.2 Completed observational universe

Independently define the coherent observation universe as compatible data over all finite windows. Conceptually:

- each `(A,B)` supplies a finite observation;
- larger windows restrict to smaller windows;
- a complete observation is a family compatible under every restriction.

This object is the inverse-limit face of the cosmology and corresponds to unrestricted global coefficient fields when the reconstruction theorem is established.

The existing coherent `WindowTower` / stream philosophy becomes a model for this layer: infinity is witnessed through all finite observations plus compatibility, not by a symbolic terminal object.

### 4.3 Compact-to-completed embedding

Prove the canonical map from compact algebraic fields into completed observational fields. Establish injectivity through finite observation separation. This yields a clean distinction:

- algebraic proofs can work with finite support;
- topological/observational proofs can work with arbitrary compatible global data;
- finite theorems can be transported through windows without pretending the two infinite constructions coincide.

## 5. Finite windows become observations, not cosmic walls

The existing `WorldCell A B := Fin A x Fin B` and `WorldCoef A B` remain valuable. Their role changes.

Required structure:

- finite-window inclusion into the compact unbounded universe;
- finite-window restriction from both compact and completed universes;
- enlargement maps between windows;
- exact compatibility of repeated restriction;
- support-sensitive left/right inverse laws;
- naturality under coordinate reindexing;
- theorem that the historical `4 x 3` wave chart is exactly one finite observation.

Boundary-extinction theorems such as finite horizontal/vertical shift death remain true in a fixed window, but are reinterpreted as observation truncation, not global operator death.

## 6. Universal address geometry

The existing finite address rings are upgraded to two limitless address forms:

- compact address space, morally `Nat ->₀ R`;
- completed address space, morally `Nat -> R` or an equivalent compatible finite-address system.

Use an explicit equivalence between cosmic cells and natural addresses. Finite `Fin N -> R` address spaces become finite observations/specializations.

Strengthen chart independence:

- world-to-address and address-to-world maps for compact fields;
- completed observation analogues;
- naturality under finite windows;
- naturality under recoordination;
- support and grading preservation;
- spectral/projector/observable naturality.

The old twelve-address ring survives as an exact specialization, not as a foundational carrier.

## 7. Recoordination becomes a chart calculus

The finite equal-cardinality recoordination groupoid is extended into a broader chart calculus.

The upgraded framework should distinguish:

- finite shape equivalences;
- embeddings of finite windows into the unbounded universe;
- restrictions/projections back to windows;
- finitely supported reindexings of compact data;
- admissible countable/global reindexings where useful for completed data.

The strongest invariants — code, grading, spectral observables, polynomial observables, Hodge support, operator kernels — should be stated naturally with respect to chart change whenever mathematically valid.

A rectangle is then a coordinate presentation, not an ontological limit.

## 8. Operators without terminal extinction

### 8.1 Unbounded shifts

Define global horizontal/digit and vertical/carry shifts on the compact cosmos with no upper wall. They must satisfy for all natural powers:

- additive iteration laws;
- commutation of independent axes;
- functoriality under finite-window restriction where the translated support remains observable;
- exact characterization of what a finite window truncates.

### 8.2 Limitless Lefschetz evolution

Define the global Lefschetz operator `L = H + V` on the unbounded algebraic universe.

Prove for every `n` the exact binomial/path expansion. Global powers do not vanish merely because `n` is large.

The current finite theorem `L^(A+B-1)=0` is preserved as a finite-window quotient/restriction theorem. Its upgraded meaning is:

> after enough evolution, no path remains visible inside a fixed bounded observation.

The cosmos itself continues.

### 8.3 Exact causal kernel

Lift the existing exact Lefschetz transition kernel to the unbounded grid:

- reachability by coordinatewise forward motion;
- unique causal time as Manhattan distance;
- binomial transition coefficient;
- zero coefficient for noncausal targets;
- finite-window kernel recovered by restriction.

This becomes one of the principal operator laws of the repository.

### 8.4 Operator algebra

Introduce a clean algebraic interface in which global shifts act as commuting generators. The natural unrestricted algebra is polynomial in two commuting directions, morally `R[H,V]`.

Finite `A x B` operator algebras are quotient specializations by truncation ideals morally generated by `H^B` and `V^A`.

Thus nilpotence belongs to a quotient/window, not to the global operator algebra.

## 9. Graded algebra and abstract algebraic geometry

This upgrade must make algebraic geometry first-class rather than leaving it as a late translation layer.

### 9.1 Universal coordinate algebra

Develop the GST coordinate algebra using a genuine two-generator commutative polynomial model, preferably through Mathlib structures such as multivariate polynomials when practical.

Required structure:

- natural bigrading by the two axes;
- total grading;
- diagonal/Hodge grading;
- operator action on world coefficients;
- exact finite-window quotient ideals;
- natural quotient maps under window enlargement/restriction;
- basis/monomial correspondence with world cells.

### 9.2 Truncated worlds as quotient geometry

The existing truncated world cohomology ring should be absorbed into the general statement

`R[H,V] / (H^B, V^A)`

or its exact Lean analogue.

Prove the support criterion for the truncation ideal generically, not only through isolated historical dimensions. Every finite world then becomes an algebraic thickening/finite quotient of the same universal coordinate geometry.

### 9.3 Adic/formal completion direction

The inverse system of all truncations naturally points toward `(H,V)`-adic or equivalent formal completion. Where Mathlib supports the required structures cleanly, expose the completed algebra through existing completion APIs. Where it does not, define a precise compatible-family interface without claiming library structures that have not been formalized.

This layer is allowed to be abstract and sophisticated, but every object must have exact finite-quotient projections.

### 9.4 Geometric interfaces

Strengthen the bridge between GST coordinate algebra and the existing actual Mathlib scheme layer:

- explicit ring-hom interfaces;
- induced maps on affine spectra when available;
- graded/Proj-compatible interfaces where appropriate;
- compatibility of finite quotient geometry with chart maps;
- clean separation between internal GST geometry and arbitrary external smooth projective complex schemes.

No scheme-level identification is asserted without an actual Lean map and proof.

## 10. Topology and observable completion

The cosmology needs a native topology of observation.

### 10.1 Finite-observation topology

Finite windows/cylinder observations should generate the topology on completed worlds. For ternary stream realizations, this should align with the product topology on `Nat -> Fin 3` when formalized.

Targets:

- observation maps are continuous;
- compatible finite observations separate global states;
- reconstruction maps are continuous when appropriate;
- current traces become topological observables, not only set-theoretic injections;
- translations/recoordinations obtain continuity/homeomorphism theorems where valid.

### 10.2 Compact versus complete behavior

Do not conflate compact support with topological compactness. The term `compact algebraic sector` means finite support only unless an actual topological compactness theorem is proved.

### 10.3 Analytification boundary

The existing Stage 2 analytification structures remain the gateway to actual topological spaces associated with complex schemes. Internal GST observation topology may be compared to them only through explicit realization maps.

## 11. Cohomology and homological architecture

Cohomology must be upgraded together with the universe rather than remaining a fixed finite ornament.

### 11.1 Window-indexed complexes

Organize finite cochain/chain objects as a directed/inverse family over windows, with explicit restriction or extension maps and commuting diagrams.

### 11.2 Compact-support cohomology direction

Use the finite-support unbounded universe as the natural domain for compactly supported chain/cochain constructions where existing GST definitions permit it.

Prove compatibility of wave coboundaries, row classes, source decompositions, and N-cohomology under window extension.

### 11.3 Completed/limit cohomology direction

For completed observations, define the appropriate compatible-family cochain layer before asserting any derived limit theorem. If actual categorical limits or colimits are practical in Mathlib, use them; otherwise expose exact finite-stage compatibility and reconstruction theorems first.

### 11.4 Naturality

Operators, recoordination, window restriction, wave transport, and address equivalences should commute with the relevant differentials/cohomology maps whenever mathematically valid.

The target is not merely more groups. The target is a functorial cohomological universe.

## 12. Wave, Omega, TailF, and coherent cosmology

### 12.1 Local laws remain exact

The physical law `C + 4*d = e + 3*C'`, Happy cells, dual current, seven-axis ontology, and mixed-emergence equations remain local exact laws. They should be promoted through naturality rather than discarded.

### 12.2 Infinite propagation

Wave transport and Omega evolution should admit arbitrary time/depth on the unbounded cosmos. Terminal behavior caused only by a finite chart is rewritten as observation loss or quotient extinction.

### 12.3 Coherent world reconstruction

Fuse the existing `WindowTower` / stream classification with the new completed world observation system. The strongest target is an explicit reconstruction theorem showing that a global completed world is uniquely determined by its compatible finite observations, with current traces or other observables promoted where sufficient.

### 12.4 Source and singularity structures

Upgrade wave cohomology, N-cohomology, vortex/singularity laws, ignition witnesses, and cut selectors so that finite support/cut windows are parameters inside an unbounded propagation law.

No global theorem should require a final time solely because an earlier representation did.

## 13. Hodge cosmology without terminal weight

### 13.1 Infinite diagonal

In the unbounded world, the diagonal cell `(p,p)` exists for every natural `p`.

Define the universal weight-`p` Hodge generator for every `p` and prove the rank-one weight classification in the compact algebraic sector.

Existing finite statements that classes vanish for `p` outside a finite rectangle remain true after restriction to that rectangle; they cease to describe the global Hodge universe.

### 13.2 Pure Hodge sector

The compact pure Hodge sector should be equivalent to finitely supported integer/rational sequences over the diagonal, morally

`Nat ->₀ Z`

or the appropriate coefficient ring.

The completed pure sector should analogously be represented by unrestricted/compatible diagonal data where useful.

Finite `min(A,B)` coordinate descriptions become truncations.

### 13.3 Bigrading

Strengthen the world grading so that total degree and diagonal/off-diagonal information are encoded simultaneously. A clean candidate uses coordinates such as total degree and charge/difference where integrality/parity are handled correctly.

Do not blindly copy branch experiments; re-derive the strongest form against current `main`, then integrate only theorems that compile and fit the universal architecture.

## 14. Poincare duality without a fictional last cell

An unbounded grid has no distinguished global top cell. Therefore global Poincare duality must not be fabricated by pretending infinity has a last coordinate.

The upgrade uses two legitimate forms:

1. **finite-window/relative duality** — every bounded rectangle has its exact complement involution and perfect pairing;
2. **compact-support versus completed/ordinary pairing** — where formalization supports it, pair compactly supported data with unrestricted observations, reflecting the standard geometry of noncompact spaces.

Prove naturality under translation and window enlargement. The existing finite Poincare theorems remain exact corollaries.

## 15. Lefschetz–Hodge–duality synthesis

Once the unbounded Hodge grading and global Lefschetz operator exist, prove the interaction laws at the universal level:

- exact movement of bidegrees under horizontal/vertical operators;
- exact movement under `L^n` through binomial paths;
- diagonal-to-off-diagonal path classification;
- finite-window Hard-Lefschetz-style matrices as restrictions of universal transition kernels;
- determinant and integral-surjectivity facts retained exactly at finite stages;
- rationalization only when justified by coefficient change, never by prose.

This should absorb the historical fixed `4 x 3` crown into a general operator/geometry theorem family.

## 16. Analytic absorption, de Rham, and Stage 2

The analytic/de Rham/Hodge comparison files are not peripheral. They must be migrated so their finite certificates are visibly finite realizations of the strengthened universal machinery.

### 16.1 Preserve actual external objects

`SmoothProjectiveComplexScheme`, actual Mathlib `Scheme`, actual algebraic cycles, singular cohomology carriers, Hodge bigradings, and cycle-class maps remain explicit external structures.

### 16.2 Strengthen realization interfaces

Replace fixed-rank/fixed-address assumptions in realization certificates wherever they are artificial. New certificates should be able to consume:

- arbitrary finite windows;
- arbitrary finite diagonal ranges;
- universal coordinate/algebra maps specialized to a finite geometric situation;
- functorial maps between resolutions.

### 16.3 Realization obligations remain visible

If the official geometric conclusion still requires an analytic or algebraic realization theorem, that obligation remains a named theorem target. The limitless GST upgrade may make it easier to attack, but it is not erased by architecture.

## 17. V1/V2 and historical theorem migration

The repository currently contains historical and strengthened theorem layers. The upgrade should reduce duplication without destroying stable APIs.

For each family:

1. identify the strongest current theorem;
2. lift it to the universal structure when possible;
3. recover V2/current finite theorems as specializations;
4. recover V1/historical names through compatibility aliases or short corollaries where needed;
5. remove redundant implementation bodies only after dependents compile;
6. keep documentation explicit about which theorem is canonical.

No new `V3` namespace is created merely as a wrapper layer. New names are justified only by genuinely new objects or theorem strength.

## 18. Repository-wide audit and migration matrix

Every production `.lean` file must be classified before modification:

- **Foundation** — definitions that constrain all later worlds;
- **Local physical law** — exact finite/local rule to be made natural under the universal layer;
- **Window theorem** — legitimate bounded result to be recast as restriction/quotient behavior;
- **Universal theorem** — already unbounded; preserve and connect;
- **Operator theorem** — migrate to unrestricted action plus finite restriction;
- **Cohomology/topology theorem** — add functorial window/limit structure;
- **Hodge/Lefschetz/duality theorem** — migrate grading and remove artificial terminal weight;
- **Abstract geometry theorem** — connect universal coordinate algebra, quotients, spectra/Proj interfaces;
- **Stage 2 theorem** — preserve external semantics and strengthen realization inputs;
- **Verification fixture** — change only if public API migration requires it.

The implementation plan must enumerate files by this classification before source edits begin.

## 19. Dependency direction after migration

The intended mathematical flow is:

```text
LIMITLESS UNIVERSE
  |
  +-- compact algebraic cosmos (finite support / direct-limit face)
  +-- completed observational cosmos (compatible windows / inverse-limit face)
  +-- universal address and chart calculus
  +-- global shifts and operator algebra
  +-- universal coordinate algebra / abstract geometry
  +-- topology of finite observation
  +-- cohomology and wave complexes
  +-- infinite Hodge grading
  +-- relative/compact-support duality
  |
  v
FINITE WINDOW / QUOTIENT / REALIZATION
  |
  +-- arbitrary A x B worlds
  +-- truncated operator/cohomology rings
  +-- finite Poincare and Lefschetz matrices
  +-- finite Hodge sectors
  +-- finite wave/Omega observations
  |
  v
HISTORICAL 4 x 3 / TWELVE-CELL CHART
  |
  +-- original wave cells
  +-- original finite Hodge classification
  +-- finite Clay/transfer interfaces
  |
  v
ACTUAL ALGEBRAIC-GEOMETRIC REALIZATION
  |
  +-- smooth projective complex schemes
  +-- analytification / singular cohomology
  +-- Hodge bigrading
  +-- algebraic cycles and cycle-class maps
  +-- explicit Stage 2 realization obligations
```

The direction is deliberate: the historical finite universe becomes a faithful specialization of a larger cosmology rather than the source of global ceilings.

## 20. Verification contract

No migration phase is considered complete without receipts.

Required checks include:

- no new `sorry`;
- no new custom axiom used to manufacture strength;
- `#print axioms` receipts for crown theorems where the repository uses them;
- compilation of every directly modified module;
- full `lake build` after coherent batches;
- comparator/smoke checks preserved;
- existing CI gates preserved;
- exact old-theorem specialization checks;
- window round-trip checks;
- restriction/enlargement coherence checks;
- operator naturality checks;
- finite-vs-unbounded test examples;
- Stage 2 semantic boundary documentation remains accurate.

When a stronger theorem invalidates an old proof strategy but not the theorem itself, rewrite the proof rather than weaken the statement.

## 21. Implementation sequencing constraints

The source migration must proceed from low-level structures upward. High-level Hodge/Stage 2 files must not be rewritten first and forced to guess future APIs.

Required order:

1. complete repository-wide theorem/boundary inventory;
2. introduce the compact and completed limitless world foundations;
3. build window inclusion/restriction/reconstruction;
4. upgrade addresses and recoordination;
5. upgrade global operators and coordinate algebra;
6. migrate graded algebra and finite quotient rings;
7. upgrade topology/observation completion;
8. upgrade wave/Omega/TailF/coherent cosmology;
9. upgrade cohomology and naturality;
10. upgrade Hodge, Lefschetz, and duality;
11. strengthen abstract algebraic geometry interfaces;
12. migrate analytic/de Rham/finite Hodge/Clay/transfer;
13. migrate Stage 2 realization interfaces without changing their external meaning;
14. absorb historical/V2 duplication where safe;
15. run repository-wide verification and documentation audit.

The detailed implementation plan will break these into compile-safe batches and enumerate exact files/dependencies.

## 22. Definition of done

The repo-wide upgrade is complete only when all of the following hold:

- the strongest world geometry no longer has a terminal row/column;
- global shifts and Lefschetz evolution have arbitrary depth;
- finite nilpotence is expressed as quotient/window behavior;
- finite address spaces are specializations of limitless address structures;
- compact algebraic and completed observational infinities are both formalized and correctly related;
- coherent finite observations reconstruct the intended global objects;
- topology is expressed through finite observations where appropriate;
- cohomology is functorial across windows/transport rather than isolated to one chart;
- the Hodge diagonal exists at every natural weight in the unbounded cosmos;
- finite Hodge truncation is recovered exactly;
- Poincare duality is formulated honestly through finite/relative or compact-support pairings;
- the universal coordinate algebra and finite quotient geometries are explicit;
- abstract algebraic geometry is integrated with world/operator structure;
- actual external scheme/cohomology/cycle objects remain semantically distinct and correctly bridged;
- all existing historically important theorems compile as exact specializations or compatibility results;
- the production Lean tree has been audited file-by-file;
- no fake strength, placeholder assumption, or hidden wall has been introduced;
- the full verification suite is green.

## 23. Design principle

The central principle is:

> A boundary may describe an observation, a quotient, a support envelope, a relative geometric object, or a chosen finite realization. It must not be promoted to a law of the entire cosmos unless Lean proves that it truly is one.

The final architecture should therefore look more abstract, more powerful, and more unusual than the current one, while becoming easier to reason about: local finite mathematics remains exact, and every finite phenomenon has a precise location inside the limitless universe.