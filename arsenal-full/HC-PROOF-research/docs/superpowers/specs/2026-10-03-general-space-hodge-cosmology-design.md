# General Space Cosmology → Exact Hodge Design

Date: 2026-10-03
Repository: `kyo-oo/HC-PROOF`
Branch: `sol/hodge-strict-betti-correspondence-fusion-20261003`
Baseline inspected before this spec: `6fc01a82b01d2f99958261e8f4b84cbed0942230`
Status: approved architectural direction; written specification pending final user review before implementation

## 1. Objective

Elevate General Space Theory (GST) from an unbounded coordinate/wave cosmology into a carrier-independent ontology in which coordinates, dimensions, metrics, arithmetic sheets, Graph-V2 states, Hodge decompositions, singular cohomology, projective cycles, correspondences, and finite observations are realizations of one more primitive General Space object rather than the definition of that object.

The mathematical target remains exact and unchanged:

> For every smooth projective complex variety `X`, every rational Hodge class in `H^(2p)(X,Q) ∩ H^(p,p)` is a rational linear combination of algebraic codimension-`p` cycle classes.

The implementation must terminate at the repository's exact target

```lean
GSTClassicalHodgeExactClayStatement.EveryHodgeClassIsFiniteRationalCombination H
```

and must not silently replace that target by a finite GST analogue, a reachability proxy, an operator-stability theorem, a basis hypothesis, or a packaged Hodge conclusion.

## 2. Why the foundation must change

The current repo already contains powerful non-Euclidean, limitless, recoordination, duality, wave, and Hodge machinery. However, several foundational carriers are still concrete coordinate objects. In particular, the world cosmology uses a global carrier morally `Nat × Nat`, while Graph V2 realizes its seven non-dimensional axes from arithmetic data such as ternary digits/carries and finite observation parameters.

Those constructions are valuable and must remain exact, but they should become charts/realizations of GST rather than GST's ontology.

This matters for Hodge. If GST and the supplied cycle-class map are semantically independent structures, a model can preserve all GST-coordinate equations while changing the cycle-class interpretation. Therefore no amount of stronger coordinate algebra alone can force the actual geometric cycle-class range.

The correction is not to postulate algebraicity. The correction is to move the relevant geometric semantics into the same General Space realization calculus so that Hodge, Betti, native-cycle, and correspondence faces are proven compatible realizations of common geometric data.

## 3. Core design principle

**Coordinates describe a General Space; coordinates do not define the General Space.**

The primitive object therefore has no built-in dimension, no metric, no Euclidean structure, no `Nat × Nat` coordinate system, and no arithmetic sheet.

A minimal first Lean shape is:

```lean
universe u v

structure GeneralSpace where
  Point : Type u
  Path : Point → Point → Type v
  idPath : ∀ x, Path x x
  compPath : Path x y → Path y z → Path x z
```

The production version may package identity/associativity as a small category/groupoid-compatible interface when that gives cleaner reuse, but it must preserve the principle that the point carrier and path family are arbitrary universe-polymorphic types.

Dimension is an optional realization property, never a core field.

## 4. Capability layers

Do not create one monolithic structure requiring every geometry to possess every classical property. Build orthogonal capability interfaces over `GeneralSpace`.

### 4.1 Incidence geometry

A relation or typed incidence witness between states/points/subobjects. This layer supports graph edges, algebraic incidence, projective principal cuts, and correspondence supports without imposing metric geometry.

### 4.2 Transport geometry

Every path may induce transport on a chosen coefficient/state system. Composition must be functorial:

`transport (γ₂ ∘ γ₁) = transport γ₂ ∘ transport γ₁`.

Existing digit shifts, carry shifts, Lefschetz motion, projective words, correspondence push-pull, and Graph-V2 path evolution become instances or realizations of this law.

### 4.3 Recoordination geometry

A chart change is a proof that two presentations represent one General Space state or one equivalent observation. Intrinsic observables and predicates must transport across recoordination.

This abstracts the existing U-cut/scale-equivariance principle, where equality of the physical packet already transports arbitrary observables and predicates.

### 4.4 Graded geometry

Gradings, bigradings, weights, codimensions, Hodge `(p,q)` labels, and world degrees become optional structure attached to a realization, not coordinates of the ontology.

### 4.5 Duality geometry

Pairing/probe/Poincare-style duality is a capability. Nondegenerate probes may identify a state through all observations, but no finite-dimensional assumption belongs to the core.

### 4.6 Cohomological geometry

A General Space realization may carry chain, cochain, cohomology, cup, boundary/coboundary, and induced transport structures. This is where the repo's singular-cohomology and GST cohomology layers connect.

### 4.7 Algebraic/native geometry

Projective points, codimension cycles, principal cuts, algebraic correspondences, finite words, and native cycle programs become one realization of General Space incidence/transport.

### 4.8 Spectral/observable geometry

Existing spectral projectors, matrix units, coordinate probes, and finite-window observables become realization-level observables. Their invariance follows from recoordination when they are intrinsic.

## 5. Charts and observations

Introduce a generic chart/observation interface:

```lean
structure GeneralSpace.Chart (G : GeneralSpace) where
  Coord : Type w
  observe : G.Point → Coord
```

Stronger charts may add injectivity, local recovery, overlap/recoordination maps, or finite-observation coherence.

Required adapters:

1. **Graph-V2 realization**: the existing seven-axis/non-Euclidean state becomes a chart/realization of a General Space sector.
2. **World-cosmology realization**: `Nat × Nat`, finite rectangles, compact fields, and completed fields become observations of a more primitive GST space.
3. **Address realization**: natural addresses and finite addresses become coordinate presentations.
4. **Hodge realization**: Hodge sheet/bigraded coordinates become a realization of geometric cohomology states.
5. **Betti realization**: rational singular cohomology becomes a realization of the same geometric states.
6. **Native-cycle realization**: codimension cycles and projective-program states become a realization generated by genuine geometric operations.

The historical `Nat × Nat` limitless cosmos remains an important exact chart; it ceases to be the universal ontology.

## 6. General Space recoordination groupoid

Unify the repo's existing recoordination ideas under an abstract groupoid-like interface.

A recoordination `ρ : A ⟶ B` must transport states and satisfy identity/composition laws. For any intrinsic observable `F`, prove naturality:

`F (transport ρ s) = transportedObservable ρ (F s)`.

For invariant scalar observables this reduces to literal equality.

Required exact specializations:

- existing finite-window reindexing;
- existing world recoordination groupoid;
- Graph-V2 U-cut semigroup/coherence;
- canonical N-wave recoordination;
- Hodge sheet address changes;
- native projective address changes where already justified.

No old theorem is weakened. Each becomes an adapter theorem or specialization of the stronger law.

## 7. General Space state systems and representations

A single General Space may admit many state systems. Use explicit realization maps rather than conflating them.

Conceptually:

```lean
structure Realization (G : GeneralSpace) where
  State : Type w
  realize : G.Point → State
```

For linear/graded/cohomological realizations, add the appropriate module and naturality data separately.

The Hodge proof needs at least four synchronized faces:

- `Native`: genuine algebraic cycle/program data;
- `Betti`: rational singular cohomology;
- `Hodge`: Hodge/bigraded coordinates inside Betti;
- `GST`: limitless General Space observables/program coordinates.

The design explicitly forbids proving Hodge by defining `Native` to be all Hodge states or by including surjectivity of `Native → Hodge` as a field. That would be the conclusion in disguise.

## 8. Geometric cycle class must stop being arbitrary semantic data

The current semantic firewall showed why an arbitrary supplied linear `cycleClass` cannot be forced by unrelated GST equations.

The new foundation therefore introduces a **geometric cycle-class realization** built from independently meaningful geometric/topological primitives already being developed in the repo:

- analytification of the relevant projective/scheme geometry;
- fundamental class / Gysin-style or equivalent singular-cohomological construction;
- proper/finite correspondence transfer where required;
- rational singular chain/cochain functoriality;
- projective principal-cut/native-cycle construction.

The production theorem must identify the supplied Stage2G `cycleClass` with this geometric construction, or replace downstream use of the arbitrary field by the geometric realization while proving a compatibility theorem back to Stage2G.

Allowed primitive obligations are geometric functoriality/transfer identities that make sense independently of Hodge algebraicity.

Forbidden primitive obligations include:

- every Hodge class is a cycle class;
- every Hodge basis vector is algebraic;
- cycle-class surjectivity onto Hodge classes;
- a universal target-sheet hit assumption;
- defect-zero or separator nonexistence.

## 9. Finite correspondence transfer inside General Space

The strict-correspondence work already constructed the correct upper pipeline:

strict algebraic correspondence
→ analytic carrier
→ singular chain maps
→ finite chain transfer
→ cohomology trace
→ normalized total Betti push-pull.

General Space absorbs this as a transport realization rather than leaving it Hodge-specific.

For a genuine finite right projection `r`, the target identity is the finite-degree trace law

`Tr_r ∘ r^* = d • id`, with `d ≠ 0`.

Normalize to obtain

`Tr̄_r ∘ r^* = id`

and define the full Betti action

`K_* = Tr̄_r ∘ l^*`.

This action is defined on the entire rational Betti carrier, including nonalgebraic classes; it is not the weaker relation-inversion construction requiring `l^*(α)` to lie in `range(r^*)`.

The chain-transfer primitive itself must be constructed from genuine geometry or a proved general transfer theorem. It must not be introduced as an unexplained Hodge assumption.

## 10. GST algebra is upgraded from coordinate algebra to path/operator algebra

The old polynomial/two-axis coordinate algebra survives as a realization. The stronger General Space algebra is generated by admissible transport/recoordination paths and their linear combinations/compositions.

For a chosen state realization `M`, define a representation

`ρ : GSTPathAlgebra → End(M)`

with exact composition laws.

Existing operators become named elements/representations:

- digit/carry shifts;
- Lefschetz operators;
- world matrix units;
- spectral projectors;
- U-cuts/recoordination;
- projective words;
- correspondence push-pull;
- Poincare/probe operations when represented linearly.

The existing `R[H,V]` and `R[H,V]/(H^B,V^A)` layers remain exact commutative subalgebras/quotient realizations, not the whole ontology.

## 11. Cosmic synchronization theorem

The central new theorem family is realization synchronization.

If two realizations arise from the same General Space geometric state and the same admissible path/program, then the corresponding actions commute with realization maps.

Schematic form:

```lean
realize₂ (nativeTransport γ z) =
  bettiTransport γ (realize₂ z)
```

and similarly for Hodge/GST observations wherever defined.

For cycle classes, the key geometric naturality specialization is:

`cycleClass (nativeProgram γ Z) = bettiProgram γ (cycleClass Z)`.

This theorem must be proved from the geometric construction of the realization and program semantics. It cannot be a free field of the program structure.

The existing point-normal-form machinery may then globalize verified point-generator naturality to arbitrary native cycles.

## 12. Global Hodge sheet cosmos as a realization, not the ontology

Retain the current exact Hodge-defect design, but reinterpret its global sheet cosmos as one General Space realization.

For every basis sheet `(p,j)`, keep a canonical sheet address and delta state. Preserve:

- finite support;
- exact coordinate probes;
- same-weight matrix units;
- spectral projectors;
- Poincare/duality probes;
- recoordination invariance;
- relation to existing Hodge matrix units and GST cosmic matrix units.

The crucial difference is that these sheet operations must be linked to actual geometric GST programs through synchronization; pure Hodge-coordinate irreducibility alone is not accepted as geometric algebraicity.

## 13. Canonical native source and geometric program compiler

Use the repo's genuine codimension-zero fundamental cycle and projective/Lefschetz spine as the canonical algebraic origin.

For each relevant weight `p`, construct a synchronized nonzero source packet containing:

- an actual native codimension-`p` cycle;
- its geometrically constructed Betti class;
- its Hodge realization;
- a nonzero GST observable/probe coordinate.

Compile General Space path/operator programs into the existing genuine `GradedGeometricProgram`/projective-word infrastructure.

The compiler is **source-specific** when global operator descent is false. The theorem needed for the Hodge route is:

> From the canonical synchronized algebraic source, every target Hodge basis sheet can be reached by a finite admissible GST geometric program whose Betti/Hodge action is the synchronized image of its native action and whose target coefficient is nonzero.

This must be proved using GST transport, recoordination, duality, spectral separation, and the existing projective/native machinery—not assumed as `ClosedCorrespondenceHitsSheet` or equivalent.

## 14. Defect as a General Space realization discrepancy

Generalize the current Hodge defect.

For two synchronized linear realizations `R₁` and `R₂` into a common comparison carrier, define

`Defect(s) = R₁(s) - R₂(s)`.

Prove defect naturality under admissible GST transport/recoordination.

The Hodge cycle-class defect is the specialization comparing:

- the geometric Betti realization of an actual native algebraic state;
- the target Hodge-sheet realization selected by the GST program.

The goal is not to assume this defect is zero. The proof must show extinction by combining:

- canonical nonzero algebraic source;
- global GST probes/duality;
- spectral/projective program generation;
- geometric synchronization/naturality;
- separator annihilation of actual algebraic cycle classes.

## 15. Exact Hodge contradiction route

Fix a Hodge weight `p` and suppose a Hodge basis sheet `e_j` is outside the rational algebraic cycle-class span.

1. Use the existing linear separator machinery to obtain a rational functional `λ` annihilating the actual algebraic cycle-class span but with `λ(e_j) ≠ 0`.
2. Represent `λ` as a finite General Space/Hodge defect observable through the global sheet cosmos and nondegenerate probe/duality layer.
3. Select the canonical synchronized nonzero native algebraic source at weight `p`.
4. Use the General Space geometric program compiler to produce an admissible finite program `γ` whose Hodge realization sends the source to `q • e_j` for some `q ≠ 0`.
5. Execute the same `γ` natively, producing an actual algebraic cycle `Z_γ`.
6. By the geometric synchronization theorem,
   `cycleClass Z_γ = q • e_j` in the actual Betti/Hodge carrier.
7. Since `λ` annihilates every algebraic cycle class,
   `λ(cycleClass Z_γ) = 0`.
8. But synchronization and `q ≠ 0` give
   `λ(cycleClass Z_γ) = q * λ(e_j) ≠ 0`.
9. Contradiction.

Therefore every Hodge basis sheet lies in the rational algebraic cycle-class span. Finite basis expansion then yields every rational Hodge class as a finite rational linear combination of algebraic cycles.

## 16. Exact capstone

The final theorem must be literally of the form

```lean
theorem gst_general_space_exact_rational_hodge_conjecture
    (...) :
    GSTClassicalHodgeExactClayStatement.EveryHodgeClassIsFiniteRationalCombination H := by
  ...
```

No assumption may be definitionally/equivalently the target.

In particular the capstone may not assume:

- `BigradedBettiHodgeStatement V H`;
- `EveryHodgeClassIsRationalAlgebraic H`;
- all Hodge basis vectors have cycle representatives;
- universal Hodge-sheet reachability supplied as data;
- universal correspondence hits;
- arbitrary matrix-unit naturality;
- defect zero;
- separator nonexistence;
- surjectivity of the cycle-class map onto the Hodge subspace.

## 17. Migration and compatibility

Existing mathematics is preserved by adapters rather than deleted.

Required exact recovery theorems include:

- `GSTGraphV2NonEuclidean` seven-axis states as a General Space realization;
- Graph-V2 forward paths as General Space paths;
- U-cut and N-wave laws as General Space recoordination specializations;
- `GSTWorldCosmology` finite/compact/completed fields as charted state realizations;
- `GSTWorldRecoordinationGroupoid` as a specialization of general recoordination;
- existing Poincare/Lefschetz/cohomology laws as capability instances;
- Hodge global sheet cosmos as a graded realization;
- strict correspondence analytic/chain/Betti machinery as a cohomological transport realization;
- Stage2G data through an explicit geometric-cycle-class compatibility adapter.

Public theorem names that are already green should remain available whenever practical. Foundational files are extended or adapted surgically; unrelated mathematics is not rewritten.

## 18. Planned focused modules

### Foundation

1. `GSTGeneralSpace.lean`
   - carrier-independent General Space;
   - paths, identity, composition;
   - minimal laws.

2. `GSTGeneralSpaceTransport.lean`
   - state systems;
   - functorial path transport;
   - path/operator representation interface.

3. `GSTGeneralSpaceRecoordination.lean`
   - chart/recoordination groupoid;
   - observable/predicate/relationship transport;
   - finite observation coherence.

4. `GSTGeneralSpaceRealization.lean`
   - realization interfaces;
   - comparison/intertwining maps;
   - synchronization schema.

5. `GSTGeneralSpaceDuality.lean`
   - probes/pairings;
   - nondegenerate observation principles;
   - coordinate separation without dimension assumptions.

6. `GSTGeneralSpaceCohomology.lean`
   - chain/cochain/cohomology realization capability;
   - induced path transport;
   - comparison hooks for singular and GST cohomology.

### Existing-GST adapters

7. `GSTGraphV2GeneralSpaceRealization.lean`
   - seven-axis Graph-V2 embedding;
   - forward-path realization;
   - U-cut/N-wave recoordination adapters.

8. `GSTWorldCosmologyGeneralSpaceRealization.lean`
   - compact/completed world realization;
   - finite rectangle observation adapters;
   - shift/Lefschetz representation.

### Geometric/Hodge realization

9. `GSTClassicalHodgeGeneralSpaceBettiRealization.lean`
   - actual rational singular cohomology realization;
   - Hodge graded observation.

10. `GSTClassicalHodgeGeneralSpaceCycleRealization.lean`
    - genuine native algebraic cycle realization;
    - geometric cycle-class construction/identification;
    - principal-cut/projective program semantics.

11. `GSTClassicalHodgeGeneralSpaceCorrespondenceTransfer.lean`
    - strict finite correspondence chain transfer;
    - trace identity;
    - normalized total Betti push-pull;
    - transpose compatibility.

12. `GSTClassicalHodgeGeneralSpaceSynchronization.lean`
    - native/Betti/Hodge/GST intertwining;
    - cycle-class naturality from geometric semantics;
    - point-generator-to-global-cycle propagation.

### Hodge finale

13. `GSTClassicalHodgeGeneralSpaceProgramCompiler.lean`
    - canonical algebraic source;
    - source-specific General Space geometric program generation;
    - nonzero target-sheet action.

14. `GSTClassicalHodgeGeneralSpaceDefectExtinction.lean`
    - separator encoding;
    - dual probe selection;
    - synchronized contradiction;
    - every basis sheet algebraic.

15. `GSTClassicalHodgeGeneralSpaceExactFinale.lean`
    - finite rational basis assembly;
    - exact Clay target.

File boundaries may be merged when Lean's APIs make a split artificial, but responsibilities must remain explicit.

## 19. Verification discipline

- Every production theorem receives targeted `#check` coverage.
- Critical capstones and semantic bridges receive `#print axioms` audits.
- `sorry`, `admit`, custom axioms, or assumptions equivalent to the desired conclusion are forbidden in the final proof route.
- GLM may repair Lean syntax, elaboration, imports, typeclass/API mismatches, and proof terms, but may not strengthen hypotheses, replace constructions by assumptions, or repackage the Hodge conclusion.
- A file is not called green until compilation/CI verifies it.
- Existing green files are not rewritten speculatively.
- Countermodels/semantic-separation theorems are preserved as regression tests: the new route must escape them by adding genuine geometric semantics, not by deleting the counterexample.

## 20. Implementation order

Burst 1 — carrier-independent foundations:
`GSTGeneralSpace` → transport → recoordination → realization → duality.

Burst 2 — prove old GST is a realization:
Graph V2 + world cosmology adapters, with exact recovery of existing U-cut, N-wave, shift, and observation laws.

Burst 3 — geometric cohomology realization:
singular chain/cochain realization + finite correspondence transfer + geometric cycle-class construction/identification.

Burst 4 — synchronization:
prove native/Betti/Hodge/GST program naturality from the common General Space semantics.

Burst 5 — global Hodge program generation:
use the repo's full GST cosmology, Poincare probes, recoordination, spectral projectors, projective words, and canonical spine to generate the required source-specific target action.

Burst 6 — defect extinction and exact finale:
separator contradiction → every Hodge basis sheet algebraic → arbitrary rational Hodge class finite rational cycle combination.

## 21. Acceptance criteria

The architecture is complete only when all of the following are true:

1. General Space has no built-in Euclidean, metric, finite-dimensional, rectangular, or arithmetic carrier assumption.
2. Existing Graph-V2/world cosmology is recovered exactly as realizations, not discarded.
3. Hodge coordinates are a realization, not the ontology.
4. The actual cycle-class map is geometrically constructed or identified with a constructed geometric map.
5. Finite correspondence action on full Betti cohomology is constructed from genuine transfer semantics.
6. Native geometric programs and Betti/Hodge actions are proven synchronized.
7. No universal Hodge-sheet reachability is assumed as data; the source-specific generation theorem is proved using GST machinery.
8. Semantic-separation countermodels no longer apply because the geometric cycle-class realization is part of the synchronized semantics, not an arbitrary independent field.
9. Every basis-sheet algebraicity theorem is proved without assuming the desired conclusion.
10. The final theorem has exactly the repository's rational Hodge-conjecture target and passes the axiom/sorry audits.
