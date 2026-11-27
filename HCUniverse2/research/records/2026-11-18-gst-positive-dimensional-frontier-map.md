# 2026-11-18 — The positive-dimensional frontier map (Wave 44): the live-core kit certified, the sphere wall fenced, the lane designed

## The target

BOSS's directive: **the general live rank >= 2 core on positive-dimensional
worlds** — `NativeGSTSingleFoldOrbitLaw` on a positive-dimensional
`SmoothProjectiveComplexScheme` with a live Hodge fiber of rank >= 2.

## The state before this wave

The campaign's two certified lanes (`twelvePointWorld` at `cd72153`, the
`finitePointWorld N` family at `c5385a02`, run 44290094898, zero sorry,
axioms `[propext, Classical.choice, Quot.sound]`) are 0-dimensional. Their
live weight-0 fibers (rank N) were computed through
`singularChainComplexFunctorIsoOfTotallyDisconnectedSpace`; their positive
weights are honestly dead by PROVED vanishing of the singular cohomology of
a finite discrete space. The records list "live weights at p >= 1 on
positive-dimensional worlds" as the genuine remaining core.

## The war council (recon, three agents)

1. **Framework (R1)**: `AnalytificationData` is data-only (a `TopCat` space
   + a bare type `Equiv` from the complex points — no topology obligation is
   even expressible). `HodgeBigradedBettiData` is data-only (`cycleClass`
   unconstrained). `HodgeBigrading` has exactly three fields
   (`component/independent/spans`) — the **stash bigrading is legal**:
   `(⊤, ⊥, …, ⊥)` typechecks with NO condition on `H^{2p}`, and its rational
   fiber is `ker(complexificationMapQ)`. No injectivity lemma for
   `complexificationMapQ` existed in the corpus (this wave supplies it).
   `RealizesAmbientOnPoints` binds the operator to the geometry through the
   point-class equation at the SAME codimension p; the point-kernel engine
   lifts to `CycleClassOperatorPair` given only `CompactSpace`.
2. **Repo arsenal (R2)**: NO positive-dimensional world exists (both worlds
   are `Spec (Fin N → ℂ)`); no honest class in any `H^{2p}`, p >= 1, has
   ever been constructed (the Betti side is supplied data:
   `PointBettiClass`, `ProjectiveDegreeTraceSemantics`,
   `GeometricCycleClassSpine` — with the `zeroCycleClassData` firewall
   rejecting content-free instances). The graph correspondence
   (`graphCorrespondence f`, left = 𝟙, hence singleton left fibers) is the
   exempted finite-left-fiber case — the correct letter shape for an
   automorphism world. No scheme coproducts/products of worlds exist;
   `sigmaSpec` (Mathlib Limits.lean) is unused.
3. **Mathlib at the pin v4.33.0-rc2 (R3, verified against the tarball)**:
   singular homology exists (functor, homotopy invariance, `H₀ ≅ free on
   path components` via `TopCat.singularHomology₀Iso`, totally-disconnected
   computations) — but **no tool computes Hₙ of any positive-dimensional
   space**: no excision, no Mayer-Vietoris, no Hurewicz, no Brouwer degree,
   no singular cohomology, no de Rham map, no `Hₙ(Sⁿ)`. Found and verified:
   `isPathConnected_sphere`, `onePointHyperplaneHomeoUnitSphere` (the
   Riemann sphere homeomorphism!), scheme coproducts
   (`HasColimitsOfShape (Discrete σ) Scheme`), closed-immersion stability
   (comp, base change), `Proj.map` + `map_comp`/`map_id`.

## The wall (the council's theorem-grade finding)

**Every honest positive-dimensional world requires positive-degree singular
cohomology of a non-discrete compact space.** The dodge table, exhausted:

- *Discrete topology on the complex points*: breaks the law itself — H⁰
  becomes all functions on an uncountable set, unspannable by any orbit.
- *Zariski topology*: uncomputable (its singular complex is wild).
- *Zero cycle class at positive weights*: the campaign's own
  `zeroCycleClassData` firewall (content-free data, rejected).
- *Stash-declared empty `(1,1)`-slot on a curve*: dishonest — the true
  `(1,1)`-part of a curve's H² is all of H².
- *Mixed-dimension components, contractible analytifications,
  homotopy-equivalent-to-discrete*: impossible for smooth projective
  worlds (compact analytic pieces with live top degree).
- *Build H²(S²) in-round*: requires MV / simplicial approximation /
  Hurewicz-class infrastructure — a research-grade Mathlib contribution.

## The design (the finiteLine lane — frozen interface)

The world: `finiteLineWorld M` := the disjoint union of M projective lines,
presented as `Proj (ℂ[x₀..x_{2M-1}] / cross-monomials)` (the M coordinate
lines in ℙ^{2M-1}); smooth chartwise (each chart `Spec ℂ[t]`); projective
via the chartwise surjections (transplanting the finite-point lane's
Zariski-local closed-immersion pattern); the M-cycle automorphism = the
graded ring automorphism permuting the blocks, through `Proj.map`.

- **Weight 0 (UNCONDITIONAL live rank-M core)**: H⁰ ≅ ℚ^M via the H⁰
  machine: H⁰ = ker δ⁰ ≅ Hom(H₀, ℚ) (the degree-0 special case of UCT,
  constructible: 0-chains have no boundary), composed with
  `TopCat.singularHomology₀Iso` and the path-component identification
  (per-block: `isPathConnected_sphere`; blocks = the M clopen components).
  The analytification: `Σ i : Fin M, sphere 0 1` with the honest
  equiv (chart classification of the complex points; the Riemann-sphere
  homeo supplies the per-block identification).
- **Weight 1 (THE GATE)**: the disclosed 3-field gate
  `FiniteLinePointClassData M` := (pointClass : Fin M → H²,
  pointClass_zero_ne, pointClass_indep) — the honest H² classes of the M
  lines (classically: H²(⊔M S²; ℚ) ≅ ℚ^M freely generated by the component
  fundamental classes). The span engine (this kit) makes the declared
  fiber EXACTLY the span of the gate family; the law's content at weight 1
  becomes the Krylov cyclicity of that span under the M-cycle letter
  (the graph correspondence, residue degree 1, `realizes_on_points` =
  the point-class equations).
- **Weights p >= 2 (honestly dead)**: the stash bigrading (this kit) —
  true for dimension reasons, and now free of any vanishing proof.

The API contract for the lane's six files is frozen at
`campaign/wave44/API_CONTRACT.md` (agent-drafting of the carrier found the
sub-agent execution window too short this session; the commander drafted
the kit directly; the carrier is the next wave's construction).

## What this wave certifies

`GSTPositiveDimensionalLiveCoreKit.lean` (the lane's algebraic engines,
all unconditional, no world assumed):

1. `exists_complex_retraction` + `complexificationMapQ_injective` — the
   retraction of ℂ onto ℚ•1 (via `LinearMap.exists_extend` over the field
   ℚ), contracted against the tensor factor as an explicit left inverse.
2. `stashBigrading` + `rationalHodgeSubspace_stash_eq_bot` — the
   dead-positive-weight engine, NO vanishing proof needed.
3. `spanBigrading` + `rationalHodgeSubspace_span_eq` — the
   gated-live-weight engine; the (⊆) direction is the tensor-projection
   argument (`id ⊗ πW` kills the complex span because πW kills the
   rational span; injectivity forces the conclusion).
4. `native_GST_single_fold_orbit_law_of_stashed_positive_weights` — the
   frontier reduction: weight-0 cyclicity + stashed positive weights
   ⟹ the full law.

## The fork (for BOSS)

The positive-dimensional law itself is gated on the sphere machine:
constructing honest nonzero point classes in H²(⊔M S²; ℚ). Options:

(a) **Fund the sphere machine**: a dedicated Mathlib-scale campaign
    (Mayer-Vietoris for singular chains, or the normalized-chains route
    through a triangulation of S², or Hurewicz). This unlocks EVERY
    positive-dimensional world, in this campaign and beyond.
(b) **The gated lane**: build `finiteLineWorld M` + the H⁰ machine + the
    certificates with the 3-field gate as an explicit hypothesis — the
    law lands as a conditional theorem, honestly disclosed, and the
    campaign's next kill becomes just the gate.

The kit certified this wave is the common substrate of both forks.

## Ledger

- Files: `GSTPositiveDimensionalLiveCoreKit.lean` (523 lines, zero sorry).
- CI lane: `gst-positive-dimensional-live-core.yml` (kernel check, sorry
  gate, artifact upload), lib `GSTPositiveDimensionalLiveCoreLib`.
- AGENTS.md: deleted (BOSS directive, commit `d1bc1e5`), never to return.
