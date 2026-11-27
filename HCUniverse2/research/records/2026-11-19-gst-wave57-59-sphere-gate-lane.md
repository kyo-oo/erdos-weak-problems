# 2026-11-19 — Waves 57-59: the sphere point-class gate lane (F1-F3) + the war council's sphere-machine verdict

## THE VERDICT (final, end of round)

* **Wave 57 — `GSTSingularCohomologyMaps.lean` — GREEN** (run 44601531424,
  the six-adjudication arc 44574228416 → 44578135994 → 44595996727 →
  44599387094 → 44601531424 complete: zero errors, zero sorry).
* **Waves 58-59 — F1 `GSTSphereCycleLegs.lean` + F2
  `GSTSpherePointSpaceCohomology.lean` + F3
  `GSTSphereUnionPointClassGate.lean` — GREEN** (run 44604829367, the
  two-adjudication arc 44603065326 → 44604829367: zero errors, zero
  sorry; F1/F2 built clean on their FIRST compile after 58.1's two
  mod-arithmetic diseases, F3 after 59.1's two).

**THE WEIGHT-1 GATE'S ENTIRE CARRIER-FREE CALCULUS IS NOW CERTIFIED.**
Given the honest sphere class `ω ∈ H²(S²; ℚ)`, `ω ≠ 0` (the single fenced
hypothesis), the certified lane delivers: the honest point-class family
`(spherePointClass M ω i)_i`, the on-slice restriction (= ω), the
off-slice restriction (= 0), nonzero, linear independence, and the
M-cycle equivariance — every input the final law-landing consumes at
weight 1 except the carrier-side assembly.

## THE ROUND'S TWO FRONTS


BOSS's directive: the FULL unconditional `NativeGSTSingleFoldOrbitLaw` on a
positive-dimensional world — the two last parts (the weight-1 honest point
classes and the scheme carrier), with new Mathlib modules written without
hesitation, corpus maths only.  This round ran a three-agent war council on
the sphere-machine core and landed the carrier-free half of the weight-1
gate.

## THE WAR COUNCIL (three agents, full-pin-source verification)

* **The Doubter** (verdicts on the commander's dead-route registry):
  - H₂(∂Δ[3]; ℚ) ≠ 0 in the SIMPLICIAL-SET normalized chains is
    ESSENTIALLY FREE at the pin: `SSet.normalizedChainComplex` +
    `HasDimensionLT (boundary 3) 3` kills degree-3 (B₂ = 0 — every nonzero
    2-cycle is non-bounding), `ιNormalizedChainComplex_eq_ι` +
    `isColimitCofanNormalizedChainComplex` separate the fundamental cycle
    from 0.  NO Brouwer content on the sset side.
  - The field-duality lemma (non-bounding cycle ⟹ nonzero cohomology
    class, over ℚ) is fully loaded at the pin:
    `LinearMap.exists_extend_of_notMem`
    (LinearAlgebra/Basis/VectorSpace.lean:294) is exactly the separator.
  - **THE WALL (verified first-hand, all routes)**: transferring ANY of
    this to the SINGULAR chains of a TOPOLOGICAL 2-sphere requires the
    comparison theorem (`sSetTopAdj`'s unit being a quasi-iso / excision /
    simplicial approximation) — absent at the pin, zero theorems in
    `Subdivision.lean` (only the functors), no `πₙ(Sⁿ)`, no Brouwer, no
    winding number, no MV, no Hurewicz.  This is a multi-month
    research-grade formalization (the irreducible ingredient: excision or
    the sd/ex comparison).
* **The Strategist** (the assembly map): the complete 9-file, ~3,200-line
  landing plan with the carrier battle map (Route A: the coproduct
  ∐(Fin M) P¹ via `Sigma.desc`/`Sigma.reindex`, projectivity through the
  per-line coordinate-line immersions with the chartwise
  `IsZariskiLocalAtTarget` fallback), the honesty ledger (the
  `zeroCycleClassData` firewall; the honest cycleClass choices; the
  p ≥ 2 disclosure), and the plug-in gate structure
  (`FiniteLinePointClassData M` — the frozen 3 fields PLUS the
  cycle-equivariance field).  Carrier pricing: 6-10 CI waves, the critical
  path; the two designated research points (Proj.map-closed-immersion of
  surjective graded maps — CONFIRMED absent at the pin by direct fetch of
  `ProjectiveSpectrum/Functor.lean` (226 lines: comap/map/map_comp/map_id
  only); the coproduct-pullback interchange).
* **The Attacker** (the sphere-class construction): timed out (context
  deadline); its target was covered by the Doubter's verdict.

## WHAT LANDED THIS ROUND (CI lanes pending at record time)

**Wave 57.4/57.5 — the maps module's second/third adjudication** (runs
44578135994 → 44595996727, 14 diseases → 9 diseases → this push), every
name root-caused against the pin's source:

* `TopCat.ext` (pointwise, Basic.lean:129) replaces `TopCat.hom_ext`
  (a `.hom`-equality lemma, Basic.lean:125) — after `apply` the goal is a
  ∀-binding, `intro` not `funext` (the 57.3 misdiagnosis);
* `stdFace` rebuilt as `⟨stdSimplex.map k.succAbove,
  stdSimplex.continuous_map k.succAbove⟩` — the pin's
  `stdSimplex.continuous_map` is a LEMMA supplying `Continuous (map f)`
  (Convex/StdSimplex.lean:347), not a map; the rebuilt coface is exactly
  the one of the pinned `toSSetObjEquiv_δ_apply` (itself `rfl`);
* `toSSetObj₂_face` restated pointwise, proved by `calc` through the
  pinned face formula + the equiv roundtrip (h2 on
  `rw [apply_symm_apply]`);
* the pinned `isOpen_sigma_iff` RHS is PREIMAGE-spelled — the collapse's
  hsets restated as `Sigma.mk j ⁻¹'` compositions; `Set.mem_setOfEq` does
  not exist at the pin — the hsets close by plain `simp` (which reduces
  the Fin-decidable `j = j` propositionally); the ite-over-membership
  decidability trap dissolved by the two-branch split;
* the pin's `Functor.map_comp` takes the functor EXPLICIT-first.

**Wave 58, file F1 — `GSTSphereCycleLegs.lean`**: `cyclicPred` + both
roundtrips + injectivity; **THE CYCLE/COLLAPSE LEG IDENTITY**
(`sphereCycle ≫ sphereCollapse j = sphereCollapse (cyclicPred j)`);
the off-slice const leg; the cohomology-level calculi.

**Wave 58, file F2 — `GSTSpherePointSpaceCohomology.lean`**: the point
carrier (definitionally the certified `finitePointSpace 1`); the
const-factorization legs; **THE POINT-SPACE H² VANISHING** (the green
`finitePointCohomology_subsingleton` at N = 1, defeq-transported);
**THE OFF-SLICE DETECTION INPUT** (`constSphere_pullback_two`).

**Wave 59, file F3 — `GSTSphereUnionPointClassGate.lean`**:
`pullback_pair`; **THE HONEST POINT-CLASS FAMILY**
`spherePointClass M ω i := (collapse_i)^* ω`; the on-slice restriction
(= ω, the restriction-section calculus); the off-slice restriction
(= 0); nonzero; linear independence
(`Finset.sum_eq_single_of_mem` slice detection); **THE
CYCLE-EQUIVARIANCE** (`cycle_pointClass`); **THE RAW-SPACE GATE BUNDLE**
`spherePointClass_gate`.

## THE HONESTY LEDGER OF THE GATE

Every statement in F1-F3 is unconditional.  The single input is the honest
sphere class `ω ∈ H²(S²; ℚ)` with `ω ≠ 0` — the fenced sphere-machine
core.  The council's verdict is recorded above: this input is
research-grade at the pin (the singular/simplicial comparison), and the
gate is designed so that when it lands — by whatever future route (the
sset-sphere computation + the comparison theorem, or a from-scratch
excision) — the final law assembles by discharging one hypothesis.

## THE STATE OF THE TARGET

| Target component | State |
|---|---|
| The kit (algebra engines) | GREEN (run 44382896351) |
| The component H⁰ machine | GREEN (run 44545624743) |
| The sphere-union component machine | GREEN (run 44545624743) |
| THE UNCONDITIONAL LIVE RANK-M ≥ 2 CORE | GREEN (run 44545624743) |
| The merged law + the sphere-union plug-point | GREEN (run 44545624743) |
| The maps module (wave 57) | **GREEN (run 44601531424, this round)** |
| The point-class gate calculus (F1-F3) | **GREEN (run 44604829367, this round)** |
| The honest sphere class ω ≠ 0 | THE FENCED CORE — research-grade at the pin (the comparison theorem), the war council's verified verdict |
| The scheme carrier `finiteLineWorld M` | the priced 6-10-wave battle (Route A, the Strategist's map) |
| The final assembly (F7-F9) | the plug-in design frozen (the gate + the green merged law) |

## NEXT WAVES (the frozen order)

1. ~~Land F1-F3 green~~ — DONE (runs 44601531424 + 44604829367).
2. The carrier recon's two research points → the carrier waves (F4-F6,
   Route A: scheme+smooth+cycle → residueDegree → projectivity → points
   classification → analytification+receipts).
3. F7 (the Hodge data) → F8 (the cycle word) → F9 (the law landing,
   `positive_dimensional_live_core_law h0cyc h1cyc hstash`).
4. The ω-core remains the campaign's fenced frontier: the sset-side
   computation (free) + the comparison theorem (the multi-month project)
   — or any future Mathlib upgrade that ships excision.
