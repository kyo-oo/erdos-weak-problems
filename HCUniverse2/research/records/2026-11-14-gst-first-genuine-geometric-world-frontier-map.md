# 2026-11-14 — The first genuine geometric world: the construction frontier map

**Provenance:** the final assault's honest content boundary (W7-E) and
battle notes name the next frontier: *construct the first genuine geometric
world `(V₀, H₀)` so the owner's twelve-cell cyclic fold can be realized as
a `RealizedCorrespondenceWord` on it.*  This record is the complete
construction map: every field's exact proof terms, verified against the
PINNED Mathlib source (`mathlib4` @ `51e6992efd06126df61a496bebf8f49482a4e129`,
the corpus's `lake-manifest.json` pin), the one remaining hard fact, and
the honest verdicts.  No Lean is claimed written here; this is the
LaTeX-first-for-new-geometry record the corpus's own law demands.

## Why the frontier was blocked (the original session's three walls)

1. `Smooth` for a concrete scheme: zero constructions corpus-wide; no
   attested Mathlib route to smoothness of any concrete structure map.
2. Singular cohomology of a concrete space: never computed anywhere in
   Mathlib or the corpus — the `hodgeBigrading` fields and every
   cyclicity obligation looked unreachable.
3. A concrete `(V, H)` pair: zero exist in the repository; the recon's
   verdict: "all three semantic inputs of the Hodge side have zero
   constructor support."

## Wall 1 is DEAD at the pin (the smoothness arsenal)

* **Isomorphisms are smooth:** `AlgebraicGeometry.IsOpenImmersion.of_isIso`
  (`Mathlib/AlgebraicGeometry/Morphisms/OpenImmersion.lean:481`, priority
  100) + `instance (priority := 900) [IsOpenImmersion f] : Smooth f`
  (`Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean:182-184`).  Proof
  term: `inferInstance` for any `𝟙`.
* **Empty-source morphisms are smooth:** `instance (priority := 100)
  isOpenImmersion_of_isEmpty (f : X ⟶ Y) [IsEmpty X] : IsOpenImmersion f`
  (`Mathlib/AlgebraicGeometry/Limits.lean:107`).
* **The étale-Pi chain (the 12-point carrier):** `Algebra.Etale R R`
  (`Mathlib/RingTheory/Etale/Basic.lean:221`) → `instance [Finite I]
  [∀ i, Etale R (A i)] : Etale R (Π i, A i)`
  (`Mathlib/RingTheory/Etale/Pi.lean:39`) → `instance [Etale R A] :
  Smooth R A` (`Etale/Basic.lean:223`) → `RingHom.smooth_algebraMap`
  (`Mathlib/RingTheory/RingHom/Smooth.lean:82`).  **So
  `Smooth` of the structure map of `Spec (Fin 12 → ℂ)` over `Spec ℂ` is
  pure instance synthesis.**
* Supporting: `IsFinite.SpecMap_iff` + `Module.Finite.pi` ⇒ `IsFinite` ⇒
  `IsProper` (`Morphisms/Proper.lean:69`).

## Wall 2 is DEAD at the pin (the cohomology arsenal)

`Mathlib/AlgebraicTopology/SingularHomology/Basic.lean:104-143` computes
the singular homology of **totally disconnected spaces**:

* `singularChainComplexFunctorIsoOfTotallyDisconnectedSpace` (:110): the
  chain complex of a totally disconnected space is iso to
  `ChainComplex.alternatingConst.obj (∐ fun _ : X ↦ R)`.
* `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace` (:126):
  `IsZero (H_n)` for every `n ≠ 0`.
* `singularHomologyFunctorZeroOfTotallyDisconnectedSpace` (:136):
  `H₀ ≅ ∐ fun _ : X ↦ R` — for a 12-point space, the free ℚ-module of
  rank 12.

The corpus's `RationalSingularCohomology` is the COHOMOLOGY (the homology
of `linearYonedaObj`-dualized cochains, `GSTGeometricRealizationStage2F.lean:79-99`).
The cohomology version follows by functoriality: the chains-iso dualizes
(`linearYonedaObj` applied to an iso is an iso) and homology of iso
complexes is iso; the dual of `alternatingConst (∐_{12} ℚ)` has the same
parity scalars, so `H⁰ ≅ (∐_{12} ℚ)^*` and `H^{n≠0} = 0` (finite free
duality).  **The twelve-cell world IS the H⁰ of a 12-point discrete space:
rank 12, everything (0,0)-type — the honest Hodge structure of a
zero-dimensional analytic space.**

## The 12-point world — field by field (the construction plan)

Carrier: `V₀.X := Spec (.of (Fin 12 → ℂ))`, equivalently
`∐_{i : Fin 12} Spec ℂ` via `IsIso (sigmaSpec _)`
(`Mathlib/AlgebraicGeometry/Limits.lean:641`).

1. `V₀.structureMap := Spec.map (CommRingCat.ofHom (algebraMap ℂ (Fin 12 → ℂ)))`
   (the diagonal).
2. `V₀.smooth := inferInstance` (the étale-Pi chain above).
3. `V₀.projective`: **the single hard fact.**  A closed immersion
   `Spec ℂ^12 ⟶ projectiveSpace n` over `Spec ℂ` (12 distinct ℂ-points of
   ℙ¹ as a closed subscheme).  Route: the evaluation ring map
   `ℂ[T] → ℂ^12` (`T ↦ (a₁,…,a₁₂)` for 12 distinct `aᵢ`) is surjective
   (Lagrange interpolation — check Mathlib's
   `Mathlib/LinearAlgebra/Lagrange.lean` support), so `Spec.map` of it is a
   closed immersion (`IsClosedImmersion.spec_of_surjective`,
   `ClosedImmersion.lean:98-102`); then compose with the standard open
   `𝔸¹ = D₊(T₁) ⊂ Proj ℂ[T₀,T₁]` and prove the composite closed into ℙ¹
   (`IsClosedImmersion.of_isPreimmersion` + closed range — a finite set of
   closed points is closed).  Feasible-but-real work; no single existing
   lemma closes it.  **This is the frontier's one remaining wall.**
4. `H₀.analytification := ⟨space := TopCat.discrete.obj (Fin 12),
   pointsEquiv := …⟩`: the equivalence from `ComplexPoint V₀` (the 12
   ℂ-algebra maps `ℂ^12 → ℂ`, classified by
   `PrimeSpectrum.exists_commap_evalRingHom_eq`
   (`Mathlib/RingTheory/Spectrum/Prime/RingHom.lean:164`) +
   `Unique (PrimeSpectrum ℂ)` (`Spectrum/Prime/Basic.lean:399`) +
   `Spec.map_eq_id`), built through `Spec.homEquiv`
   (`Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean:579`) and
   `sigmaToPiHomeo` (`Spectrum/Prime/Topology.lean:718`).
5. `H₀.hodgeBigrading`: the honest zero-dimensional bigrading — at
   `2p = 0`: `component 0 := ⊤`, all others `⊥` (valid for ANY module:
   `iSupIndep` of a family with `⊥`-tail + `⨆ = ⊤` by the `⊤`-head); at
   `2p ≥ 2`: the module is the zero module (`IsZero`), where every
   component family trivially satisfies both laws.  This is the GENUINE
   Hodge bigrading of `H⁰` (everything is (0,0)) — not a rigged span.
6. `H₀.cycleClass`: the honest degree map
   `codimensionCycles V₀.X 0 →ₗ[ℚ] H⁰ ≅ ∐_{12} ℚ` (a 0-cycle
   `Z = Σ aᵢ pᵢ ↦ (a₁,…,a₁₂)` — the genuine class map of a
   zero-dimensional variety).
7. The certificate at the live weight `p = 0` (rank 12 — exactly the
   owner's twelve-cell world): the fold `T = U + J + M` as a
   `RealizedCorrespondenceWord` — 12×12 point-correspondence letters
   (carrier = `Spec` of quotient algebras of `ℂ^144`, closed immersion
   into `selfProduct V₀` via `spec_of_surjective`, finite left fibers via
   the finite spectrum), the matrix-unit operators on `H⁰`, the
   `realizes_on_points` pointwise equations, the genuine seed
   `e_{(0,0)} + e_{(0,1)}`, and the cyclicity = Face 1's Gauss-Jordan
   Krylov certificate (det −1149656584000 ≠ 0) transported through the
   `H⁰`-iso.  No-free-lunch is satisfied honestly: every Hodge class of
   this world is genuinely algebraic (the indicator classes of points).

## The rejected alternative

The EMPTY world (`Scheme.empty`, `Limits.lean:77-102`) is constructible
with every field a one-liner — and is REJECTED: its fibers are all dead,
instantiating the already-discharged cheap class, adding zero theorems;
the corpus's own semantic firewall
(`HodgeConjecture.lean:746-772`, `zeroCycleClassData`) exists precisely
to refuse content-free worlds, and the campaign's battle notes demand a
world that can HOST the twelve-cell fold.

## Verdict

The first genuine geometric world is constructible in Lean at the pinned
toolchain, with ONE remaining wall (the closed immersion
`Spec ℂ^12 ⟶ ℙ¹_ℂ`) and one computation block (the cohomology
dualization + the pointwise realization equations).  This is a multi-file
development for a verified round with CI available — the next campaign's
opening assault.  The reconstruction/registration state of the campaign
chain it will import is recorded in
`2026-11-14-gst-native-law-to-fs-hypothesis-bridge.md`.
