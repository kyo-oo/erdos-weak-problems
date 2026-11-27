# 2026-11-14 — The twelve-point native geometric world: the first genuine (V, H) and the first live-weight discharge

**Provenance:** W3-F, the record-writer wave of the GST hypothesis campaign.  This is
the LaTeX-first derivation record for the first genuine geometric world, per the corpus's
own law (AGENTS.md: "LaTeX first for new geometry, then Lean after substantive mathematical
derivation").  It completes the plan of
`2026-11-14-gst-first-genuine-geometric-world-frontier-map.md`: the concrete pair `(V₀, H₀)`
that map designed, with the owner's twelve-cell fold realized as a genuine
`RealizedCorrespondenceWord` on it.  The Lean landing runs as the parallel author wave —
`GSTTwelvePointWorldCarrier.lean`, `GSTTwelvePointAnalytification.lean`,
`GSTTwelvePointCohomology.lean`, `GSTTwelvePointHodgeData.lean`,
`GSTTwelvePointFoldWord.lean`, and the landing module `GSTTwelvePointLawLanding.lean`
(a parallel agent writes it).  Every external lemma name below is the pinned Mathlib's
(`mathlib4` @ `51e6992efd06126df61a496bebf8f49482a4e129`); every number is exact rational
data verified this campaign.  No Lean compilation is claimed from this sandbox.

## What this is

The main target `NativeGSTSingleFoldOrbitLaw` (`GSTHodgeSingleHypothesisConditional.lean:50-55`):

```
∀ p : Nat, ∃ C : RealizedCorrespondenceKrylovCertificate V H p, C.IsKrylovCyclic
```

had, before this construction, never been discharged for any
`(V, H : HodgeBigradedBettiData V)` — it appeared only as the hypothesis of
`exactHodge_of_one_GST_fold_orbit` — and zero concrete `(V, H)` pairs existed anywhere in the
repository (no `AnalytificationData`, no `HodgeBigrading` instance, not even a bundled
`Spec ℂ`).  The 2026-11-14 landing module discharged the entire cheap class (dead or
monogenic weights, via the empty word) and proved the no-free-lunch boundary: cyclicity at
a live weight of rank ≥ 2 forces a genuine algebraic cycle.  The live core was untouched —
because no world to host it existed.

This record documents that world, now under construction by the parallel author wave:
**V₀ := Spec(ℂ¹²) — twelve disjoint complex points** — the world whose weight-0 Hodge fiber
is the owner's twelve-cell fiber (`H⁰ ≅ (Fin 12 → ℚ)`, rank 12 — LIVE rank ≥ 2), on it the
fold T = U + J + M as 26 genuine point-pair correspondences, and the certificate that
discharges the law at a live weight for the first time.  The rejected alternative (the empty
world, all fibers dead — the already discharged cheap class) was rejected by the frontier map:
the world is chosen to HOST the twelve-cell fold.

## The construction

### Part 1 — the world (`GSTTwelvePointWorldCarrier.lean`)

`V₀.X := Spec (.of (Fin 12 → ℂ))`, equivalently `∐_{i : Fin 12} Spec ℂ` via
`IsIso (sigmaSpec _)` (`Mathlib/AlgebraicGeometry/Limits.lean:641`); the structure map is the
diagonal `Spec.map (algebraMap ℂ (Fin 12 → ℂ))`.

1. **Smooth** — pure instance synthesis through the étale-Pi chain: `Algebra.Etale ℂ
   (Fin 12 → ℂ)` (the self-instance `Mathlib/RingTheory/Etale/Basic.lean:221` on each factor
   ℂ + the Pi instance `Mathlib/RingTheory/Etale/Pi.lean:39`) → `instance [Etale R A] :
   Smooth R A` (`Etale/Basic.lean:223`) → `RingHom.smooth_algebraMap`
   (`Mathlib/RingTheory/RingHom/Smooth.lean:82`) → `HasRingHomProperty.Spec_iff`
   (`Mathlib/AlgebraicGeometry/Morphisms/RingHomProperties.lean:360`); `V₀.smooth :=
   inferInstance`.
2. **Projective** — the frontier map's one remaining wall, resolved by the Lagrange-
   interpolation assembly.  The ring map `f := MvPolynomial.aeval ![a, 1] : ℂ[X₀,X₁] →ₐ ℂ¹²`
   with `a i = i` (twelve distinct values): `f(X₁) = 1` makes the irrelevant ideal map to ⊤,
   so `Proj.fromOfGlobalSections`
   (`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:443`) gives
   `Spec(ℂ¹²) ⟶ Proj ℂ[X₀,X₁] = ℙ¹`.  Closed immersion by Zariski-locality on the two charts
   `D₊(X₀)`, `D₊(X₁)` + `IsClosedImmersion.spec_of_surjective`
   (`Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean:101`); chart surjectivity is
   Lagrange interpolation — `Lagrange.interpolate univ a values` with `Set.InjOn a univ` from
   the distinctness of the twelve values (`Mathlib/LinearAlgebra/Lagrange.lean:299`) —
   transported to the homogeneous charts through `Polynomial.homogenize` (degree ≤ 11) +
   `aeval_homogenize_of_eq_one`.
3. **Dimension zero** — every point has coheight 0: `ℂ¹²` is Artinian, all primes maximal,
   each prime `ker (eval i)` (`PrimeSpectrum.exists_comap_evalRingHom_eq`,
   `Mathlib/RingTheory/Spectrum/Prime/RingHom.lean:164`).  Twelve closed points, no
   positive-dimensional local geometry anywhere.

### Part 2 — the Hodge data (`GSTTwelvePointAnalytification.lean`,
`GSTTwelvePointCohomology.lean`, `GSTTwelvePointHodgeData.lean`)

4. `H₀.analytification := ⟨space := TopCat.discrete.obj (Fin 12), pointsEquiv := …⟩` — the
   discrete 12-point space.  `ComplexPoint V₀ ≃ Fin 12`: sections over `Spec ℂ` are the twelve
   evaluation algebra maps `ℂ¹² →ₐ ℂ`, classified through `Spec.homEquiv`
   (`Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean:579`) + kernel-maximality +
   `exists_comap_evalRingHom_eq`.
5. **The singular cohomology — the first computation of the corpus's
   `RationalSingularCohomology` of an actual concrete space.**  Chains ≅
   `ChainComplex.alternatingConst.obj (∐₁₂ ℚ)` by
   `singularChainComplexFunctorIsoOfTotallyDisconnectedSpace`
   (`Mathlib/AlgebraicTopology/SingularHomology/Basic.lean:110`); the `linearYonedaObj`-
   dualized cochains have differential alternating 0/id; therefore `H⁰ = Hom(∐₁₂ ℚ, ℚ) ≅
   (Fin 12 → ℚ)` (through `biproductIsoPi` + `homCongr` + `Basis.constr`) and `Hⁿ = 0` for
   `n ≥ 1` (`isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`, :126; the ker/im
   computation on the alternating complex; `singularHomologyFunctorZeroOfTotallyDisconnectedSpace`,
   :136, the homology side).
6. `H₀.hodgeBigrading` — the honest (0,0)-grading: at weight `2p = 0` the bigrading of `H⁰`
   has the single component `H^{0,0} = ⊤` (weight-0 means one index; independence and
   spanning are the `⊤`-head laws, valid for any module); at `2p ≥ 2` the module is the zero
   module, where the component laws hold trivially.  Everything is (0,0)-type — the genuine
   Hodge structure of a 0-dimensional analytic space, not a rigged span; dead weights above.
7. `H₀.cycleClass` at `p = 0` — the genuine degree map `codimensionCycles V₀.X 0 →ₗ[ℚ] H⁰ ≅
   (Fin 12 → ℚ)`: a 0-cycle `Z = Σ aᵢ pᵢ ↦ (a₁,…,a₁₂)` (the multiplicity vector through the
   H⁰ iso); point classes are the indicator vectors (`Pi.single`).

### Part 3 — the fold (`GSTTwelvePointFoldWord.lean`)

8. **T = U + J + M realized as a genuine `RealizedCorrespondenceWord`** — 26 weighted
   point-pair correspondences `(i, j, q)`: for each nonzero entry `q = Twave r c`, one letter
   whose left leg is `p_c`, right leg `p_r`, weight `q`.  Each letter is the closed point-pair
   subscheme `Spec ℂ ⟶ X ×_ℂ X`: `spec_of_surjective` of the evaluation composite on the
   tensor product (`ℂ¹² ⊗_ℂ ℂ¹² ≅ ℂ¹⁴⁴` through `pullbackSpecIso`), finite legs, residue
   degree 1.  The realization equation on all 12 point classes is the matrix column: the
   word's operator sends `e_j ↦ Σᵣ Twave r j • e_r` (`Twave.mulVec`), so the word operator
   IS the Twave matrix.  The 26 nonzero entries: `(0,0)=1, (0,11)=1, (1,4)=1, (1,10)=1,
   (2,8)=1, (2,9)=−1, (3,1)=1, (3,8)=1, (4,4)=1, (4,5)=1, (4,7)=1, (5,6)=1, (5,9)=1,
   (6,2)=1, (6,5)=−1, (7,4)=−1, (7,6)=1, (8,3)=−1, (8,8)=1, (8,10)=1, (9,2)=1, (9,3)=1,
   (10,1)=−1, (10,7)=1, (11,0)=−1, (11,11)=3` — the owner's `Twave`
   (`GSTHypothesisSpanningCompilerFace.lean:63-77`), there proved to BE the owner's fold
   `N12` (`Twave_bridge`, 144 decide checks).

### Part 4 — the law (`GSTTwelvePointLawLanding.lean`)

9. **The certificate at the live weight `p = 0`** (rank 12 — the LIVE rank ≥ 2 case, the
   owner's twelve-cell fiber): the 26-letter word + the genuine seed cycle `e_{(0,0)} +
   e_{(0,1)}` (two point cycles; `coordSeed` = indicator of the two leading cells).
   `word_hodge` / `seed_hodge` at the maximal fiber (`rationalHodgeSubspace
   (H₀.hodgeBigrading 0) = ⊤`, since H⁰ is all (0,0)-type).  `IsKrylovCyclic`: the orbit IS
   the Krylov table — the twelve iterates of the seed under the word operator span
   `(Fin 12 → ℚ)`; the exact Gauss-Jordan certificate is the nonzero Krylov determinant
   `−1149656584000 ≠ 0` (§ The numeric certificate).
10. **Dead weights `p ≥ 1` are FREE**: `H^{2p} = 0` by Part 2, so the fibers are subsingleton
   and the empty-word discharge (`isKrylovCyclic_of_subsingleton`,
   `emptyWordKrylovCertificate` — the landing module's own cheap-class machinery) applies.
11. **CONSEQUENCE:** `NativeGSTSingleFoldOrbitLaw V₀ H₀` — the first discharge at a LIVE
   weight — through `gst_FS_of_native_law` (`GSTNativeSingleFoldOrbitLawLanding.lean:513-523`):
   for every `p` a genuine typed datum with `GSTHypothesisComplete D ∧ D.hodgeFiber =
   rationalHodgeSubspace (H₀.hodgeBigrading p)` — the native⇒typed bridge, both instantiated
   and FED for the first time; and `EveryHodgeClassIsRationalAlgebraic H₀` through
   `exactHodge_of_one_GST_fold_orbit` — honest: every Hodge class of the twelve-point world
   is genuinely algebraic (the indicator classes of points, `exists_cycle` at each weight).

### Part 5 — the honest scope

The world is zero-dimensional: the law's content here is the twelve-cell spanning at
weight 0.  The weight-≥2 fibers (`2p ≥ 2`) are DEAD by dimension (`H^{≥1} = 0`); the
positive-dimensional live core (the `p ≥ 1` with `H^{2p} ≠ 0` case) requires a
positive-dimensional world and remains open.  The twelve-cell fold is realized as genuine
correspondences on a native world — the first time the typed twelve-cell cyclic content
(Face 1 / Face 2) has an actual scheme-theoretic carrier.

## What is proved (exact statements)

* `GSTTwelvePointWorldCarrier.lean` — `V₀ : SmoothProjectiveComplexScheme` with
  `V₀.X = Spec (.of (Fin 12 → ℂ))`, `V₀.smooth` by the étale-Pi chain (1.1),
  `V₀.projective` by the Lagrange assembly (1.2), the coheight-0 statement (1.3).
* `GSTTwelvePointAnalytification.lean` — `H₀.analytification : AnalytificationData V₀` with
  `space = TopCat.discrete.obj (Fin 12)` and `ComplexPoint V₀ ≃ Fin 12` (2.4).
* `GSTTwelvePointCohomology.lean` — the chains-iso, the H⁰ iso
  `RationalSingularCohomology H₀.analytification 0 ≅ (Fin 12 → ℚ)`, the vanishing
  `Hⁿ = 0` for `n ≥ 1` (2.5).
* `GSTTwelvePointHodgeData.lean` — `H₀ : HodgeBigradedBettiData V₀`: the honest
  (0,0)-`hodgeBigrading` (2.6) and the degree-map `cycleClass` (2.7) — the first concrete
  inhabitant of the Stage-2F/2G semantic stack.
* `GSTTwelvePointFoldWord.lean` — the 26-letter word: `RealizedCorrespondenceWord V₀ H₀ 0`
  whose `realizedWordPair` cohomology operator is the Twave matrix under the H⁰ iso, with
  the pointwise realization equations (3.8).
* `GSTTwelvePointLawLanding.lean` (parallel agent) — the certificate
  `C : RealizedCorrespondenceKrylovCertificate V₀ H₀ 0` (26-letter word, `word_hodge`/
  `seed_hodge` at the maximal fiber, seed `e_{(0,0)} + e_{(0,1)}`, `IsKrylovCyclic` by the
  Gauss-Jordan certificate), the per-weight assembly `NativeGSTSingleFoldOrbitLaw V₀ H₀`,
  and the master composition: `gst_FS_of_native_law` at `(V₀, H₀)` (per-weight
  `GSTHypothesisComplete` on genuine data) + `EveryHodgeClassIsRationalAlgebraic H₀` via
  `exactHodge_of_one_GST_fold_orbit`.

## The numeric certificate

* **The Krylov determinant**: `det K = −1149656584000 ≠ 0`, where `K = [C 0, C 1, …, C 11]`
  is the 12×12 orbit table of the seed under the Twave operator.  First entries of the orbit
  (the Krylov table, `Cvec` of the compiler face): `C 0 = e₀ + e₁` (the seed),
  `C 1 = e₀ + e₃ − e₁₀ − e₁₁`, `C 2 = −e₁ − 2e₈ + e₉ − 4e₁₁`,
  `C 3 = −4e₀ − 3e₂ − 3e₃ + e₅ − 2e₈ + e₁₀ − 12e₁₁`, …
* **Three independent algorithms** (all exact, no numerical tolerance):
  1. the exact Wolfram Krylov computations of the 2026-11-11/12 campaign
     (`research/computations/GST_originalX_GST_wave_Chow_orbit_inverse_20261111.wl`,
     `GST_originalX_full_N_physical_wave_Chow_CRT_20261111.wl`, the five `GST_20261112_*.wl`
     audit scripts — every one asserts `Det == −1149656584000`);
  2. the independent SymPy audit `research/computations/
     GST_20261112_independent_sympy_original12_spectral_audit.py` — rebuilds U, J, M from the
     original 4×3 Wave-I definitions with no Wolfram output consumed, asserts
     `k0.det() == −1149656584000` (and `U⁵ = I`, `J² = −I`, `UJ = JU`; the Navigation-ON
     determinant `−445265540949` also verified nonzero);
  3. the Lean Gauss-Jordan certificate — Face 1's `span_range_worldOrbit_eq_top` and Face 2's
     `eIdx_eq_cert` / `span_range_C_eq_top` (`GSTHypothesisSpanningProof.lean`,
     `GSTHypothesisSpanningCompilerFace.lean:228-255`): the explicit inverse table is a
     constructive two-sided-inverse proof, hence a kernel-checked certificate of `det ≠ 0`.
* **The Gauss-Jordan inverse table = Face 2's `certRow`**
  (`GSTHypothesisSpanningCompilerFace.lean:212-226`): the 12×12 = 144 exact fractions
  expressing every indicator `eIdx s` as a rational combination of the twelve orbit values.
  Sample row `s = 4`: `−321340982133/71853536500, 289078573103/35926768250,
  1972211392251/287414146000, −222341135573/57482829200, −2561034108797/287414146000,
  1495609060489/114965658400, −1534796826903/143707073000, 4537167712259/574828292000,
  −139786417941/28741414600, 132586088003/57482829200, −30218089597/35926768250,
  88913498431/574828292000`.  Largest-magnitude coefficient
  `1495609060489/114965658400` (row 4, column 5); largest numerator
  `4537167712259/574828292000` (row 4, column 7); largest denominator `574828292000 =
  |det|/2` (adjugate/Cramer: every denominator divides the determinant).
* **Cross-checks**: all 144 fractions kernel-checked in Lean (`eIdx_eq_cert`,
  `fin_cases <;> fin_cases <;> norm_num`); the two Lean orbit tables (Face 1's `Kvec`/
  `worldOrbit` and Face 2's `Cvec`) are the same table in two indexings; the 26 Twave
  entries are decided (`Twave_bridge`, 144 decide checks); the SymPy seed
  `v = indicator{(0,0),(0,1)}` matches `coordSeed` and the genuine seed cycle of Part 4.

## Disclosure

* The Hodge conclusion on this world is honest but elementary: on a 0-dimensional space every
  rational cohomology class is (0,0)-type and every class is the class of a genuine 0-cycle
  (the degree map is an iso), so `EveryHodgeClassIsRationalAlgebraic H₀` carries no
  transcendental content.  What is NEW: (a) the first concrete `(V, H)` inhabitant of the
  full Stage-2F/2G semantic stack — the first `RationalSingularCohomology` computation of an
  actual space anywhere in the corpus; (b) the first discharge of the law at a LIVE weight of
  rank ≥ 2 — the no-free-lunch zone (rank 12), previously untouched; (c) the first FEEDING of
  the native⇒typed bridge: `gst_FS_of_native_law` was a conditional shell over an empty class
  of worlds; it is now instantiated and fed by the certificate.
* The fold's 26 letters are genuine closed correspondences (point-pair subschemes, finite
  legs, residue degree 1) — the operator content is actual geometry, not a free linear
  operator — but on a zero-dimensional world.
* This record is the LaTeX-first derivation (the corpus law); the Lean wave lands the same
  construction in the same tree; nothing in this sandbox is compiled; the numeric evidence
  class is exact rational arithmetic only (Wolfram/SymPy externally, Gauss-Jordan in Lean).

## Non-claims (exact scope)

* NOT the Hodge conjecture and not a positive-dimensional case: restricted lemmas under
  the AGENTS.md acceptance test; the world is 0-dimensional, every class is (0,0)-type.
* The weight-≥2 fibers are dead by dimension; the positive-dimensional live core
  (`p ≥ 1` with `H^{2p} ≠ 0`) requires a positive-dimensional world and remains open.  No
  smooth projective positive-dimensional `(V, H)` is constructed anywhere.
* The typed twelve-cell faces (`GSTHypothesisSpanningProof.lean`,
  `GSTHypothesisSpanningCompilerFace.lean`) and this native world remain formally distinct
  laws; the bridge used is native ⇒ typed only (`gst_FS_of_native_law`); no typed ⇒ native
  transport exists anywhere in the repository.
* No Lean compilation is claimed from this sandbox; no CI run exists at any SHA of this
  tree; no green run is cited (none exists).  The Wolfram/SymPy determinants are external
  exact evidence, not Lean proofs; the in-Lean certificate is the Gauss-Jordan inverse table.

## Registration

* `lakefile.toml`: new lean_lib `GSTTwelvePointNativeWorldUpgrade`, roots the six new
  modules — `GSTTwelvePointWorldCarrier`, `GSTTwelvePointAnalytification`,
  `GSTTwelvePointCohomology`, `GSTTwelvePointHodgeData`, `GSTTwelvePointFoldWord`,
  `GSTTwelvePointLawLanding` (the only closure modules not registered elsewhere; the full
  import closure is appended at CI time by `scripts/gst_lean_dependency_roots.py`).
* CI lane: `.github/workflows/gst-twelve-point-native-world.yml` — mirrors the hardened
  landing lane: elan `v4.33.0-rc2`, `lake exe cache get`, the dependency-roots script,
  `timeout 16800 lake build GSTTwelvePointLawLanding` (the five carrier roots first),
  `sorryAx` hard-fail, log artifact upload; triggers on push to `main` and
  `research/gpt6-gst-hypothesis-part1-chow-square-20261110` with the six-file path filter
  (+ the lane file itself) plus manual dispatch; job timeout 300 min.
* The six files: `GSTTwelvePointWorldCarrier.lean`, `GSTTwelvePointAnalytification.lean`,
  `GSTTwelvePointCohomology.lean`, `GSTTwelvePointHodgeData.lean`,
  `GSTTwelvePointFoldWord.lean`, `GSTTwelvePointLawLanding.lean` (the landing module by the
  parallel agent).

## CI status

No Lean compilation is claimed from this sandbox.  The lane above owns the kernel check;
per AGENTS.md rule 7, no green run is cited until the run exists at the pushed SHA.  None
exists yet — the six modules are landing in the parallel wave; the kernel verdict belongs to
GitHub CI at the pushed SHA.
