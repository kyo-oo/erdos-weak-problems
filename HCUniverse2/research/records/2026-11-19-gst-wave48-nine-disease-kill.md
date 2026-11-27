# 2026-11-19 — Wave 48: the nine-disease kill — the pre-hunted first compile of the two downstream files

## The directive

BOSS: "okay okay do not stop!! full agresxsion and continue and are you
mapping evbery round detailed worklog? continue invoke the skill and
complete the proof!!"

The prove-that-shit skill is invoked; this record IS the round worklog.

## The state at round open

* The kit (`GSTPositiveDimensionalLiveCoreKit.lean`) is CI-GREEN since
  run 44382896351 (a6ceb54).
* The law lane (`gst-positive-dimensional-live-core-law.yml`) is at 12
  runs, all RED.  Wave 47.9 (9bdcb45, run 44455008683) left exactly ONE
  error in `GSTComponentCohomologyZero.lean:259:7`.
* The two downstream files (`GSTSphereUnionComponents.lean`,
  `GSTPositiveDimensionalLiveCoreLaw.lean`) import the sick file and
  have NEVER been compiled — 100% unadjudicated surface.

## The root-cause of the last error (first-hand pin verification)

Error body: `ModuleCat.Hom.hom φ` has type
`↑(Opposite.unop (Opposite.op ((rationalSingularChains A).X 0))) →ₗ[ℚ] ↑rationalCoefficient`
but is expected to have type `↑((rationalSingularCochains A).X 0) →ₗ[ℚ] ℚ`.

Ground truth chain, every link fetched from the pinned Mathlib
(51e6992efd06126df61a496bebf8f49482a4e129, v4.33.0-rc2):

1. `ChainComplex.linearYonedaObj` (Mathlib/CategoryTheory/Abelian/Ext.lean:58,
   `@[simps! X d]`): the cochain complex "in degree i consists of the
   module of morphisms `X.X i ⟶ Y`" — the dual's elements ARE
   `ModuleCat.Hom`-structures; the domain object is the
   `Opposite.unop (Opposite.op …)`-wrapped chain degree.
2. `ModuleCat.Hom` (Mathlib/Algebra/Category/ModuleCat/Basic.lean:92):
   a structure with field `hom'`; `Hom.hom` is the abbrev projection;
   `ofHom_apply : ofHom f x = f x := rfl` (line 185);
   `example (M : ModuleCat R) : of R M = M := by with_reducible rfl`
   (line 86 — the of-carrier roundtrip is REDUCIBLE).
3. Therefore the ascription `(φ.hom : (rationalSingularCochains A).X 0 →ₗ[ℚ] ℚ)`
   demanded the BIDUAL (domain = the space of cochains) — mathematically
   wrong, never compilable.  The CHAIN spelling
   `(φ.hom : (rationalSingularChains A).X 0 →ₗ[ℚ] ℚ)` is the green form
   (already compiling at `leftComp_apply_eq`, proven BY rfl).

THE FIX (one word): line 259 `rationalSingularCochains` → `rationalSingularChains`.
The show-bridge's defeq chain to the goal `d 0 1 φ = 0` is then the
composition of three green links: `cochains_d_zero_one` (exact-proven),
`ofHom_apply` (rfl), `leftComp_apply_eq` (rfl) — all at default transparency.

## The pre-hunt (the two never-compiled files, audited BEFORE the push)

Every suspect API was verified first-hand against the pin:

* `Path` (Mathlib/Topology/Path.lean:58): extends `C(I, X)` — **NO `.hom`
  field**; `Path.source : γ 0 = x`, `Path.target : γ 1 = y` (lines 96-100);
  `Path.continuous`; **`Path.map (γ) (h : Continuous f)` takes a
  CONTINUITY PROOF, not a ContinuousMap structure** (line 342).
* `I = unitInterval` (Mathlib/Topology/UnitInterval.lean:36) — an ABBREV
  for `Set.Icc 0 1`; `instance : ConnectedSpace I` at line 164 (rides the
  abbrev, TC finds it at `↥(Set.Icc 0 1)`).
* `ZerothHomotopy.lift (f) (hf : ∀ ⦃x y⦄ (_ : Path x y), f x = f y)`
  (Mathlib/Topology/Connected/PathConnected.lean:149) — the hf needs the
  three-binder form (the wave-47.1 receipt), and the direction is
  `f x = f y` (the sphere file's `.symm` was REVERSED).
* `joinedIn_iff_joined (x_in) (y_in) : JoinedIn F x y ↔ Joined (⟨x, _⟩ : F) (⟨y, _⟩ : F)`
  (PathConnected.lean:205) — the sphere file's usage is CORRECT (IsPathConnected
  destructures to JoinedIn, `.mp` lands in the subtype-Path).
* `isPathConnected_sphere (h : 1 < Module.rank ℝ E) (x) (hr : 0 ≤ r)`
  (Mathlib/Analysis/Normed/Module/Connected.lean:209) — arg order verified.
* `finrank_euclideanSpace_fin {n} : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n`
  — ROOT-LEVEL (Mathlib/Analysis/InnerProductSpace/PiL2.lean:207, the
  EuclideanSpace namespace starts at line 210, AFTER it).
* `Module.finrank_eq_rank [Module.Finite R M] : ↑(finrank R M) = rank R M`
  — inside `namespace Module` (Mathlib/LinearAlgebra/Dimension/
  StrongRankCondition.lean:523).
* `isOpen_range_sigmaMk {i} : IsOpen (range (@Sigma.mk ι σ i))` and
  `continuous_sigmaMk {i}` (Mathlib/Topology/Constructions.lean:1248/1229).
* `Subtype.connectedSpace (h : IsConnected s) : ConnectedSpace ↥s`
  (Mathlib/Topology/Connected/Basic.lean:753) — **`IsConnected.connectedSpace`
  does NOT exist** (the dot-notation would fail).
* `isConnected_Icc (h : a ≤ b) : IsConnected (Icc a b)`
  (Mathlib/Topology/Order/IntermediateValue.lean:492) — **ONE explicit
  proof argument**, not two index arguments.
* `Pi.basisFun_apply` (Mathlib/LinearAlgebra/StdBasis.lean:126):
  **`basisFun R η i = Pi.single i 1` — basisFun-FIRST** — the law file's
  `.symm` was REVERSED at BOTH sites.
* `LinearIndependent.comp` (Mathlib/LinearAlgebra/LinearIndependent/Basic.lean)
  is the **INDEX-reindexing** lemma; the value-map lemma is
  `LinearIndependent.map' (hv) (f : M →ₗ[R] M') (hf_inj : LinearMap.ker f = ⊥)
  : LinearIndependent R (f ∘ v)` (line 348) — the law file passed a VALUE
  map to `.comp` — WRONG LEMMA.
* `Submodule.map_eq_top_of_surjective` — **DOES NOT EXIST**.  The correct
  lemma for linear equivs: `Submodule.map_eq_top_iff` (protected,
  Mathlib/Algebra/Module/Submodule/Map.lean:444).  But the whole span
  bullet was rebuilt on the membership route instead (below).
* `Submodule.apply_mem_span_image_of_mem_span (f) (h : x ∈ span R s) :
  f x ∈ span R₂ (f '' s)` (Mathlib/LinearAlgebra/Span/Basic.lean:263) —
  the span-membership transport WITHOUT any image-rewriting.
* `Submodule.map_span / span_image / span_image_linearEquiv`
  (Span/Basic.lean:73/254/259) — available but NOT used: the law file's
  `E.symm ''` vs `↑E.symm ''` coe-spelling is exactly the kabstract trap
  the finite-point lane died on in its wave 20 — the membership route
  avoids it entirely.
* `LinearMap.ker_eq_bot` (Mathlib/Algebra/Module/Submodule/Ker.lean) —
  corpus-green usage exists; `EquivLike.injective` (23 Mathlib usages).
* `Set.eq_univ_of_forall` — proves `s = univ`, CANNOT close a
  `A = ⋃ …` goal (the sphere file's preimage computation was ill-typed).

## The nine fixes applied this wave

| # | File:Site | Disease | Fix |
|---|-----------|---------|-----|
| C1 | ComponentCohomologyZero:259 | the bidual ascription (the last error) | `rationalSingularCochains` → `rationalSingularChains` |
| S1 | SphereUnion:133-152 | `p.hom` (nonexistent field); the `⟨0,_⟩` rfl-shows | rewritten on the pinned Path API: `p t`, `p.source/p.target`, `congrFun hb 0/1` |
| S2 | SphereUnion:117 | `Set.eq_univ_of_forall` on a `= ⋃` goal | `ext z` + membership-iff with `⟨z.1, h, z.2, rfl⟩` |
| S3 | SphereUnion:229 | the `.symm` reversal + one-binder hf | `fun _ _ p => sigma_path_index_const p` |
| S4 | SphereUnion:217-219 | `γ.map { toFun := … }` (Path.map takes a proof) | `γ.map hcont` |
| L1 | Law:158 | `Pi.basisFun_apply … .symm` reversed | drop the `.symm` |
| L2 | Law:159 | `hbasis.comp E.symm …` (wrong lemma) | `hbasis.map' (↑E.symm : …) (LinearMap.ker_eq_bot.mpr (EquivLike.injective E.symm))` |
| L3 | Law:173 | the same `.symm` reversal | drop the `.symm` |
| L4 | Law:174-179 | `Submodule.map_eq_top_of_surjective` (nonexistent) + the image/coe kabstract trap | rebuilt on `Submodule.eq_top_iff'` + `apply_mem_span_image_of_mem_span` + `span_le` — zero image-rewrites |

## The honesty ledger

* Zero mathematics changed: every theorem statement is byte-identical to
  the wave-46 declarations; only proofs and elaboration spellings repaired.
* Zero `sorry`, zero new axioms, zero `native_decide`.
* The lane's kernel check (sorryAx-gate) owns the certification.
* The three-file push triggers `gst-positive-dimensional-live-core-law.yml`
  (path filter covers all three files) — this is the FIRST run on which
  the two downstream files are even elaborated.

## The target after this wave

| Target component | State |
|---|---|
| The kit (algebra engine) | GREEN (run 44382896351) |
| The component H⁰ machine | one-word fix pushed this wave |
| The sphere-union component machine | four fixes pushed this wave (first compile) |
| The merged law file | four fixes pushed this wave (first compile) |
| Weight-1 honest point classes (sphere machine) | OPEN (fenced gate — the disclosed hypothesis) |
| The scheme carrier `finiteLineWorld M` | OPEN (the frozen next kill) |

## WAVE 49 ADDENDUM (run 44513557276, 5c6d671 — the adjudication)

**THE COMPONENT H⁰ MACHINE IS GREEN**: `Built GSTComponentCohomologyZero`
(warnings only) — the one-word bidual fix landed; the custom
positive-dimensional cohomology tool
(`componentCohomologyZeroEquiv : H⁰(A) ≃ₗ (ZerothHomotopy ↥A.space → ℚ)`,
computed through the genuine singular chain complex) is now CI-certified.

The sphere file's 13 latent diseases surfaced on its first compile (all
pre-hunted against the pin within the hour):

| # | Site | Disease | Fix |
|---|------|---------|-----|
| 1 | :92 | trailing `rfl` after a rw that auto-closed syntactically | deleted |
| 2 | :95 | `isClosed_compl_iff.mpr` (wrong direction) | `⟨hUcomplopen⟩` — `IsClosed`'s own constructor (`class IsClosed where isOpen_compl : IsOpen sᶜ`, Topology/Defs/Basic.lean:107) |
| 3 | :96 | `IsClopen` field order | `⟨hUclosed, hUopen⟩` (`def IsClopen := IsClosed s ∧ IsOpen s`, Topology/Defs/Basic.lean:111 — closed FIRST) |
| 4 | :100 | `Set.not_mem_empty` (renamed) | `Set.notMem_empty` (Data/Set/Basic.lean:321) |
| 5 | :111/:133 | `[DiscreteTopology ι]` without the superclass-parameter binder | `[TopologicalSpace ι]` added before it (DiscreteTopology takes TopologicalSpace as a class-parameter — must be synthesizable at the binder) |
| 6 | :195/:196 | `hj _ hs` — the `_` consumed the membership (both binders implicit-before-explicit) | `hj hs` |
| 7 | :116/:203-209 | `Sigma.mk (X := …)` — the parameter is named `β` | `(β := …)` |
| 8 | :229-230 | rw+rfl auto-close ambiguity in left_inv | `exact (ZerothHomotopy.sound p).symm` (the lift-eval/invFun-beta chains are rfl at default) |
| 9 | :250 | `∃ e : T :=` — missing the exists-body | `∃ e : … ≃ Fin M, True` + `⟨…, trivial⟩`; the law file's `obtain ⟨e⟩` → `⟨e, -⟩` |

The carrier battle map (reconnaissanced this round against the pin):
Mathlib HAS scheme coproducts (`CoproductsOfShapeDisjoint`, Limits.lean:224;
`Sigma.ι`, `Sigma.desc`, `isOpenImmersion_sigmaDesc`, "Spec preserves finite
coproducts"), a rich Proj API (`Proj.map` for graded ring homs + `map_comp`/
`map_id` for the M-cycle, `affineOpenCover`, `basicOpenIsoSpec`, `stalkIso`),
and polynomial/localization formal smoothness
(`instFormallySmoothMvPolynomial` + `Localization`-instance, RingTheory/
Smooth/Basic.lean:112/:497).  The quotient-graded-ring fight is AVOIDABLE:
the lean carrier is `∐ (Fin M) P¹` with the index-rotation M-cycle.

## WAVE 50 ADDENDUM (run 44517591925, 0f64bf8 — the adjudication)

The sphere machine's remaining three ROOT diseases (all first-hand
pin-verified before the fix):

1. **`Continuous` is a STRUCTURE at the pin** (Topology/Defs/Basic.lean:153,
   `structure Continuous (f : X → Y) : Prop where isOpen_preimage : …`) —
   `continuous_iff_isOpen_preimage` does not exist in this form; the
   preimage computation rebuilt on the structure constructor.
2. **The scoped `I`-notation** (`scoped[unitInterval] notation "I" =>
   unitInterval`, UnitInterval.lean:36) — `open unitInterval` added
   (Mathlib's own idiom, Topology/Path.lean:51).
3. **THE INSTANCE-SHADOW DISEASE** — the file's hand-rolled
   `inferInstance`-copies (`instTopologicalSpaceUnitSphereType`,
   `instTopologicalSpaceSphereUnionSpace`) shadowed the canonical
   subtype/sigma instances and broke elaboration-unification against
   `continuous_sigmaMk` (instance-defs cannot unfold at instances
   transparency) — BOTH DELETED; the abbrevs let TC find the canonical
   instances directly.
4. **The missing `open GSTProjectiveOverC`** — the file's
   `SmoothProjectiveComplexScheme` binder resolved to a foreign root-level
   homonym, mismatching `AnalytificationData`'s expectation — the green
   component file's open-list restored verbatim.

Run 44521065517 (cb2739b, wave 50) is the first run in which the sphere
machine and the merged-law file are expected to elaborate end-to-end.
