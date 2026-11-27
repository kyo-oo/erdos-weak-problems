# WAVE 8 — THE GATE-A FULL DISCHARGE: THE COMPLETE BATTLE DESIGN

Written by the commander (the wave-8 round). The design is FINAL: every
step verified against the pin (`research/pin/mathlib-51e6992/`) and the
green corpus. Two files land: the CORE (the machinery) and the DISCHARGE
(the assembly). EXECUTE EXACTLY THIS DESIGN. Companion dossier:
`research/records/2026-11-23-wave8-gate-restriction-dossier.md`.

## THE TARGET

`FiniteLinePointsGate M := ComplexPoint (finiteLineWorld M) ≃ (Sigma (fun _ : Fin M => Option ℂ))`
(the abbrev at GSTFiniteLineAnalytification.lean:403). Construct it
unconditionally for every `M ≥ 1`, then discharge the gate-formed
unconditional law (GSTFiniteLineUnconditionalSource.lean:148) by one
substitution.

## THE CLASSICAL CONTENT

A ℂ-point of M disjoint lines (= ℙ¹'s) is: a line index `i : Fin M` plus
a point of ℙ¹(ℂ) = `Option ℂ`. On line `i` (variables `X_{2i}, X_{2i+1}`):
the point `[a:b]` with `a = X_{2i}`, `b = X_{2i+1}` values, `(a,b) ≠ (0,0)`
(the cover: some variable avoided). If `a ≠ 0` (left chart territory): the
left coordinate is `b/a` — output `(i, some (b/a))`. If `a = 0` (so `b ≠ 0`,
right-chart only): the left coordinate is `∞` — output `(i, none)`.
`coordPoint` (GREEN, GSTFiniteLineAnalytification.lean:352-358) is the exact
inverse: `(i, some c) ↦ chartPoint (lineLeftChart M i) c`;
`(i, none) ↦ chartPoint (lineRightChart M i) 0` (the point `[0:1]` — whose
right coordinate `a/b = 0` because `a = 0`).

## FILE 1 — GSTFiniteLinePointsGateCore.lean (the machinery)

Preamble: mirror GSTFiniteLinePointsGate.lean's imports/opens (it is
CI-green at 4cf9e85) + `GSTFiniteLineAnalytification` + `set_option
maxHeartbeats 200000000` + `set_option maxRecDepth 1000000` +
`noncomputable section` + `namespace GSTFiniteLinePointsGateCore`.

### §0 THE ONE-POINT HEAD (the preimage law)

```
lemma complexBase_preimage_eq_top_of_mem {Y : Scheme} (p : complexBase ⟶ Y)
    (U : Y.Opens) (h : ∀ x : complexBase, p.base x ∈ U) : p ⁻¹ᵁ U = ⊤
```
Proof (dossier CARD B): `Subsingleton ↥complexBase` — the instance route
`inferInstanceAs (Subsingleton ↥(Spec (CommRingCat.of ℂ)))` (green corpus
route: GSTFinitePointShiftWord.lean:513 has the analogous instance
synthesis — VERIFY by searching the corpus for the exact green spelling of
a complexBase/Subsingleton or one-point receipt; if the instance does not
fire, author it from `PrimeSpectrum` of a field: `Subsingleton (ι) via
eq_bot_or_top`/`isField`... find the green route). Then opens-equality:
`TopologicalSpace.Opens.ext`/`eq_top_iff` + `Set.eq_univ_iff_forall`;
the membership dance `rw [← SetLike.mem_coe]; simp only
[TopologicalSpace.Opens.map_coe, Set.mem_preimage]` (the pin's own TODO'd
shape — Basic.lean:464-465's pattern; NO mem-lemma exists). The hypothesis
`h` reduces to the single point by `Subsingleton.elim`.

### §1 THE SECTION-INTO-CHART (the head composite)

```
noncomputable def sectionInto {Y : Scheme} (p : complexBase ⟶ Y)
    (U : Y.Opens) (hpre : p ⁻¹ᵁ U = ⊤) : complexBase ⟶ U.toScheme :=
  (Scheme.topIso complexBase).inv ≫ p.resLE U ⊤ hpre.ge
```
(Names: `Scheme.topIso` Restrict.lean:439 — `↑(⊤ : X.Opens) ≅ X` with
`.inv : X ⟶ ⊤.toScheme`; `Scheme.Hom.resLE` Restrict.lean:775 —
`resLE (f) (U) (V) (e : V ≤ f ⁻¹ᵁ U) : V.toScheme ⟶ U.toScheme := X.homOfLE e ≫ f ∣_ U`;
`e := hpre.ge : ⊤ ≤ p ⁻¹ᵁ U`.)

THE FACTORIZATION RECEIPT:
```
theorem sectionInto_ι {Y : Scheme} (p : complexBase ⟶ Y) (U : Y.Opens)
    (hpre : p ⁻¹ᵁ U = ⊤) : sectionInto p U hpre ≫ U.ι = p := by
  simp only [sectionInto, Category.assoc, ← Scheme.Hom.resLE_comp_ι]
  rw [← Scheme.toIso_inv_ι]   -- Restrict.lean:444-446, the simp lemma
                               -- topIso.inv ≫ ⊤.ι = 𝟙 (inv_hom_id form)
  simpa using Category.id_comp p   -- or exact (Category.comp_id p).symm shape
```
(`resLE_comp_ι` Restrict.lean:782 is `@[reassoc (attr := simp)] lemma
resLE_comp_ι : f.resLE U V e ≫ U.ι = V.ι ≫ f` — so the composite becomes
`topIso.inv ≫ ⊤.ι ≫ p` and `Scheme.toIso_inv_ι` kills the front pair.)

### §2 THE CHART LEG + THE READING (per chart variable j : Fin (2*M))

Notation: `chartVar M j := lineQuotientMap M (MvPolynomial.X j)` (the
variable's image in the line ring); `f_deg := lineCoverHomogeneousOneQ M j`
(the degree-1 membership, GREEN — used verbatim in GSTFiniteLineAnalytification
chartPointHomOf); `U j := Proj.basicOpen (lineGrading M) (chartVar M j)`.

```
noncomputable def chartLeg (M) [NeZero M] (j : Fin (2*M))
    (p : ComplexPoint (finiteLineWorld M)) (hpre : ...) :
    complexBase ⟶ Spec (.of (HomogeneousLocalization.Away (lineGrading M) (chartVar M j)))
```
COMPOSE: `sectionInto p.1 (U j) hpre ≫ (Proj.basicOpenIsoSpec (lineGrading M)
(chartVar M j) f_deg zero_lt_one).hom` — where `basicOpenIsoSpec` :
`(basicOpen 𝒜 f).toScheme ≅ Spec (.of (Away 𝒜 f))` (Basic.lean:161;
`.hom : U.toScheme ⟶ Spec(Away)`).

THE FACTORIZATION: `chartLeg ... ≫ Proj.awayι (lineGrading M) (chartVar M j)
f_deg zero_lt_one = p.1` — because `awayι := (basicOpenIsoSpec).inv ≫ U.ι`
(Basic.lean:186, `basicOpenIsoSpec_inv_ι` :190 = rfl) so
`.hom ≫ awayι = .hom ≫ .inv ≫ U.ι = 𝟙 ≫ U.ι` (Iso.hom_inv_id + assoc),
then §1's receipt. CAREFUL: the world-vs-Proj carrier `(finiteLineWorld M).X`
vs `Proj (lineGrading M)` — the green defeq `finiteLineWorld_hWX`
(GSTFiniteLineOverBase.lean:339-340: `(finiteLineWorld M).X ≡ finiteLineScheme M`
and the scheme IS `Proj (lineGrading M)` — check the exact defeq form the
green PointsGate module uses; it states the cover lemmas at `finiteLineScheme
M = Proj ...` directly).

### §3 THE READING + THE CHART-POINT MEMBERSHIP

```
noncomputable def chartReading (M) [NeZero M] (j) (p) (hpre) :
    HomogeneousLocalization.Away (lineGrading M) (chartVar M j) →+* ℂ :=
  (Spec.homEquiv (R := CommRingCat.of (HomogeneousLocalization.Away
    (lineGrading M) (chartVar M j))) (S := CommRingCat.of ℂ)
    (chartLeg M j p hpre)).hom
```
(Binder orientation VERBATIM from the green home
GSTFinitePointAnalytification.lean:211-214 `sectionRingHom`.)

THE ℂ-LINEARITY (the chartPointSpace membership):
```
theorem chartReading_mem (M) (j) (p) (hpre) :
    ∀ c : ℂ, chartReading M j p hpre (chartRingHom M j c) = c
```
Proof: the chartPointHomOf_section calc (GSTFiniteLineAnalytification.
lean:283-317) RUN IN REVERSE. Steps: (a) the factorization p = ψ ≫ awayι;
(b) `chart_awayι_comp' M j` (GREEN, GSTFiniteLineSmoothness.lean:377):
`awayι ≫ finiteLineStructureMap = Spec.map (ofHom (chartRingHom M j))`;
(c) the section property `p.2 : p.1 ≫ structureMap = 𝟙` — wait CAREFUL:
p.2 is about `(finiteLineWorld M).structureMap`; the world's structure map
on X — the defeq to `finiteLineStructureMap M` — the green home's
chartPointHomOf_section uses `finiteLineStructureMap` directly at the
scheme level; mirror it; (d) associativity regroup; (e) the contravariant
Spec.map_comp fusion; (f) `Spec.preimage`-level ring ext (the
`section_h_algebraMap` pattern, GSTFinitePointAnalytification.lean:225-240:
`Spec.preimage_map`, `Spec.preimage_comp`, `Spec.preimage_id` — ALL GREEN
corpus-consumed); the conclusion is the ring-level identity
`chartRingHom ≫ h = RingHom.id ℂ` — the `chartPointSpace_comp` form
(GSTFiniteLineAnalytification.lean:250-256) hence the chartPointSpace
membership (chartPointSpace M j := {h // ∀ c, h (chartRingHom c) = c},
:def :215).

THE COORDINATE: `c := chartReading ... (chartRatio M j)` and then
`chartPointSpace_eval` (GREEN :376-392) gives the reading's full identity:
`chartReading ... = chartEvalRingHom M j (chartReading ... (chartRatio M j))`.

### §4 THE VALUE COMPUTATION (the none-case; THE transport)

```
theorem chartReading_ratio_eq_zero_of_mem (M) [NeZero M] (i : Fin M)
    (p : ComplexPoint (finiteLineWorld M)) (x : complexBase)
    (hmem : chartVar M (MvPolynomial.X (lineLeftChart M i)) ∈
      (finiteLineComplexPointImage M p x).asHomogeneousIdeal.toIdeal)
    (hpre : ...) :
    chartReading M (lineRightChart M i) p hpre (chartRatio M (lineRightChart M i)) = 0
```
THE ROUTE (verified at the pin):
1. `h := chartReading M (lineRightChart M i) p hpre`; `ψ := chartLeg ...`;
2. `q₀ := ψ.base x` — the image point of the chart leg (a point of
   `Spec(.of (Away ...))` = a prime ideal of the Away ring);
3. **the kernel receipt**: `q₀.asIdeal = Ideal.comap h (⊥)` — the image
   point of `Spec.map (g)` at the unique base point is `comap g (the
   unique prime of ℂ)`: the unique prime of ℂ is ⊥ (`(0 : Ideal ℂ)` — the
   field receipt: `eq_bot_of_isField`/`isField_iff`... find the green form
   — search the corpus for `Ideal.eq_bot` usages on fields). The base-apply
   of Spec.map: search the pin for the receipt (`Spec.map_base`?? hmm — if
   absent, derive: the counit `Spec.map_preimage` (green) + `Spec.preimage`
   def — the base behavior of Spec.map is definitional:
   `Spec.map g`'s base = `PrimeSpectrum.comap g` by `rfl`-class defeq —
   VERIFY by reading the pin's ProjectiveSpectrum files where `Spec.map`'s
   base is used; the pin's `toSpecZero`/`awayMap` lemmas (Basic.lean:69+:
   `SpecMap_awayMap_awayι`) manipulate exactly these — find the base-apply
   receipt name there);
4. **the point-level factorization chain**: `p.base x = (ψ ≫ awayι).base x =
   awayι.base (ψ.base x)` (the composite base receipt — `Scheme.Hom.comp_base`
   or the congr_arg pattern of morphismRestrict_base_coe) — so the image
   point `finiteLineComplexPointImage M p x` (defeq `p.1 x`) equals
   `awayι.base q₀`;
5. **the transport**: `awayι.base q₀`'s homogeneous ideal's membership of
   `chartVar M (X_{2i})` ↔ `mk(the chartRatio NumDenSameDeg) ∈ q₀.asIdeal` —
   THE PIN RECEIPT: `mk_mem_toSpec_base_apply` (Scheme.lean:691-698):
   `HomogeneousLocalization.mk z ∈ ((toSpec 𝒜 f).base x).asIdeal ↔
   z.num.1 ∈ x.1.asHomogeneousIdeal` — the chart point of `x` = `toSpec.base`;
   FOR awayι's base: `awayι = .inv ≹ U.ι` and `.inv = (asIso basicOpenToSpec).inv`
   whose base is the INVERSE function of `basicOpenToSpec.base` — hmm —
   the cleanest: relate `awayι.base q₀` to the pin's `fromSpec` (Scheme.lean
   :483-:553: `fromSpec (f_deg) (hm)` builds the Proj-point from the
   Spec-point `q` via `carrier.asHomogeneousIdeal`; the roundtrips
   `fromSpec_toSpec`/`toSpec_fromSpec` :492/:505, `toSpec_injective` :512,
   `toSpec_bijective` :523; `projIsoSpecTopComponent` :579) — the carrier
   membership receipts: `mem_carrier_iff_of_mem` (:299: for homogeneous a of
   degree n: `a ∈ carrier f_deg q ↔ mk⟨m*n, ⟨a^m, _⟩, ⟨f^n, _⟩, _⟩ ∈ q.asIdeal`)
   and `num_mem_carrier_iff` (:325). FOR OUR CASE: `f = X_{2i+1}` (degree
   m = 1), `a = chartVar M (X_{2i})` (degree n = 1): the carrier-membership
   iff becomes `chartVar(X_{2i}) ∈ (awayι.base q₀).asHomogeneousIdeal.toIdeal ↔
   mk⟨1, ⟨chartVar(X_{2i})^1, _⟩, ⟨chartVar(X_{2i+1})^1, _⟩, _⟩ ∈ q₀.asIdeal`
   — and the RHS element IS `chartRatio M (lineRightChart M i)` (the mk's
   num = the partner var `X_{2i}`, den = `X_{2i+1}` — the chartRatio def
   GSTFiniteLineAnalytification: the mk form proven in
   `chartRetracts_chartRatio`'s first rewrite: `chartRatio M j =
   HomogeneousLocalization.Away.mk (lineGrading M) (lineCoverHomogeneousOneQ
   M j) 1 (lineQuotientMap M (MvPolynomial.X (linePartner M j)))
   (linePartner_mem_smul_one M j)` — the partner of `2i+1` IS `2i` ✓
   (verify `linePartner` in GSTFiniteLineRing: the partner of the odd is
   the even of the same block);
6. `q₀.asIdeal = ker h` (from step 3) ⇒ the RHS iff `chartRatio ∈ ker h`
   ⇒ `h chartRatio = 0` (Ideal.mem_ker_iff). ∎

THE OTHER DIRECTION (the forward map's branch-decision on the constructed
point):
```
theorem chartPoint_right_zero_mem (M) [NeZero M] (i : Fin M) :
    chartVar M (MvPolynomial.X (lineLeftChart M i)) ∈
      (finiteLineComplexPointImage M (chartPoint M (lineRightChart M i) 0) x).asHomogeneousIdeal.toIdeal
```
Route: the same transport with `q₀ := ker (chartEvalRingHom M
(lineRightChart M i) 0)` — hmm — the chartPointHomOf = Spec.map(ofHom eval)
≫ awayι — its image point = awayι.base(comap eval ⊥) = awayι.base(ker eval)
— then the carrier iff: `chartVar(X_{2i}) ∈ ... ↔ chartRatio_right ∈ ker
(chartEvalRingHom ... 0)` — and `chartEvalRingHom_chartRatio` (GREEN :229)
reads the ratio as the coordinate 0 ⇒ IN the kernel ⇒ membership ✓.

### Static battery for FILE 1: zero sorry; brackets; receipts `#check` +
`#print axioms` for every theorem; every external name's home in a comment.

## FILE 2 — GSTFiniteLinePointsGateDischarge.lean (the assembly)

Imports FILE 1 + GSTFiniteLineUnconditionalSource (for the final
discharge) + mirror its opens.

### §1 THE FORWARD MAP

```
noncomputable def finiteLinePointsGateForward (M) [NeZero M] :
    ComplexPoint (finiteLineWorld M) → (Sigma (fun _ : Fin M => Option ℂ))
```
Design: `p ↦ ⟨finiteLineComplexPointLineIndex M p, the option⟩` where the
option: by cases on whether the image point avoids the LEFT chart variable
(`lineLeftChart M i`, i := the line index):
- avoids (the cover at the left var — from `finiteLineComplexPoint_cover`
  :218-226 + `finiteLineComplexPoint_on_line`/`avoids_chartPair` :368/:428
  — the green case-split machinery): output `some (chartReading M
  (lineLeftChart M i) p hpre (chartRatio M (lineLeftChart M i)))` — the
  reading through the LEFT chart;
- else (the right var avoided): output `none`.
The hpre for the chart leg: `complexBase_preimage_eq_top_of_mem` fed by the
basicOpen membership (`basicOpen_of_avoids`-pattern — the PointsGate module
has it private :228; either re-derive (2 lines) or state the cover
membership via `finiteLineComplexPoint_cover_basicOpen` :240 GREEN).

### §2 THE INVERSE LAWS

LAW 1 (surjectivity — the constructive half): `∀ z, ∃ p, forward p = z`
— for `(i, some c)`: `p := chartPoint M (lineLeftChart M i) c`:
- the line index of p = i (the image point's line — the green on-line
  machinery; the point chartPoint(left,c) has image in the left chart's
  basicOpen ⇒ its line index is i via `finiteLineComplexPoint_on_line_iff`
  :416 + the unique-line law);
- the reading of p = `chartEvalRingHom (left) c` with value c at the ratio
  ⇒ forward = (i, some c). THE KEY LEMMA (state + prove in FILE 2):
  for `p := chartPointHomOf M j h`-built points, `chartLeg M j p hpre =
  Spec.map (CommRingCat.ofHom h.val)` — via MONO-CANCELLATION: both
  compose with `awayι` to `p` (chartPointHomOf is green =
  `Spec.map (ofHom h.val) ≫ awayι`; chartLeg's factorization §2 of FILE 1
  is `chartLeg ≫ awayι = p.1`) ⇒ equal by `cancel_mono awayι` (the opens-ι
  mono pattern — Restrict.lean's own idiom; awayι is an open immersion
  (instance at Basic.lean:194) ⇒ mono — find the `IsOpenImmersion` mono
  instance/lemma name: the pin's `cancel_mono U.ι` usages mean the
  instance-path exists; if the instance is not found, use
  `Scheme.Opens.ι`'s mono with awayι's def-unfold = `.inv ≫ U.ι` hmm —
  `.inv` is iso ⇒ mono and `U.ι` mono ⇒ comp mono ⇒ cancel via
  `cancel_mono` with the comp-form). Then `chartReading = h.val` by
  `Spec.preimage_map`/homEquiv (the unit — GREEN satellites).
  With `h := chartPointSpaceEval M j c` (val = chartEvalRingHom j c):
  the reading's ratio-value = `chartEvalRingHom_chartRatio` (GREEN :229) = c.
For `(i, none)`: `p := chartPoint M (lineRightChart M i) 0`:
- the branch-decision lands in none (FILE 1 §4's other-direction receipt);
- forward = (i, none) via the line index (on-line machinery).

LAW 2 (injectivity): `forward p = forward p' → p = p'` — hmm — OR
structure as `Equiv.ofBijective` (surjective + injective). INJECTIVITY
route: `p = coordPoint (forward p) = p'` (LAW 3) applied twice — if LAW 3
is proven, injectivity is immediate. PROVE LAW 3 (the left-inverse):
`coordPoint (finiteLinePointsGateForward p) = p`:
- the some-case: p's branch = some; `coordPoint (i, some c) = chartPoint
  (left, c)`; the equality `p = chartPoint (left, c)`: SUBTYPE.ext — both
  sections' underlying morphisms equal: `p.1 = chartPointHomOf ... ≫ ...`:
  MONO-CANCELLATION on awayι: `chartLeg(left) ≫ awayι = p.1` (FILE 1 §2)
  and `chartPointHomOf(left, eval-c) = Spec.map(ofHom eval-c) ≫ awayι`;
  need `chartLeg(left) = Spec.map(ofHom eval-c)`: their readings agree
  (both = chartEvalRingHom at c: p's reading by `chartPointSpace_eval`
  (the coordinate identity — GREEN :376) at c := the forward coordinate;
  the chartPointHomOf-side by construction) ⇒ the morphisms equal by the
  AFFINE FAITHFULNESS: `Spec.map (Spec.preimage f) = f` (the counit —
  `Spec.map_preimage`, GREEN) — i.e. chartLeg = Spec.map(ofHom (preimage
  chartLeg)) = Spec.map(ofHom (reading)) = Spec.map(ofHom eval-c) ✓;
  then `p.1 = chartLeg ≫ awayι = Spec.map(...) ≫ awayι = chartPointHomOf`
  ✓ (all green-form).
- the none-case: same shape at the right chart with the reading = eval
  at 0 (FILE 1 §4's value computation) ⇒ p.1 = chartPointHomOf(right,
  eval-0) = (chartPoint (right, 0)).1 = (coordPoint (i, none)).1 ✓.

### §3 THE GATE + THE DISCHARGE

```
noncomputable def finiteLinePointsGate (M) [NeZero M] : FiniteLinePointsGate M
```
= `Equiv.ofBijective (finiteLinePointsGateForward M) ⟨coordPoint-surj-bij,
inj⟩` hmm — OR the explicit Equiv with toFun := forward, invFun := coordPoint,
left_inv := LAW-3, right_inv := LAW-R (forward (coordPoint z) = z — mirror
of LAW 1 at the point level: the branch-decision + the reading receipts
(the same §2-of-FILE-2 machinery)). PICK whichever you finish; the explicit
Equiv is preferred (the abbrev's `.trans` usages downstream are cleaner).

```
noncomputable def finiteLineAnalytificationUnconditional (M) [NeZero M] :
    AnalytificationData (finiteLineWorld M) :=
  finiteLineAnalytificationOfGate M (finiteLinePointsGate M)

theorem finiteLineAnalytificationUnconditional_space (M) [NeZero M] :
    (finiteLineAnalytificationUnconditional M).space = TopCat.of (sphereUnionSpace M) :=
  finiteLineAnalytificationOfGate_space M (finiteLinePointsGate M)

theorem native_GST_single_fold_orbit_law_finiteLine_unconditional_gatefree
    (M) [NeZero M] (ω) : NativeGSTSingleFoldOrbitLaw (finiteLineWorld M)
    (finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
      (finiteLineAnalytificationUnconditional_space M) ω) :=
  native_GST_single_fold_orbit_law_finiteLine_unconditional M
    (finiteLinePointsGate M) ω   -- one substitution; defeq-show if needed
```

## THE DISEASE CATALOG (campaign law — avoid every one)

ofHom-fusion DIRECTION (check the ≫-form); subtype-motive (show-bridges/
Subtype.ext); Fin-mk-vs-OfNat (`⟨0, Nat.pos_of_neZero ‹_›⟩`); semireducible
rw-visibility (show-unfold first); stale-Decidable (`split`); universe
pinning (universe 0); rw-pattern direction (read the error's display); NO
autoImplicit (explicit binders); `lineCoverHomogeneousOneQ`-style named
membership proofs exactly as the green homes spell them.

## THE HONESTY LAW

Zero sorry/admit/native_decide/new axioms. A piece that resists is NOT
stated — it is documented in the module's ledger for the next wave. The
CI lanes own the kernel verdict.

## THE REGISTRATION (the commander's job — DO NOT do it)

lakefile `[[lean_lib]]` roots + the lane
`.github/workflows/gst-finite-line-points-gate-discharge.yml` (mirror
gst-finite-line-points-gate.yml: elan v4.33.0-rc2, Mathlib cache, the
corpus-proven `if: always()` cache-bank save step with key
`hc-lean-incremental-Linux-finite-line-points-gate-discharge-<run-id>`,
restore-keys prefix `hc-lean-incremental-Linux-finite-line-`, the sorryAx
hard-fail, artifact upload, path filter carrying the two new files + the
direct import chain).
