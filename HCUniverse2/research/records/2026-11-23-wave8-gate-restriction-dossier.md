# 2026-11-23 — WAVE 8-B: THE GATE-RESTRICTION API DOSSIER (GATE-A, second-method verification)

Agent: W8-B (Task ID 8-B), the independent API-DOSSIER agent of Wave 8 of the GST
campaign (HC-PROOF). RESEARCH ONLY — this file is the deliverable; no repo-root
`.lean` files were touched.

Method: every name below was read **verbatim** against the pinned Mathlib
reference copies at `research/pin/mathlib-51e6992/` (= Mathlib@`51e6992` =
v4.33.0-rc2) and cross-checked against the corpus's CI-green modules (trust
order: corpus-green > pin-copy > memory). `Restrict.lean` and `Restrict_full.lean`
are byte-identical (`diff -q` clean); likewise `Basic.lean` ≡
`ProjectiveSpectrum_Basic.lean` and `Scheme.lean` ≡ `ProjectiveSpectrum_Scheme.lean`
(duplicate copies of the same fetch — line numbers coincide).

**The green corpus baseline used for cross-checks** (lane → run/SHA, from the
records):
* `GSTFiniteLineAnalytification` — GREEN, run 45107965587 @ 115f96f (imports, and
  therefore kernel-checks, `GSTFiniteLineOverBase` → {`GSTFiniteLineRing`,
  `GSTFiniteLineWorldCarrier`, `GSTFiniteLineClosedImmersion`,
  `GSTFiniteLineSmoothness`, `GSTProjectiveOverC`} and `GSTFiniteLineRiemann` →
  {`GSTSphereUnionComponents`} — all transitively green).
* `GSTFiniteLineClosedImmersion` — GREEN, run 44918529342 @ 1cf6ff2 (wave 66).
* `GSTFiniteLineWorldCarrier` — GREEN, run 44899187702 @ 99f6366 (wave 65.1).
* `GSTFiniteLineHonestHodgeData` — GREEN, run 45093883420 @ ff48e2f (imports
  `GSTFiniteLinePointAlgebra` → transitively green).
* `GSTFiniteLineWorldDischarge` — GREEN, run 45090036794 @ 35aa0dc.
* `GSTFinitePointAnalytification` (+ `GSTFinitePointWorldCarrier`,
  `GSTFinitePointShiftWord`, `GSTFinitePointLawLanding`) — GREEN, run 44290094898
  @ c5385a02 (wave 43, "all six modules built").
* `GSTTwelvePointAnalytification` — GREEN (twelve-point lane tier 2, "analytification
  run 15"); `GSTTwelvePointWorldCarrier` — GREEN (tier 1, "carrier run 11").
* `GSTFiniteLinePointsGate` (the W7-B cover module) — lane
  `gst-finite-line-points-gate.yml` **REGISTERED BUT NOT YET CI-CONFIRMED GREEN**
  at this dossier's write time (see RED FLAGS §R7).

---

## PART 1 — THE FULL API TABLE

### 1A. The restriction API (`research/pin/mathlib-51e6992/Restrict.lean`, root
namespace `AlgebraicGeometry`; module header imports `Mathlib.AlgebraicGeometry.Cover.Open`
+ `Mathlib.AlgebraicGeometry.Over`)

| # | Name | Pin file:line | Exact signature (verbatim from the pin) | Corpus-green home |
|---|------|-----------|------------------------------------------|--------------------|
| 1 | `Scheme.Opens.toScheme` | Restrict.lean:46 | `def toScheme {X : Scheme.{u}} (U : X.Opens) : Scheme.{u} := X.restrict U.isOpenEmbedding` (+ `@[coe]`; `instance : CoeOut X.Opens Scheme` :49) | every `∣_`/`basicOpenIsoSpec`-shaped corpus term; e.g. ClosedImmersion :211 |
| 2 | `Scheme.Opens.ι` | :52 | `def ι : ↑U ⟶ X := X.ofRestrict _` (+ `IsOpenImmersion U.ι` instance :57; `ι_apply` :55 `rfl`; `ι_appTop` :86; `opensRange_ι` :104; `ι_preimage_self` :119 simp) | Analytification :291 (`(Proj.basicOpen 𝒜 f).ι`-class); ClosedImmersion :245/:254 |
| 3 | `Scheme.Opens.ι_image_top` | :111 | `lemma ι_image_top : U.ι ''ᵁ ⊤ = U` | pin-internal only (used by `topIso`/`opensFunctor` proofs) |
| 4 | `Scheme.Opens.range_ι` | :108 | `@[simp] lemma range_ι : Set.range U.ι = U` | pin-internal (basicOpenIsoSpecAway :525, restrictRestrictComm :382) |
| 5 | `Scheme.homOfLE` | :241 | `protected noncomputable def Scheme.homOfLE (X : Scheme.{u}) {U V : X.Opens} (e : U ≤ V) : (U : Scheme.{u}) ⟶ V := IsOpenImmersion.lift V.ι U.ι (by simpa using e)` | pin-internal (Basic.lean:384/:391; corpus: none direct) |
| 6 | `Scheme.homOfLE_ι` | :245 | `@[reassoc (attr := simp)] lemma Scheme.homOfLE_ι (X) {U V} (e : U ≤ V) : X.homOfLE e ≫ V.ι = U.ι` | pin-internal (Basic.lean:453 via `fromOfGlobalSections_morphismRestrict`) |
| 7 | `morphismRestrict` | :569 | `def morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : (f ⁻¹ᵁ U).toScheme ⟶ U := (pullbackRestrictIsoRestrict f U).inv ≫ pullback.snd _ _` | **ClosedImmersion :197/:210 (5 real uses, CI-green 44918529342)**; FinitePointWorldCarrier :577; TwelvePointWorldCarrier :566 |
| 8 | notation `∣_` | :573 | `infixl:85 " ∣_ " => morphismRestrict` | same (the corpus always uses the infix) |
| 9 | `morphismRestrict_ι` | :581 | `@[reassoc (attr := simp)] theorem morphismRestrict_ι (f : X ⟶ Y) (U : Y.Opens) : f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f` | **ClosedImmersion :277 (CI-green — the restriction law, real use)** |
| 10 | `morphismRestrict_base_coe` | :643 | `@[simp] theorem morphismRestrict_base_coe (f) (U) (x) : ((f ∣_ U) x).1 = f x.1` | pin-internal (Basic.lean:470) |
| 11 | `morphismRestrict_base` | :648 | `theorem morphismRestrict_base (f) (U) : ⇑(f ∣_ U) = U.1.restrictPreimage f` | pin-internal (Basic.lean:470) |
| 12 | `morphismRestrict_appTop` | :666 | `theorem morphismRestrict_appTop (f) (U) : (f ∣_ U).appTop = f.app (U.ι ''ᵁ ⊤) ≫ X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op` | pin-internal only |
| 13 | `pullbackRestrictIsoRestrict` | :553 | `def pullbackRestrictIsoRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : pullback f U.ι ≅ f ⁻¹ᵁ U` (target via the `CoeOut`; `inv_fst` :559 simp; `hom_ι` :564 simp) | pin-internal only |
| 14 | `isPullback_morphismRestrict` | :586 | `theorem isPullback_morphismRestrict (f) (U) : IsPullback (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι f` | pin-internal (Restrict.lean:654, Morphisms_Basic) |
| 15 | `morphismRestrictOpensRange` | :702 | `def morphismRestrictOpensRange {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y) [IsOpenImmersion g] : Arrow.mk (f ∣_ g.opensRange) ≅ Arrow.mk (pullback.snd f g)` | pin-internal (Morphisms_Basic.lean:459) |
| 16 | `Scheme.isoOfEq` | :455 | `noncomputable def Scheme.isoOfEq (X : Scheme.{u}) {U V : X.Opens} (e : U = V) : (U : Scheme.{u}) ≅ V` (+ `hom_ι` :460, `inv_ι` :465, `hom = X.homOfLE e.le := rfl` :469, `inv = X.homOfLE e.ge := rfl` :473, `isoOfEq_rfl` :476) | **FinitePointWorldCarrier :610/:614 (green)**; TwelvePointWorldCarrier :540/:544 |
| 17 | `Scheme.Hom.isoImage` (dot: `U.ι.isoImage V`) | :388 | `noncomputable def Scheme.Hom.isoImage {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Opens) : U.toScheme ≅ f ''ᵁ U` (+`hom_ι` :394, `inv_ι` :400, `hom_homOfLE` :406, `inv_homOfLE` :412, `Scheme.Opens.isoImage_ι_inv_ι` :418) | pin-internal (Restrict.lean:594/:604 `V.ι.isoImage _`) |
| 18 | `IsOpenImmersion.isoOfRangeEq` | **NOT IN PIN** (lives in unpinned `Mathlib/AlgebraicGeometry/Morphisms/OpenImmersion.lean`) | used ~25× in the pin with satellites `isoOfRangeEq_hom_fac` / `isoOfRangeEq_inv_fac` (Restrict.lean:397/:403/:462/:467/:493/:498; Basic.lean:269/:476; Functor.lean via `pullbackAwayιIso_hom_awayι` :269). Signature (from the usage shapes, corpus-unverified): `noncomputable def IsOpenImmersion.isoOfRangeEq {X Y : Scheme} (f g : X ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g] (h : Set.range ⇑f = Set.range ⇑g) : X ≅ Y` | **none** — see RED FLAG R1 |
| 19 | `Scheme.OpenCover.iSup_opensRange` | **NOT IN PIN def** — used 6× in pin `Morphisms_Basic.lean` (:132/:161/:246/:277/:568/:575) | inferred type from uses: `𝒰.iSup_opensRange : ⨆ i, (𝒰.f i).opensRange = ⊤` | **none** — RED FLAG R4 (not needed on the critical path) |
| 20 | `Scheme.topIso` (scheme-level!) | :439 | `@[simps hom] def Scheme.topIso (X : Scheme) : ↑(⊤ : X.Opens) ≅ X` — `hom := Scheme.Opens.ι _`, `inv := ⟨X.restrictTopIso.inv⟩`; `toIso_inv_ι` :446 simp (`inv ≗ ι = 𝟙 X`); `ι_toIso_inv` :450 simp (`ι ≗ inv = 𝟙 ⊤.toScheme`) | pin-internal **with the pin's own direct precedent: `Proj.toSpecZero` (Basic.lean:151-153) is built as `(Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ (basicOpen_one _)).inv ≫ basicOpenToSpec 𝒜 1 ≫ …` — the exact W8 route shape** |
| 21 | `Scheme.Opens.topIso` (sections-level! NAME COLLISION with #20) | :146 | `@[simps!] def topIso : Γ(U, ⊤) ≅ Γ(X, U) := X.presheaf.mapIso (eqToIso U.ι_image_top.symm).op` | pin-internal (Basic.lean:146 `topIso.inv`; Restrict.lean:827 `resLE_app_top`) — see RED FLAG R5 |
| 22 | `Scheme.Hom.resLE` | :775 | `def Scheme.Hom.resLE (f : Hom X Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) : V.toScheme ⟶ U.toScheme := X.homOfLE e ≫ f ∣_ U` (+ `resLE_eq_morphismRestrict` :780; **`resLE_comp_ι` :789** `@[reassoc (attr := simp)] : f.resLE U V e ≫ U.ι = V.ι ≫ f`) | pin-internal (Basic.lean:372/:386/:391 — `toBasicOpenOfGlobalSections` is built on `X.toSpecΓ ∣_ _`; corpus: no direct use) |
| 23 | `IsIso (f ∣_ U)` instance | :639 | `instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (U : Y.Opens) : IsIso (f ∣_ U)` | **FinitePointWorldCarrier :628-637 (green, with the `delta AlgebraicGeometry.morphismRestrict; infer_instance` seam-trick receipt)** |
| 24 | `Scheme.Opens.isoOfLE` | :501 | `noncomputable def Scheme.Opens.isoOfLE {X : Scheme.{u}} {U V : X.Opens} (hUV : U ≤ V) : (V.ι ⁻¹ᵁ U).toScheme ≅ U` (+`hom_ι` :509, `inv_ι` :514) | pin-internal |
| 25 | `Scheme.Hom.preimageIso` | :483 | `noncomputable def Scheme.Hom.preimageIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso (C := Scheme) f] (U : Y.Opens) : (f ⁻¹ᵁ U).toScheme ≅ U` | pin-internal |
| 26 | `Scheme.Hom.isoOpensRange` | :423 | `def Scheme.Hom.isoOpensRange {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] : X ≅ f.opensRange` | pin-internal |

### 1B. The one-point-source receipts (target 2)

| Name | Where | Exact fact | Green home |
|------|------|-----------|------------|
| `Subsingleton ↥(Spec (CommRingCat.of ℂ))` | GSTFinitePointShiftWord.lean:511-513 | `instance pointPairGeometry_carrier_subsingleton (r c : Fin N) : Subsingleton ↥(pointPairGeometry N r c).carrier := inferInstanceAs (Subsingleton ↥(Spec (CommRingCat.of ℂ)))` — the instance chain RESOLVES at `import Mathlib` | **GSTFinitePointShiftWord (finite-point lane, wave-43 green)** |
| `∀ x y : PrimeSpectrum ℂ, x = y` | GSTFinitePointShiftWord.lean:95-96 | `have hdfl : ∀ x y : PrimeSpectrum ℂ, x = y := fun _ _ => Subsingleton.elim _ _` | same (green, inside `comap_evalRingHom_default`) |
| `default : Spec (CommRingCat.of ℂ)` as a term | GSTFinitePointShiftWord.lean:507-509 | `Inhabited ↥(pointPairGeometry N r c).carrier := ⟨(default : Spec (CommRingCat.of ℂ))⟩` | same |
| `Unique (Spec (X.residueField x))` | pin ResidueField.lean:51 | `instance (x : X) : Unique (Spec (X.residueField x)) := inferInstanceAs (Unique (Spec <| .of _))` — the instance-path evidence for `Unique (Spec (of K))` off a `Field K` | pin (the residue-field file's own instance) |
| **the dual-instance-path hazard** | GSTFinitePointShiftWord.lean:80-96 (AUDIT-1) | "the two `default`s ride different `Unique (PrimeSpectrum ℂ)` instance paths (the scheme-level instance of AlgebraicGeometry/Scheme.lean:627 resolves through `Field ℂ`, the `sigmaUnique` binder through the artinian-krull-dim-zero-local chain) — so the equation is closed by `Subsingleton.elim` … never by a bare `rfl`" + the WAVE-32 term-mode law | same — see RED FLAG R6 |

**There is NO named `complexBase`-subsingleton lemma anywhere in the corpus or
the pin** (repo-wide grep). W8-A must author it in-module, exactly the ShiftWord
pattern: `have : ∀ x y : complexBase, x = y := fun _ _ => Subsingleton.elim _ _`
(riding the resolvable `Subsingleton ↥(Spec (CommRingCat.of ℂ))` instance), or
`Subsingleton ↥complexBase := inferInstanceAs …` — never a bare-`rfl` default
equation.

### 1C. The preimage machinery (target 3)

| Name | Where | Exact fact | Green home |
|------|------|-----------|------------|
| `f ⁻¹ᵁ U` notation | unpinned (`Mathlib/AlgebraicGeometry/Scheme.lean`, via `TopologicalSpace.Opens.map f.base`) | pervasive in the pin; **one real corpus-green use: GSTFiniteLineClosedImmersion.lean:271** (`(Proj.map … ⁻¹ᵁ (Proj.basicOpen …))` inside the `morphismRestrict_ι` application) | ClosedImmersion (green) |
| `TopologicalSpace.Opens.map_coe` | unpinned; pin usages Basic.lean:307/:465/:477, Morphisms_Basic.lean:186 | `(f ⁻¹ᵁ U)`'s carrier = `f.base ⁻¹' ↑U` — the membership-level unfolding | pin-verified-by-usage |
| **NO `x ∈ f ⁻¹ᵁ U ↔ f.base x ∈ U` lemma exists** | pin's own TODO, Basic.lean:464 | "TODO : mem version of `TopologicalSpace.Opens.map_coe`" — the mandatory three-step dance: `rw [← SetLike.mem_coe]` → `simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage]` | pin's own pattern (Basic.lean:464-477) |
| `Scheme.Hom.comp_preimage` | pin usages Restrict.lean:818 | `(f ≫ g) ⁻¹ᵁ U = f ⁻¹ᵁ (g ⁻¹ᵁ U)`-class | pin-verified-by-usage |
| `Scheme.Hom.preimage_mono` | Restrict.lean:630 | preimage preserves `≤` | pin-verified-by-usage |
| `Proj.mem_basicOpen` | **Basic.lean:58** (CONFIRMED at the exact line the wave cited) | `@[simp] theorem mem_basicOpen (x : Proj 𝒜) : x ∈ basicOpen 𝒜 f ↔ f ∉ x.asHomogeneousIdeal := Iff.rfl` | **PointsGate :233 (first corpus consumption, lane unconfirmed); pin-internal :464-485** |
| `Scheme.evaluation_ne_zero_iff_mem_basicOpen` | pin ResidueField.lean:111 | `X.evaluation U x hx f ≠ 0 ↔ x ∈ X.basicOpen f` (the scheme-level basicOpen membership receipt; also `evaluation_eq_zero_iff_notMem_basicOpen` :107 simp) | pin |
| preimage-open equality precedents | Basic.lean:301-315 (`awayι_preimage_basicOpen`, via `ext1` + Set/range reasoning) and Basic.lean:459-493 (`fromOfGlobalSections_preimage_basicOpen`, via `le_antisymm` + the point-membership dance) | the pin's own two shapes for exactly the `(f ⁻¹ᵁ basicOpen = …)` goal class | pin |

### 1D. The chart isos (target 4) — pin `Basic.lean` (= `ProjectiveSpectrum_Basic.lean`), namespace `AlgebraicGeometry.Proj`

Variables in force: `{σ : Type*} {A : Type u} [CommRing A] [SetLike σ A]
[AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]`, `variable (f g : A)` (:51),
and for the iso block `variable {m} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)` (:155).

| Name | Line | Exact signature | Green home |
|------|------|-----------------|-------------|
| `Proj.basicOpen` | :54 | `def basicOpen : (Proj 𝒜).Opens := ProjectiveSpectrum.basicOpen 𝒜 f` | PointsGate :231; ClosedImmersion :198 (green) |
| `Proj.mem_basicOpen` | :58 | as above (1C) | PointsGate (unconfirmed lane) |
| `basicOpen_one` / `basicOpen_mul` / `basicOpen_mono` | :62 / :69 / :72 | `basicOpen 𝒜 1 = ⊤`; `basicOpen 𝒜 (f*g) = basicOpen 𝒜 f ⊓ basicOpen 𝒜 g`; `f ∣ g → basicOpen 𝒜 g ≤ basicOpen 𝒜 f` | pin-internal |
| `iSup_basicOpen_eq_top'` | :97 | `(hf : Algebra.adjoin (𝒜 0) (Set.range f) = ⊤) → ⨆ i, basicOpen 𝒜 (f i) = ⊤` | **FinitePointWorldCarrier :651 (green, `Proj.iSup_basicOpen_eq_top' grading …`)**; ClosedImmersion §4 (green) |
| `Proj.basicOpenIsoSpec` | :161 | `@[simps! -isSimp hom] noncomputable def basicOpenIsoSpec : (basicOpen 𝒜 f).toScheme ≅ Spec (.of \| Away 𝒜 f)` — full arg spine `(𝒜) (f) {m} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)`; generates `basicOpenIsoSpec_hom`; `basicOpenIsoSpec_inv_ι` :190 is `rfl` | **ClosedImmersion :212/:218/:241/:249/:255/:262/:268/:274/:283/:289/:303/:306 — TWELVE real uses, CI-green 44918529342** |
| `Proj.basicOpenIsoAway` | :176 | `@[simps! -isSimp hom] noncomputable def basicOpenIsoAway : CommRingCat.of (Away 𝒜 f) ≅ Γ(Proj 𝒜, basicOpen 𝒜 f)` (same `f_deg hm` include) | pin-internal (Basic.lean:177-182) |
| `Proj.awayι` | :186 | `noncomputable def awayι : Spec (.of \| Away 𝒜 f) ⟶ Proj 𝒜 := (basicOpenIsoSpec 𝒜 f f_deg hm).inv ≫ (Proj.basicOpen 𝒜 f).ι` — arg spine `(𝒜) (f) {m} (f_deg) (hm)` | **Analytification :270/:287/:298/:302/:306 (green 45107965587); OverBase :176/:178/:183…(transitively green); pin Basic.lean:187** |
| `IsOpenImmersion (Proj.awayι …)` instance | :193 | `instance : IsOpenImmersion (Proj.awayι 𝒜 f f_deg hm) := IsOpenImmersion.comp _ _` | Analytification :271-class uses |
| `opensRange_awayι` | :196 | `(Proj.awayι 𝒜 f f_deg hm).opensRange = Proj.basicOpen 𝒜 f` | pin-internal (:202/:262/:311/:331) |
| `isAffineOpen_basicOpen` | :201 | `IsAffineOpen (basicOpen 𝒜 f)` (include `f_deg hm`) | pin-internal |
| `awayι_toSpecZero` | :206 | `@[reassoc] awayι 𝒜 f f_deg hm ≫ toSpecZero 𝒜 = Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _))` | **OverBase :201/:223 (transitively green); Smoothness :388 (the `chart_awayι_comp'` engine)** |
| `basicOpenIsoSpecAway` | **Restrict.lean:520** (NOT Basic.lean!) | `def basicOpenIsoSpecAway {R : CommRingCat.{u}} (f : R) : Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f) ≅ Spec (.of \| Localization.Away f)` — **this is the AFFINE (Spec/localization) chart iso, `PrimeSpectrum.basicOpen` + `Localization.Away f`, NOT the graded `Away`**; satellites `basicOpenIsoSpecAway_hom_SpecMap` :529, `basicOpenIsoSpecAway_inv_homOfLE` :536 | pin-internal (Basic.lean:373/:396 — `toBasicOpenOfGlobalSections`); corpus: comments only (FinitePointWorldCarrier :599, TwelvePointWorldCarrier :529) |
| `Proj.awayι_comp_map` | pin **Functor.lean:192** | `@[reassoc] theorem awayι_comp_map {i : ℕ} (hi : 0 < i) (s : A) (hs : s ∈ 𝒜 i) : awayι ℬ (f s) (f.2 hs) hi ≫ map f hf = Spec.map (CommRingCat.ofHom (Away.map f s)) ≫ awayι 𝒜 s hs hi` | **OverBase :192 (green); ClosedImmersion :223 (green)** |
| `Proj.mapAffineOpenCover` | Functor.lean:203 | `@[simps! I₀ f] noncomputable def mapAffineOpenCover : (Proj ℬ).AffineOpenCover` | **OverBase :171/:175 (green — the `openCover.hom_ext` + `openCover_f` consumption)** |
| `Proj.affineOpenCover` | Basic.lean:336 | `@[simps! f] noncomputable def affineOpenCover : (Proj 𝒜).AffineOpenCover` | pin-internal (Functor.lean:218) |
| `awayι_preimage_basicOpen` | Basic.lean:301 | `awayι 𝒜 f f_deg hm ⁻¹ᵁ basicOpen 𝒜 g = PrimeSpectrum.basicOpen (Away.isLocalizationElem f_deg g_deg)` | pin-internal |
| `SpecMap_awayMap_awayι` | Basic.lean:248 | the away-neighbor square (`Spec.map (awayMap …) ≫ awayι f = awayι (f*g)`) | pin-internal (the two-chart-consistency candidate engine) |
| `awayι_toSpecZero`-driven chart square (corpus) | **GSTFiniteLineSmoothness.lean:377** | `theorem chart_awayι_comp' (M : ℕ) [NeZero M] (j : Fin (2 * M)) : Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j)) (lineCoverHomogeneousOneQ M j) zero_lt_one ≫ finiteLineStructureMap M = Spec.map (CommRingCat.ofHom ((fromZeroRingHom …).comp (algebraMap ℂ (lineGrading M 0))))` | **Analytification :291 (green consumption); Smoothness (transitively green)** |

### 1E. The ring-reading route (target 5)

| Name | Where | Exact fact | Green home |
|------|------|-----------|------------|
| `Scheme.Hom.appTop` | unpinned (`Mathlib/AlgebraicGeometry/Scheme.lean`); pin-internal 20+ uses | **direction (derived from pin Basic.lean:144-147 + ClosedImmersion.lean:336): for `f : X ⟶ Y`, `f.appTop : Γ(Y, ⊤) ⟶ Γ(X, ⊤)` — CONTRAVARIANT (target sections → source sections); `.app V : Γ(Y, V) ⟶ Γ(X, f ⁻¹ᵁ V)`** | **ZERO corpus uses (repo-wide grep) — RED FLAG R3** |
| `Scheme.ΓSpecIso R` | unpinned (`Mathlib/AlgebraicGeometry/AffineScheme.lean`); pin uses Basic.lean:145, ClosedImmersion.lean:336/:340, ResidueField.lean:310 | `Scheme.ΓSpecIso R : Γ(Spec R, ⊤) ≅ R` (`.hom : Γ(Spec R,⊤) ⟶ R` per Basic.lean:145's composite; `.inv ≫ f.appTop` at ClosedImmersion.lean:336 with `f : X ⟶ Spec R`; accessor `.commRingCatIsoToRingEquiv` :340) | pin-verified-by-usage; corpus: none direct |
| **`Spec.homEquiv`** (THE corpus route) | unpinned (`Mathlib/AlgebraicGeometry/Spec.lean`); not in pin | green-verified binder orientation (from GSTFinitePointAnalytification.lean:213-214 verbatim): `(Spec.homEquiv (R := CommRingCat.of A) (S := CommRingCat.of ℂ) f.1).hom : A →+* ℂ` for `f.1 : Spec ℂ ⟶ Spec A` (i.e. `Spec S ⟶ Spec R`), the result a CommRingCat hom whose `.hom` is the RingHom | **GSTFinitePointAnalytification :211-214 (green 44290094898); GSTTwelvePointAnalytification :169-172 (green)** |
| **`Spec.preimage`** | same | `(Spec.preimage (R := CommRingCat.of A) (S := CommRingCat.of ℂ) f.1 : A ⟶ ℂ)` — the ring-hom reading of a Spec-morphism; satellites (all corpus-green): `Spec.preimage_comp` (:241 — contravariant), `Spec.preimage_map` (:238), `Spec.preimage_id` (:243), `Spec.map_preimage` (:436, `.symm` gives `f = Spec.map (preimage f)`) | same two green homes |
| `ΓSpec.locallyRingedSpaceAdjunction.homEquiv` | pin ProjectiveSpectrum_Scheme.lean:658, Basic.lean:165 | the heavyweight adjunction route | pin-internal; **not recommended** (corpus-unconsumed) |
| `Scheme.toSpecΓ` / `Scheme.isoSpec` / `IsAffine.affine` | unpinned; pin uses ClosedImmersion.lean:256/:337/:344, Basic.lean:372/:518 | `X.toSpecΓ : X ⟶ Spec (Γ(X, ⊤))`; `Scheme.isoSpec` the affine iso; `IsAffine.affine : IsIso X.toSpecΓ` (AffineScheme.lean:59) | **FinitePointWorldCarrier :624-627 (green — `@IsAffine.affine (finitePointScheme N) haff`)** |

### 1F. The section-equality ext (target 6)

| Name | Where | Exact fact | Green home |
|------|------|-----------|------------|
| `Scheme.OpenCover.hom_ext` | unpinned (`Mathlib/AlgebraicGeometry/Cover.lean`); NOT a def in the pin | call shape (two-method verified): `𝒰.hom_ext _ _ fun i ↦ ?_` closes `f = g` (two `X ⟶ Z`) from `∀ i : 𝒰.I₀, 𝒰.f i ≫ f = 𝒰.f i ≫ g` (PREcomposition) | **pin Functor.lean:211/:218 (`(mapAffineOpenCover _ _).openCover.hom_ext _ _ fun s ↦ ?_`), Basic.lean:519 (`(openCoverOfMapIrrelevantEqTop …).hom_ext _ _ fun x ↦ ?_`); corpus-green OverBase :171 — THE green usage the wave asked about** |
| `Scheme.AffineOpenCover.openCover` (+`openCover_f` simp) | unpinned; pin Functor.lean:212 | the coercion `X.AffineOpenCover → X.OpenCover` with the `f`-field simp lemma | pin + OverBase :171-176 (green) |
| `Scheme.hom_ext` (a bare global ext) | **DOES NOT EXIST at the pin** (grep: no def) | — the ext MUST go through a cover: `(𝒰 : X.AffineOpenCover).openCover.hom_ext` or an explicitly-built `X.OpenCover` (e.g. `Scheme.openCoverOfIsOpenCover`, Restrict.lean:182, pin-internal) | — |
| `CommRingCat.hom_ext` | unpinned; corpus everywhere | ring-hom equality ext | **Analytification :295 (green); FinitePointAnalytification :153/:432; TwelvePointAnalytification :113/:384** |
| `DFunLike.ext` / `RingHom.ext` | unpinned | the one-level function ext (the AUDIT-8 lesson: pin the ext to `DFunLike.ext`, not the Pi-ext registry) | FinitePointAnalytification :367 (green) |

### 1G. The constructive half (target 7) — `GSTFiniteLineAnalytification.lean` §3-§4 (:150-392), verbatim signatures

```
chartMap_C (M) [NeZero M] (j : Fin (2*M)) (c : ℂ) :
    chartMap M j (MvPolynomial.C c) = chartRingHom M j c                       -- :156
chartMap_X0 (M) [NeZero M] (j : Fin (2*M)) :
    chartMap M j (MvPolynomial.X (0 : Fin 1)) = chartRatio M j                  -- :165
chartRetracts_chartRatio (M) [NeZero M] (j) :
    chartRetracts M j (chartRatio M j) = MvPolynomial.X (0 : Fin 1)             -- :174
polyEval_ext (f g : MvPolynomial (Fin 1) ℂ →+* ℂ)
    (hC : ∀ a, f (MvPolynomial.C a) = g (MvPolynomial.C a))
    (hX : f (MvPolynomial.X 0) = g (MvPolynomial.X 0)) : f = g                  -- :188
noncomputable def chartEvalRingHom (M) [NeZero M] (j) (c : ℂ) :
    HomogeneousLocalization.Away (lineGrading M) (lineQuotientMap M (MvPolynomial.X j)) →+* ℂ
      := (MvPolynomial.eval (fun _ : Fin 1 => c)).comp (chartRetracts M j)     -- :201
chartEval_chartRingHom (M) (j) (c c' : ℂ) :
    chartEvalRingHom M j c (chartRingHom M j c') = c'                          -- :212
chartEvalRingHom_chartRatio (M) (j) (c : ℂ) :
    chartEvalRingHom M j c (chartRatio M j) = c                                 -- :224
def chartPointSpace (M) [NeZero M] (j : Fin (2*M)) : Type :=
    { h : HomogeneousLocalization.Away (lineGrading M) (lineQuotientMap M (MvPolynomial.X j)) →+* ℂ //
        ∀ c : ℂ, h (chartRingHom M j c) = c }                                   -- :235
noncomputable def chartPointSpaceEval (M) (j) (c : ℂ) : chartPointSpace M j     -- :242
chartPointSpace_comp (M) (j) (h : chartPointSpace M j) :
    RingHom.comp h.val (chartRingHom M j) = RingHom.id ℂ                        -- :250
def lineLeftChart (M) [NeZero M] (i : Fin M) : Fin (2*M) := ⟨2*i.val, …⟩        -- :257
def lineRightChart (M) [NeZero M] (i : Fin M) : Fin (2*M) := ⟨2*i.val+1, …⟩     -- :261
noncomputable def chartPointHomOf (M) [NeZero M] (j) (h : chartPointSpace M j) :
    complexBase ⟶ (finiteLineWorld M).X :=
    Spec.map (CommRingCat.ofHom h.val) ≫ Proj.awayι (lineGrading M)
      (lineQuotientMap M (MvPolynomial.X j)) (lineCoverHomogeneousOneQ M j) zero_lt_one  -- :267
chartPointHomOf_section (M) (j) (h) :
    chartPointHomOf M j h ≫ (finiteLineWorld M).structureMap = 𝟙 complexBase    -- :283
noncomputable def chartPoint (M) [NeZero M] (j) (c : ℂ) : ComplexPoint (finiteLineWorld M)  -- :321
noncomputable def coordPoint (M) [NeZero M] :
    (Sigma (fun _ : Fin M => Option ℂ)) → ComplexPoint (finiteLineWorld M) :=
    fun z => match z.2 with
    | some c => chartPoint M (lineLeftChart M z.1) c
    | none   => chartPoint M (lineRightChart M z.1) 0                            -- :332
chartPointSpace_eval (M) (j) (h : chartPointSpace M j) :
    h.val = chartEvalRingHom M j (h.val (chartRatio M j))                        -- :356
noncomputable def chartPointSpaceEquiv (M) [NeZero M] (j) : chartPointSpace M j ≃ ℂ  -- :387
abbrev FiniteLinePointsGate (M) [NeZero M] : Type _ :=
    ComplexPoint (finiteLineWorld M) ≃ (Sigma (fun _ : Fin M => Option ℂ))        -- :403
noncomputable def finiteLineAnalytificationOfGate (M) [NeZero M] (gate) : AnalytificationData … -- :412
finiteLineAnalytificationOfGate_space (M) (gate) : … = TopCat.of (sphereUnionSpace M) := rfl  -- :423
finiteLineAnalytificationOfGate_components (M) (gate) : ZerothHomotopy ↥… ≃ Fin M -- :434
```

Supporting world-carrier spine (all in the green import closure):
`finiteLineScheme M := Proj (lineGrading M)` (abbrev, WorldCarrier:65);
`finiteLineStructureMap M : finiteLineScheme M ⟶ complexBase := Proj.toSpecZero
(lineGrading M) ≫ Spec.map (…algebraMap ℂ (lineGrading M 0))` (WorldCarrier:77-80);
`finiteLineWorld M : SmoothProjectiveComplexScheme` (OverBase:331, with the `rfl`
gates `finiteLineWorld_hWX` :339 / `finiteLineWorld_hWmap` :344);
`complexBase : Scheme := Spec (.of ℂ)` (abbrev, GSTProjectiveOverC.lean:37);
`ComplexPoint V := { f : complexBase ⟶ V.X // f ≫ V.structureMap = 𝟙 complexBase }`
(abbrev, GSTGeometricRealizationStage2F.lean:51); `lineGrading` (Ring:155),
`lineQuotientMap` (Ring:126), `lineCoverHomogeneousOneQ` (Smoothness:201),
`chartRingHom` (Smoothness:417), `chartRatio` (Smoothness:469), `chartMap`
(Smoothness:488), `chartRetracts` (Smoothness:925), `chart_retract` (:960),
`chartMap_surjective` (:907), `riemannSphereEquiv : unitSphereType ≃ Option ℂ`
(Riemann:321), `sphereUnionCoordEquiv : sphereUnionSpace M ≃ Σ _ : Fin M, Option ℂ`
(Analytification:137).

**The inverse-shape requirement (what W8-A's forward map's inverse must
produce):** the gate equiv's `invFun` must BE `coordPoint M` verbatim (some-case:
left chart at the coordinate; none-case: right chart at 0). Its two laws ride:
(i) `forward (coordPoint z) = z` — the ring-level chart reading via
`chartPointSpace_eval` + `chartEvalRingHom_chartRatio` (the coordinate of
`chartPoint M j c` is `c`) plus the line-index machinery of PointsGate §2-§3;
(ii) `coordPoint (forward p) = p` — the decomposition: `p` restricted to its
image's chart, read through `basicOpenIsoSpec.inv` + `Spec.homEquiv`, lands in
`chartPointSpace M j` (ℂ-linearity from the section property), and
`chartPointHomOf` reproduces it — modulo the `Spec.map_preimage` roundtrip and
the `chartPointHomOf_section`-reverse calc.

---

## PART 2 — THE ROUTE CARDS (the cleanest green line per battle step)

### CARD A — one-point-source route (the gate's restriction head)

**Goal shape:** from `p : complexBase ⟶ Y` (Y any scheme) with the image point in
`U : Y.Opens`, produce `complexBase ⟶ U.toScheme` with the factorization receipt.

```
-- INPUT: hpre : p ⁻¹ᵁ U = ⊤   (CARD B)
def sectionInto (p : complexBase ⟶ Y) (U : Y.Opens) (hpre : p ⁻¹ᵁ U = ⊤) :
    complexBase ⟶ U.toScheme :=
  (Scheme.topIso complexBase).inv ≫ p.resLE U ⊤ hpre.ge
-- receipt:  (sectionInto … ) ≫ U.ι = p
--   := (resLE_comp_ι p U ⊤ hpre.ge) ▸ … composed with Scheme.toIso_inv_ι (simp)
```
* `p.resLE U ⊤ hpre.ge : ⊤.toScheme ⟶ U.toScheme` — Restrict.lean:775
  (`resLE (f) (U) (V) (e : V ≤ f ⁻¹ᵁ U)`).
* `(Scheme.topIso complexBase).inv : complexBase ⟶ (⊤ : complexBase.Opens).toScheme`
  — Restrict.lean:439.
* Unfolded alternative (defeq; `isoOfEq_inv = homOfLE e.ge := rfl`, :473):
  `(Scheme.topIso complexBase).inv ≫ (Scheme.isoOfEq complexBase hpre).inv ≫ p ∣_ U`.
* Alternative route (same file): `Scheme.Opens.isoOfLE` (:501) when the cover is
  given as `U ≤ ⊤` shape; NOT needed here.
* **PIN PRECEDENT for the exact composite shape:** `Proj.toSpecZero`
  (Basic.lean:151-153) is literally `(Scheme.topIso _).inv ≫ (Scheme.isoOfEq _
  (basicOpen_one _)).inv ≫ basicOpenToSpec 𝒜 1 ≫ Spec.map …` — the pin itself
  builds a global morphism out of a one-`D₊(1)`-restriction by
  `topIso.inv ≫ isoOfEq.inv ≫ chart-map`. The W8 head is this pattern with
  `D₊(f)` in place of `D₊(1)`.
* Then the chart leg: `sectionInto p (Proj.basicOpen …) hpre ≫
  (Proj.basicOpenIsoSpec (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
  (lineCoverHomogeneousOneQ M j) zero_lt_one).hom : complexBase ⟶ Spec (.of (Away
  (lineGrading M) (…)))` — the full restriction-to-chart composite, whose every
  factor is corpus-green (`basicOpenIsoSpec` + `awayι` family: ClosedImmersion
  twelve uses; `topIso`/`isoOfEq`/`resLE`: pin + the `toSpecZero` precedent).

### CARD B — `p ⁻¹ᵁ basicOpen = ⊤` (the one-point preimage law)

In-module lemma to author (nothing at pin/corpus states it):
```
lemma complexBase_preimage_eq_top_of_mem (p : complexBase ⟶ Y) (U : Y.Opens)
    (h : ∀ x : complexBase, p.base x ∈ U) : p ⁻¹ᵁ U = ⊤
```
Proof pieces (every one two-method verified):
1. `Subsingleton ↥complexBase` — the ShiftWord:513 instance route
   (`inferInstanceAs (Subsingleton ↥(Spec (CommRingCat.of ℂ)))`); the hypothesis
   `h` reduces to the single point by `Subsingleton.elim`.
2. opens-equality: `Opens.ext`/`eq_top_iff` + `Set.eq_univ_iff_forall`
   (order/Set core lemmas; pin precedent `awayι_preimage_basicOpen` Basic.lean:301
   via `ext1`, and `fromOfGlobalSections_preimage_basicOpen` :459 via
   `le_antisymm`).
3. point membership: the mandatory dance `rw [← SetLike.mem_coe]; simp only
   [TopologicalSpace.Opens.map_coe, Set.mem_preimage]` (pin's own TODO'd shape,
   Basic.lean:464-465) — NO mem-lemma exists.
4. image-point membership in the chart territory: the W7-B receipt
   `finiteLineComplexPoint_cover_basicOpen` (PointsGate:240) — or, if that lane
   is red, re-derive: `exists_variable_not_mem` (PointAlgebra:885, green) +
   `basicOpen_of_avoids`-bridge (PointsGate:228-235 private, reproducible:
   `Proj.mem_basicOpen` + `HomogeneousIdeal.mem_iff`).
5. `Proj.mem_basicOpen` (Basic.lean:58, `Iff.rfl` simp) is the
   `f ∉ x.asHomogeneousIdeal` reading at the image point.

### CARD C — the chart iso (restriction to the affine chart and back)

`Proj.basicOpenIsoSpec 𝒜 f f_deg hm : (basicOpen 𝒜 f).toScheme ≅ Spec (.of (Away 𝒜 f))`
(Basic.lean:161; `basicOpenIsoSpec_hom` generated by `@[simps! -isSimp hom]`;
`basicOpenIsoSpec_inv_ι` :190 `rfl`). Corpus-green homes: ClosedImmersion :212
x12. The away-neighbor square for the two-chart consistency:
`SpecMap_awayMap_awayι` (Basic.lean:248) + `basicOpenIsoSpecAway_inv_homOfLE`
(Restrict.lean:536 — note: the AFFINE `Localization.Away` version, Restrict.lean,
NOT the graded `Away` version in Basic.lean:161 — DO NOT confuse the two
`basicOpenIsoSpec*` names).

### CARD D — ring reading (the corpus-green line)

```
-- φ : complexBase ⟶ Spec (.of A)   (A = the chart ring, after CARD A + CARD C)
def ringReading (φ : complexBase ⟶ Spec (.of A)) : A →+* ℂ :=
  (Spec.homEquiv (R := CommRingCat.of A) (S := CommRingCat.of ℂ) φ).hom
```
* Binder orientation VERBATIM from the green home
  (GSTFinitePointAnalytification.lean:211-214; GSTTwelvePointAnalytification.
  lean:169-172): named args `(R := the TARGET's ring)` `(S := ℂ)`, input
  `f : Spec ℂ ⟶ Spec A`, result a CommRingCat hom `A ⟶ ℂ`, `.hom` the RingHom.
* Satellites (all green): `Spec.preimage` (same named-arg orientation),
  `Spec.preimage_comp` (contravariant), `Spec.preimage_map`,
  `Spec.preimage_id`, `Spec.map_preimage` (the roundtrip
  `f = Spec.map (Spec.preimage f)`), `Spec.map_id`, `Spec.map_comp`,
  `CommRingCat.ofHom/hom_ext/hom_id/hom_comp`.
* The ℂ-linearity (`chartPointSpace` membership of `ringReading`) follows from the
  section property `p ≫ structureMap = 𝟙` restricted to the chart + the chart
  square `chart_awayι_comp'` (Smoothness:377) — the `chartPointHomOf_section`
  calc (Analytification:283-317) run in reverse (the calc chain is verbatim
  reusable: assoc regroup → chart square → `Spec.map_comp` fusion → ring ext →
  `Spec.map_id`).
* Fallback (pin-verified, corpus-unexercised): `(Scheme.ΓSpecIso A).inv ≫
  φ.appTop ≫ (Scheme.ΓSpecIso ℂ).hom` — NOT recommended (RED FLAG R3).

### CARD E — section equality (the ext)

```
refine (Proj.affineOpenCover (lineGrading M)).openCover.hom_ext _ _ fun i ↦ ?_
-- or: (Proj.mapAffineOpenCover g hg).openCover.hom_ext _ _ fun s ↦ ?_   (OverBase:171 verbatim)
```
* Closes `f = g : Proj 𝒜 ⟶ Z` from `∀ i, 𝒰.f i ≫ f = 𝒰.f i ≫ g` —
  PREcomposition by the cover legs. There is NO bare `Scheme.hom_ext`.
* Ring-level legs inside each chart: `CommRingCat.hom_ext` (green: Analytification
  :295) or `DFunLike.ext`-pinned (FinitePointAnalytification :367's AUDIT-8
  lesson: avoid the Pi-ext registry).

---

## PART 3 — RED FLAGS (anything missing / different / first-consumption risk)

* **R1 — `IsOpenImmersion.isoOfRangeEq` is NOT in the pin and has ZERO
  corpus-green uses.** Its signature above is reconstructed from ~25 pin usage
  sites (`isoOfRangeEq (f) (g) (h : Set.range …)` + `_hom_fac`/`_inv_fac`
  three-arg calls). It is the ENGINE inside the wrapped isos (`isoOfEq`,
  `topIso`-adjacent, `basicOpenIsoSpecAway`, `isoImage`) — **W8-A should call
  only the WRAPPED names (all corpus-green or pin-direct), never
  `isoOfRangeEq` itself.** If it must be called, verify the `Set.range`
  argument's exact form in CI (it is stated over the coerced base functions;
  the pin's own proofs pass `by simp [Set.range_comp]`-style terms).
* **R2 — `morphismRestrict_base`, `morphismRestrict_base_coe`,
  `morphismRestrict_appTop`, `pullbackRestrictIsoRestrict`,
  `isPullback_morphismRestrict`, `morphismRestrictOpensRange` are
  pin-verified but corpus-unexercised** (first-consumption risk, not absence
  risk). Only `morphismRestrict` + `morphismRestrict_ι` + the `IsIso (f ∣_ U)`
  instance are corpus-green (ClosedImmersion :197/:210/:277;
  FinitePointWorldCarrier :577-637 with the `delta` seam-trick).
* **R3 — `Scheme.Hom.appTop` and `Scheme.ΓSpecIso` have ZERO corpus uses** (the
  contravariant direction `f.appTop : Γ(Y,⊤) ⟶ Γ(X,⊤)` is derived from pin
  composites, not stated anywhere verbatim). The ring-reading MUST go through
  the corpus-green `Spec.homEquiv`/`Spec.preimage` route (CARD D).
* **R4 — `Scheme.OpenCover.iSup_opensRange` is pin-verified-by-usage only,
  corpus-unconsumed**, and is NOT needed on the W8 critical path (the cover at
  the point level is already in hand from W7-B / the prime-lattice module). Do
  not pull it in.
* **R5 — THE `topIso` NAME COLLISION.** TWO different `topIso`s live in
  Restrict.lean: `Scheme.topIso X : ↑(⊤ : X.Opens) ≅ X` (:439, the scheme-level
  iso W8 needs) vs `Scheme.Opens.topIso : Γ(U, ⊤) ≅ Γ(X, U)` (:146, a
  sections-level iso used by `resLE_app_top` :827). W8-A must always spell the
  scheme-level one (`(Scheme.topIso complexBase).inv`) and never let dot-resolution
  or `open`s pick the Opens one.
* **R6 — the `Unique (PrimeSpectrum ℂ)` dual-instance-path hazard**
  (GSTFinitePointShiftWord AUDIT-1 :80-96): two different instance paths to the
  same one-point fact (scheme-level via `Field ℂ` vs artinian-krull-dim chain).
  Consequences: (a) never close one-point equations by bare `rfl` — use
  `Subsingleton.elim`; (b) mixed `Spec`-carrier/`PrimeSpectrum`-spelled equations
  are ill-typed at implicit transparency — cross the seam only in TERM MODE at
  default transparency (the WAVE-32 law); (c) state the gate's forward map at an
  explicit base point (the W7-B honest quantification) or at `default`, never
  compare defaults across paths.
* **R7 — the W8 cover input rides `GSTFiniteLinePointsGate`, whose lane is
  registered but NOT CI-confirmed green** at the dossier's write time (wave 7's
  push carried it; verdict pending). Contingency: re-derive the cover from the
  GREEN `exists_variable_not_mem` (PointAlgebra:885, transitively green via the
  honest-hodge-data lane) + `Proj.mem_basicOpen` + `HomogeneousIdeal.mem_iff`
  (the `basicOpen_of_avoids` bridge is 8 lines, PointsGate:228-235).
* **R8 — no `x ∈ f ⁻¹ᵁ U ↔ f.base x ∈ U` membership lemma exists** (the pin's
  own TODO, Basic.lean:464). The three-step `SetLike.mem_coe`/`map_coe`/
  `Set.mem_preimage` dance is mandatory and corpus-invisible (must be authored
  inline, exactly the pin's spelling).
* **R9 — the `basicOpenIsoSpec*` family split:** `basicOpenIsoSpec` (Basic.lean:161,
  graded `Away`, Proj) vs `basicOpenIsoSpecAway` (Restrict.lean:520, affine
  `Localization.Away`, `PrimeSpectrum.basicOpen`, ROOT namespace). Different
  files, different rings, different namespaces. The wave's target list citing
  `basicOpenIsoSpecAway` alongside the Proj family is correct only in the
  `toBasicOpenOfGlobalSections`-engine role (pin Basic.lean:373); the W8 chart
  leg uses `basicOpenIsoSpec`, never `basicOpenIsoSpecAway`.
* **R10 — `resLE` and `Scheme.topIso` are pin-internal-only** (no corpus use);
  the pin's own `Proj.toSpecZero` (Basic.lean:151) and
  `toBasicOpenOfGlobalSections` (Basic.lean:372: `(X.isoOfEq …).inv ≫ X.toSpecΓ
  ∣_ _`) are the direct precedents — first-consumption risk is real but the
  pattern is twice pin-embedded.
* **R11 — universe discipline:** every restriction API piece is `Scheme.{u}`
  uniform; `complexBase = Spec (.of ℂ)` and `finiteLineScheme M` share the
  default universe — no universe bridging required (corpus never needed it on
  this chain).

---

## PART 4 — THE HONESTY VERDICT

**Is the restriction route to the gate FULLY constructible from the pin +
corpus-green? — YES.** Every API name on the critical path resolves, with the
following named gaps — ALL of them are in-module lemmas (new mathematics inside
the corpus's own discipline), NONE requires a missing Mathlib name:

1. **The one-point receipt** (`Subsingleton ↥complexBase` / `∀ x y, x = y`) —
   must be authored in-module, riding the resolvable instance chain (the green
   ShiftWord:513 pattern verbatim), with the R6 hazards respected.
2. **The one-point preimage law** (`p ⁻¹ᵁ basicOpen = ⊤`) — must be authored
   (CARD B; all five pieces verified; the W7-B cover or its green re-derivation).
3. **The restricted-section ring reading** (`ringReading` + its
   `chartPointSpace` membership / ℂ-linearity) — must be authored (CARD D; the
   section-property → ℂ-linearity calc is the green `chartPointHomOf_section`
   chain reversed).
4. **The two-chart consistency and the two inverse laws of the equiv** — the
   actual W8 mathematics; every consumed name is verified above
   (`chartPointSpace_eval`, `chartPointSpaceEquiv`, `chartEvalRingHom_chartRatio`,
   `SpecMap_awayMap_awayι`, `resLE_comp_ι`, `Spec.map_preimage`, the
   PointsGate line-index machinery).
5. **The image-point independence from the base point** — one
   `Subsingleton.elim` (R6 law).

The wave-7 "Proj universal property INTO Proj is absent" diagnosis is CONFIRMED
as accurate-but-OBSOLETE: the pinned Mathlib indeed has only the construction
direction (`fromOfGlobalSections`, Basic.lean:443, no converse — verified), but
`morphismRestrict` (Restrict.lean:569) + `Scheme.topIso` (:439) +
`resLE` (:775) + `Scheme.isoOfEq` (:455) replace the needed decomposition —
the restriction composite `topIso.inv ≫ resLE ≫ basicOpenIsoSpec.hom` IS the
factorization of the section through the away chart, with
`resLE_comp_ι`/`morphismRestrict_ι` as the triangle receipts and the pin's own
`toSpecZero`/`toBasicOpenOfGlobalSections` as the embedded precedents.

Top-3 risks for the lane: (R7) the points-gate cover dependency's unconfirmed
lane; (R6/R8) the one-point instance-path and membership-dance elaboration
diseases (both are documented corpus lessons — the exact failure classes of
waves 28-32 and the pin's own TODO); (R2/R10) the first-consumption risk on the
pin-internal-only restriction lemmas (`resLE`, `Scheme.topIso`) — mitigated by
the two embedded pin precedents, but designated CI repair points.

— W8-B, 2026-11-23. Static two-method verification only (no local Lean by repo
law); the kernel verdict belongs to CI at the pushed SHA.
