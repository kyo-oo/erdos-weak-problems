# W2-E DOSSIER — pinned-Mathlib homology / singular-cohomology API for `GSTTwelvePointCohomology.lean`

Pin: `mathlib4` @ `51e6992efd06126df61a496bebf8f49482a4e129` = `v4.33.0-rc2`
(commit msg `chore: bump toolchain to v4.33.0-rc2 (#42401)`, dated 2026-08-03; tree sha
`e7bfd7bc39c98874e58fa69f2644bb0fa9c0e5bf`; 8842 `.lean` files). All files below were fetched
verbatim at the pin and cached in `/tmp/Pin*.lean` (manifest §9). This pinned Mathlib uses the
**module system** (`module` / `public import`) and the **`CategoryWithHomology` / `HasHomology`**
homology architecture; `Mathlib/CategoryTheory/Homology/` does not exist (homology lives in
`Mathlib/Algebra/Homology/`), and there is no standalone `CochainComplex.lean` (the abbrevs live
in `HomologicalComplex.lean`).

## 0. VERDICT (defects found)

| # | Name used by corpus file | Status at pin |
|---|---|---|
| 1 | `isoHomologyι` (GSTTwelvePointCohomology.lean:219, called with **2** explicit args) | **EXISTS but with 4 explicit args** — ARITY MISMATCH, blocking |
| 2 | `pOpcyclesIso` (:220, called with **2** explicit args) | **EXISTS but with 4 explicit args** — ARITY MISMATCH, blocking |
| 3 | `IsZero.eq` (AUDIT(12) comment) | **NOT FOUND at pin** (`IsZero` API has `eq_to/to_eq/eq_from/from_eq/eq_of_src/eq_of_tgt/of_iso/op`, no bare `eq`); the actual proof body uses `ModuleCat.subsingleton_of_isZero`, which exists — comment-only defect |
| 4 | `HomologicalComplex.shortComplexFunctor_obj_f` / `_obj_g` (:309,:323) | Generated `@[simps!]` lemmas of `shortComplexFunctor` (SCHC:47); **sibling-attested** (`…_obj_X₂` used at SCHC:857/886; primed `shortComplexFunctor'_obj_f/g` used at SCHC:873/903). Moderate confidence — designated CI repair point; fallback = primed names. |
| 5 | everything else | verified at the pin with the exact arity the corpus file uses |

Repair shapes (type-checked against pinned signatures):
```lean
-- GSTTwelvePointCohomology.lean:217-221 becomes
noncomputable def twelvePointHomologyZero :
    twelvePointDualCochains.homology 0 ≅ twelvePointDualCochains.X 0 :=
  twelvePointDualCochains.isoHomologyι 0 1 upNext_zero dualCochains_d_zero_one ≪≫
    (twelvePointDualCochains.pOpcyclesIso 0 0 upPrev_zero dualCochains_d_zero_zero).symm
```
Instances: `[K.HasHomology 0]` fires for any `ModuleCat ℚ` complex via
`CategoryTheory.categoryWithHomology_of_abelian` (SC/Abelian.lean:193) → `CategoryWithHomology.hasHomology`
(SC/Homology.lean:816-819) → `K.HasHomology i := (K.sc i).HasHomology` (SCHC:77).

---

## 1. HomologicalComplex homology core — `Mathlib/Algebra/Homology/ShortComplex/HomologicalComplex.lean` (cache `/tmp/PinShortComplexHomologicalComplex.lean`, 947 lines; corpus imports exactly this file)

Section variables (line 63): `(K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)` — all explicit unless re-bound implicit at line 326 (`variable {K L M}`).

| Name | file:line | Verbatim pinned signature | Explicit args |
|---|---|---|---|
| `HomologicalComplex.sc` | :69 | `noncomputable abbrev sc := (shortComplexFunctor C c i).obj K` — `K.sc i`, the short complex `K.X (c.prev i) ⟶ K.X i ⟶ K.X (c.next i)` | `i` (K by dot) |
| `HomologicalComplex.HasHomology` | :77 | `abbrev HasHomology := (K.sc i).HasHomology` | — |
| `HomologicalComplex.homology` | :90 | `noncomputable def homology := (K.sc i).homology` (`variable [K.HasHomology i]`) | `i` |
| `HomologicalComplex.cycles` | :93 | `noncomputable def cycles := (K.sc i).cycles` | `i` |
| `HomologicalComplex.iCycles` | :96 | `noncomputable def iCycles : K.cycles i ⟶ K.X i := (K.sc i).iCycles` | `i` |
| `HomologicalComplex.homologyπ` | :99 | `noncomputable def homologyπ : K.cycles i ⟶ K.homology i := (K.sc i).homologyπ` | `i` |
| `HomologicalComplex.opcycles` | :217 | `noncomputable def opcycles := (K.sc i).opcycles` | `i` |
| `HomologicalComplex.pOpcycles` | :220 | `noncomputable def pOpcycles : K.X i ⟶ K.opcycles i := (K.sc i).pOpcycles` | `i` |
| `HomologicalComplex.homologyι` | :223 | `noncomputable def homologyι : K.homology i ⟶ K.opcycles i := (K.sc i).homologyι` | `i` |
| `HomologicalComplex.homologyMap` | :330 | `noncomputable def homologyMap : K.homology i ⟶ L.homology i := ShortComplex.homologyMap ((shortComplexFunctor C c i).map φ)` | `φ i` — corpus `homologyMap e.hom n` ✓ |
| `HomologicalComplex.homologyMap_id` | :356 | `@[simp] lemma homologyMap_id : homologyMap (𝟙 K) i = 𝟙 _` | `i` |
| `HomologicalComplex.homologyMap_comp` | :371 | `@[reassoc] lemma homologyMap_comp : homologyMap (φ ≫ ψ) i = homologyMap φ i ≫ homologyMap ψ i` | `φ ψ i` |
| `HomologicalComplex.homologyMapIso` | :421 | `noncomputable def homologyMapIso : K.homology i ≅ L.homology i where hom := homologyMap iso.hom i; inv := homologyMap iso.inv i …` | `iso i` — **ready-made replacement for the corpus's hand-rolled `homologyIsoOfIso`** |
| `HomologicalComplex.cyclesMap` / `opcyclesMap` | :334 / :338 | duals of `homologyMap` | `φ i` |
| **`HomologicalComplex.isoHomologyι`** | **:563** | section :534 `variable (hj : c.next i = j) (h : K.d i j = 0) [K.HasHomology i]`, `include hj h`; `@[simps! hom] noncomputable def isoHomologyι : K.homology i ≅ K.opcycles i` (body `asIso (K.homologyι i)`) | **`i j hj h` — 4 explicit** (K implicit, from `variable {K L M}` :326). Verified by in-file calls `K.isoHomologyι i j hj h` (:569, :575) |
| **`HomologicalComplex.pOpcyclesIso`** | **:590** | section :581 `variable (hi : c.prev j = i) (h : K.d i j = 0) [K.HasHomology j]`, `include hi h`; `@[simps! hom] noncomputable def pOpcyclesIso : K.X j ≅ K.opcycles j` (body `asIso (K.pOpcycles j)`) | **`i j hi h` — 4 explicit**, note `i` FIRST (`hi : c.prev j = i`) |
| `HomologicalComplex.iCyclesIso` | :543 | section :534; `noncomputable def iCyclesIso : K.cycles i ≅ K.X i` | `i j hj h` — 4 explicit |
| `HomologicalComplex.isoHomologyπ` | :610 | section :581; `noncomputable def isoHomologyπ : K.cycles j ≅ K.homology j` | `i j hi h` — 4 explicit |
| `HomologicalComplex.ExactAt` | :651 | `def ExactAt := (K.sc i).Exact` (Prop) | `i` |
| `HomologicalComplex.exactAt_iff` | :653 | `K.ExactAt i ↔ (K.sc i).Exact := by rfl` | `i` |
| `HomologicalComplex.ExactAt.of_iso` | :657 | `lemma ExactAt.of_iso (hK : K.ExactAt i) {L} (e : K ≅ L) : L.ExactAt i` | `hK e` |
| `HomologicalComplex.ExactAt.of_isZero` | :663 | `lemma ExactAt.of_isZero (h : IsZero (K.X i)) : K.ExactAt i` | `h` |
| `HomologicalComplex.exactAt_iff_isZero_homology` | :670 | `K.ExactAt i ↔ IsZero (K.homology i)` (`[K.HasHomology i]`) | `i` |
| **`HomologicalComplex.ExactAt.isZero_homology`** | **:676** | `lemma ExactAt.isZero_homology [K.HasHomology i] (h : K.ExactAt i) : IsZero (K.homology i)` — exactly the corpus call `(...).isZero_homology`; consumed by pinned `SingularHomology/Basic.lean:131` | `h` |
| `HomologicalComplex.Acyclic` | :681 | `def Acyclic := ∀ i, K.ExactAt i` | — |
| `HomologicalComplex.homologyFunctor` | :469 | `@[simps] noncomputable def homologyFunctor [CategoryWithHomology C] : HomologicalComplex C c ⥤ C` | `C c i` |
| `HomologicalComplex.shortComplexFunctor'` | :38 | `@[simps] def shortComplexFunctor' (i j k : ι) : HomologicalComplex C c ⥤ ShortComplex C where obj K := ShortComplex.mk (K.d i j) (K.d j k) (K.d_comp_d i j k)` — generated lemmas `shortComplexFunctor'_obj_f` (attested :873) and `_obj_g` (attested :903) | `C c i j k` |
| `HomologicalComplex.shortComplexFunctor` | :47 | `@[simps!] noncomputable def shortComplexFunctor (i : ι) := shortComplexFunctor' C c (c.prev i) i (c.next i)` — generated `shortComplexFunctor_obj_X₂` (attested :857/:886) and, by the same `@[simps!]`, `shortComplexFunctor_obj_f` / `_obj_g` (**generated, not text-attested — see defect #4**) | `C c i` |

Degree-zero specialisations (section :695-761):
- `ChainComplex.isIso_iCycles₀` :700, `ChainComplex.cycles₀Iso : K.cycles 0 ≅ K.X 0` :705, `ChainComplex.isIso_homologyι₀` :708, **`ChainComplex.isoHomologyι₀ : K.homology 0 ≅ K.opcycles 0`** :714 — **ChainComplex-only** (`K : ChainComplex C ℕ`).
- `CochainComplex.isIso_pOpcycles₀` :734, **`CochainComplex.opcycles₀Iso : K.X 0 ≅ K.opcycles 0`** :739, `CochainComplex.isIso_homologyπ₀` :742, **`CochainComplex.isoHomologyπ₀ : K.cycles 0 ≅ K.homology 0`** :748 — **CochainComplex-only**. (The corpus's dual cochain complex must use the general 4-arg `isoHomologyι`/`pOpcyclesIso`, since `isoHomologyι₀` is not available for cochains.)

## 2. ShortComplex API

- **`Mathlib/Algebra/Homology/ShortComplex/Basic.lean`** (cache `/tmp/PinShortComplexBasic.lean`):
  `structure ShortComplex where {X₁ : C} X₂ X₃, f : X₁ ⟶ X₂, g : X₂ ⟶ X₃, zero : f ≫ g = 0` (:34-46), namespace `CategoryTheory.ShortComplex`; Hom fields `τ₁ τ₂ τ₃`; `unopFunctor` :300.
- **`Mathlib/Algebra/Homology/ShortComplex/Exact.lean`** (`/tmp/PinShortComplexExact.lean`):
  `structure Exact : Prop` (:45); `exact_iff_isZero_homology` (:59); `exact_iff_of_iso` (:118); `exact_iff_of_epi_of_isIso_of_mono` (:139).
- **`Mathlib/Algebra/Homology/ShortComplex/Homology.lean`** (`/tmp/PinShortComplexHomology.lean`):
  `ShortComplex.homology` :384; `homologyMap` :435; `homologyMap_id` :504; `homologyMap_comp` :529;
  **`class _root_.CategoryTheory.CategoryWithHomology : Prop where hasHomology : ∀ (S : ShortComplex C), S.HasHomology`** :816 (+ `attribute [instance]` :819; opposite instance :821; `ShortComplex.homologyFunctor` :826).
- **`Mathlib/Algebra/Homology/ShortComplex/Abelian.lean`** (`/tmp/PinSCAbelian.lean`):
  **`instance _root_.CategoryTheory.categoryWithHomology_of_abelian [Abelian C] : CategoryWithHomology C`** (:193) — supplies `CategoryWithHomology (ModuleCat ℚ)`; also `Abelian (ShortComplex C)` :207.
- **`Mathlib/Algebra/Homology/ShortComplex/RightHomology.lean`** (`/tmp/PinShortComplexRightHomology.lean`):
  `ShortComplex.pOpcycles : S.X₂ ⟶ S.opcycles` :540; `f_pOpcycles` :546; `isIso_pOpcycles (hf : S.f = 0)` :579; **`ShortComplex.opcyclesIsoX₂ (hf : S.f = 0) : S.opcycles ≅ S.X₂`** :585 (SC-level analogue of the corpus's `pOpcyclesIso` move); `moduleCatOpcyclesIso` (referenced in ModuleCat file).
- **`Mathlib/Algebra/Homology/ShortComplex/ModuleCat.lean`** (`/tmp/PinShortComplexModuleCat.lean`, namespace `CategoryTheory.ShortComplex`, `variable (S : ShortComplex (ModuleCat.{v} R))`):
  - `moduleCat_exact_iff` :48 — `S.Exact ↔ ∀ (x₂ : S.X₂) (_ : S.g x₂ = 0), ∃ (x₁ : S.X₁), S.f x₁ = x₂`
  - `moduleCat_exact_iff_ker_sub_range` :52 — `S.Exact ↔ LinearMap.ker S.g.hom ≤ LinearMap.range S.f.hom`
  - **`moduleCat_exact_iff_range_eq_ker` :57 — `lemma moduleCat_exact_iff_range_eq_ker : S.Exact ↔ LinearMap.range S.f.hom = LinearMap.ker S.g.hom`** (S explicit; corpus `rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]` unifies S from the goal — VERIFIED, arity correct). Companions: `Exact.moduleCat_range_eq_ker` :64, `ShortExact.moduleCat_exact_iff_function_exact` :78.
  - `moduleCatMk` :37, `moduleCatToCycles` :96, `moduleCat_pOpcycles_eq_iff` :163, `moduleCatOpcyclesIso` (used :159).

## 3. Singular homology of (totally disconnected) spaces — `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean` (cache `/tmp/PinSingularHomologyBasic.lean`; 148 lines)

Section variables :32-33: `(C : Type u) [Category.{v} C] [HasCoproducts.{w} C]`, `[Preadditive C] (n : ℕ)`; TotallyDisconnected section :104: `(R : C) (X : TopCat.{w}) [TotallyDisconnectedSpace X]`.

| Name | file:line | Verbatim pinned signature |
|---|---|---|
| `AlgebraicTopology.singularChainComplexFunctor` | :36 | `def singularChainComplexFunctor : C ⥤ TopCat.{w} ⥤ ChainComplex C ℕ := SSet.chainComplexFunctor.{w} C ⋙ …` — **1 explicit arg `C`**; corpus `((singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient).obj A.space` ✓ |
| `AlgebraicTopology.singularHomologyFunctor` | :55 | `def singularHomologyFunctor [CategoryWithHomology C] : C ⥤ TopCat.{w} ⥤ C` — explicit `C n` (n from :33) |
| **`singularChainComplexFunctorIsoOfTotallyDisconnectedSpace`** | **:110** | `noncomputable def … : ((singularChainComplexFunctor C).obj R).obj X ≅ (ChainComplex.alternatingConst.obj (∐ fun _ : X ↦ R))` — **3 explicit args `C R X`** (+ implicit `[HasCoproducts.{w} C] [Preadditive C] [TotallyDisconnectedSpace X]`). Corpus call `singularChainComplexFunctorIsoOfTotallyDisconnectedSpace (ModuleCat ℚ) rationalCoefficient twelvePointSpace` ✓ arity-correct. |
| `singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace` | :118 | `lemma … (hn : n ≠ 0) : (((singularChainComplexFunctor C).obj R).obj X).ExactAt n` |
| **`isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`** | **:126** | `lemma … [CategoryWithHomology C] (hn : n ≠ 0) : IsZero (((singularHomologyFunctor C n).obj R).obj X)` |
| **`singularHomologyFunctorZeroOfTotallyDisconnectedSpace`** | **:136** | `noncomputable def … [CategoryWithHomology C] : ((singularHomologyFunctor C 0).obj R).obj X ≅ ∐ fun _ : X ↦ R` — the H₀ ≅ ∐-of-R shape |
| support | :40, :46 | `instance : (singularChainComplexFunctor C).Additive`; `instance [Limits.HasPullbacks C] {X : C} : ((singularChainComplexFunctor C).obj X).PreservesMonomorphisms` |

Companion `Mathlib/AlgebraicTopology/SingularHomology/HomologyZero.lean` (cache `/tmp/PinSHomologyZero.lean`):
`TopCat.singularHomology₀Iso : ((singularHomologyFunctor C 0).obj R).obj X ≅ ∐ (fun (_ : ZerothHomotopy X) ↦ R)` :36; `TopCat.singularHomology₀ε` :42; `instance [PathConnectedSpace X] : IsIso (X.singularHomology₀ε R)` :53.

## 4. Alternating constant complex — `Mathlib/Algebra/Homology/AlternatingConst.lean` (cache `/tmp/PinAlternatingConst.lean`)

- :47-48 variables `{C} [Category C] [HasZeroMorphisms C] (A : C) {φ : A ⟶ A} {ψ : A ⟶ A} (hOdd : φ ≫ ψ = 0) (hEven : ψ ≫ φ = 0)`.
- **`HomologicalComplex.alternatingConst`** :55 (with :73 `{c : ComplexShape ℕ} [DecidableRel c.Rel] (hc : ∀ i j, c.Rel i j → Odd (i + j))`): `@[simps!] noncomputable def alternatingConst … : HomologicalComplex C c where X n := A; d i j := if hij : c.Rel i j then if hi : Even i then φ else ψ else 0` — explicit args `A hOdd hEven hc` (φ,ψ implicit). The `@[simps!]` generates **`HomologicalComplex.alternatingConst_d`** (and `alternatingConst_X`) — the corpus's `HomologicalComplex.alternatingConst_d` ✓.
- `alternatingConstScIsoEven` :80 / `alternatingConstScIsoOdd` :95 — `(alternatingConst A hOdd hEven hc).sc' i j k ≅ ShortComplex.mk ψ φ hEven` / `… ≅ ShortComplex.mk φ ψ hOdd`.
- `alternatingConstHomologyIsoEven` :135 / `Odd` :142 — `(alternatingConst A hOdd hEven hc).homology j ≅ (ShortComplex.mk ψ φ hEven).homology` (`[CategoryWithHomology C]`, args `hpj hnj h`).
- **`ChainComplex.alternatingConst`** :159: `@[simps] noncomputable def alternatingConst [HasZeroMorphisms C] : C ⥤ ChainComplex C ℕ` (0 explicit args; body `HomologicalComplex.alternatingConst X (Category.id_comp 0) (Category.comp_id 0) down_nat_odd_add`) — generates **`ChainComplex.alternatingConst_obj`** ✓ (corpus's simp name) and `_map`.
- `instance (X : C) (n : ℕ) : (alternatingConst.obj X).HasHomology n` :195 — **HasHomology is free on alternatingConst**.
- **`ChainComplex.alternatingConst_exactAt`** :203: `lemma alternatingConst_exactAt (X : C) (n : ℕ) (hn : n ≠ 0) : (alternatingConst.obj X).ExactAt n`.
- **`ChainComplex.alternatingConstHomologyZero`** :211: `noncomputable def alternatingConstHomologyZero (X : C) : (alternatingConst.obj X).homology 0 ≅ X`.
- `AlgebraicTopology.alternatingFaceMapComplexConst` :221; `ChainComplex.alternatingConstHomotopyEquiv` :232.
- `ComplexShape.up_nat_odd_add` :33 / `down_nat_odd_add` :37.

## 5. Shapes — `Mathlib/Algebra/Homology/ComplexShape.lean` (`/tmp/PinComplexShape.lean`) + `Mathlib/Algebra/Homology/HomologicalComplex.lean` (`/tmp/PinHomologicalComplex.lean`)

- `ComplexShape` structure :63 (`Rel`, `next_eq`, `prev_eq`); `ComplexShape.next (c) (i)` :144; `next_eq'` :148; `ComplexShape.up (α) [Add α] [IsRightCancelAdd α] [One α]` :190 (= `up' 1`), `up_mk` :194; `down` = to_dual of `up`; **`ComplexShape.up_Rel` / `down_Rel`** exist as simp lemmas (attested: `PinHomologicalComplex.lean:679` `simp only [ComplexShape.down_Rel]`, `:943` `simp only [ComplexShape.up_Rel]`).
- `abbrev ChainComplex (α) [AddRightCancelSemigroup α] [One α] := HomologicalComplex V (ComplexShape.down α)` :151; `abbrev CochainComplex (α) … := HomologicalComplex V (ComplexShape.up α)` :157.
- **`CochainComplex.next`** :191: `@[simp] theorem next (α : Type*) [AddRightCancelSemigroup α] [One α] (i : α) : (ComplexShape.up α).next i = i + 1` — **2 explicit args**; corpus `CochainComplex.next ℕ 0` ✓ (result `0 + 1`, defeq `1`).
- **`CochainComplex.prev`** :187: `@[simp] theorem prev (α : Type*) [AddGroup α] [One α] (i : α) : (ComplexShape.up α).prev i = i - 1`.
- **`CochainComplex.prev_nat_zero`** :196: `@[simp] theorem prev_nat_zero : (ComplexShape.up ℕ).prev 0 = 0` — **0 explicit args**; corpus ✓.
- **`CochainComplex.prev_nat_succ`** :203: `@[simp] theorem prev_nat_succ (i : ℕ) : (ComplexShape.up ℕ).prev (i + 1) = i` — **1 explicit arg**; corpus `prev_nat_succ (2*k)` ✓.
- ChainComplex duals: `ChainComplex.prev` :163 (`(down α).prev i = i + 1`), `next` :168, `next_nat_zero` :172, `next_nat_succ` :179.
- `HomologicalComplex.XIsoOfEq` :95, `xPrevIso` :406, `xNextIso` :425, `eval` :329, `forget` :337.

## 6. Linear / dualization family

- **`Mathlib/CategoryTheory/Linear/Yoneda.lean`** (`/tmp/PinLinearYoneda.lean`): `CategoryTheory.linearYoneda` — :32-33 `variable (R : Type w) [Ring R] {C} [Category C] [Preadditive C] [Linear R C]`, `variable (C)`; :39 `@[simps] def linearYoneda : C ⥤ Cᵒᵖ ⥤ ModuleCat R` — **2 explicit args `R C`**; corpus `CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)` ✓. (`linearCoyoneda` :51; `linearYoneda_obj_additive` :59.)
- **`Mathlib/CategoryTheory/Abelian/Ext.lean`** (`/tmp/PinAbelianExt.lean`): **`ChainComplex.linearYonedaObj`** :57-61 — `@[simps! X d] def ChainComplex.linearYonedaObj {α : Type*} [AddRightCancelSemigroup α] [One α] (X : ChainComplex C α) (A : Type*) [Ring A] [Linear A C] (Y : C) : CochainComplex (ModuleCat A) α := ((((linearYoneda A C).obj Y).rightOp.mapHomologicalComplex _).obj X).unop` — **explicit `X A Y`** (C, α implicit); corpus `K.linearYonedaObj ℚ rationalCoefficient` ✓ (dot supplies X). The `@[simps! X d]` generates **`ChainComplex.linearYonedaObj_X`** and **`ChainComplex.linearYonedaObj_d`** (corpus `rw [ChainComplex.linearYonedaObj_d]` ✓). Note the `#adaptation_note`/`set_option backward.isDefEq.respectTransparency.types false` at :52-54 guarding the generated signatures.
- **`Mathlib/Algebra/Homology/Additive.lean`** (`/tmp/PinHomologyAdditive.lean`): **`CategoryTheory.Functor.mapHomologicalComplex`** :103 — `def Functor.mapHomologicalComplex (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms] (c : ComplexShape ι) : HomologicalComplex W₁ c ⥤ HomologicalComplex W₂ c` — **2 explicit `F c`**; corpus `.mapHomologicalComplex (ComplexShape.down ℕ)` ✓; additive instance :120; linear instance in `Linear.lean:57-59`.
- **`Mathlib/Algebra/Homology/Opposite.lean`** (`/tmp/PinHomologyOpposite.lean`): **`HomologicalComplex.unopFunctor`** :175 — `@[simps] def unopFunctor : (HomologicalComplex Vᵒᵖ c)ᵒᵖ ⥤ HomologicalComplex V c.symm` — **2 explicit `V c`**; corpus `HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)` ✓ (also `opFunctor` :116, both equivalences :227/:169).
- **`Mathlib/CategoryTheory/Linear/Basic.lean`** (`/tmp/PinCatLinearBasic.lean`, namespace `CategoryTheory.Linear`):
  - **`Linear.leftComp`** :120-124: `variable (R)` then `@[simps] def leftComp {X Y : C} (Z : C) (f : X ⟶ Y) : (Y ⟶ Z) →ₗ[R] X ⟶ Z` — explicit `R Z f`; the generated **`leftComp_apply`** is attested in-file (:157, :161) — corpus `simp [Linear.leftComp_apply, …]` ✓.
  - `Linear.rightComp` :131 (`@[simps]`, explicit `R X g`).
  - **`Linear.homCongr`** :148-149: `def homCongr (k : Type*) {C : Type*} [Category C] [Semiring k] [Preadditive C] [Linear k C] {X Y W Z : C} (f₁ : X ≅ Y) (f₂ : W ≅ Z) : (X ⟶ W) ≃ₗ[k] Y ⟶ Z` — **explicit `k f₁ f₂` (both ISOs)**; corpus `CategoryTheory.Linear.homCongr ℚ twelvePointEIso (Iso.refl rationalCoefficient)` ✓ arity-correct. Companions `homCongr_apply` :164 (`homCongr k f₁ f₂ f = (f₁.inv ≫ f) ≫ f₂.hom`), `homCongr_symm_apply` :169.
  - `Linear.comp` :194.
- `CategoryTheory.Functor.rightOp` — attested at pin via Ext.lean:45-46 (`((linearYoneda R C).obj Y).rightOp`). `Quiver.Hom.op`, `Functor.map_comp`/`map_id` — core, attested throughout.

## 7. ModuleCat / biproduct family

- **`Mathlib/Algebra/Category/ModuleCat/Basic.lean`** (`/tmp/PinModuleCatBasic.lean`):
  - **`LinearEquiv.toModuleIso`** :278 (root namespace, after `end ModuleCat`/`open ModuleCat`): `@[simps] def LinearEquiv.toModuleIso {g₁ : AddCommGroup X₁} {g₂ : AddCommGroup X₂} {m₁ : Module R X₁} {m₂ : Module R X₂} (e : X₁ ≃ₗ[R] X₂) : ModuleCat.of R X₁ ≅ ModuleCat.of R X₂` — 1 explicit `e` ✓.
  - **`CategoryTheory.Iso.toLinearEquiv`** :285-289 (namespace `CategoryTheory.Iso`): `def toLinearEquiv (i : X ≅ Y) : X ≃ₗ[R] Y` (X Y : ModuleCat R implicit) — corpus dot-call `twelvePointCohomologyZeroObj.toLinearEquiv` ✓; simp lemmas `toLinearEquiv_apply` :292, `toLinearEquiv_symm` :293, `toLinearMap_toLinearEquiv` :294; `linearEquivIsoModuleIso` :301.
  - **`ModuleCat.subsingleton_of_isZero`** :376: `theorem subsingleton_of_isZero (h : IsZero M) : Subsingleton M` ✓; `isZero_iff_subsingleton` :381.
  - ModuleCat is root-namespace (`namespace ModuleCat` :67; Preadditive instance :365; hom = LinearMap defeq lemmas :340-363).
- **`Mathlib/Algebra/Category/ModuleCat/Biproducts.lean`** (`/tmp/PinModuleCatBiproducts.lean`, namespace `ModuleCat`): **`ModuleCat.biproductIsoPi`** :125-126: `noncomputable def biproductIsoPi [Finite J] (f : J → ModuleCat.{v} R) : ((⨁ f) : ModuleCat.{v} R) ≅ ModuleCat.of R (∀ j, f j)` — explicit `f` (+`[Finite J]`); simp lemma `biproductIsoPi_inv_comp_π` :130.
- **`Mathlib/CategoryTheory/Limits/Shapes/Biproducts.lean`** (`/tmp/PinLimitsBiproducts.lean`, namespace `CategoryTheory.Limits`): **`biproduct.isoCoproduct`** :539: `def biproduct.isoCoproduct (f : J → C) [HasBiproduct f] : ⨁ f ≅ ∐ f` — explicit `f`; `isoCoproduct_hom` :550, `isoCoproduct_inv` :544, `biproduct.isoProduct : ⨁ f ≅ ∏ᶜ f` :523. Corpus chain `(isoCoproduct f).symm ≪≫ ModuleCat.biproductIsoPi f : ∐ f ≅ of R (∀ j, f j)` types correctly at the pin.
- **`Mathlib/CategoryTheory/Limits/Shapes/ZeroObjects.lean`** (`/tmp/PinZeroObjects.lean`): `structure IsZero (X : C) : Prop` :44 (fields `unique_to`/`unique_from`); namespace `IsZero` :50 with `to_` :58, `eq_to` :61, `to_eq` :64, `from_` :71, `eq_from` :74, `from_eq` :77, **`eq_of_src` :80, `eq_of_tgt` :83**, `epi` :86, `mono` :89, `iso` :93, `isIso` :99, `of_iso` :118, `op` :126 — **NO bare `IsZero.eq` at the pin** (the "X = 0" route is `IsZero.iff_id_eq_zero`, attested via ModuleCat/Basic:379). Defect #3 is comment-only: the corpus proof body uses `ModuleCat.subsingleton_of_isZero` + `Subsingleton.elim` + `LinearEquiv.symm_apply_apply`, all present.
- `Mathlib/Algebra/Homology/HomologicalComplexAbelian.lean` (`/tmp/PinHCAbelian.lean`): `instance : Abelian (HomologicalComplex C c)` :45 (+ injective/projective degree instances :85/:93) — the abelian backing for all `HasHomology` instances used above.
- `Mathlib/Algebra/Category/ModuleCat/Topology/Homology.lean` (`/tmp/PinModuleCatHomology.lean`): `instance : CategoryWithHomology (TopModuleCat R)` :96 (the analogue for topological modules; `kerι`/`cokerπ`/`isLimitKer`/`isColimitCoker` :41-:83).

## 8. Corpus usage shapes (same-tree attestation)

The corpus's dualization core is byte-shared with the "corpus-verified pattern" family
(no CI receipts for these files exist in the sandbox records — the twelve-point lane itself has
no CI run yet, per `research/records/2026-11-14-gst-twelve-point-native-geometric-world.md` §CI status;
the shapes below are the corpus's attested working forms, importing
`Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex` directly):

- `GSTClassicalHodgeSingularCohomologyFunctoriality.lean` :38-59 —
  `((singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient).map f`;
  `(HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map (Quiver.Hom.op ((((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp |>.mapHomologicalComplex (ComplexShape.down ℕ)).map (…)))`;
  `HomologicalComplex.homologyMap (…) n`.
- `GSTClassicalHodgeAmbientBettiSelfProduct.lean` :88-166 —
  `((singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient).obj space`;
  `(productSingularChains A).linearYonedaObj ℚ rationalCoefficient`;
  `(productSingularCochains A).homology n`;
  identical `unopFunctor`/`rightOp`/`mapHomologicalComplex` dualization block (:127-151);
  `HomologicalComplex.homologyMap f n` (:156-166);
  functor-law proofs via `← F.map_comp`, `F.map_id` (:173-187) and `rw [HomologicalComplex.homologyMap_comp]` (:209).
- `GSTClassicalHodgeStrictGraphBettiTrace.lean` :163-198, `GSTClassicalHodgeStrictCorrespondenceAnalyticSpan.lean` :132-175, `GSTClassicalHodgeStrictCorrespondenceChainTransfer.lean` :91-140 — same family.

## 9. Cache manifest (fetched at the pin, `/tmp/`)

`PinSingularHomologyBasic.lean`, `PinSHomologyZero.lean`, `PinHomologicalComplex.lean`,
`PinAlternatingConst.lean`, `PinShortComplexHomologicalComplex.lean`, `PinShortComplexBasic.lean`,
`PinShortComplexExact.lean`, `PinShortComplexHomology.lean`, `PinShortComplexLeftHomology.lean`,
`PinShortComplexRightHomology.lean`, `PinShortComplexModuleCat.lean`, `PinSCAbelian.lean`,
`PinSCPreservesHomology.lean`, `PinComplexShape.lean`, `PinHomologyFunctor.lean`,
`PinHomologyAdditive.lean`, `PinHomologyLinear.lean`, `PinHomologyOpposite.lean`,
`PinHCAbelian.lean`, `PinLinearYoneda.lean`, `PinCatLinearBasic.lean`, `PinAbelianExt.lean`,
`PinHomCongr.lean`, `PinModuleCatBasic.lean`, `PinModuleCatBiproducts.lean`,
`PinLimitsBiproducts.lean`, `PinModuleCatHomology.lean`, `PinZeroObjects.lean`,
`PinTree.json` (full recursive file tree of the pin).
