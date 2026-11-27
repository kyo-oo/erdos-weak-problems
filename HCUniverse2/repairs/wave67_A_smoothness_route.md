# Wave 67-A — THE F3 RECON: the exact smoothness route for the finite-line world

Date: 2026-11-21. Author: Wave 67 Agent A (smoothness-route recon).
Pin: Mathlib `51e6992efd06126df61a496bebf8f49482a4e129` (v4.33.0-rc2). Every
line number below is against the pinned sources (fetched verbatim into
`/tmp/mlpin` during this recon; the wave-65.2-R pin copies at
`research/pin/mathlib-51e6992/` remain the reference set — this wave adds the
Morphisms/RingTheory/Localization files cited here).

Target: `theorem finiteLine_smoothness (M : ℕ) [NeZero M] :
Smooth (finiteLineStructureMap M)` — F3 of the frozen order, the missing
certificate to instantiate `GSTProjectiveOverC.SmoothProjectiveComplexScheme`
for the finite-line world (F2 supplies the `ProjectiveOverC` witness).

---

## 0. The mathematical ground truth (verified from GSTFiniteLineRing.lean)

`lineRing M = MvPolynomial (Fin (2*M)) ℂ` (GSTFiniteLineRing.lean:79); the
coordinate blocks are the pairs `{X (2b), X (2b+1)}`; `crossMonomials M`
(:85) = the products `X a * X b` with `a/2 ≠ b/2` (different blocks);
`crossIdeal M = Ideal.span (crossMonomials M)` (:98); `lineQuotient M`
(:115) with `lineQuotientMap M` (:126) and the quotient grading
`lineGrading M n = Submodule.map q (homogeneousSubmodule _ _ n)` (:155).

**The chart at `X j` (j in block `b = j/2`) is `ℂ[t]`.** In the homogeneous
localization at `f = q (X j)`:

* every other-block variable dies: `q (X a) * f = 0` (cross pair), so
  `q (X a) / f = q (X a)·f / f² = 0`;
* the partner `j'` (the index with `j' / 2 = j / 2`, `j' ≠ j`) survives only
  through the ratio `ρ := q (X j') / f`, and every fraction `x / fⁿ` with
  `x` homogeneous of degree `n` is a ℂ-linear combination of powers `ρ^k`
  (a same-block monomial `X j^p X j'^{n-p}` over `fⁿ` is `ρ^{n-p}`; a
  multi-block monomial is `0` in the quotient; an other-block monomial
  gives a zero fraction);
* no relation: the retraction `χ` (below) sends `ρ ↦ T` and fixes ℂ.

So `Away (lineGrading M) (q (X j)) ≃ₐ[ℂ] MvPolynomial (Fin 1) ℂ`. Two charts
per block glue to a ℙ¹; charts of different blocks are disjoint
(`basicOpen (f·g) = ⊥` because cross products vanish — `basicOpen_zero`,
ProjectiveSpectrum/Basic.lean:64); total: the disjoint union of `M` copies of
ℙ¹. Sanity anchor: **`M = 1` is literal ℙ¹** (2 variables, one block, so
`crossIdeal 1 = ⊥` and `lineGrading 1` IS `ProjectiveGrading 1`), and the
chart identification is the textbook `D+(X₀) = Spec ℂ[X₁/X₀]`.

---

## 1. What exists at the pin — and what does NOT

### 1.1 Scheme-level smoothness (`Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`)

* `class Smooth (f : X ⟶ Y)` (:62): `smooth_appLE` — all `Γ(Y,U) → Γ(X,V)`
  are `RingHom.Smooth`.
* **`instance : HasRingHomProperty @Smooth RingHom.Smooth` (:73)** — THE
  affine criterion. `Smooth = affineLocally RingHom.Smooth`
  (`HasRingHomProperty.eq_affineLocally`, RingHomProperties.lean:280).
* `instance : MorphismProperty.IsStableUnderComposition @Smooth` (:105),
  `instance smooth_comp` (:109).
* `instance : MorphismProperty.Respects @Smooth @IsOpenImmersion` (:120);
  open immersions are smooth (:183); `Smooth (f ∣_ V)` (:197).
* `Smooth.iff_forall_exists_isStandardSmooth` (:84) — the per-point escape
  hatch (fallback material, not needed).

### 1.2 The locality API (`Morphisms/Basic.lean`, `Morphisms/RingHomProperties.lean`)

Because `HasRingHomProperty @Smooth RingHom.Smooth` is a global instance,
`Smooth` gets, for free: `IsZariskiLocalAtTarget` (RingHomProperties.lean:291,
priority 900), `IsZariskiLocalAtSource` (:382), `P.RespectsIso` (via
`IsLocalAtTarget extends RespectsIso`, CategoryTheory/MorphismProperty/Local.lean:51).

* **`IsZariskiLocalAtSource.iff_of_iSup_eq_top {ι} (U : ι → X.Opens)
  (hU : iSup U = ⊤) : P f ↔ ∀ i, P ((U i).ι ≫ f)`**
  (Morphisms/Basic.lean:272; the `of_` half :265). THE source-cover reducer.
* `MorphismProperty.cancel_left_of_respectsIso (P) [P.RespectsIso] (f) (g)
  [IsIso f] : P (f ≫ g) ↔ P g` (CategoryTheory/MorphismProperty/Basic.lean:517).
* **`HasRingHomProperty.Spec_iff {R S : CommRingCat} {φ : R ⟶ S} :
  P (Spec.map φ) ↔ Q φ.hom`** (RingHomProperties.lean:360).
* `HasRingHomProperty.iff_of_isAffine` (:355), `of_source_openCover` /
  `iff_of_source_openCover` (:322/:350), `HasRingHomProperty.of_iSup_eq_top`
  (affineOpens-typed, :367) — alternate Stage-3 shapes.

### 1.3 Ring-level smoothness (`Mathlib/RingTheory/RingHom/Smooth.lean`, `Mathlib/RingTheory/Smooth/Basic.lean`)

* **`RingHom.Smooth (f : R →+* S) : Prop := Algebra.Smooth R S`** under
  `f.toAlgebra` (RingHom/Smooth.lean:74).
* **`RingHom.smooth_algebraMap : (algebraMap R S).Smooth ↔ Algebra.Smooth R S`**
  (:82) — with `RingHom.algebraMap_toAlgebra : algebraMap R S = f` for
  `f.toAlgebra` (used at Morphisms/Smooth.lean:222).
* `RingHom.smooth_def : f.Smooth ↔ f.FormallySmooth ∧ f.FinitePresentation` (:86);
  `RingHom.Smooth.comp` (:103); `RingHom.Smooth.of_bijective` (:122);
  `RingHom.Smooth.holdsForLocalizationAway` (:116);
  `RingHom.Smooth.propertyIsLocal : PropertyIsLocal Smooth` (:144) — this is
  what powers locality + `respectsIso` (:154).
* `class Algebra.Smooth (R A) : formallySmooth + finitePresentation`
  (Smooth/Basic.lean:540, both fields default `by infer_instance`).
* **`Algebra.Smooth.of_equiv (e : A ≃ₐ[R] B) [Smooth R A] : Smooth R B`**
  (:554) — THE transport.
* `Algebra.Smooth.of_isLocalization_Away (r) [IsLocalization.Away r A] :
  Smooth R A` (:559); `Algebra.Smooth.comp` (:568).
* Polynomial smoothness at the pin (assembled, not a single instance):
  `instance instFormallySmoothMvPolynomial (σ) : FormallySmooth R (MvPolynomial σ R)`
  (Smooth/Basic.lean:112, **no finiteness hypothesis**);
  `instance Algebra.FinitePresentation.mvPolynomial [FinitePresentation R A]
  (ι) [Finite ι] : FinitePresentation R (MvPolynomial ι A)`
  (RingTheory/FinitePresentation.lean:190, with `Algebra.FinitePresentation.self`
  :195). Hence **`Algebra.Smooth ℂ (MvPolynomial (Fin 1) ℂ) := ⟨⟩` closes by
  pure instance synthesis.** (`FormallySmooth R R[X]` :395, `FormallySmooth R R`
  :398 exist too; there is NO ready-made `Algebra.Smooth R R[X]` instance.)
* Noetherian upgrade: `Algebra.FinitePresentation.of_finiteType
  [IsNoetherianRing R] : FiniteType R A ↔ FinitePresentation R A`
  (FinitePresentation.lean:69) — the fallback FP half.
* Standard-smooth machinery (fallback): `Algebra.IsStandardSmooth`
  (StandardSmooth.lean:62), `IsStandardSmooth.of_algEquiv` (:123),
  `IsStandardSmooth.localization_away` (:156), `[Subsingleton S] →
  IsStandardSmooth` (:185), `instance [IsStandardSmooth R S] : Smooth R S`
  (StandardSmoothCotangent.lean:343), `PreSubmersivePresentation.naive`
  (Extension/Presentation/Submersive.lean:470) + `jacobiMatrix_naive` (:479)
  — the "quotient of a polynomial ring by a coordinate ideal" constructor.

### 1.4 The Proj chart API (ProjectiveSpectrum + HomogeneousLocalization)

* `Proj.toSpecZero : Proj 𝒜 ⟶ Spec (.of <| 𝒜 0)` (Basic.lean:151).
* `Proj.basicOpenIsoSpec 𝒜 f (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
  (basicOpen 𝒜 f).toScheme ≅ Spec (.of <| Away 𝒜 f)` (:161).
* `Proj.awayι` (:186, open immersion :193), with the rfl-equation
  `Proj.basicOpenIsoSpec_inv_ι : (basicOpenIsoSpec …).inv ≫ (basicOpen 𝒜 f).ι =
  awayι 𝒜 f f_deg hm` (:191).
* **`Proj.awayι_toSpecZero : awayι 𝒜 f f_deg hm ≫ toSpecZero 𝒜 =
  Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _))`** (:206, reassoc) —
  THE per-chart square of the structure map.
* `Proj.iSup_basicOpen_eq_top (f : ι → A) (hf : irrelevant ≤ span (range f))`
  (:86) and **`Proj.iSup_basicOpen_eq_top' (f) (hfn : ∀ i, ∃ n, f i ∈ 𝒜 n)
  (hf : Algebra.adjoin (𝒜 0) (Set.range f) = ⊤)`** (:97) — the variable
  cover of `Proj`.
* `Proj.affineOpenCoverOfIrrelevantLESpan` (:321) — builds an
  `AffineOpenCover` from a spanning family (alternate Stage-3).
* `Proj.isAffineOpen_basicOpen` (:201).
* **THE PROVEN MODEL: `instance [Algebra.FiniteType (𝒜 0) A] :
  LocallyOfFiniteType (Proj.toSpecZero 𝒜)`** (Proper.lean:138-147) — the
  exact chartwise cascade we replicate, step for step, for `Smooth`.
* HomogeneousLocalization (RingTheory/GradedAlgebra/HomogeneousLocalization.lean):
  `Away 𝒜 f := HomogeneousLocalization 𝒜 (Submonoid.powers f)` (:601);
  `Away.mk 𝒜 hf n x hx` = `x/fⁿ` (:609); `Away.val_mk` (:613, rfl);
  `Away.mk_surjective` (:618); `fromZeroRingHom : 𝒜 0 →+* HomogeneousLocalization
  𝒜 x` (:502) with `Algebra (𝒜 0) (HomogeneousLocalization 𝒜 x)` (:509) and
  `algebraMap_eq` (:512, rfl); `val : HomogeneousLocalization 𝒜 x →+* Localization x`
  (via `homogeneousLocalizationAlgebra` :477-490, `algebraMap_apply` :489 rfl);
  `val_injective`/`ext_iff_val` (:557); `Away.finiteType` (:1097,
  `[Algebra.FiniteType (𝒜 0) A]`).
* Localization kit: `Localization.awayLift (f : R →+* P) (r) (hr : IsUnit (f r)) :
  Localization.Away r →+* P` (Localization/Away/Basic.lean:485) with the
  computation rule `awayLift_mk` (:489); `Localization.mk_eq_mk_iff` /
  `r_iff_exists` / `add_mk` / `mk_mul` / `mk_pow` (Localization/Defs.lean —
  the pinned idiom Proper.lean:229-237 uses for mk-equalities).
* MvPolynomial kit: `MvPolynomial.as_sum (p) : p = ∑ v ∈ p.support,
  monomial v (coeff v p)` (Algebra/MvPolynomial/Basic.lean:978);
  `MvPolynomial.mem_homogeneousSubmodule : p ∈ homogeneousSubmodule σ R n ↔
  p.IsHomogeneous n` (MvPolynomial/Homogeneous.lean:101, rfl);
  `MvPolynomial.induction_on` (C/add/mul_X — the span_cover eliminator).

### 1.5 What does NOT exist at the pin (verified by exhaustive grep)

* **NO smoothness lemma or instance for `Proj.toSpecZero`** — the whole
  ProjectiveSpectrum directory contains the word "Smooth" zero times. The
  only properties of `toSpecZero` are: `IsSeparated` (Proper.lean:82),
  `Scheme.IsSeparated` (:130), `LocallyOfFiniteType` (:138), `QuasiCompact`
  (:154), `UniversallyClosed` (:366), `IsProper` (:372). This is expected:
  `toSpecZero` is smooth **iff the charts are**, which is false for general
  gradings (singular Proj) — no such general lemma can exist.
* No identification of `Away (homogeneousSubmodule …) (X j)` with a
  polynomial ring (not even for projective space).
* No `Away.map`-surjectivity lemma (the F2 sub-battle, wave-65.2-R recon).
* No relative-Proj smoothness, no `Algebra.Smooth R R[X]` instance.

### 1.6 Verdict on the composition route (mission question 3a)

`finiteLineStructureMap M = Proj.toSpecZero (lineGrading M) ≫
Spec.map (ofHom (algebraMap ℂ (lineGrading M 0)))` (carrier :77-80).
`smooth_comp` (Morphisms/Smooth.lean:109) would need BOTH factors smooth:

* `Smooth (Spec.map (algebraMap ℂ (𝒜 0)))` — true (`𝒜 0 ≅ ℂ`) but needs the
  degree-0 identification (`homogeneousSubmodule 0` = constants) anyway;
* `Smooth (Proj.toSpecZero (lineGrading M))` — **no pin lemma, and its
  proof is exactly the same chartwise battle** (chart of `toSpecZero` is
  `Spec.map (fromZeroRingHom)` by awayι_toSpecZero, and we still must show
  the chart ring is smooth over `𝒜 0 ≅ ℂ`).

The composition route buys nothing. **GO CHARTWISE DIRECTLY on the full
structure map.**

---

## 2. THE CHOSEN ARCHITECTURE (four stages)

```
Stage 0  cover twins + index involution + block projection   (shared with F2)
Stage 1  the chart equivalence  MvPolynomial (Fin 1) ℂ ≃ₐ[ℂ] Away (lineGrading M) (q (X j))
         and  chart_ringHom_smooth : RingHom.Smooth (chartRingHom M j)
Stage 2  the chart square  awayι ≫ finiteLineStructureMap M = Spec.map (ofHom (chartRingHom M j))
Stage 3  the Proper.lean-style locality cascade  →  Smooth (finiteLineStructureMap M)
```

Everything except Stage 1 is pin-API plumbing with compiling precedents;
Stage 1 is the one real battle (surjectivity = the irreducible monomial
content; injectivity is cheap via the retraction χ).

### Stage 0 — the shared substrate lemmas (twins of CI-green corpus lemmas)

```lean
-- (T1) the partner involution on Fin (2*M): j' = j XOR 1 (same block, ≠ j)
def linePartner (M : ℕ) [NeZero M] (j : Fin (2 * M)) : Fin (2 * M) :=
  ⟨j.val ^^^ 1, by omega⟩
-- lemmas: linePartner_ne, linePartner_block (j'/2 = j/2), linePartner_involution

-- (T2) the variables are homogeneous of degree 1 in the quotient grading
theorem lineCover_homogeneous (M : ℕ) (j : Fin (2 * M)) :
    ∃ n : ℕ, lineQuotientMap M (MvPolynomial.X j) ∈ lineGrading M n :=
  ⟨1, lineQuotientMap_mem_lineGrading M 1 _
    ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X ℂ j))⟩
  -- GSTFiniteLineRing.lean:167 + the finite-point twin variables_homogeneous
  -- (GSTFinitePointWorldCarrier.lean:219-223)

-- (T2') the degree-1 form (for basicOpenIsoSpec / awayι, which want f ∈ 𝒜 m, 0 < m)
theorem lineCover_homogeneous_one (M : ℕ) (j : Fin (2 * M)) :
    lineQuotientMap M (MvPolynomial.X j) ∈ lineGrading M 1 :=
  lineQuotientMap_mem_lineGrading M 1 _
    ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X ℂ j))

-- (T3) the variables adjoin-generate the quotient over its degree-0 piece
theorem lineCover_adjoin (M : ℕ) :
    Algebra.adjoin (lineGrading M 0)
      (Set.range (fun j : Fin (2 * M) => lineQuotientMap M (MvPolynomial.X j))) = ⊤
  -- the twin of span_cover (GSTFinitePointWorldCarrier.lean:202-215):
  -- surjectivity (lineQuotientMap_surjective, GSTFiniteLineRing.lean:137)
  -- + MvPolynomial.induction_on (C / add / mul_X),
  -- C-case via S.algebraMap_mem ⟨q (C a), lineQuotientMap_mem_lineGrading M 0 _ (isHomogeneous_C a)⟩

-- (T4) the block projection (the ℂ-algebra retraction onto block j)
noncomputable def blockEval (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    lineRing M →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  MvPolynomial.aeval fun a =>
    if a = j then 1 else if a = linePartner M j then MvPolynomial.X () else 0
-- (T5) it kills the cross ideal  ⟹ descends to the quotient
theorem blockEval_mem_ker (M) [NeZero M] (j) :
    crossIdeal M ≤ RingHom.ker (blockEval M j).toRingHom
  -- Ideal.span_le + crossMonomials ⊆ ker: one of the two factors maps to 0
noncomputable def blockEvalQuot (M) [NeZero M] (j) : lineQuotient M →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  Ideal.Quotient.liftₐ ℂ (crossIdeal M) (blockEval M j) (blockEval_mem_ker M j)
-- (T6) constants through degree zero (the corpus's finitePoint_over_base STAGE-3 idiom,
--      GSTFinitePointWorldCarrier.lean:676-688):
theorem hzero (M : ℕ) (c : ℂ) :
    (algebraMap ℂ (lineGrading M 0) c : lineQuotient M) = algebraMap ℂ (lineQuotient M) c
```

### Stage 1 — the chart equivalence (THE battle)

Notation: `q := lineQuotientMap M`, `f := q (MvPolynomial.X j)`,
`hf₁ : f ∈ lineGrading M 1` (T2), `f' := q (X (linePartner M j))`,
`𝒜 := lineGrading M`.

```lean
-- the chart ring map: exactly what the structure map does on the chart (see Stage 2)
noncomputable def chartRingHom (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    ℂ →+* Away 𝒜 f :=
  (fromZeroRingHom 𝒜 (Submonoid.powers f)).comp (algebraMap ℂ (𝒜 0))

-- the ratio generator
noncomputable def chartRatio (M) [NeZero M] (j) : Away 𝒜 f :=
  Away.mk 𝒜 hf₁ 1 f' hf₁'          -- q (X j') / f

-- the forward map (a ℂ-algebra hom for chartRingHom.toAlgebra)
letI : Algebra ℂ (Away 𝒜 f) := (chartRingHom M j).toAlgebra
noncomputable def chartMap (M) [NeZero M] (j) :
    MvPolynomial (Fin 1) ℂ →ₐ[ℂ] Away 𝒜 f :=
  MvPolynomial.aeval (chartRatio M j)

-- the retraction χ (kills everything outside block j; f ↦ 1):
noncomputable def chartRetracts (M) [NeZero M] (j) : Away 𝒜 f →+* MvPolynomial (Fin 1) ℂ :=
  (Localization.awayLift (blockEvalQuot M j).toRingHom f
    (by simp [map_one])).comp          -- IsUnit (blockEvalQuot f) = IsUnit 1
    (algebraMap (Away 𝒜 f) (Localization (Submonoid.powers f)))
```

**Injectivity is cheap — no linear independence needed:**

```lean
theorem chart_retract_apply (M) [NeZero M] (j) (p) :
    chartRetracts M j (chartMap M j p) = p := by
  induction p using MvPolynomial.induction_on with
  | C c => -- χ (φ c) = c : awayLift_mk + hzero + blockEvalQuot is a ℂ-alg hom
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p k hp => -- χ (ψ p * ρ) = χ (ψ p) * χ (ρ) and χ (ρ) = X ()
                    -- awayLift_mk: χ (ρ) = blockEvalQuot f' * 1 = X ()
theorem chart_injective (M) [NeZero M] (j) : Function.Injective (chartMap M j)
  -- ψ p = ψ p' → p = χ (ψ p) = χ (ψ p') = p'
```

**Surjectivity is the irreducible content** (per-monomial, via `Away.mk_surjective`
+ `mem_lineGrading` (GSTFiniteLineRing.lean:160) + `MvPolynomial.as_sum`):

```lean
-- the per-monomial lemma: a monomial's chart value is always a polynomial in ρ
theorem chart_monomial (M) [NeZero M] (j) (d : Fin (2 * M) →₀ ℕ) (c : ℂ) :
    ∃ p : MvPolynomial (Fin 1) ℂ, chartMap M j p =
      Away.mk 𝒜 hf₁ (d.sum fun _ e => e) (q (MvPolynomial.monomial d c)) (…) := by
  classical
  -- trichotomy on d.support (all inside the section context of Away 𝒜 f):
  -- (A) ∃ a b ∈ d.support, a/2 ≠ b/2:
  --     monomial d c = (X a * X b) * monomial (d - single a 1 - single b 1) c
  --     (MvPolynomial.monomial_add twice)  ⟹ q (monomial d c) = 0
  --     (X a * X b ∈ crossMonomials ⊆ crossIdeal, GSTFiniteLineRing.lean:146)
  --     ⟹ the fraction is 0 = chartMap 0.
  -- (B) support inside one block b ≠ j/2: pick a₀ ∈ support; the numerator
  --     times f is 0 (cross pair); re-index the fraction:
  --     val (mk n x) = Localization.mk x ⟨fⁿ⟩ = Localization.mk (x*f) ⟨f^{n+1}⟩
  --     (Localization.mk_eq_mk_iff, witness 1) = mk 0 = 0 = chartMap 0.
  -- (C) support ⊆ {j, j'}: d j + d j' = n;
  --     val comparison (Localization.mk_eq_mk_iff, witness 1:
  --     c X_j^{dj} X_{j'}^{dj'} · f^{dj'} = c X_{j'}^{dj'} · fⁿ):
  --     the fraction = φ(c) * ρ^{d j'} = chartMap (C c * X () ^ (d j')).
theorem chart_surjective (M) [NeZero M] (j) : Function.Surjective (chartMap M j)
  -- z ← Away.mk_surjective (HomogeneousLocalization.lean:618)
  --   ← mem_lineGrading (GSTFiniteLineRing.lean:160): a = q t, t homogeneous
  --   ← MvPolynomial.as_sum: t = ∑ monomials; Away.mk additivity
  --     (val + Localization.add_mk) distributes; per monomial use chart_monomial;
  --     reassemble as chartMap (∑ p_d) via map_sum.
```

**Then smoothness of the chart ring map:**

```lean
noncomputable def chartAlgEquiv (M) [NeZero M] (j) :
    MvPolynomial (Fin 1) ℂ ≃ₐ[ℂ] Away 𝒜 f :=
  AlgEquiv.ofBijective (chartMap M j) ⟨chart_injective M j, chart_surjective M j⟩

instance mvpoly_smooth : Algebra.Smooth ℂ (MvPolynomial (Fin 1) ℂ) := ⟨⟩
  -- FormallySmooth: instFormallySmoothMvPolynomial (Smooth/Basic.lean:112)
  -- FinitePresentation: Algebra.FinitePresentation.mvPolynomial
  --   (FinitePresentation.lean:190; base = ℂ via .self :195, Finite (Fin 1))

theorem chart_ringHom_smooth (M) [NeZero M] (j) : (chartRingHom M j).Smooth := by
  algebraize [chartRingHom M j]      -- or: letI := (chartRingHom M j).toAlgebra
  rw [RingHom.smooth_algebraMap]     -- RingHom/Smooth.lean:82
                                     -- (algebraMap = chartRingHom, algebraMap_toAlgebra)
  exact Algebra.Smooth.of_equiv (chartAlgEquiv M j).symm   -- Smooth/Basic.lean:554
```

**Does an intermediate `RingHom.Smooth` suffice WITHOUT the identification?**
No — and this is now sharp: `RingHom.Smooth φ` unfolds (smooth_def :86) to
FormallySmooth + FinitePresentation, and
* the FP half CAN be dodged (Noetherianity: `Algebra.FinitePresentation.of_finiteType`
  :69 + FiniteType via `Away.finiteType` HomogeneousLocalization.lean:1097
  with `[Algebra.FiniteType (𝒜 0) (lineQuotient M)]`, itself needing the
  degree-0 identification), but
* the FormallySmooth half has no dodge: without injectivity of `chartMap`,
  the chart could be `ℂ[t]/(t²)`-like, and the cross-monomial non-vanishing
  (the actual mathematical content) must enter somewhere. The
  `SubmersivePresentation.naive` route (1.3) needs a polynomial-ring
  presentation with kernel control = the same content, strictly more API.
  The chosen structure minimizes it: injectivity rides on the retraction χ
  (no monomial-independence lemma), and only SURJECTIVITY carries the
  monomial analysis.

### Stage 2 — the chart square

```lean
theorem chart_awayι_comp (M) [NeZero M] (j) :
    Proj.awayι 𝒜 f (lineCover_homogeneous1 M j) (by norm_num) ≫
      finiteLineStructureMap M =
    Spec.map (CommRingCat.ofHom (chartRingHom M j)) := by
  rw [finiteLineStructureMap, ← Category.assoc, Proj.awayι_toSpecZero,
      ← Spec.map_comp]
  rfl   -- ofHom fusion: CommRingCat.ofHom f ≫ ofHom g = ofHom (g.comp f)
  -- (GSTFiniteLineWorldCarrier.lean:77-80 for the definitional unfolding)
```

### Stage 3 — the locality cascade (the Proper.lean:138-147 pattern, verbatim shape)

```lean
theorem finiteLine_smoothness (M : ℕ) [NeZero M] :
    Smooth (finiteLineStructureMap M) := by
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Smooth) _
    (Proj.iSup_basicOpen_eq_top' 𝒜
      (fun j : Fin (2 * M) => q (MvPolynomial.X j))
      lineCover_homogeneous lineCover_adjoin)]
  intro j
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Smooth)
      (Proj.basicOpenIsoSpec 𝒜 f (lineCover_homogeneous_one M j) (by norm_num)).inv,
    ← Category.assoc, Proj.basicOpenIsoSpec_inv_ile, ← Category.assoc,
    chart_awayι_comp]
  -- goal: Smooth (Spec.map (CommRingCat.ofHom (chartRingHom M j)))
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (chart_ringHom_smooth M j)
  -- φ.hom = chartRingHom M j definitionally (CommRingCat.ofHom_hom); if the
  -- defeq is not found, prepend `rw [show … from rfl]` or use
  -- `CommRingCat.ofHom_hom (chartRingHom M j)` explicitly.
```

Step audit against the compiling model (Proper.lean:144-147 — that proof is
for `toSpecZero` alone; ours adds one `← Category.assoc` and the
`← Spec.map_comp` fusion for the `Spec.map (algebraMap ℂ (𝒜 0))` factor,
both handled in Stage 2 so Stage 3 stays a pure rewrite chain):
`iff_of_iSup_eq_top` (Basic.lean:272) → per-chart `Smooth (ι ≫ f)`;
`cancel_left_of_respectsIso` (MorphismProperty/Basic.lean:517 — the
`RespectsIso @Smooth` instance comes from `HasRingHomProperty` →
`IsZariskiLocalAtTarget` → `extends RespectsIso`, Local.lean:51);
`basicOpenIsoSpec_inv_ι` (:191, rfl); `awayι_toSpecZero` (:206);
`Spec_iff` (RingHomProperties.lean:360). NOTE: Proper.lean writes the
awayι-step as `← Proj.awayι` (def-as-rule); if that spelling misbehaves in
our file, use the explicit rfl-lemma `Proj.basicOpenIsoSpec_inv_ι` forward.

### Stage 4 — the bundling (after F2)

```lean
def finiteLineSmoothProjective (M : ℕ) [NeZero M] :
    GSTProjectiveOverC.SmoothProjectiveComplexScheme where
  X := finiteLineScheme M
  structureMap := finiteLineStructureMap M
  smooth := finiteLine_smoothness M
  projective := ⟨2 * M - 1, finiteLineEmbedding M, finiteLine_closedImmersion M,
    finiteLine_over_base M⟩   -- F2's outputs
```

---

## 3. Risks (ranked) and fallbacks

### RISK 1 (top) — the Stage-1 surjectivity computation (chart_monomial + chart_surjective)
The trichotomy on `d.support` (two blocks / other block / same block) and the
`Localization.mk_eq_mk_iff` re-indexings are elementary but coercion-heavy
(NumDenSameDeg ↔ Away.mk ↔ val ↔ Localization.mk), each equality needing the
witness-1 trick. Estimate 150-250 lines. Mitigations: (i) the pinned idiom
Proper.lean:229-237 (mk-equalities via val + mk_eq_mk_iff + r_iff_exists)
is exactly this manipulation class, inside a proof that compiles at the pin;
(ii) the F2 sub-battle (`awayMap_surjective`) trains the same muscle in the
same file family — do F2 first; (iii) the `n • 1 = n` scalar and the
`homogeneousSubmodule`-membership of monomials are the two spots to
pre-prove as tiny lemmas (`mem_homogeneousSubmodule` is rfl-to-IsHomogeneous,
Homogeneous.lean:101; monomial support is a singleton).
Fallback within Stage 1: replace the explicit witness-polynomial by the
adjoin formulation (`Algebra.adjoin ℂ {chartRatio} = ⊤`, consuming
`chart_monomial` unchanged) — same content, sometimes friendlier `Finset`
bookkeeping.

### RISK 2 — block combinatorics on `Fin (2*M)`
The partner involution and the "support within one block" predicates
(`a/2 = b/2` with `Nat.div`) need careful `omega`-backing. Mitigation:
define `linePartner` once with exactly the three lemmas used (ne, block,
involution), mirroring the carrier's `blockRotFn` lemma family
(GSTFiniteLineWorldCarrier.lean:86-93); keep ALL block logic behind those
three names.

### RISK 3 — instance/defeq plumbing (medium, CI-friction not math)
The `letI : Algebra ℂ (Away 𝒜 f) := (chartRingHom M j).toAlgebra` +
`algebraize` + `RingHom.algebraMap_toAlgebra` bridge; the GradeZero subtype
coercions (`hzero`); `Away` being an abbrev (reducible — good). Direct
precedents: Morphisms/Smooth.lean:222-294 (the algebraize pattern),
GSTFinitePointWorldCarrier.lean:676-688 (the constants-through-degree-zero
battle, STAGE 3 of finitePoint_over_base — fought and green). Designated CI
repair: provision each `letI` as `haveI` with explicit `RingHom.toAlgebra`
and rewrite `algebraMap` via `RingHom.algebraMap_toAlgebra` before
`RingHom.smooth_algebraMap`.

### RISK 4 (low) — the Stage-3 rewrite chain
Copied from Proper.lean:138-147, which compiles at the pin with the SAME
lemma names and the same `(P := @…)` spelling; the only new step
(`chart_awayι_comp`) is a two-rewrite proof. Fallback spelling for the
awayι step: `Proj.basicOpenIsoSpec_inv_ι` forward instead of `← Proj.awayι`.

### RANKED FALLBACK ROUTES (if Route 1 stalls)

1. **(Chosen) Route 1** — chartwise + full chart equivalence, as above.
2. **Route 2 (Stage-3 variant, same Stages 0-2)** — replace the
   `iff_of_iSup_eq_top` cascade with the pin's own affine open cover:
   `Proj.affineOpenCoverOfIrrelevantLESpan 𝒜 (fun j => q (X j)) …`
   (ProjectiveSpectrum/Basic.lean:321) +
   `HasRingHomProperty.iff_of_source_openCover` (RingHomProperties.lean:350);
   per-chart goal `RingHom.Smooth ((awayι ≫ f).appTop.hom)` — one extra
   ΓSpecIso-iso-cancel vs Route 1 (`iff_of_isAffine` :355 shape). Use if the
   morphism-restriction rewrites of Route 1 fight back.
3. **Route 3 (ring-level split)** — `RingHom.smooth_def` (:86): prove
   `FinitePresentation` via Noetherianity (`of_finiteType` :69 +
   `Away.finiteType` :1097 + degree-0 identification) and
   `FormallySmooth` via `IsStandardSmooth.of_algEquiv`-style presentation
   (`SubmersivePresentation.naive` :470 with the killed variables as the
   jacobian-witness pair) — strictly more work than Route 1's χ-injectivity;
   only worth it if `AlgEquiv.ofBijective` transport misfires.
4. **Route 4 (last resort — NOT recommended)** — decompose the world as a
   coproduct of M copies of ℙ¹ and transport smoothness of `projectiveSpace 1`
   (which would itself need the same chart battle at arity 2, plus a
   scheme-level coproduct iso). More work in every dimension; kept only as
   the "known dead" marker alongside the closed-immersion-composition idea
   (a closed subscheme of a smooth scheme is not smooth — the charts must be
   verified regardless).

---

## 4. The exact Lean skeleton (draft, consolidated)

```lean
import GSTFiniteLineWorldCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Smooth.Basic    -- Algebra.Smooth.of_equiv

-- (file: GSTFiniteLineSmoothness.lean — the F3 module, on the F1/F2 substrate)

namespace GSTFiniteLineSmoothness

open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial
open GSTFiniteLineRing GSTFiniteLineWorldCarrier

attribute [local instance] MvPolynomial.gradedAlgebra

-- §0 Stage 0: linePartner + T2/T3/T4/T5/T6 (see §2) — ~120 lines

-- §1 Stage 1: chartRingHom, chartRatio, chartMap, chartRetracts,
--    chart_retract_apply, chart_injective, chart_monomial, chart_surjective,
--    chartAlgEquiv, mvpoly_smooth, chart_ringHom_smooth — ~250 lines

-- §2 Stage 2: chart_awayι_comp — ~15 lines

-- §3 Stage 3:
theorem finiteLine_smoothness (M : ℕ) [NeZero M] :
    Smooth (finiteLineStructureMap M) := by
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Smooth) _
    (Proj.iSup_basicOpen_eq_top' (lineGrading M)
      (fun j : Fin (2 * M) => lineQuotientMap M (MvPolynomial.X j))
      lineCover_homogeneous lineCover_adjoin)]
  intro j
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Smooth)
      (Proj.basicOpenIsoSpec (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
        (lineCover_homogeneous_one M j) (by norm_num)).inv,
    ← Category.assoc, Proj.basicOpenIsoSpec_inv_ile, ← Category.assoc,
    chart_awayι_comp]
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (chart_ringHom_smooth M j)

#print axioms finiteLine_smoothness   -- CI: [propext, Quot.sound] only

end GSTFiniteLineSmoothness
```

## 5. Staged CI plan (the frozen order within F3)

* **F3.1** — Stage 0 (index/cover/projection lemmas; no smoothness). Pure
  substrate; CI-green expected first try (all twins of green corpus lemmas).
* **F3.2** — Stage 1 (the chart equivalence + `chart_ringHom_smooth`).
  The battle wave; land `chart_monomial` as its own CI declaration first.
* **F3.3** — Stages 2-3 (`finiteLine_smoothness`) + the Stage-4 bundling
  once F2's `finiteLine_closedImmersion`/`finiteLine_over_base` are in.

## 6. Honest ledger

Every API claim above was read verbatim from the pinned sources during this
recon (fetched tree at /tmp/mlpin, SHA 51e6992…). Nothing here is
kernel-checked yet — per the campaign law, the CI lane owns that; the
skeleton is a draft for the F3 waves, with the load-bearing steps matched
declaration-by-declaration to pin files that compile. The mathematical
ground truth (§0) is derived by hand from GSTFiniteLineRing.lean's
definitions, with the M = 1 = ℙ¹ anchor as the degenerate sanity check.
