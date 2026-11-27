/-!
# Wave 66-C — `chart_closed`: the per-chart closed immersion of the finite-line embedding

THE KILL of Wave 66 Agent C (HC-PROOF GST campaign, task 66-C): `chart_closed`
— the per-chart closed-immersion theorem of the finite-line embedding, the
exact transposition of the green finite-point carrier's five-stage
iso-cancellation cascade (GSTFinitePointWorldCarrier.lean:568-643, CI-green)
onto `finiteLineEmbedding M = Proj.map (lineGradedQuotientHom M)
(line_irrelevant_le M)` (GSTFiniteLineWorldCarrier.lean:654-656), riding the
PINNED `Proj.map` chart API (research/pin/mathlib-51e6992/, Mathlib @
51e6992efd06126df61a496bebf8f49482a4e129).

SPLICE SITE: at the end of §5 of `GSTFiniteLineWorldCarrier.lean`, immediately
after the `finiteLineEmbedding` definition and before the `## Receipts`
section, inside `namespace GSTFiniteLineWorldCarrier`, under the carrier's
ambient context (`noncomputable section`, `open AlgebraicGeometry
CategoryTheory`, `open GSTProjectiveOverC GSTFiniteLineRing`, `open
MvPolynomial DirectSum`, `attribute [local instance] MvPolynomial.gradedAlgebra`,
`set_option maxHeartbeats 100000000`, `set_option maxRecDepth 1000000` — all
inherited from the carrier head).  This file is a SPLICE BODY in the wave-65
repair convention (cf. repairs/wave65_1_D.lean): NO imports, NO namespace, NO
`noncomputable section` — the assembler concatenates it into the carrier
module.

## Notation for the cascade (fixed once)

`𝒜 := ProjectiveGrading (2 * M - 1)` (the ambient grading, the target),
`ℬ := lineGrading M` (the line grading, the source),
`f := lineGradedQuotientHom M : 𝒜 →+*ᵍ ℬ`,
`hf := line_irrelevant_le M : ℬ₊ ≤ 𝒜₊.map f`,
`s := MvPolynomial.X j` (the chart section),
`U𝒜 := Proj.basicOpen 𝒜 s` (the target chart `D+(s)`),
`Uℬ := Proj.basicOpen ℬ (f s)` (the source chart `D+(f s)`),
`iso𝒜 := Proj.basicOpenIsoSpec 𝒜 s hXj zero_lt_one`,
`isoℬ := Proj.basicOpenIsoSpec ℬ (f s) ((f).2 hXj) zero_lt_one`.

## THE CASCADE (five stages, the green shape transposed)

* STAGE 0 (the retype; green :574-579): the goal's restricted embedding is
  restated at `Proj ℬ ⟶ Proj 𝒜` — `finiteLineScheme M` is a reducible abbrev
  (carrier :65-66) and `finiteLineEmbedding M` delta-unfolds to `Proj.map f hf`
  (carrier :654-656), so the equation is `rfl`.  (The `projectiveSpace (2 * M - 1)`
  wrapper is defeq but not reducible — the green carrier's own Stage 0-1 law.)
* STAGE 1 (the restriction key; task: "morphismRestrict onto the preimage
  chart"): `AlgebraicGeometry.morphismRestrict_ι` (pinned Restrict.lean:581,
  @[reassoc (attr := simp)]) gives
  `Proj.map f hf ∣_ U𝒜 ≫ U𝒜.ι = (Proj.map f hf ⁻¹ᵁ U𝒜).ι ≫ Proj.map f hf`,
  and `Proj.map_preimage_basicOpen` (pinned Functor.lean:160, @[simp], proof
  `rfl`) rewrites the preimage open: `map f hf ⁻¹ᵁ basicOpen 𝒜 s = basicOpen ℬ (f s)`.
  THE KEY: the preimage of the target's `D+(s)` chart under the embedding IS
  the domain's `D+(f s)` chart, definitionally (that is why no `Scheme.isoOfEq`
  transport is needed anywhere below — the green cascade's two extra
  `cancel_left` peels for exactly those transports collapse into STAGE 4 here).
* STAGE 2 (the per-chart square): `Proj.awayι_comp_map` (pinned
  Functor.lean:192, @[reassoc]) —
  `awayι ℬ (f s) (f.2 hXj) 1 ≫ Proj.map f hf =
     Spec.map (CommRingCat.ofHom (Away.map f s)) ≫ awayι 𝒜 s hXj 1`
  — with both `awayι` unfolded by `Proj.basicOpenIsoSpec_inv_ι` (pinned
  Basic.lean:190, proof `rfl`; the pin's own definition of `awayι` at
  Basic.lean:186-187 IS `(basicOpenIsoSpec _ _ _ _).inv ≫ (basicOpen _ _).ι`).
  Splicing STAGE 1 into the square and cancelling the chart inclusion
  `U𝒜.ι` (a mono: `Opens.ι` is an open immersion, pinned Restrict.lean:57;
  `CategoryTheory.cancel_mono`, pinned Category/Basic.lean:337 — the pin's own
  idiom at Functor.lean:198) yields the chart square
  `isoℬ.inv ≫ (Proj.map f hf ∣_ U𝒜) =
     Spec.map (CommRingCat.ofHom (Away.map f s)) ≫ iso𝒜.inv`,
  and `CategoryTheory.Iso.inv_comp_eq` (pinned Iso.lean:186) inverts the left
  iso into the factorization
  `Proj.map f hf ∣_ U𝒜 =
     isoℬ.hom ≫ (Spec.map (CommRingCat.ofHom (Away.map f s)) ≫ iso𝒜.inv)`.
* STAGE 3 (the right peel — green :606-607 verbatim shape):
  `MorphismProperty.cancel_right_of_respectsIso` (pinned
  MorphismProperty/Basic.lean:521) with `P := @IsClosedImmersion`
  (`MorphismProperty.RespectsIso` instance: pinned
  Morphisms/ClosedImmersion.lean:91) cancels the TARGET chart isomorphism
  `iso𝒜.inv`.
* STAGE 4 (the left peel — green :609-641 collapsed):
  `MorphismProperty.cancel_left_of_respectsIso` (pinned
  MorphismProperty/Basic.lean:517) cancels the SOURCE chart isomorphism
  `isoℬ.hom`, reducing to
  `IsClosedImmersion (Spec.map (CommRingCat.ofHom (Away.map f s)))`.
* STAGE 5 (the affine closer — green :642-643 verbatim shape):
  `IsClosedImmersion.spec_of_surjective` (pinned
  Morphisms/ClosedImmersion.lean:101) on the chart ring map, given the
  **W66-B PLUG** below.

SYNTACTIC-MATCH DISCIPLINE (CI-critical): the rewrites inside the STAGE 2
square ride EXACT term matches.  The degree-1 membership certificate is
written `((lineGradedQuotientHom M).2 hXj)` — the positional `map_mem`
projection, the pin's own spelling (Functor.lean:204 `f.2 s.2.2`) — at EVERY
occurrence, because `Proj.awayι_comp_map`'s conclusion mentions `f.2 hs` and
the `basicOpenIsoSpec` arguments must match it literally for `rw` to fire.
Do NOT refactor those into a `have` (an opaque local would break the match).

DESIGNATED CI REPAIR POINTS (if the kernel complains, in order of likelihood):
1. `rw [← hmr] at h` failing to find `Uℬ.ι ≫ Proj.map f hf`:
   replace by `simp only [← hmr] at h` (simp matches up to reducible defeq).
2. STAGE 1 rewrite failing on `hmr`: replace the two steps by the pin's own
   square-lemma route
   `rw [Proj.ι_comp_map (lineGradedQuotientHom M) (line_irrelevant_le M)
     (MvPolynomial.X j), AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict] at h`
   (Functor.lean:164 + Restrict.lean:780).
3. STAGE 0 `rw … from rfl` motive issue: mirror green exactly (it is green's
   own shape at GSTFinitePointWorldCarrier.lean:577-579; if the elaborator
   refuses, add explicit `@AlgebraicGeometry.morphismRestrict`-type ascriptions
   on both sides).

## THE EXTERNAL DEPENDENCY — Agent B's kill (the W66-B PLUG)

`awayMap_surjective` (repairs/wave66_B_away.lean, spliced ABOVE this module by
the assembler) — THE expected statement, exactly as consumed at the plug below:

```
theorem awayMap_surjective (M : ℕ) [NeZero M] (j : Fin (2 * M - 1 + 1)) :
    Function.Surjective
      (HomogeneousLocalization.Away.map (lineGradedQuotientHom M) (MvPolynomial.X j))
```

NOTE the index type: `Fin (2 * M - 1 + 1)` — the AMBIENT coordinate index type
(`ProjectiveCoordinateRing (2 * M - 1) = MvPolynomial (Fin (2 * M - 1 + 1)) ℂ`,
GSTProjectiveOverC.lean:40-41) — NOT the line-world `Fin (2 * M)`.  The two
are equipotent via `lineFinEquiv` (carrier :563) but NOT definitionally equal
for variable `M`; the frozen F2 design's `(j : Fin (2 * M))` sketch
(records/2026-11-21-wave65-2R-f2-recon.md:63) is off by exactly this bridge.
Agent B's route (the frozen design's, all CI-green substrate):
`HomogeneousLocalization.Away.mk_surjective` (pinned
HomogeneousLocalization.lean:618) → the existential of `mem_lineGrading`
(GSTFiniteLineRing.lean:160) → `HomogeneousLocalization.Away.map_mk` (pinned
HomogeneousLocalization.lean:730, @[simp]).

## THE DOWNSTREAM ASSEMBLY — Agent A's kill (for reference; NOT this file)

```
theorem finiteLine_closedImmersion (M : ℕ) [NeZero M] :
    IsClosedImmersion (finiteLineEmbedding M) :=
  IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
    (fun j => Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j))
    (Proj.iSup_basicOpen_eq_top' (ProjectiveGrading (2 * M - 1)) MvPolynomial.X
      lineCover_homogeneous lineCover_span)
    (fun j => chart_closed M j)
```

with the arity-(2M) twins of the green `span_cover` / `variables_homogeneous`
(GSTFinitePointWorldCarrier.lean:202-223, same `MvPolynomial.induction_on`
skeleton at `Fin (2 * M - 1 + 1)`):
`lineCover_homogeneous : ∀ j : Fin (2 * M - 1 + 1), ∃ n, MvPolynomial.X j ∈
ProjectiveGrading (2 * M - 1) n` (witness `⟨1, hXj⟩` — the same certificate as
below) and `lineCover_span : Algebra.adjoin (↑(ProjectiveGrading (2 * M - 1) 0))
(Set.range (MvPolynomial.X : Fin (2 * M - 1 + 1) → ProjectiveCoordinateRing
(2 * M - 1))) = ⊤`.
(`IsZariskiLocalAtTarget.of_iSup_eq_top`: pinned Morphisms/Basic.lean:146;
`Proj.iSup_basicOpen_eq_top'`: pinned Basic.lean:97, adjoin side condition at
:99.)

## HONESTY LEDGER

This module contains NO auxiliary lemmas: the pin's own `Proj.map` chart API
makes the cascade self-contained (the only ring-level input, the chart-ring
surjectivity, is Agent B's `awayMap_surjective`).  Every Mathlib name used
below is verified against the pinned sources or the CI-green finite-point
carrier (table in the wave-66 worklog entry); the single non-Mathlib
non-corpus name is `awayMap_surjective` (Agent B, same wave).  No `sorry`, no
`admit`, no `native_decide`, no new axioms.  The GitHub CI lane owns the
kernel check (the repo law: no local Lean).
-/

/-- **THE PER-CHART CLOSED IMMERSION** — restricted to each basic open chart
`D+(X j)` of the ambient projective space, the finite-line embedding is a
closed immersion, because on that chart it is `Spec` of the chart ring map
`Away.map (lineGradedQuotientHom M) (MvPolynomial.X j)`, which is surjective
(Agent B's kill).  The transposition of the green
`GSTFinitePointWorldCarrier.chart_closed` (:568). -/
theorem chart_closed (M : ℕ) [NeZero M] (j : Fin (2 * M - 1 + 1)) :
    IsClosedImmersion
      (finiteLineEmbedding M ∣_
        Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j)) := by
  -- W66-B PLUG: the Away-surjectivity of the chart ring map — Agent B's kill
  -- (wave66_B_away.lean, spliced above this module).  INTERFACE CONTRACT:
  -- `awayMap_surjective (M : ℕ) [NeZero M] (j : Fin (2 * M - 1 + 1)) :
  --     Function.Surjective
  --       (HomogeneousLocalization.Away.map (lineGradedQuotientHom M)
  --         (MvPolynomial.X j))`
  -- (see the header: the index type is the AMBIENT `Fin (2 * M - 1 + 1)`).
  have hsurj : Function.Surjective
      (HomogeneousLocalization.Away.map (lineGradedQuotientHom M) (MvPolynomial.X j)) :=
    awayMap_surjective M j
  -- The chart section's degree-1 certificate (the green :571-573 two-liner):
  -- `X j` is homogeneous of degree `1` in the ambient grading.
  have hXj : MvPolynomial.X j ∈ ProjectiveGrading (2 * M - 1) 1 := by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_X ℂ j
  -- STAGE 0 (the retype; green :577-579): restate the restricted embedding at
  -- `Proj (lineGrading M) ⟶ Proj (ProjectiveGrading (2 * M - 1))` — the
  -- `finiteLineScheme M` / `projectiveSpace (2 * M - 1)` wrappers are defeq
  -- but not reducible, and `finiteLineEmbedding M` delta-unfolds to its
  -- `Proj.map` body (carrier :654-656).
  rw [show (finiteLineEmbedding M ∣_
      Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j)) =
    (Proj.map (lineGradedQuotientHom M) (line_irrelevant_le M) ∣_
      (Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j))) from rfl]
  -- STAGE 1 (the restriction key): the restriction law
  -- (`morphismRestrict_ι`, Restrict.lean:581) with the preimage chart
  -- rewritten by `map_preimage_basicOpen` (Functor.lean:160, `rfl`): the
  -- preimage of the target's `D+(X j)` chart IS the domain's
  -- `D+(f (X j))` chart.  `hmr` is consumed inside STAGE 2.
  have hmr := AlgebraicGeometry.morphismRestrict_ι
    (Proj.map (lineGradedQuotientHom M) (line_irrelevant_le M))
    (Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j))
  rw [Proj.map_preimage_basicOpen] at hmr
  -- STAGE 2 (the per-chart square): the `awayι_comp_map` square
  -- (Functor.lean:192), both `awayι` unfolded through their definition
  -- (`basicOpenIsoSpec_inv_ι`, Basic.lean:190, `rfl`), spliced with STAGE 1,
  -- and the chart inclusion `U𝒜.ι` cancelled (`cancel_mono`,
  -- Category/Basic.lean:337) — giving the chart square
  -- `isoℬ.inv ≫ (embedding ∣_ U𝒜) = Spec.map (Away.map) ≫ iso𝒜.inv`.
  have hsq : (Proj.basicOpenIsoSpec (lineGrading M)
        ((lineGradedQuotientHom M) (MvPolynomial.X j))
        ((lineGradedQuotientHom M).2 hXj) zero_lt_one).inv ≫
      (Proj.map (lineGradedQuotientHom M) (line_irrelevant_le M) ∣_
        (Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j))) =
      Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.Away.map (lineGradedQuotientHom M)
          (MvPolynomial.X j))) ≫
        (Proj.basicOpenIsoSpec (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j)
          hXj zero_lt_one).inv := by
    have h := Proj.awayι_comp_map (lineGradedQuotientHom M) (line_irrelevant_le M)
      zero_lt_one (MvPolynomial.X j) hXj
    rw [← Proj.basicOpenIsoSpec_inv_ι (lineGrading M)
        ((lineGradedQuotientHom M) (MvPolynomial.X j))
        ((lineGradedQuotientHom M).2 hXj) zero_lt_one,
      ← Proj.basicOpenIsoSpec_inv_ι (ProjectiveGrading (2 * M - 1))
        (MvPolynomial.X j) hXj zero_lt_one] at h
    -- `h : (isoℬ.inv ≫ Uℬ.ι) ≫ map = Spec.map ≫ (iso𝒜.inv ≫ U𝒜.ι)`
    simp only [CategoryTheory.Category.assoc] at h
    -- `h : isoℬ.inv ≫ (Uℬ.ι ≫ map) = Spec.map ≫ (iso𝒜.inv ≫ U𝒜.ι)`
    rw [← hmr] at h
    -- `h : isoℬ.inv ≫ ((map ∣_ U𝒜) ≫ U𝒜.ι) = Spec.map ≫ (iso𝒜.inv ≫ U𝒜.ι)`
    simp only [← CategoryTheory.Category.assoc] at h
    -- `h : (isoℬ.inv ≫ (map ∣_ U𝒜)) ≫ U𝒜.ι = (Spec.map ≫ iso𝒜.inv) ≫ U𝒜.ι`
    exact (CategoryTheory.cancel_mono
      (Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j)).ι).mp h
  -- STAGE 2b (the factorization): invert the left chart isomorphism
  -- (`Iso.inv_comp_eq`, Iso.lean:186) — the restricted embedding IS
  -- `isoℬ.hom ≫ Spec.map (Away.map) ≫ iso𝒜.inv` on the chart.
  have hfac : (Proj.map (lineGradedQuotientHom M) (line_irrelevant_le M) ∣_
      (Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j))) =
      (Proj.basicOpenIsoSpec (lineGrading M) ((lineGradedQuotientHom M)
          (MvPolynomial.X j))
        ((lineGradedQuotientHom M).2 hXj) zero_lt_one).hom ≫
      (Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.Away.map (lineGradedQuotientHom M)
            (MvPolynomial.X j))) ≫
        (Proj.basicOpenIsoSpec (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j)
          hXj zero_lt_one).inv) :=
    (CategoryTheory.Iso.inv_comp_eq
      (Proj.basicOpenIsoSpec (lineGrading M) ((lineGradedQuotientHom M)
          (MvPolynomial.X j))
        ((lineGradedQuotientHom M).2 hXj) zero_lt_one)).mp hsq
  rw [hfac]
  -- STAGE 3 (the right peel; green :606-607 shape): cancel the TARGET chart
  -- isomorphism `iso𝒜.inv` — the affine chart of the ambient projective
  -- target.  `.mpr` so every factor match is definitional
  -- (proof-irrelevant iso arguments), not syntactic — the green law.
  refine (MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _
    (Proj.basicOpenIsoSpec (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j) hXj
      zero_lt_one).inv).mpr ?_
  -- STAGE 4 (the left peel; green :609-641 collapsed to one peel): cancel the
  -- SOURCE chart isomorphism `isoℬ.hom` — the affine chart of the line world.
  -- (Green needed two further `cancel_left` peels for its `Scheme.isoOfEq`
  -- transports; the pin's `map_preimage_basicOpen` is `rfl`, so the source
  -- chart needs no transport here.)
  refine (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    (Proj.basicOpenIsoSpec (lineGrading M) ((lineGradedQuotientHom M)
        (MvPolynomial.X j))
      ((lineGradedQuotientHom M).2 hXj) zero_lt_one).hom _).mpr ?_
  -- STAGE 5 (the affine closer; green :642-643 shape): the chart ring map is
  -- Agent-B-surjective, so its `Spec` is a closed immersion.
  exact IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom
      (HomogeneousLocalization.Away.map (lineGradedQuotientHom M)
        (MvPolynomial.X j))) hsurj
