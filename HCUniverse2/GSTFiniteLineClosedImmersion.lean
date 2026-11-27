import Mathlib
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import HCUniverse2.GSTFiniteLineRing
import HCUniverse2.GSTProjectiveOverC
import HCUniverse2.GSTFiniteLineWorldCarrier

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE FINITE-LINE CLOSED IMMERSION (Wave 66, F2 — the chartwise certification)

THE CLOSED-IMMERSION CERTIFICATION of `finiteLineEmbedding M` — the frozen
F2 design (research/records/2026-11-21-wave65-2R-f2-recon.md), executed by
the four-agent wave 66 (A: the cover twins; B: the Away-lift surjectivity;
C: the per-chart cascade; D: the assembly — this file).

* `lineCoverHomogeneous` / `lineCoverSpan` / `lineCover_iSup` (§1) — the
  arity-(2M-1+1) cover twins feeding `Proj.iSup_basicOpen_eq_top'`: the
  `D+(X j)` charts cover the ambient projective space (the green
  finite-point carrier's span_cover/variables_homogeneous transposed);
* `awayMap_surjective` (§2) — THE Away-lift sub-battle: on each ambient
  chart the graded quotient presentation's Away-map is surjective (the
  piece-level lift `mem_lineGrading` + `Away.mk_surjective` + `Away.map_mk`
  + the arity roundtrip);
* `chart_closed` (§3) — the per-chart closed immersion: the five-stage
  cascade (morphismRestrict + map_preimage_basicOpen + the awayι square +
  the cancel-of-respectsIso peels + spec_of_surjective);
* `finiteLine_closedImmersion` (§4) — THE ASSEMBLY: the embedding is a
  closed immersion, chartwise via `IsZariskiLocalAtTarget.of_iSup_eq_top`.

Every Mathlib name is pin-verified at 51e6992efd06126df61a496bebf8f49482a4e129
(reference copies under research/pin/mathlib-51e6992/) or CI-green in the
corpus. Zero sorry, zero new axioms.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry CategoryTheory
open GSTProjectiveOverC GSTFiniteLineRing GSTFiniteLineWorldCarrier
open MvPolynomial DirectSum

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GSTFiniteLineClosedImmersion

/-! ## §1 The D+(X j) cover of the ambient projective space — the cover twins -/
/-- **THE COVER TWIN (HOMOGENEITY)** — every ambient variable `X j` is
homogeneous of degree one in the target grading `ProjectiveGrading (2 * M - 1)`:
the `hfn` side condition of `Proj.iSup_basicOpen_eq_top'`
(Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:98) at
`f := MvPolynomial.X`, `𝒜 := ProjectiveGrading (2 * M - 1)`.  The arity is
the target grading's own, `Fin (2 * M - 1 + 1)` (see the arity resolution in
the file header); the body is the green twin `variables_homogeneous`
(GSTFinitePointWorldCarrier.lean:219-223) verbatim under the renames. -/
theorem lineCoverHomogeneous (M : ℕ) (j : Fin (2 * M - 1 + 1)) :
    ∃ n : ℕ, MvPolynomial.X j ∈ ProjectiveGrading (2 * M - 1) n := by
  refine ⟨1, ?_⟩
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact MvPolynomial.isHomogeneous_X ℂ j

/-- **THE COVER TWIN (SPAN)** — the ambient variables generate the target
homogeneous coordinate ring `MvPolynomial (Fin (2 * M - 1 + 1)) ℂ` as an
algebra over its degree-zero piece: the `hf` side condition of
`Proj.iSup_basicOpen_eq_top'`
(Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:99) at
`f := MvPolynomial.X`, `𝒜 := ProjectiveGrading (2 * M - 1)`.  The body is
the green twin `span_cover` (GSTFinitePointWorldCarrier.lean:202-215)
verbatim under the renames: every polynomial is built from constants
(degree zero, hence in the base ring, via `algebraMap_mem` and the
`IsHomogeneous (C a) 0` membership, definitionally the submodule membership)
and variables (in the adjoined set). -/
theorem lineCoverSpan (M : ℕ) :
    Algebra.adjoin ↥(ProjectiveGrading (2 * M - 1) 0)
      (Set.range (MvPolynomial.X : Fin (2 * M - 1 + 1) →
        MvPolynomial (Fin (2 * M - 1 + 1)) ℂ)) = ⊤ := by
  set S := Algebra.adjoin ↥(ProjectiveGrading (2 * M - 1) 0)
      (Set.range (MvPolynomial.X : Fin (2 * M - 1 + 1) →
        MvPolynomial (Fin (2 * M - 1 + 1)) ℂ))
  refine top_unique fun p hp => ?_
  clear hp
  induction p using MvPolynomial.induction_on with
  | C a =>
      exact S.algebraMap_mem
        ⟨MvPolynomial.C a,
          MvPolynomial.isHomogeneous_C (σ := Fin (2 * M - 1 + 1)) (R := ℂ) a⟩
  | add p q hp hq => exact S.add_mem hp hq
  | mul_X p j hp => exact S.mul_mem hp (Algebra.subset_adjoin (Set.mem_range_self j))

/-- **THE APPLIED COVER LEMMA** — the `D+(X j)` charts cover the target
`Proj (ProjectiveGrading (2 * M - 1))`: the pinned
`Proj.iSup_basicOpen_eq_top'` fed with the two cover twins.  This is the
assembler's iSup argument for `IsZariskiLocalAtTarget.of_iSup_eq_top`
(pinned signature: Mathlib/AlgebraicGeometry/Morphisms/Basic.lean:146-148,
`{ι} (U : ι → Y.Opens) (hU : iSup U = ⊤) (H : ∀ i, P (f ∣_ U i)) : P f`,
with `P`/`f` implicit), pre-packaged so the F2 assembly site needs no twin
application at all. -/
theorem lineCover_iSup (M : ℕ) :
    ⨆ j : Fin (2 * M - 1 + 1),
      Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' (ProjectiveGrading (2 * M - 1)) MvPolynomial.X
    (lineCoverHomogeneous M) (lineCoverSpan M)

/-! ## §2 The Away-lift surjectivity — the chart ring maps are surjective -/
/-- **THE AWAY-LIFT SURJECTIVITY** — F2's sub-battle: on each ambient chart
`D₊(X j)` of `ℙ^{2M-1}`, the graded quotient presentation's Away-map is
surjective.  Every element of `Away (lineGrading M) (image of X j)` is a
fraction `a / (image of X j) ^ n` (`Away.mk_surjective`); the numerator `a`
lifts through the line grading's piece-level lift `mem_lineGrading` to an
ambient homogeneous `t` of degree `n • 1`; the back-lift
`rename (lineFinEquiv M).symm t` is the numerator of the preimage fraction
`Away.mk (ProjectiveGrading (2*M-1)) hX n (back-lift) hs`; `Away.map_mk`
evaluates, and the arity roundtrip identifies the transported numerator with
the lifted one, so the two fractions are equal by proof irrelevance. -/
theorem awayMap_surjective (M : ℕ) [NeZero M] (j : Fin (2 * M - 1 + 1)) :
    Function.Surjective
      (HomogeneousLocalization.Away.map (lineGradedQuotientHom M)
        (MvPolynomial.X j)) := by
  intro z
  -- STEP 1: the chart variable is homogeneous of degree one (ambient side)
  -- — the point carrier's `hXj` mirror.
  have hX : (MvPolynomial.X j : ProjectiveCoordinateRing (2 * M - 1))
      ∈ ProjectiveGrading (2 * M - 1) 1 := by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_X ℂ j
  -- STEP 2: its image is homogeneous of degree one (line side) — the
  -- graded-map law of `lineGradedQuotientHom` (the pin's own `map_mem g hf`
  -- of `Away.map_mk`'s right-hand side).
  have hImg : lineGradedQuotientHom M (MvPolynomial.X j) ∈ lineGrading M 1 :=
    Graded.map_mem (lineGradedQuotientHom M) hX
  -- STEP 3: every target element is a fraction `a / (image of X j) ^ n`
  -- (`Away.mk_surjective`; the `rfl` substitutes `z` by the fraction).
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (lineGrading M) hImg z
  -- STEP 4: the piece-level lift (`mem_lineGrading`'s existential) — `a` is
  -- the image of an ambient homogeneous `t` of degree `n • 1`.
  obtain ⟨t, ht, hta⟩ := (mem_lineGrading M (n • 1) a).mp ha
  -- STEP 5: the back-lift numerator — rename along the arity bridge's
  -- inverse preserves the homogeneous degree (the carrier's
  -- `ambientQuotientHom_mem` composite).
  have hs : MvPolynomial.renameEquiv ℂ (lineFinEquiv M).symm t
      ∈ ProjectiveGrading (2 * M - 1) (n • 1) := by
    rw [MvPolynomial.renameEquiv_apply]
    exact (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (MvPolynomial.IsHomogeneous.rename_isHomogeneous
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mp ht))
  -- STEP 6: the arity roundtrip — the transported numerator IS the lifted
  -- one (the carrier's `ambientQuotient_surjective` show; the rewrite chain
  -- is Mathlib's own `renameEquiv` right_inv computation).
  have hgs : lineGradedQuotientHom M
      (MvPolynomial.renameEquiv ℂ (lineFinEquiv M).symm t) = a := by
    show lineQuotientMap M (MvPolynomial.rename ⇑(lineFinEquiv M)
      (MvPolynomial.rename ⇑((lineFinEquiv M).symm) t)) = a
    rw [MvPolynomial.rename_rename, Equiv.self_comp_symm, MvPolynomial.rename_id_apply]
    exact hta
  -- STEP 7: the preimage fraction — the back-lift over `(X j) ^ n`.
  refine ⟨HomogeneousLocalization.Away.mk (ProjectiveGrading (2 * M - 1)) hX
    n (MvPolynomial.renameEquiv ℂ (lineFinEquiv M).symm t) hs, ?_⟩
  -- STEP 8: the evaluation cascade (`Away.map_mk`).
  first
  | rw [HomogeneousLocalization.Away.map_mk]
  | simp only [HomogeneousLocalization.Away.map_mk]
  -- STEP 9: the fraction equality — substitute the numerator equation; the
  -- two `.mk`-terms then differ only in membership proofs of the SAME
  -- propositions, so proof irrelevance closes it.  Fallback (the point
  -- carrier's `first`-idiom): the `val`-injectivity route.
  subst hgs
  first
  | rfl
  | (apply HomogeneousLocalization.val_injective; rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk])

/-! ## §3 The per-chart closed immersion — the five-stage cascade -/
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
  -- W66-B PLUG: the Away-surjectivity of the chart ring map (§2 above).
  have hsurj : Function.Surjective
      (HomogeneousLocalization.Away.map (lineGradedQuotientHom M) (MvPolynomial.X j)) :=
    awayMap_surjective M j
  -- The chart section's degree-1 certificate (the green :571-573 two-liner):
  have hXj : MvPolynomial.X j ∈ ProjectiveGrading (2 * M - 1) 1 := by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_X ℂ j
  -- STAGE 0 (the retype; green :577-579): restate the restricted embedding at
  -- `Proj (lineGrading M) ⟶ Proj (ProjectiveGrading (2 * M - 1))` — the
  -- wrappers are defeq but not reducible, and `finiteLineEmbedding M`
  -- delta-unfolds to its `Proj.map` body.
  rw [show (finiteLineEmbedding M ∣_
      Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j)) =
    (Proj.map (lineGradedQuotientHom M) (line_irrelevant_le M) ∣_
      (Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j))) from rfl]
  -- STAGE 2 (THE FACTORIZATION — the pin's own
  -- `fromOfGlobalSections_morphismRestrict` pattern, Basic.lean:499-502,
  -- transposed to the `Proj.map` chart square): the restricted embedding
  -- factors as the source chart isomorphism, the Spec of the chart ring
  -- map, and the inverse target chart isomorphism.  Every rewrite below
  -- abstracts a CLOSED morphism term (motive-safe); the final defeq — the
  -- preimage open `map ⁻¹ᵁ U` vs the chart open `basicOpen ℬ (f s)`,
  -- `map_preimage_basicOpen` being rfl — is discharged by `exact h` at
  -- default transparency.
  have hfac : (Proj.map (lineGradedQuotientHom M) (line_irrelevant_le M) ∣_
      (Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j))) =
      (Proj.basicOpenIsoSpec (lineGrading M)
        ((lineGradedQuotientHom M) (MvPolynomial.X j))
        ((lineGradedQuotientHom M).2 hXj) zero_lt_one).hom ≫
      (Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.Away.map (lineGradedQuotientHom M)
          (MvPolynomial.X j))) ≫
        (Proj.basicOpenIsoSpec (ProjectiveGrading (2 * M - 1))
          (MvPolynomial.X j) hXj zero_lt_one).inv) := by
    -- the per-chart square (Functor.lean:192), both `awayι` unfolded through
    -- their definition (`basicOpenIsoSpec_inv_ι`, Basic.lean:190, rfl),
    -- right-associated by `Category.assoc`:
    have h := Proj.awayι_comp_map (lineGradedQuotientHom M) (line_irrelevant_le M)
      zero_lt_one (MvPolynomial.X j) hXj
    rw [← Proj.basicOpenIsoSpec_inv_ι (lineGrading M)
        ((lineGradedQuotientHom M) (MvPolynomial.X j))
        ((lineGradedQuotientHom M).2 hXj) zero_lt_one,
      ← Proj.basicOpenIsoSpec_inv_ι (ProjectiveGrading (2 * M - 1))
        (MvPolynomial.X j) hXj zero_lt_one] at h
    simp only [CategoryTheory.Category.assoc] at h
    -- h : isoℬ.inv ≫ ((basicOpen ℬ (f (X j))).ι ≫ map) =
    --     Spec.map ≫ (iso𝒜.inv ≫ U𝒜.ι)
    -- The pin's own two-step goal reduction (Basic.lean:500), in TERM MODE
    -- (default transparency): the equation's type rides the rfl-defeq of the
    -- two open spellings (preimage vs chart open — `map_preimage_basicOpen`
    -- is rfl), which `rw`'s implicit-transparency pattern matching cannot
    -- see, but `refine`/`congrArg`/`Eq.trans`/`exact` elaborate at default
    -- transparency where the defeq IS found.  (The wave-66.2 lesson: any
    -- `rw` against this goal shape dies at implicit transparency.)
    refine (CategoryTheory.Iso.inv_comp_eq
      (Proj.basicOpenIsoSpec (lineGrading M)
        ((lineGradedQuotientHom M) (MvPolynomial.X j))
        ((lineGradedQuotientHom M).2 hXj) zero_lt_one)).mp ?_
    refine (CategoryTheory.cancel_mono
      (Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j)).ι).mp ?_
    -- goal : (isoℬ.inv ≫ (map ∣_ U𝒜)) ≫ U𝒜.ι = (Spec.map ≫ iso𝒜.inv) ≫ U𝒜.ι
    -- the four-step Eq.trans chain (assoc-symm, the restriction square,
    -- h at the defeq spelling, assoc):
    have e1 : ((Proj.basicOpenIsoSpec (lineGrading M)
        ((lineGradedQuotientHom M) (MvPolynomial.X j))
        ((lineGradedQuotientHom M).2 hXj) zero_lt_one).inv ≫
      (Proj.map (lineGradedQuotientHom M) (line_irrelevant_le M) ∣_
        (Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j)))) ≫
      (Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j)).ι =
      (Proj.basicOpenIsoSpec (lineGrading M)
        ((lineGradedQuotientHom M) (MvPolynomial.X j))
        ((lineGradedQuotientHom M).2 hXj) zero_lt_one).inv ≫
      ((Proj.map (lineGradedQuotientHom M) (line_irrelevant_le M) ∣_
        (Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j))) ≫
      (Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j)).ι) :=
      CategoryTheory.Category.assoc _ _ _
    have e2 : (Proj.basicOpenIsoSpec (lineGrading M)
        ((lineGradedQuotientHom M) (MvPolynomial.X j))
        ((lineGradedQuotientHom M).2 hXj) zero_lt_one).inv ≫
      ((Proj.map (lineGradedQuotientHom M) (line_irrelevant_le M) ∣_
        (Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j))) ≫
      (Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j)).ι) =
      (Proj.basicOpenIsoSpec (lineGrading M)
        ((lineGradedQuotientHom M) (MvPolynomial.X j))
        ((lineGradedQuotientHom M).2 hXj) zero_lt_one).inv ≫
      ((Proj.map (lineGradedQuotientHom M) (line_irrelevant_le M) ⁻¹ᵁ
        (Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j))).ι ≫
      Proj.map (lineGradedQuotientHom M) (line_irrelevant_le M)) :=
      congrArg (fun t => (Proj.basicOpenIsoSpec (lineGrading M)
          ((lineGradedQuotientHom M) (MvPolynomial.X j))
          ((lineGradedQuotientHom M).2 hXj) zero_lt_one).inv ≫ t)
        (AlgebraicGeometry.morphismRestrict_ι
          (Proj.map (lineGradedQuotientHom M) (line_irrelevant_le M))
          (Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j)))
    have e4 : Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.Away.map (lineGradedQuotientHom M)
          (MvPolynomial.X j))) ≫
      ((Proj.basicOpenIsoSpec (ProjectiveGrading (2 * M - 1))
        (MvPolynomial.X j) hXj zero_lt_one).inv ≫
      (Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j)).ι) =
      (Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.Away.map (lineGradedQuotientHom M)
            (MvPolynomial.X j))) ≫
      (Proj.basicOpenIsoSpec (ProjectiveGrading (2 * M - 1))
        (MvPolynomial.X j) hXj zero_lt_one).inv) ≫
      (Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j)).ι :=
      (CategoryTheory.Category.assoc _ _ _).symm
    -- the middle defeq (e2's preimage-open ι vs h's chart-open ι) closes at
    -- default transparency by the rfl-lemma `map_preimage_basicOpen`:
    exact e1.trans (e2.trans (h.trans e4))
  rw [hfac]
  -- STAGE 3-5 (the peels + the affine closer; the green :603-643 shape):
  -- left-associate first (the green's own `simp only [← Category.assoc]`
  -- before the right peel), then cancel the target chart iso (right), the
  -- source chart iso (left), and close by the affine criterion.
  simp only [← CategoryTheory.Category.assoc]
  refine (MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _
    (Proj.basicOpenIsoSpec (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j) hXj
      zero_lt_one).inv).mpr ?_
  refine (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    (Proj.basicOpenIsoSpec (lineGrading M) ((lineGradedQuotientHom M)
        (MvPolynomial.X j))
      ((lineGradedQuotientHom M).2 hXj) zero_lt_one).hom _).mpr ?_
  exact IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom
      (HomogeneousLocalization.Away.map (lineGradedQuotientHom M)
        (MvPolynomial.X j))) hsurj

/-! ## §4 THE ASSEMBLY — the closed immersion -/

/-- **THE CLOSED IMMERSION OF THE FINITE-LINE WORLD** — the embedding of
`Proj (lineGrading M)` into `P^{2M-1}` is a closed immersion: chartwise on
the ambient `D+(X j)` cover (§1), each restriction is a closed immersion
(§3), so `IsZariskiLocalAtTarget.of_iSup_eq_top`
(Mathlib/AlgebraicGeometry/Morphisms/Basic.lean:146) assembles the global
property. The F2 gate of the frozen order — CLOSED. -/
theorem finiteLine_closedImmersion (M : ℕ) [NeZero M] :
    IsClosedImmersion (finiteLineEmbedding M) :=
  IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
    (fun j => Proj.basicOpen (ProjectiveGrading (2 * M - 1)) (MvPolynomial.X j))
    (lineCover_iSup M)
    (fun j => chart_closed M j)

/-! ## Receipts -/

#check lineCoverHomogeneous
#check lineCoverSpan
#check lineCover_iSup
#check awayMap_surjective
#check chart_closed
#check finiteLine_closedImmersion

#print axioms awayMap_surjective
#print axioms chart_closed
#print axioms finiteLine_closedImmersion

end GSTFiniteLineClosedImmersion

end
