import Mathlib
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import HCUniverse2.GSTFiniteLineRing
import HCUniverse2.GSTProjectiveOverC
import HCUniverse2.GSTFiniteLineWorldCarrier

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE CHART RING HOM BATTLE (Wave 67-C retry 2 — Stage 1 of the F3 module)

THE BATTLE OF F3 STAGE 1, executed from the wave-67-A recon
(`repairs/wave67_A_smoothness_route.md` §2 "Stage 1 — the chart equivalence")
on the substrate of the two predecessor sections
(`repairs/wave67_B_substrate.lean` — Stage 0 + Stage 2; the wave-67-C partial
`repairs/wave67_C_chart_equiv.lean` — the partner/homogeneity lemmas, whose
`linePartner_mem_smul_one` syntax bug is fixed here).

## The three kills

1. `chartRingHom M j : MvPolynomial (Fin 1) ℂ →+* Away (lineGrading M) (q (X j))`
   — the chart ring map, `T ↦ ρ := q (X j') / q (X j)` (the partner fraction):
   the `toRingHom` of `MvPolynomial.aeval (fun _ => chartRatio M j)` over the
   `ℂ`-algebra structure `chartAwayAlgebra` (the `fromZeroRingHom` composite
   `chartConstHom`, the pin's `Algebra (𝒜 0) (HomogeneousLocalization 𝒜 x)`
   at HomogeneousLocalization.lean:509 fed by `SetLike.GradeZero.instAlgebra`,
   DirectSum/Internal.lean:411).
2. `chartRingHom_surjective` — every element of the homogeneous localization
   is a polynomial in the ratio ρ.  Route (route map §2, SIMPLIFIED: the
   three-way monomial trichotomy collapses to TWO cases — an outside-pair
   index annihilates against the denominator, an inside-pair monomial IS a
   monomial in ρ): `Away.mk_surjective` (HomogeneousLocalization.lean:618) +
   `mem_lineGrading` (GSTFiniteLineRing.lean:160) + `MvPolynomial.as_sum`
   (MvPolynomial/Basic.lean:978) + `Localization.mk_sum`
   (MonoidLocalization/Basic.lean:823-area, RingTheory/Localization/Defs.lean:823)
   — the whole reassembly is ONE `val`-computation
   (`HomogeneousLocalization.val_injective`, :312).
3. `chart_ringHom_smooth` — `RingHom.Smooth.of_bijective`
   (RingTheory/RingHom/Smooth.lean:122, NO side conditions at the pin: a
   bijective ring hom is smooth via its `toAlgebra`).  Injectivity rides the
   retraction χ (`Localization.awayLift` of B's `blockEvalQuot`,
   Localization/Away/Basic.lean:485 + `awayLift_mk` :489).

## The two plugs for the assembler (W67-D / the F3 integrator)

* `chartConstHom M j : ℂ →+* Away (lineGrading M) (q (X j))` — THE Stage-2
  chart-square map: exactly the `chartRingHom`-binder shape of B's
  `chart_awayι_comp` (wave67_B_substrate.lean:382-393, instantiated with
  `hdef := rfl`).  NOTE the naming: B's §5 contract calls this composite
  `chartRingHom`; the task order for THIS wave gives that name to the
  polynomial-side map (kill 1), so the ℂ-structure map is `chartConstHom`
  here (the route map's own Stage-1 name for it).
* `chartConstHom_smooth : RingHom.Smooth (chartConstHom M j)` — the
  Stage-3-facing smoothness (route map Stage 3 consumes exactly this shape
  through `HasRingHomProperty.Spec_iff`): the composition
  `chartConstHom = chartRingHom ∘ (algebraMap ℂ ℂ[T])` of the smooth chart
  map with the smooth constants map
  (`Algebra.Smooth ℂ (MvPolynomial (Fin 1) ℂ)` by pure instance synthesis:
  `instFormallySmoothMvPolynomial`, Smooth/Basic.lean:112 +
  `Algebra.FinitePresentation.mvPolynomial`, FinitePresentation.lean:190),
  via `RingHom.Smooth.comp` (RingHom/Smooth.lean:103) +
  `RingHom.smooth_algebraMap` (:82).

## Deviation ledger (all pin-verified at 51e6992efd06126df61a496bebf8f49482a4e129)

1. The route map's Stage-1 sketch drives smoothness through
   `Algebra.Smooth.of_equiv` + `algebraize`; the pin's
   `RingHom.Smooth.of_bijective` needs NO algebra structure, so kill 3 is a
   one-liner on bijectivity — the cheapest route, as the task order demands.
2. The trichotomy of the route map (cross-block / other-block / same-block)
   collapses to a dichotomy: a monomial with ANY support index outside the
   block pair `{j, j'}` is annihilated by one factor of the denominator
   (`X a * X j` is a cross monomial whenever `a / 2 ≠ j / 2`), and a monomial
   with support inside the pair is `C c * X (0 : Fin 1) ^ (d j')`.  A
   cross-block monomial always has an outside-pair index (both block members
   are in the same block), so the cross-block case is subsumed.
3. All fraction arithmetic is done at the `Localization` level through
   `val` (`HomogeneousLocalization.val_injective`, :312): the master
   equalities are `Localization.mk_eq_mk'_apply` (Defs.lean:850) +
   `IsLocalization.mk'_eq` (Defs.lean:330, the witness-1 form) and
   `IsLocalization.mk'_eq_zero_iff` (:334) — no `Away`-level
   add/mul/reindex helpers are needed at all.
4. `MvPolynomial.X (0 : Fin 1)` (B's Deviation 3 spelling; the unit notation
   does not elaborate at `Fin 1`).
5. `Finsupp.degree` (Finsupp/Weight.lean:218, `degree_apply` :223 rfl,
   `degree_single` :229) is the degree currency; the homogeneity extraction
   runs through `MvPolynomial.isHomogeneous_monomial`
   (MvPolynomial/Homogeneous.lean:132) and `Finsupp.degree_eq_weight_one`
   (Finsupp/Weight.lean:248).

Honesty ledger: zero `sorry`, zero new axioms, zero `native_decide`.  Every
non-local name is pin-verified at Mathlib 51e6992efd06126df61a496bebf8f49482a4e129
(reference copies under research/pin/mathlib-51e6992/ and the wave-67-A
fetches) or CI-green in the corpus (file:line in each docstring).  Not yet
kernel-checked — per the campaign law, the CI lane owns compilation; the
`first | rfl | …` ladders mark the designated CI-repair points.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry CategoryTheory
open GSTProjectiveOverC GSTFiniteLineRing GSTFiniteLineWorldCarrier
open MvPolynomial DirectSum

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GSTFiniteLineSmoothness

/-! ## §0 Stage 0 — the absorbed substrate (partner involution, homogeneity,
the block projection)

Everything in this section is absorbed from the two predecessor sections:
the `linePartner` family and the homogeneity lemmas from the wave-67-C
partial (`repairs/wave67_C_chart_equiv.lean` — with its
`linePartner_mem_smul_one` syntax bug FIXED), the block projection family
from wave-67-B (`repairs/wave67_B_substrate.lean` §3).  The assembler
dedupes; each duplicate is marked `DEDUPE: also in wave67_B`. -/

/-- **THE PARTNER VALUE FUNCTION** — toggles the last bit at the value level:
`2b + e ↦ 2b + (1 - e)` (the wave-67-C partial's spelling; the route map's
`j.val ^^^ 1` is not `omega`-supported at the pin, B's Deviation 1). -/
def linePartnerVal (v : ℕ) : ℕ := if v % 2 = 0 then v + 1 else v - 1

/-- The partner stays in the same block (`omega`-verified). -/
theorem linePartnerVal_block (v : ℕ) : linePartnerVal v / 2 = v / 2 := by
  unfold linePartnerVal; split <;> omega

/-- The partner is different (`omega`-verified). -/
theorem linePartnerVal_ne (v : ℕ) : linePartnerVal v ≠ v := by
  unfold linePartnerVal; split <;> omega

/-- The partner of an index below `2 * M` stays below `2 * M`. -/
theorem linePartnerVal_lt (M : ℕ) [NeZero M] {v : ℕ} (hv : v < 2 * M) :
    linePartnerVal v < 2 * M := by
  have : 0 < M := Nat.pos_of_neZero _
  unfold linePartnerVal; split <;> omega

/-- **THE PARTNER INDEX** — the other index of `j`'s coordinate block
(the block is `{X j, X (linePartner M j)}`).  DEDUPE: also in wave67_B. -/
def linePartner (M : ℕ) [NeZero M] (j : Fin (2 * M)) : Fin (2 * M) :=
  ⟨linePartnerVal j.val, linePartnerVal_lt M j.isLt⟩

theorem linePartner_val (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    (linePartner M j).val = linePartnerVal j.val := rfl

/-- The partner is in the same block as `j`.  DEDUPE: also in wave67_B. -/
theorem linePartner_block (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    (linePartner M j).val / 2 = j.val / 2 :=
  linePartnerVal_block j.val

/-- The partner is different from `j`.  DEDUPE: also in wave67_B. -/
theorem linePartner_ne (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    linePartner M j ≠ j := fun h =>
  linePartnerVal_ne j.val (by
    have hv : (linePartner M j).val = j.val := congrArg Fin.val h
    rw [← linePartner_val M j]
    exact hv)

/-- **THE SAME-BLOCK CLASSIFICATION** — two indices in the same block are
`j` and its partner (`omega`-verified parity bookkeeping).  DEDUPE: also in
the wave-67-C partial (absorbed verbatim). -/
theorem sameBlock_or (M : ℕ) [NeZero M] (i j : Fin (2 * M))
    (h : i.val / 2 = j.val / 2) : i = j ∨ i = linePartner M j := by
  have hi : i.val < 2 * M := i.isLt
  have hj : j.val < 2 * M := j.isLt
  have hval : i.val = j.val ∨ i.val = linePartnerVal j.val := by
    by_cases hp : j.val % 2 = 0
    · by_cases hip : i.val % 2 = 0
      · exact Or.inl (by omega)
      · refine Or.inr ?_
        unfold linePartnerVal
        rw [if_pos hp]
        omega
    · by_cases hip : i.val % 2 = 0
      · refine Or.inr ?_
        unfold linePartnerVal
        rw [if_neg hp]
        omega
      · exact Or.inl (by omega)
  rcases hval with h' | h'
  · exact Or.inl (Fin.ext h')
  · refine Or.inr (Fin.ext ?_)
    rw [linePartner_val]
    exact h'

/-! ### The homogeneity of the two block variables -/

/-- The chart denominator `q (X j)` is homogeneous of degree `1` in the
quotient grading (the twin of `variables_homogeneous`,
GSTFinitePointWorldCarrier.lean:219-223, via the substrate's
`lineQuotientMap_mem_lineGrading`, GSTFiniteLineRing.lean:167).  DEDUPE: the
wave-67-B form is `lineCoverHomogeneousOneQ` (wave67_B_substrate.lean:184). -/
theorem lineX_mem_one (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    lineQuotientMap M (MvPolynomial.X j) ∈ lineGrading M 1 :=
  lineQuotientMap_mem_lineGrading M 1 _
    ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X ℂ j))

/-- The partner variable `q (X j')` is homogeneous of degree `1` as well. -/
theorem linePartner_mem_one (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    lineQuotientMap M (MvPolynomial.X (linePartner M j)) ∈ lineGrading M 1 :=
  lineQuotientMap_mem_lineGrading M 1 _
    ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X ℂ _))

/-- **THE FIXED LEMMA** — the `Away.mk`-graded form of the partner's
homogeneity, at degree `1 • 1` (the membership shape `Away.mk` demands at
`n := 1`, HomogeneousLocalization.lean:609-610).  The wave-67-C partial's
version carried a bracket bug (`rw one]`); fixed to the `rw [hone]` form
(the green `nsmul_one` idiom, GSTFinitePointWorldCarrier.lean:485). -/
theorem linePartner_mem_smul_one (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    lineQuotientMap M (MvPolynomial.X (linePartner M j)) ∈ lineGrading M (1 • 1) := by
  have h := linePartner_mem_one M j
  have hone : (1 : ℕ) • (1 : ℕ) = 1 := one_nsmul 1
  rw [hone]
  exact h

/-- **T6** — the constants through the degree-zero piece: the pin's
`SetLike.GradeZero.coe_algebraMap` (Mathlib/Algebra/DirectSum/Internal.lean:
413-414, `@[simp, norm_cast]`, `rfl`), at `S := ℂ`, `A := lineGrading M`,
`R := lineQuotient M`.  DEDUPE: also in wave67_B (wave67_B_substrate.lean:
319-321). -/
theorem hzero (M : ℕ) (c : ℂ) :
    (algebraMap ℂ (lineGrading M 0) c : lineQuotient M) = algebraMap ℂ (lineQuotient M) c :=
  SetLike.GradeZero.coe_algebraMap (lineGrading M) c

/-- The doubly-embedded constant IS the quotient image of the polynomial
constant — the `hzero` bridge composed with the quotient map's
`AlgHom.commutes` and `MvPolynomial.algebraMap_eq`
(MvPolynomial/Basic.lean:111). -/
theorem hzero_C (M : ℕ) (c : ℂ) :
    (algebraMap ℂ (lineGrading M 0) c : lineQuotient M)
      = lineQuotientMap M (MvPolynomial.C c) := by
  rw [hzero M c, ← (lineQuotientMap M).commutes c, MvPolynomial.algebraMap_eq]

/-! ### The block projection (the retraction's ambient half) -/

/-- **THE BLOCK PROJECTION (T4)** — the ℂ-algebra retraction of the
coordinate ring onto block `j`: `X j ↦ 1`, `X j' ↦ t` (the partner), every
other variable ↦ 0.  DEDUPE: also in wave67_B (wave67_B_substrate.lean:237). -/
noncomputable def blockEval (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    lineRing M →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  MvPolynomial.aeval fun a =>
    if a = j then (1 : MvPolynomial (Fin 1) ℂ)
    else if a = linePartner M j then MvPolynomial.X (0 : Fin 1) else 0

/-- The computation rule of the block projection on variables.  DEDUPE: also
in wave67_B (wave67_B_substrate.lean:245). -/
theorem blockEval_X (M : ℕ) [NeZero M] (j k : Fin (2 * M)) :
    blockEval M j (MvPolynomial.X k) =
      (if k = j then (1 : MvPolynomial (Fin 1) ℂ)
        else if k = linePartner M j then MvPolynomial.X (0 : Fin 1) else 0) := by
  simp only [blockEval, MvPolynomial.aeval_X]

/-- **T5 (generators, pointwise)** — every cross-monomial generator
evaluates to zero on the block projection.  DEDUPE: also in wave67_B
(wave67_B_substrate.lean:255). -/
theorem blockEval_crossMonomials (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    ∀ p ∈ crossMonomials M, blockEval M j p = 0 := by
  rintro _ ⟨a, b, hab, rfl⟩
  rw [map_mul, blockEval_X, blockEval_X, mul_eq_zero]
  by_cases hblk : a = j ∨ a = linePartner M j
  · refine Or.inr ?_
    have hablk : a.val / 2 = j.val / 2 := by
      rcases hblk with h | h
      · rw [h]
      · rw [h, linePartner_block]
    have hbj : b ≠ j := by
      intro hb
      subst hb
      exact hab hablk
    have hbp : b ≠ linePartner M j := by
      intro hb
      exact hab (by rw [hb, linePartner_block]; exact hablk)
    simp [hbj, hbp]
  · refine Or.inl ?_
    push_neg at hblk
    simp [hblk.1, hblk.2]

/-- **T5** — the block projection kills the cross ideal.  DEDUPE: also in
wave67_B (wave67_B_substrate.lean:281). -/
theorem blockEval_mem_ker (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    crossIdeal M ≤ RingHom.ker (blockEval M j).toRingHom := by
  rw [show crossIdeal M = Ideal.span (crossMonomials M) from rfl, Ideal.span_le]
  intro p hp
  exact (RingHom.mem_ker (blockEval M j).toRingHom).mpr
    (blockEval_crossMonomials M j p hp)

/-- **T5 (pointwise, ideal-level)**.  DEDUPE: also in wave67_B
(wave67_B_substrate.lean:290). -/
theorem blockEval_mem_crossIdeal (M : ℕ) [NeZero M] (j : Fin (2 * M))
    {p : lineRing M} (hp : p ∈ crossIdeal M) : blockEval M j p = 0 :=
  (RingHom.mem_ker (blockEval M j).toRingHom).mp (blockEval_mem_ker M j hp)

/-- **THE BLOCK PROJECTION'S DESCENT (T5)** — the retraction of the
cross-monomial quotient onto `ℂ[t]` (the pointwise `liftₐ` spelling of B's
Deviation 2, Ideal/Quotient/Operations.lean:471).  DEDUPE: also in wave67_B
(wave67_B_substrate.lean:299). -/
noncomputable def blockEvalQuot (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    lineQuotient M →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  Ideal.Quotient.liftₐ (crossIdeal M) (blockEval M j)
    (fun p hp => blockEval_mem_crossIdeal M j hp)

/-- The computation rule of the descent on quotient classes (`rfl`, the
carrier's `lineRotateHom_mk` pattern, GSTFinitePointWorldCarrier.lean:291).
DEDUPE: also in wave67_B (wave67_B_substrate.lean:306). -/
theorem blockEvalQuot_mk (M : ℕ) [NeZero M] (j : Fin (2 * M)) (t : lineRing M) :
    blockEvalQuot M j (lineQuotientMap M t) = blockEval M j t :=
  rfl
