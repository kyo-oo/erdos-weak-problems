import Mathlib
import HCUniverse2.GSTFiniteLineAnalytification
import HCUniverse2.GSTFiniteLinePointAlgebra
import HCUniverse2.GSTFiniteLineSmoothness
import HCUniverse2.GSTFiniteLineRiemann
import HCUniverse2.GSTFiniteLineOverBase
import HCUniverse2.GSTFiniteLinePointsGate
import HCUniverse2.GSTFiniteLinePointsGateCoreBasic
/- SPLIT PIECE of GSTFiniteLinePointsGateCore.lean (the wave-9-G module-split law: the runner-kill window demands small pieces) -/

/-!
# THE FINITE-LINE POINTS GATE CORE — THE RESTRICTION MACHINERY (wave 8-A2, GATE-A)

FILE 1 of the Wave 8 gate-discharge pair
(`research/campaign/wave8-gate-discharge-battle-map.md`, its "FILE 1" section
§0-§4, exactly as designed).  This module delivers the DECOMPOSITION side of
the last open gate of Task 2: reading an arbitrary complex point of the
finite-line world `finiteLineWorld M` (`GSTFiniteLineOverBase.lean:331`)
through the away charts of `Proj (lineGrading M)` — the machinery the
DISCHARGE file (FILE 2) assembles into `FiniteLinePointsGate M`
(`GSTFiniteLineAnalytification.lean:403`).

## The declarations (the battle map's FILE 1 list)

* **§0 THE ONE-POINT HEAD** — `complexBase_preimage_eq_top_of_mem`: a
  morphism from the one-point base whose every image point lies in an open
  pulls that open back to everything (the preimage law; the pin's own
  `fromOfGlobalSections_preimage_basicOpen` point-membership shape
  `research/pin/mathlib-51e6992/Basic.lean:459-477`, through the
  membership dance of the pin's TODO'd form, `Basic.lean:464-465`).
* **§1 THE SECTION-INTO-CHART** — `sectionInto` + the factorization
  receipt `sectionInto_ι`: the head composite
  `topIso.inv ≫ resLE ≫ chart-iso`, with the triangle receipt riding the
  pin's `Scheme.topIso`/`Scheme.Hom.resLE`/`resLE_comp_ι`/`toIso_inv_ι`
  (`research/pin/mathlib-51e6992/Restrict.lean:439/:775/:789/:446`) — the
  same decomposition shape as the pin's own `hasOfPostcompProperty`
  (`Morphisms_Basic.lean:675-678`) and `Proj.toSpecZero`
  (`Basic.lean:151-153`).
* **§2 THE CHART LEG** — `chartLeg` + the factorization receipt
  `chartLeg_awayι`: the restriction of a section to a chart's basic open,
  carried into the affine chart `Spec (.of (Away 𝒜 f))` through the pinned
  `Proj.basicOpenIsoSpec` (`Basic.lean:161`) — the receipt that the leg
  composes with `Proj.awayι` (`Basic.lean:186`) back to the section.
* **§3 THE READING** — `chartReading` (the `Spec.homEquiv` ring reading of
  the chart leg, the `sectionRingHom` binder orientation of the green home
  `GSTFinitePointAnalytification.lean:211-214`), the ℂ-linearity
  `chartReading_mem` (the chartPointSpace membership — the green
  `chartPointHomOf_section` calc `GSTFiniteLineAnalytification.lean:283-317`
  run in reverse), and the coordinate identity receipt `chartReading_eval`
  (the green `chartPointSpace_eval`, `GSTFiniteLineAnalytification.lean:356`).
* **§4 THE VALUE COMPUTATION AND THE TRANSPORT** —
  `chartReading_ratio_eq_zero_of_mem` (the none-case value: a section whose
  image point swallows the left chart variable reads the right chart's ratio
  as 0) and `chartPoint_right_zero_mem` (the forward branch-decision: the
  constructed `[0:1]`-point swallows its left chart variable).

## The authored in-module bridges (the honesty ledger, part 1)

Nothing below is stated without a proof (zero `sorry`, zero new axioms, zero
`native_decide`).  §0-§3 ride names every one of which is verified against
the pinned Mathlib (`research/pin/mathlib-51e6992/`) or a CI-green corpus
module, cited at each use.  §4 required six receipts that neither the pin nor
the corpus states; each is authored here as a `private` lemma with a proof
anchored to the closest green/pin precedent, and each is a designated CI
repair point:

1. `specMap_ofHom_base_apply` — the image point of `Spec.map (ofHom g)` at a
   base point IS `PrimeSpectrum.comap g` (the show-`rfl` defeq of the green
   `pointPair_left_apply`, `GSTFinitePointShiftWord.lean:271-276`, and the
   green `finiteLineCycle_apply_ideal`,
   `GSTFiniteLineCycleCorrespondence.lean:305-309`).
2. `chartLeg_map` — the chart leg IS the `Spec.map` of its reading (the
   `Spec.map_preimage` counit + the `homEquiv`/`preimage` defeq the green
   corpus rides at `GSTFinitePointAnalytification.lean:252-258` and
   `:431-433`).
3. `chartLeg_apply_ideal_comap` — the kernel receipt (bridge 1 + 2).
4. `psMem_basicOpen` — the affine basicOpen membership `q ∈ sbo s ↔ s ∉
   q.asIdeal` (the affine twin of the pin's `Proj.mem_basicOpen`,
   `Basic.lean:58`, an `Iff.rfl`).
5. `isLocElem_eq_chartRatio` — the pinned localization element of
   `Proj.awayι_preimage_basicOpen` (`Basic.lean:301-303`) IS the corpus's
   `chartRatio` at the partner index (the `val_mk` route:
   `HomogeneousLocalization.Away.val_mk`, `HomogeneousLocalization.lean:614`;
   the green `chartRatio_val`, `GSTFiniteLineSmoothness.lean:479-483`;
   `pow_one`).
6. `away_membership_iff` — the transport: the partner variable's membership
   in the away-extended point's homogeneous ideal ↔ the chart ratio's
   membership in the chart-point's ideal (the pin's TODO'd membership dance
   `Basic.lean:464-465` + `awayι_preimage_basicOpen` + the pinned
   `HomogeneousIdeal.mem_iff`,
   `GradedAlgebra_Homogeneous_Ideal.lean:102`).

The remaining §4 steps ride pin/corpus-green names only:
`Scheme.Hom.comp_apply` (`GSTFiniteLineCycleCorrespondence.lean:97`),
`Ideal.mem_comap` (green, `GSTFiniteLineCycleCorrespondence.lean:273`),
`Ideal.eq_bot_or_top` (pin, `RingTheory_Ideal_Basic_full.lean:230`),
`Ideal.mem_bot` (pin, `RingTheory_Ideal_Operations.lean:892`),
`chartEvalRingHom_chartRatio` (green,
`GSTFiniteLineAnalytification.lean:224-229`).

## The honesty ledger (part 2 — what is NOT here)

The battle map's FILE 1 declaration list is delivered IN FULL (§0-§4, ten
public declarations above the private helpers).  Nothing was omitted; no
declaration is stated without a proof.  The kernel verdict belongs to the CI
lane at the pushed SHA; the six authored bridges above are the designated
repair points (the battle map's own §4 design carried explicit "VERIFY the
exact green spelling" hedges at exactly these seams).

Binder discipline of the lane: every declaration below that mentions `M`
takes `(M : ℕ) [NeZero M]` as its leading binders (the section variable is
kept per the lane law and shadowed by the explicit binders).

External names, every one verified against its providing module (or the
pinned Mathlib) and cited at the point of use; the imports mirror the
CI-green `GSTFiniteLinePointsGate.lean:1-6` (the module that owns
`finiteLineComplexPointImage`, `GSTFiniteLinePointsGate.lean:160`) plus the
battle map's named `GSTFiniteLineAnalytification`.

Honesty ledger: zero `sorry`, zero new axioms, zero `native_decide`.  The
GitHub CI lane of this module owns the kernel check.
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 20000
set_option trace.profiler true
set_option autoImplicit false

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2D
open GSTNativeCodimensionCyclePresentation
open GSTFiniteLineWorldCarrier
open GSTFiniteLineRing
open GSTFiniteLineOverBase
open GSTFiniteLineSmoothness
open GSTFiniteLineAnalytification
open GSTFiniteLinePointAlgebra
open GSTFiniteLinePointsGate

namespace GSTFiniteLinePointsGateCore

variable (M : ℕ) [NeZero M]
-- Lane binder discipline (the finite-point template's own law): every
-- declaration below that mentions `M` re-binds `(M : ℕ) [NeZero M]`
-- explicitly at its head (the section variable above is kept per the lane
-- law and shadowed by the explicit binders, so the shipped signatures are
-- fully deterministic).

/-! ## §4 THE VALUE COMPUTATION AND THE TRANSPORT (the authored bridges) -/

/-- **AUTHORED BRIDGE 1 (the Spec-map image point)** — the image point of
`Spec.map (ofHom g)` at a base point IS `PrimeSpectrum.comap g` of that
point: the show-`rfl` defeq of the green corpus (the `show
PrimeSpectrum.comap (Pi.evalRingHom …) z` of `pointPair_left_apply`,
`GSTFinitePointShiftWord.lean:271-276`, and the `from rfl` of
`finiteLineCycle_apply_ideal`, `GSTFiniteLineCycleCorrespondence.lean:305-309`
— the coercion chain `coe f := f.base` → `comap`'s `toFun` documented at
`GSTFiniteLineCycleCorrespondence.lean:298`).  Designated CI repair point. -/
private theorem specMap_ofHom_base_apply {A : Type} [CommRing A]
    (g : A →+* ℂ) (z : complexBase) :
    (Spec.map (CommRingCat.ofHom g)) z = PrimeSpectrum.comap g z := by
  show PrimeSpectrum.comap g z = PrimeSpectrum.comap g z
  rfl

/-- **AUTHORED BRIDGE 2 (the leg IS the Spec of its reading)** — the chart
leg is `Spec.map` of its own reading: the `Spec.map_preimage` counit (green,
`GSTFinitePointAnalytification.lean:434-436`) plus the `homEquiv`/`preimage`
defeq the green corpus rides at `GSTFinitePointAnalytification.lean:252-258`
(the `rfl` inside `CommRingCat.hom_ext` mirrors the green `exact heq` at
`:431-433`).  Designated CI repair point. -/
private theorem chartLeg_map (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (p : ComplexPoint (finiteLineWorld M))
    (hpre : p.1 ⁻¹ᵁ (Proj.basicOpen (lineGrading M)
      (lineQuotientMap M (MvPolynomial.X j))) = ⊤) :
    chartLeg M j p hpre = Spec.map (CommRingCat.ofHom (chartReading M j p hpre)) := by
  have h1 : (Spec.preimage (R := CommRingCat.of (HomogeneousLocalization.Away
        (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))))
      (S := CommRingCat.of ℂ) (chartLeg M j p hpre)) =
      CommRingCat.ofHom (chartReading M j p hpre) := by
    apply CommRingCat.hom_ext
    rfl
  rw [← h1, Spec.map_preimage]

/-- **AUTHORED BRIDGE 3 (the kernel receipt)** — the image point of the
chart leg at a base point is the comap prime of the reading at that base
point's ideal: bridge 2 followed by bridge 1's defeq and the `comap` point's
`asIdeal` iota.  This is the battle map's §4 step 3.  Designated CI repair
point. -/
private theorem chartLeg_apply_ideal_comap (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (p : ComplexPoint (finiteLineWorld M))
    (hpre : p.1 ⁻¹ᵁ (Proj.basicOpen (lineGrading M)
      (lineQuotientMap M (MvPolynomial.X j))) = ⊤)
    (x : complexBase) :
    ((chartLeg M j p hpre) x).asIdeal =
      Ideal.comap (chartReading M j p hpre) x.asIdeal := by
  rw [chartLeg_map M j p hpre]
  exact show (PrimeSpectrum.comap (chartReading M j p hpre) x).asIdeal =
    Ideal.comap (chartReading M j p hpre) x.asIdeal from rfl

/-- **AUTHORED BRIDGE 4 (the affine basicOpen membership)** — the affine twin
of the pin's `Proj.mem_basicOpen` (`research/pin/mathlib-51e6992/Basic.lean:58`,
an `Iff.rfl`): a point of `Spec R` lies in the basic open of `s` exactly
when `s` avoids the point's prime ideal.  Designated CI repair point. -/
private theorem psMem_basicOpen {R : Type*} [CommRing R]
    (q : PrimeSpectrum R) (s : R) :
    q ∈ PrimeSpectrum.basicOpen s ↔ s ∉ q.asIdeal :=
  Iff.rfl

/-- **AUTHORED BRIDGE 5 (the localization element IS the chart ratio)** — the
pinned localization element carried by `Proj.awayι_preimage_basicOpen`
(`research/pin/mathlib-51e6992/Basic.lean:301-303`) is the corpus's
`chartRatio` at the partner index: `Away.isLocalizationElem`
(`HomogeneousLocalization.lean:881-882`) is `Away.mk 𝒜 hf e (g ^ d)`, the
chart ratio (`GSTFiniteLineSmoothness.lean:469-475`) is `Away.mk 𝒜 hf 1 g`,
and the two fractions are equal through the `val_mk` route
(`HomogeneousLocalization.Away.val_mk`, `HomogeneousLocalization.lean:614`;
the green `chartRatio_val`, `GSTFiniteLineSmoothness.lean:479-483`;
`HomogeneousLocalization.val_injective`, pin
`ProjectiveSpectrum_Scheme.lean:307`; `pow_one`).  Designated CI repair
point. -/
private theorem isLocElem_eq_chartRatio (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    HomogeneousLocalization.Away.isLocalizationElem (lineCoverHomogeneousOneQ M j)
      (lineCoverHomogeneousOneQ M (linePartner M j)) =
    chartRatio M j := by
  apply HomogeneousLocalization.val_injective
  rw [chartRatio_val M j]
  simp only [HomogeneousLocalization.Away.isLocalizationElem]
  rw [HomogeneousLocalization.Away.val_mk]
  exact congrFun (congrArg Localization.mk
    (pow_one (lineQuotientMap M (MvPolynomial.X (linePartner M j))))) _

/-- **AUTHORED BRIDGE 6 (the away-transport)** — the partner variable's
membership in the away-extended point's homogeneous ideal ↔ the chart ratio's
membership in the chart point's ideal: the pin's TODO'd membership dance
(`Basic.lean:464-465`) + the pinned `Proj.awayι_preimage_basicOpen`
(`Basic.lean:301-303`) + the pinned `Proj.mem_basicOpen` (`Basic.lean:58`) and
`HomogeneousIdeal.mem_iff`
(`GradedAlgebra_Homogeneous_Ideal.lean:102`) + bridges 4 and 5.  This is the
battle map's §4 step 5.  Designated CI repair point. -/
private theorem away_membership_iff (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (q₀ : Spec (CommRingCat.of (HomogeneousLocalization.Away (lineGrading M)
      (lineQuotientMap M (MvPolynomial.X j))))) :
    lineQuotientMap M (MvPolynomial.X (linePartner M j)) ∈
      (Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
        (lineCoverHomogeneousOneQ M j) zero_lt_one q₀).asHomogeneousIdeal.toIdeal ↔
    chartRatio M j ∈ q₀.asIdeal := by
  constructor
  · intro hmem
    -- The basicOpen avoidance at the away-extended point:
    have hbot : ¬(Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
        (lineCoverHomogeneousOneQ M j) zero_lt_one q₀ ∈
        Proj.basicOpen (lineGrading M)
          (lineQuotientMap M (MvPolynomial.X (linePartner M j)))) := by
      intro hq
      rw [Proj.mem_basicOpen] at hq
      exact hq (HomogeneousIdeal.mem_iff.mp hmem)
    -- The preimage dance (the pin's own TODO'd shape, Basic.lean:464-465):
    have hq₀ : ¬(q₀ ∈ (Proj.awayι (lineGrading M)
        (lineQuotientMap M (MvPolynomial.X j))
        (lineCoverHomogeneousOneQ M j) zero_lt_one) ⁻¹ᵁ
        (Proj.basicOpen (lineGrading M)
          (lineQuotientMap M (MvPolynomial.X (linePartner M j))))) := by
      intro hq
      first
      | rw [← SetLike.mem_coe] at hq
        simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe] at hq
        rw [show (Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
            (lineCoverHomogeneousOneQ M j) zero_lt_one).base q₀ =
            (Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
              (lineCoverHomogeneousOneQ M j) zero_lt_one) q₀ from rfl] at hq
        exact hbot hq
      | simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe] at hq
        rw [show (Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
            (lineCoverHomogeneousOneQ M j) zero_lt_one).base q₀ =
            (Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
              (lineCoverHomogeneousOneQ M j) zero_lt_one) q₀ from rfl] at hq
        exact hbot hq
    -- The pinned preimage formula + the affine membership + the element bridge:
    rw [show (Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
        (lineCoverHomogeneousOneQ M j) zero_lt_one) ⁻¹ᵁ
        (Proj.basicOpen (lineGrading M)
          (lineQuotientMap M (MvPolynomial.X (linePartner M j)))) =
        PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.isLocalizationElem
          (lineCoverHomogeneousOneQ M j) (lineCoverHomogeneousOneQ M (linePartner M j))) from
      Proj.awayι_preimage_basicOpen (𝒜 := lineGrading M)
        (f := lineQuotientMap M (MvPolynomial.X j))
        (f_deg := lineCoverHomogeneousOneQ M j) (hm := zero_lt_one)
        (g_deg := lineCoverHomogeneousOneQ M (linePartner M j))
        (hm' := zero_lt_one)] at hq₀
    by_contra hne
    rw [isLocElem_eq_chartRatio M j] at hq₀
    have hiff := psMem_basicOpen q₀ (chartRatio M j)
    exact hq₀ (hiff.mpr hne)
  · intro hmem
    -- The reverse: the affine membership, the preimage formula backwards,
    -- the dance backwards, the avoidance-to-membership closes.
    have h1 : (HomogeneousLocalization.Away.isLocalizationElem
        (lineCoverHomogeneousOneQ M j) (lineCoverHomogeneousOneQ M (linePartner M j))) ∈
        q₀.asIdeal := by
      rw [isLocElem_eq_chartRatio M j]
      exact hmem
    have h2 : ¬(q₀ ∈ PrimeSpectrum.basicOpen
        (HomogeneousLocalization.Away.isLocalizationElem
          (lineCoverHomogeneousOneQ M j) (lineCoverHomogeneousOneQ M (linePartner M j)))) := by
      intro hq
      have hiff := psMem_basicOpen q₀
        (HomogeneousLocalization.Away.isLocalizationElem
          (lineCoverHomogeneousOneQ M j) (lineCoverHomogeneousOneQ M (linePartner M j)))
      exact (hiff.mp hq) h1
    rw [← show (Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
        (lineCoverHomogeneousOneQ M j) zero_lt_one) ⁻¹ᵁ
        (Proj.basicOpen (lineGrading M)
          (lineQuotientMap M (MvPolynomial.X (linePartner M j)))) =
        PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.isLocalizationElem
          (lineCoverHomogeneousOneQ M j) (lineCoverHomogeneousOneQ M (linePartner M j))) from
      Proj.awayι_preimage_basicOpen (𝒜 := lineGrading M)
        (f := lineQuotientMap M (MvPolynomial.X j))
        (f_deg := lineCoverHomogeneousOneQ M j) (hm := zero_lt_one)
        (g_deg := lineCoverHomogeneousOneQ M (linePartner M j))
        (hm' := zero_lt_one)] at h2
    have h3 : ¬((Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
        (lineCoverHomogeneousOneQ M j) zero_lt_one).base q₀ ∈
        Proj.basicOpen (lineGrading M)
          (lineQuotientMap M (MvPolynomial.X (linePartner M j)))) := by
      intro hq
      apply h2
      rw [← SetLike.mem_coe, ← Set.mem_preimage,
        ← TopologicalSpace.Opens.map_coe] at hq
      exact hq
    have h4 : ¬(lineQuotientMap M (MvPolynomial.X (linePartner M j)) ∉
        (Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
          (lineCoverHomogeneousOneQ M j) zero_lt_one q₀).asHomogeneousIdeal) := by
      intro hne
      apply h3
      rw [show (Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
          (lineCoverHomogeneousOneQ M j) zero_lt_one).base q₀ =
          (Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
            (lineCoverHomogeneousOneQ M j) zero_lt_one) q₀ from rfl]
      rw [Proj.mem_basicOpen]
      exact hne
    exact HomogeneousIdeal.mem_iff.mpr (Classical.byContradiction h4)

/-- The partner of the right chart index of a line is its left chart index
(the green `linePartner_val_odd`, `GSTFiniteLineSmoothness.lean:144-146`:
the partner of the odd `2i+1` is `2i+1-1 = 2i`). -/
private theorem linePartner_right_eq_left (M : ℕ) [NeZero M] (i : Fin M) :
    linePartner M (lineRightChart M i) = lineLeftChart M i := by
  have hv : (lineRightChart M i).val = 2 * i.val + 1 := rfl
  have hmod : ¬ ((lineRightChart M i).val % 2 = 0) := by rw [hv]; omega
  have hp : (linePartner M (lineRightChart M i)).val =
      (lineRightChart M i).val - 1 := linePartner_val_odd M (lineRightChart M i) hmod
  apply Fin.ext
  show (linePartner M (lineRightChart M i)).val = (lineLeftChart M i).val
  have hv' : (lineLeftChart M i).val = 2 * i.val := rfl
  rw [hp, hv, hv']
  omega

/-- **THE VALUE COMPUTATION (the none-case)** — a section whose image point
swallows the LEFT chart variable of line `i` reads the RIGHT chart's ratio as
0: the section's image point is the away-extension of its chart leg's image
point (§2's receipt + `Scheme.Hom.comp_apply`, green at
`GSTFiniteLineCycleCorrespondence.lean:97`), the transport (bridge 6) turns
the left variable's membership into the chart ratio's membership in the
chart point's ideal, the kernel receipt (bridge 3) turns that into the
reading's vanishing through `Ideal.mem_comap` (green,
`GSTFiniteLineCycleCorrespondence.lean:273`), the field receipt
`Ideal.eq_bot_or_top` (pin, `RingTheory_Ideal_Basic_full.lean:230` — ℂ is a
`DivisionSemiring`) with `isPrime.ne_top` (green,
`GSTFiniteLinePointAlgebra.lean:1011`), and `Ideal.mem_bot` (pin,
`RingTheory_Ideal_Operations.lean:892`). -/
theorem chartReading_ratio_eq_zero_of_mem (M : ℕ) [NeZero M] (i : Fin M)
    (p : ComplexPoint (finiteLineWorld M)) (x : complexBase)
    (hmem : lineQuotientMap M (MvPolynomial.X (lineLeftChart M i)) ∈
      (finiteLineComplexPointImage M p x).asHomogeneousIdeal.toIdeal)
    (hpre : p.1 ⁻¹ᵁ (Proj.basicOpen (lineGrading M)
      (lineQuotientMap M (MvPolynomial.X (lineRightChart M i)))) = ⊤) :
    chartReading M (lineRightChart M i) p hpre
      (chartRatio M (lineRightChart M i)) = 0 := by
  -- The section's image point is the away-extension of the chart leg's
  -- image point:
  have hpt : (Proj.awayι (lineGrading M)
      (lineQuotientMap M (MvPolynomial.X (lineRightChart M i)))
      (lineCoverHomogeneousOneQ M (lineRightChart M i)) zero_lt_one
      ((chartLeg M (lineRightChart M i) p hpre) x)) = p.1 x := by
    have h0 : (chartLeg M (lineRightChart M i) p hpre ≫
        Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X (lineRightChart M i)))
          (lineCoverHomogeneousOneQ M (lineRightChart M i)) zero_lt_one) x = p.1 x :=
      congrArg (fun φ => φ x) (chartLeg_awayι M (lineRightChart M i) p hpre)
    rw [Scheme.Hom.comp_apply] at h0
    exact h0
  -- The membership, transported to the away-extension of the leg's point:
  have hmem' : lineQuotientMap M (MvPolynomial.X (linePartner M (lineRightChart M i))) ∈
      (Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X (lineRightChart M i)))
        (lineCoverHomogeneousOneQ M (lineRightChart M i)) zero_lt_one
        ((chartLeg M (lineRightChart M i) p hpre) x)).asHomogeneousIdeal.toIdeal := by
    rw [show lineQuotientMap M (MvPolynomial.X (linePartner M (lineRightChart M i))) =
        lineQuotientMap M (MvPolynomial.X (lineLeftChart M i)) from
      congrArg (fun a => lineQuotientMap M (MvPolynomial.X a))
        (linePartner_right_eq_left M i)]
    rw [show (Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X (lineRightChart M i)))
        (lineCoverHomogeneousOneQ M (lineRightChart M i)) zero_lt_one
        ((chartLeg M (lineRightChart M i) p hpre) x)) = finiteLineComplexPointImage M p x from
      hpt.trans (rfl)]
    exact hmem
  -- The transport (bridge 6):
  have hk := (away_membership_iff M (lineRightChart M i)
    ((chartLeg M (lineRightChart M i) p hpre) x)).mp hmem'
  -- The kernel receipt (bridge 3):
  rw [chartLeg_apply_ideal_comap M (lineRightChart M i) p hpre x] at hk
  -- The comap membership (green) and the one-point ideal of ℂ:
  rw [Ideal.mem_comap] at hk
  have hxb : x.asIdeal = ⊥ := by
    rcases Ideal.eq_bot_or_top x.asIdeal with h | h
    · exact h
    · exact absurd h x.isPrime.ne_top
  rw [hxb, Ideal.mem_bot] at hk
  exact hk

/-- **THE OTHER DIRECTION (the forward map's branch-decision)** — the
constructed `[0 : 1]`-point of line `i` (the right chart at the origin)
swallows the LEFT chart variable: the image point is the away-extension of
`PrimeSpectrum.comap (chartEvalRingHom M (lineRightChart M i) 0) x` (the
`chartPointHomOf`-def unfolded definitionally, `Scheme.Hom.comp_apply`, and
bridge 1 — the battle map's §4 step 4 route), the transport (bridge 6)
serves the reciprocal direction, and the kernel side closes through the
green coordinate receipt `chartEvalRingHom_chartRatio`
(`GSTFiniteLineAnalytification.lean:224-229`) at the coordinate 0. -/
theorem chartPoint_right_zero_mem (M : ℕ) [NeZero M] (i : Fin M) (x : complexBase) :
    lineQuotientMap M (MvPolynomial.X (lineLeftChart M i)) ∈
      (finiteLineComplexPointImage M (chartPoint M (lineRightChart M i) 0) x).asHomogeneousIdeal.toIdeal := by
  -- The constructed point's underlying morphism, definitionally:
  have hcp : (chartPoint M (lineRightChart M i) 0).1 =
      chartPointHomOf M (lineRightChart M i)
        (chartPointSpaceEval M (lineRightChart M i) 0) := rfl
  have hval : (chartPointSpaceEval M (lineRightChart M i) 0).val =
      chartEvalRingHom M (lineRightChart M i) 0 := rfl
  have hcomp : chartPointHomOf M (lineRightChart M i)
      (chartPointSpaceEval M (lineRightChart M i) 0) =
      Spec.map (CommRingCat.ofHom (chartEvalRingHom M (lineRightChart M i) 0)) ≫
        Proj.awayι (lineGrading M)
          (lineQuotientMap M (MvPolynomial.X (lineRightChart M i)))
          (lineCoverHomogeneousOneQ M (lineRightChart M i)) zero_lt_one := by
    rw [chartPointHomOf, hval]
    rfl
  -- The image point is the away-extension of the comap point:
  have himg : finiteLineComplexPointImage M (chartPoint M (lineRightChart M i) 0) x =
      (Spec.map (CommRingCat.ofHom (chartEvalRingHom M (lineRightChart M i) 0)) ≫
        Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X (lineRightChart M i)))
          (lineCoverHomogeneousOneQ M (lineRightChart M i)) zero_lt_one) x := by
    rw [finiteLineComplexPointImage_eq, hcp, hcomp]
    rfl
  rw [himg, Scheme.Hom.comp_apply, specMap_ofHom_base_apply]
  -- The reciprocal transport (bridge 6, the ← direction), fed by the green
  -- coordinate receipt:
  have hker : chartRatio M (lineRightChart M i) ∈
      (PrimeSpectrum.comap (chartEvalRingHom M (lineRightChart M i) 0) x).asIdeal := by
    rw [show (PrimeSpectrum.comap (chartEvalRingHom M (lineRightChart M i) 0) x).asIdeal =
        Ideal.comap (chartEvalRingHom M (lineRightChart M i) 0) x.asIdeal from rfl]
    rw [Ideal.mem_comap]
    have hxb : x.asIdeal = ⊥ := by
      rcases Ideal.eq_bot_or_top x.asIdeal with h | h
      · exact h
      · exact absurd h x.isPrime.ne_top
    rw [hxb, Ideal.mem_bot]
    exact chartEvalRingHom_chartRatio M (lineRightChart M i) 0
  have haway := (away_membership_iff M (lineRightChart M i)
    (PrimeSpectrum.comap (chartEvalRingHom M (lineRightChart M i) 0) x)).mpr hker
  -- The partner index identification closes the statement's left-variable
  -- form:
  rw [show lineQuotientMap M (MvPolynomial.X (lineLeftChart M i)) =
      lineQuotientMap M (MvPolynomial.X (linePartner M (lineRightChart M i))) from
    congrArg (fun a => lineQuotientMap M (MvPolynomial.X a))
      (linePartner_right_eq_left M i).symm]
  exact haway


end GSTFiniteLinePointsGateCore

end -- noncomputable section
