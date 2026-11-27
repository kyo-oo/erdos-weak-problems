import Mathlib
import HCUniverse2.GSTFiniteLinePointsGateCore
import HCUniverse2.GSTFiniteLineUnconditionalSource
/- SPLIT PIECE of GSTFiniteLinePointsGateDischarge.lean (the wave-9-G module-split law: the runner-kill window demands small pieces) -/

/-!
# THE FINITE-LINE POINTS GATE DISCHARGE — THE ASSEMBLY (wave 8-A3, GATE-A)

FILE 2 of the Wave 8 gate-discharge pair
(`research/campaign/wave8-gate-discharge-battle-map.md`, its "FILE 2" section
§1-§4, exactly as designed; companion dossier
`research/records/2026-11-23-wave8-gate-restriction-dossier.md`).  This module
discharges the last open gate of Task 2: the points-classification equiv
`FiniteLinePointsGate M` (`GSTFiniteLineAnalytification.lean:403`), assembled
from FILE 1's restriction machinery (`GSTFiniteLinePointsGateCore.lean`) and
the green corpus, then the one-substitution discharge of the gate-formed
unconditional law (`GSTFiniteLineUnconditionalSource.lean:158`).

## The declarations (the battle map's FILE 2 list)

* **§1 THE FORWARD MAP** — `finiteLinePointsGateForwardIndex` (the line index
  of a section, read at the one-point base), `finiteLinePointsGateForwardOption`
  (the left-chart branch: avoids the left chart variable ⇒ the coordinate
  through the left chart's reading; else `none`), and the assembled
  `finiteLinePointsGateForward : ComplexPoint (finiteLineWorld M) →
  Σ _ : Fin M, Option ℂ`.  The branch decision rides `Classical.propDecidable`
  (the `open Classical in` discipline; never the `split` tactic — the disease
  catalog's stale-Decidable law), and the preimage inputs ride FILE 1's §0
  preimage law fed by the re-derived `basicOpen_of_avoids` bridge.
* **§2 THE INVERSE LAWS** — the KEY LEMMA `chartLeg_eq_of_chartPointHomOf`
  (the chart leg of a `chartPointHomOf`-built point IS the `Spec.map` of its
  ring reading — by mono-cancellation on `Proj.awayι`, the pin's own
  `cancel_mono` idiom `research/pin/mathlib-51e6992/Basic.lean:275`), the
  corollaries `chartLeg_eq_chartPoint`/`chartReading_of_chartPoint` (the
  reading of a constructed chart point IS the chart evaluation at its
  coordinate), the line-index receipts
  `chartPoint_forwardIndex_lineLeftChart`/`_lineRightChart` (the constructive
  half's index computation), LAW-R
  `finiteLinePointsGateForward_coordPoint` (the right-inverse: every
  two-chart coordinate round-trips), and LAW-L
  `coordPoint_finiteLinePointsGateForward` (the left-inverse: every section
  is the chart point of its own forward coordinate — the `Subtype.ext` +
  mono-counit + FILE 1 §4 value-computation route).
* **§3 THE GATE** — `finiteLinePointsGate (M) [NeZero M] : FiniteLinePointsGate
  M`, the explicit `Equiv.mk` (toFun := the forward map, invFun := the green
  `coordPoint`, left/right inverses := §2's laws).
* **§4 THE DISCHARGE** — `finiteLineAnalytificationUnconditional` (the
  analytification at the constructed gate), its space receipt, and
  `native_GST_single_fold_orbit_law_finiteLine_unconditional_gatefree`: the
  gate-formed unconditional law
  (`GSTFiniteLineUnconditionalSource.lean:158`) discharged by ONE substitution
  of the constructed gate — the wave's kill shot.

## The authored in-module bridges (the honesty ledger, part 1)

Nothing below is stated without a proof (zero `sorry`, zero new axioms, zero
`native_decide`).  The battle map's FILE 2 design named seams that neither
the pin nor the green corpus states as lemmas; each is authored here as a
`private` helper anchored to the closest green/pin precedent, and each is a
designated CI repair point:

1. `complexBase_subsingleton` — the one-point receipt (the green
   `pointPairGeometry_carrier_subsingleton` instance route,
   `GSTFinitePointShiftWord.lean:511-513`; the dossier's R6 hazards respected:
   every base-point transport is a `Subsingleton.elim`, never a bare `rfl`).
2. `isLocElem_self` — the pinned localization element of the own-variable
   preimage (`Away.isLocalizationElem f f`, the `f ^ 1 / f ^ 1 = 1` value
   computation — the green `mk_self_frac` pattern verbatim,
   `GSTFiniteLineSmoothness.lean:785-800`, through `Away.val_mk`,
   `HomogeneousLocalization.val_one` and `Localization.mk_self`).
3. `awayι_mem_basicOpen_self` — **THE CRUX of the constructive half**: the
   away-extension of ANY point of `Spec (Away 𝒜 f)` lies in the chart's own
   basic open `D₊(f)` (the battle map's LAW-1 "the point `chartPoint (left, c)`
   has image in the left chart's basicOpen" seam).  The route found against
   the pin: `Proj.awayι_preimage_basicOpen` (`Basic.lean:301`) at `g := f`
   (the preimage IS `PrimeSpectrum.basicOpen (isLocalizationElem f f)`), the
   bridge-2 value (it IS `1`), the affine membership `psMem_basicOpen`
   (the `Iff.rfl` twin) and the field receipts `Ideal.eq_top_iff_one` +
   `PrimeSpectrum.isPrime.ne_top` (the pin's own `carrier.denom_notMem`
   finisher shape, `ProjectiveSpectrum_Scheme.lean:444-453`), concluded by
   the pin's own TODO'd membership dance (`Basic.lean:464-465`).
4. `basicOpen_of_avoids` — the `D₊`-membership bridge, re-derived in 2 lines
   (the PointsGate module keeps it private, `GSTFiniteLinePointsGate.lean:228`;
   the battle map sanctions the re-derivation).
5. `right_avoids_of_left_mem` — the none-case's right-avoidance (the cover
   witness lives in the image point's own line's block by the green
   well-definedness receipt `finiteLinePointLineIndex_of_avoids`, the parity
   trichotomy by `omega`, the twin shape of the chart-pair territory law
   `finiteLinePoint_avoids_chartPair`, `GSTFiniteLinePointsGate.lean:368`).
6. `left_preimage_of_avoids` / `right_preimage_of_left_mem` — the two preimage
   laws feeding FILE 1's `complexBase_preimage_eq_top_of_mem` (the battle
   map's CARD B), the former through bridge 4 + the one-point transport, the
   latter through bridge 5.
7. `chartLeg_map` — the affine faithfulness (the chart leg IS the `Spec.map`
   of its own reading), re-derived locally from the green counit
   `Spec.map_preimage` + the `homEquiv`/`preimage` `rfl` (FILE 1 keeps its
   twin private; the corpus-green class is
   `GSTFinitePointAnalytification.lean:431-436`).

The remaining steps ride pin/corpus-green names only, cited at each use.

## The honesty ledger (part 2 — what is NOT here)

The battle map's FILE 2 declaration list is delivered IN FULL (§1-§4: three
forward-map defs, the key lemma and its two corollaries, the two index
receipts, the two laws, the gate, and the three discharge declarations).
Nothing was omitted; no declaration is stated without a proof.  The kernel
verdict belongs to the CI lane at the pushed SHA; the authored bridges above
are the designated repair points (the battle map's own design carried
explicit "VERIFY the exact green spelling" hedges at exactly these seams).

Binder discipline of the lane: every declaration below that mentions `M` takes
`(M : ℕ) [NeZero M]` as its leading binders (the section variable is kept per
the lane law and shadowed by the explicit binders).

External names, every one verified against its providing module (or the pinned
Mathlib `research/pin/mathlib-51e6992/`) and cited at the point of use; the
imports mirror FILE 1's plus the discharge's source module
(`GSTFiniteLineUnconditionalSource`, which transitively supplies the honest
Hodge data and the law statement's homes).

Honesty ledger: zero `sorry`, zero `admit`, zero `native_decide`, zero new
axioms (grep-checked below the module; the `Classical.choice` that appears in
`#print axioms` is the standard classical branch of the option `dite`, the
corpus's own discipline for Prop-indexed data).  The GitHub CI lane of this
module owns the kernel check.
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 20000
set_option trace.profiler true
set_option autoImplicit false

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicTopology
open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTFiniteLineWorldCarrier
open GSTFiniteLineRing
open GSTFiniteLineOverBase
open GSTFiniteLineSmoothness
open GSTFiniteLineAnalytification
open GSTFiniteLinePointAlgebra
open GSTFiniteLinePointsGate
open GSTFiniteLinePointsGateCore
open GSTFiniteLineHonestHodgeData
open GSTSphereUnionComponents
open GSTSingularCohomologyMaps
open GSTHodgeSingleHypothesisConditional
open GSTFiniteLineUnconditionalSource

namespace GSTFiniteLinePointsGateDischarge

variable (M : ℕ) [NeZero M]
-- Lane binder discipline (the finite-point template's own law): every
-- declaration below that mentions `M` re-binds `(M : ℕ) [NeZero M]`
-- explicitly at its head (the section variable above is kept per the lane
-- law and shadowed by the explicit binders, so the shipped signatures are
-- fully deterministic).

/-! ## §0 THE BRIDGES (the authored helpers) -/

/-- **THE ONE-POINT RECEIPT** — the complex base `Spec ℂ` is a subsingleton
space: the green instance route of the finite-point lane
(`pointPairGeometry_carrier_subsingleton`,
`GSTFinitePointShiftWord.lean:511-513`, resolved through the field structure
of `ℂ` — the dossier's R6 law: the instances are provided through the
`inferInstanceAs` spelling, never a bare-`rfl` default equation). -/
theorem complexBase_subsingleton : Subsingleton ↥complexBase :=
  inferInstanceAs (Subsingleton ↥(Spec (CommRingCat.of ℂ)))

/-- **THE `D₊`-MEMBERSHIP BRIDGE** — a non-vanishing variable puts the point
inside the pinned basic open: the re-derivation of the PointsGate module's
private bridge (`GSTFiniteLinePointsGate.lean:228-235`, itself the pinned
`Proj.mem_basicOpen` `Iff.rfl` simp lemma `Basic.lean:58` plus the pinned
`HomogeneousIdeal.mem_iff` degree-cast
`GradedAlgebra_Homogeneous_Ideal.lean:102`). -/
theorem basicOpen_of_avoids (M : ℕ) [NeZero M] (y : finiteLineScheme M)
    {j : Fin (2 * M)} (hj : lineQuotientMap M (MvPolynomial.X j) ∉
      y.asHomogeneousIdeal.toIdeal) :
    y ∈ Proj.basicOpen (lineGrading M) (lineQuotientMap M (MvPolynomial.X j)) := by
  rw [Proj.mem_basicOpen]
  intro hmem
  exact hj (HomogeneousIdeal.mem_iff.mpr hmem)

/-- **THE AFFINE BASICOPEN MEMBERSHIP** — the affine twin of the pinned
`Proj.mem_basicOpen` (`Basic.lean:58`, an `Iff.rfl`): a point of `Spec R` lies
in the basic open of `s` exactly when `s` avoids the point's prime ideal.
Designated CI repair point (the FILE 1 bridge-4 twin). -/
private theorem psMem_basicOpen {R : Type*} [CommRing R]
    (q : Spec (CommRingCat.of R)) (s : R) :
    q ∈ PrimeSpectrum.basicOpen s ↔ s ∉ q.asIdeal :=
  Iff.rfl

/-- **THE SELF-FRACTION OF THE LOCALIZATION ELEMENT** — the pinned element
carried by the own-variable preimage formula is `1`: `isLocalizationElem f f`
is the fraction `f ^ 1 / f ^ 1`, computed through the green `mk_self_frac`
pattern verbatim (`GSTFiniteLineSmoothness.lean:785-800`: the `val_injective`
route, `Away.val_mk` `HomogeneousLocalization.lean:613`, `val_one` `:440`,
`Localization.mk_self`, `pow_one`).  Designated CI repair point. -/
private theorem isLocElem_self (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    HomogeneousLocalization.Away.isLocalizationElem
      (lineCoverHomogeneousOneQ M j) (lineCoverHomogeneousOneQ M j) = 1 := by
  apply HomogeneousLocalization.val_injective (𝒜 := lineGrading M)
    (x := Submonoid.powers (lineQuotientMap M (MvPolynomial.X j)))
  simp only [HomogeneousLocalization.Away.isLocalizationElem]
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one]
  exact Localization.mk_self
    (⟨(lineQuotientMap M (MvPolynomial.X j)) ^ 1,
      (Submonoid.mem_powers_iff _ _).mpr ⟨1, rfl⟩⟩ :
      Submonoid.powers (lineQuotientMap M (MvPolynomial.X j)))

/-- **THE CRUX OF THE CONSTRUCTIVE HALF** — the away-extension of ANY point of
the chart's affine spectrum lies in the chart's own basic open `D₊(f)`: the
pinned preimage formula `Proj.awayι_preimage_basicOpen`
(`research/pin/mathlib-51e6992/Basic.lean:301`) at `g := f` turns the question
into the affine membership of the localization element `isLocalizationElem f f`
(= `1`, the bridge above), the field receipts `Ideal.eq_top_iff_one` +
`PrimeSpectrum.isPrime.ne_top` (the pin's own `carrier.denom_notMem`
finisher shape, `ProjectiveSpectrum_Scheme.lean:444-453`) close the
membership, and the pin's TODO'd preimage membership dance (`Basic.lean:464`,
the mandatory three-step `SetLike.mem_coe`/`map_coe`/`Set.mem_preimage`)
carries it back to the scheme level.  Designated CI repair point — the
battle map's LAW-1 "the point `chartPoint (left, c)` has image in the left
chart's basicOpen" seam. -/
private theorem awayι_mem_basicOpen_self (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (q₀ : Spec (CommRingCat.of (HomogeneousLocalization.Away (lineGrading M)
      (lineQuotientMap M (MvPolynomial.X j))))) :
    (Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
      (lineCoverHomogeneousOneQ M j) zero_lt_one) q₀ ∈
      Proj.basicOpen (lineGrading M) (lineQuotientMap M (MvPolynomial.X j)) := by
  have hpre : q₀ ∈ (Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
      (lineCoverHomogeneousOneQ M j) zero_lt_one) ⁻¹ᵁ
      (Proj.basicOpen (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))) := by
    rw [show (Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
        (lineCoverHomogeneousOneQ M j) zero_lt_one) ⁻¹ᵁ
        (Proj.basicOpen (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))) =
        PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.isLocalizationElem
          (lineCoverHomogeneousOneQ M j) (lineCoverHomogeneousOneQ M j)) from
      Proj.awayι_preimage_basicOpen (𝒜 := lineGrading M)
        (f := lineQuotientMap M (MvPolynomial.X j))
        (f_deg := lineCoverHomogeneousOneQ M j) (hm := zero_lt_one)
        (g_deg := lineCoverHomogeneousOneQ M j) (hm' := zero_lt_one)]
    rw [isLocElem_self M j]
    have hmem : ¬(1 : HomogeneousLocalization.Away (lineGrading M)
        (lineQuotientMap M (MvPolynomial.X j))) ∈ q₀.asIdeal :=
      fun h1 => q₀.isPrime.ne_top ((Ideal.eq_top_iff_one q₀.asIdeal).mpr h1)
    exact hmem
  first
  | rw [← SetLike.mem_coe] at hpre
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage,
      SetLike.mem_coe] at hpre
    exact hpre
  | simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage,
      SetLike.mem_coe] at hpre
    exact hpre

/-- **THE CHART POINT AVOIDS ITS OWN CHART VARIABLE** — the image point of the
constructed chart point `chartPoint M j c` never contains the chart's own
variable: the image point is the away-extension of the comap point (the
`chartPointHomOf` definitional unfolding — `chartPoint` `:321`,
`chartPointHomOf` `:267` of `GSTFiniteLineAnalytification.lean`, the FILE 1
`rfl`-class at `GSTFiniteLinePointsGateCore.lean:645-647`), and the CRUX bridge
above puts it in the chart's own basic open, which the pinned
`Proj.mem_basicOpen` (`Basic.lean:58`) and `HomogeneousIdeal.mem_iff`
(`GradedAlgebra_Homogeneous_Ideal.lean:102`) read back as ideal
non-membership. -/
theorem chartPoint_avoids (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (c : ℂ) (x : complexBase) :
    lineQuotientMap M (MvPolynomial.X j) ∉
      (finiteLineComplexPointImage M (chartPoint M j c) x).asHomogeneousIdeal.toIdeal := by
  have hmem : finiteLineComplexPointImage M (chartPoint M j c) x ∈
      Proj.basicOpen (lineGrading M) (lineQuotientMap M (MvPolynomial.X j)) := by
    show (chartPoint M j c).1 x ∈
      Proj.basicOpen (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
    show (Spec.map (CommRingCat.ofHom (chartEvalRingHom M j c)) ≫
        Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
          (lineCoverHomogeneousOneQ M j) zero_lt_one) x ∈
      Proj.basicOpen (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
    rw [Scheme.Hom.comp_apply]
    exact awayι_mem_basicOpen_self M j
      ((Spec.map (CommRingCat.ofHom (chartEvalRingHom M j c))) x)
  rw [Proj.mem_basicOpen] at hmem
  intro hcontra
  exact hmem (HomogeneousIdeal.mem_iff.mp hcontra)

/-- **THE NONE-CASE'S RIGHT-AVOIDANCE** — a point whose ideal contains the
left chart variable of its own line avoids the right one: the green cover
witness avoids some variable (`exists_variable_not_mem`,
`GSTFiniteLinePointAlgebra.lean:885`), every avoided variable's block IS the
line index (the green well-definedness receipt
`finiteLinePointLineIndex_of_avoids`, `GSTFiniteLinePointsGate.lean:282`), so
the witness sits in the index's two-element block; the parity trichotomy
(`omega`) and the left-membership then force the witness to be the right
chart index.  The shape is the chart-pair territory law's own parity split
(`finiteLinePoint_avoids_chartPair`, `GSTFiniteLinePointsGate.lean:368`). -/
theorem right_avoids_of_left_mem (M : ℕ) [NeZero M]
    (y : finiteLineScheme M)
    (hmem : lineQuotientMap M (MvPolynomial.X
        (lineLeftChart M (finiteLinePointLineIndex M y))) ∈
      y.asHomogeneousIdeal.toIdeal) :
    lineQuotientMap M (MvPolynomial.X
        (lineRightChart M (finiteLinePointLineIndex M y))) ∉
      y.asHomogeneousIdeal.toIdeal := by
  intro hR
  obtain ⟨j, hj⟩ := exists_variable_not_mem M y
  have hblk : j.val / 2 = (finiteLinePointLineIndex M y).val :=
    finiteLinePointLineIndex_of_avoids M y hj
  have hdisj : j.val = 2 * (finiteLinePointLineIndex M y).val ∨
      j.val = 2 * (finiteLinePointLineIndex M y).val + 1 := by omega
  rcases hdisj with h | h
  · have hjleft : j = lineLeftChart M (finiteLinePointLineIndex M y) :=
      Fin.ext h
    have havoid : lineQuotientMap M (MvPolynomial.X
        (lineLeftChart M (finiteLinePointLineIndex M y))) ∉
        y.asHomogeneousIdeal.toIdeal := by
      rw [show lineQuotientMap M (MvPolynomial.X
          (lineLeftChart M (finiteLinePointLineIndex M y))) =
          lineQuotientMap M (MvPolynomial.X j) from
        congrArg (fun a => lineQuotientMap M (MvPolynomial.X a)) hjleft.symm]
      exact hj
    exact havoid hmem
  · have hjright : j = lineRightChart M (finiteLinePointLineIndex M y) :=
      Fin.ext h
    have havoidR : lineQuotientMap M (MvPolynomial.X
        (lineRightChart M (finiteLinePointLineIndex M y))) ∉
        y.asHomogeneousIdeal.toIdeal := by
      rw [show lineQuotientMap M (MvPolynomial.X
          (lineRightChart M (finiteLinePointLineIndex M y))) =
          lineQuotientMap M (MvPolynomial.X j) from
        congrArg (fun a => lineQuotientMap M (MvPolynomial.X a)) hjright.symm]
      exact hj
    exact havoidR hR

/-- **THE LEFT-PREIMAGE BRIDGE** — a section whose image point at `x` avoids
the left chart variable of the line `i` pulls the left chart's basic open
back to everything: FILE 1's §0 preimage law
(`complexBase_preimage_eq_top_of_mem`,
`GSTFiniteLinePointsGateCore.lean:161`) fed pointwise by the re-derived
`basicOpen_of_avoids`, the point transport riding the one-point receipt
(bridge 1; every `x' = x` by `Subsingleton.elim`, never a bare `rfl` — the
dossier's R6 law). -/
theorem left_preimage_of_avoids (M : ℕ) [NeZero M]
    (p : ComplexPoint (finiteLineWorld M)) (x : complexBase) (i : Fin M)
    (hmem : lineQuotientMap M (MvPolynomial.X (lineLeftChart M i)) ∉
      (finiteLineComplexPointImage M p x).asHomogeneousIdeal.toIdeal) :
    p.1 ⁻¹ᵁ (Proj.basicOpen (lineGrading M)
      (lineQuotientMap M (MvPolynomial.X (lineLeftChart M i)))) = ⊤ := by
  apply complexBase_preimage_eq_top_of_mem p.1 _
  intro x'
  haveI hsub : Subsingleton ↥complexBase := complexBase_subsingleton
  have hxe : x' = x := Subsingleton.elim x' x
  rw [hxe, show p.1.base x = finiteLineComplexPointImage M p x from rfl]
  exact basicOpen_of_avoids M _ hmem


end GSTFiniteLinePointsGateDischarge

end -- noncomputable section
