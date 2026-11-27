import Mathlib
import HCUniverse2.GSTFiniteLinePointsGateCore
import HCUniverse2.GSTFiniteLineUnconditionalSource
import HCUniverse2.GSTFiniteLinePointsGateDischargeInverseA
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

/-- **THE LEFT-CHART LINE-INDEX RECEIPT** — the forward index of the
constructed left-chart point is the line: the image point avoids the chart's
own variable (the `chartPoint_avoids` bridge), so the green well-definedness
receipt `finiteLinePointLineIndex_of_avoids` pins the index to the chart's
block, `(2 * i) / 2 = i` closing by `omega`. -/
theorem chartPoint_forwardIndex_lineLeftChart (M : ℕ) [NeZero M]
    (i : Fin M) (c : ℂ) :
    finiteLinePointsGateForwardIndex M (chartPoint M (lineLeftChart M i) c) = i := by
  apply Fin.ext
  have havoid : lineQuotientMap M (MvPolynomial.X (lineLeftChart M i)) ∉
      (finiteLineComplexPointImage M (chartPoint M (lineLeftChart M i) c)
        (default : complexBase)).asHomogeneousIdeal.toIdeal :=
    chartPoint_avoids M (lineLeftChart M i) c (default : complexBase)
  have hval : (lineLeftChart M i).val / 2 =
      (finiteLinePointLineIndex M (finiteLineComplexPointImage M
        (chartPoint M (lineLeftChart M i) c) (default : complexBase))).val :=
    finiteLinePointLineIndex_of_avoids M (finiteLineComplexPointImage M
      (chartPoint M (lineLeftChart M i) c) (default : complexBase)) havoid
  show (finiteLinePointLineIndex M (finiteLineComplexPointImage M
    (chartPoint M (lineLeftChart M i) c) (default : complexBase))).val = i.val
  rw [← hval]
  have hv : (lineLeftChart M i).val = 2 * i.val := rfl
  omega

/-- **THE RIGHT-CHART LINE-INDEX RECEIPT** — the forward index of the
constructed right-chart point `[0 : 1]` is the line: the same route at the
right chart index, `(2 * i + 1) / 2 = i` closing by `omega`. -/
theorem chartPoint_forwardIndex_lineRightChart (M : ℕ) [NeZero M]
    (i : Fin M) :
    finiteLinePointsGateForwardIndex M (chartPoint M (lineRightChart M i) 0) = i := by
  apply Fin.ext
  have havoid : lineQuotientMap M (MvPolynomial.X (lineRightChart M i)) ∉
      (finiteLineComplexPointImage M (chartPoint M (lineRightChart M i) 0)
        (default : complexBase)).asHomogeneousIdeal.toIdeal :=
    chartPoint_avoids M (lineRightChart M i) 0 (default : complexBase)
  have hval : (lineRightChart M i).val / 2 =
      (finiteLinePointLineIndex M (finiteLineComplexPointImage M
        (chartPoint M (lineRightChart M i) 0) (default : complexBase))).val :=
    finiteLinePointLineIndex_of_avoids M (finiteLineComplexPointImage M
      (chartPoint M (lineRightChart M i) 0) (default : complexBase)) havoid
  show (finiteLinePointLineIndex M (finiteLineComplexPointImage M
    (chartPoint M (lineRightChart M i) 0) (default : complexBase))).val = i.val
  rw [← hval]
  have hv : (lineRightChart M i).val = 2 * i.val + 1 := rfl
  omega

open Classical in
/-- **LAW-R (the right-inverse)** — every two-chart coordinate round-trips:
the `some`-coordinates through the left chart at the coordinate (the index
receipt, the branch receipt `chartPoint_avoids`, the reading receipt
`chartReading_of_chartPoint` and the green coordinate identity
`chartEvalRingHom_chartRatio`,
`GSTFiniteLineAnalytification.lean:224-229`), the `none`-coordinate through
FILE 1's branch-decision receipt `chartPoint_right_zero_mem`
(`GSTFiniteLinePointsGateCore.lean:640` — the constructed `[0 : 1]`-point
swallows its left chart variable).  The dite reductions are explicit
`simp only [dif_pos …]` / `[dif_neg …]` (beta-reducing, never `split`). -/
theorem finiteLinePointsGateForward_coordPoint (M : ℕ) [NeZero M] :
    ∀ z : (Sigma (fun _ : Fin M => Option ℂ)),
      finiteLinePointsGateForward M (coordPoint M z) = z := by
  intro z
  obtain ⟨i, opt⟩ := z
  cases opt with
  | some c =>
      show finiteLinePointsGateForward M (chartPoint M (lineLeftChart M i) c) =
        ⟨i, some c⟩
      rw [show finiteLinePointsGateForward M (chartPoint M (lineLeftChart M i) c) =
          ⟨finiteLinePointsGateForwardIndex M (chartPoint M (lineLeftChart M i) c),
            finiteLinePointsGateForwardOption M
              (finiteLinePointsGateForwardIndex M (chartPoint M (lineLeftChart M i) c))
              (chartPoint M (lineLeftChart M i) c)⟩ from rfl]
      rw [chartPoint_forwardIndex_lineLeftChart M i c]
      rw [show finiteLinePointsGateForwardOption M i (chartPoint M (lineLeftChart M i) c) =
          (if h : lineQuotientMap M (MvPolynomial.X (lineLeftChart M i)) ∉
              (finiteLineComplexPointImage M (chartPoint M (lineLeftChart M i) c)
                (default : complexBase)).asHomogeneousIdeal.toIdeal
            then some (chartReading M (lineLeftChart M i)
              (chartPoint M (lineLeftChart M i) c)
              (left_preimage_of_avoids M (chartPoint M (lineLeftChart M i) c)
                (default : complexBase) i h)
              (chartRatio M (lineLeftChart M i)))
            else none) from rfl]
      simp only [dif_pos (chartPoint_avoids M (lineLeftChart M i) c
        (default : complexBase))]
      rw [chartReading_of_chartPoint M (lineLeftChart M i) c
          (left_preimage_of_avoids M (chartPoint M (lineLeftChart M i) c)
            (default : complexBase) i
            (chartPoint_avoids M (lineLeftChart M i) c (default : complexBase))),
        chartEvalRingHom_chartRatio M (lineLeftChart M i) c]
  | none =>
      show finiteLinePointsGateForward M (chartPoint M (lineRightChart M i) 0) =
        ⟨i, none⟩
      rw [show finiteLinePointsGateForward M (chartPoint M (lineRightChart M i) 0) =
          ⟨finiteLinePointsGateForwardIndex M (chartPoint M (lineRightChart M i) 0),
            finiteLinePointsGateForwardOption M
              (finiteLinePointsGateForwardIndex M (chartPoint M (lineRightChart M i) 0))
              (chartPoint M (lineRightChart M i) 0)⟩ from rfl]
      rw [chartPoint_forwardIndex_lineRightChart M i]
      rw [show finiteLinePointsGateForwardOption M i (chartPoint M (lineRightChart M i) 0) =
          (if h : lineQuotientMap M (MvPolynomial.X (lineLeftChart M i)) ∉
              (finiteLineComplexPointImage M (chartPoint M (lineRightChart M i) 0)
                (default : complexBase)).asHomogeneousIdeal.toIdeal
            then some (chartReading M (lineLeftChart M i)
              (chartPoint M (lineRightChart M i) 0)
              (left_preimage_of_avoids M (chartPoint M (lineRightChart M i) 0)
                (default : complexBase) i h)
              (chartRatio M (lineLeftChart M i)))
            else none) from rfl]
      have hneg : ¬(lineQuotientMap M (MvPolynomial.X (lineLeftChart M i)) ∉
          (finiteLineComplexPointImage M (chartPoint M (lineRightChart M i) 0)
            (default : complexBase)).asHomogeneousIdeal.toIdeal) :=
        fun hmem => hmem (chartPoint_right_zero_mem M i (default : complexBase))
      simp only [dif_neg hneg]

open Classical in
/-- **LAW-L (the left-inverse)** — every section IS the chart point of its
own forward coordinate: `Subtype.ext` reduces to the underlying morphisms,
and the morphism chain is FILE 1's factorization `chartLeg_awayι` (the section
decomposed through its chart) + the affine faithfulness `chartLeg_map` (the
leg IS the `Spec.map` of its reading) + FILE 1's coordinate identity
`chartReading_eval` (the reading IS the chart evaluation at its own
coordinate) — the some-case at the left chart, with the reconstructed
`chartPointHomOf` composite closing by `rfl`.  The none-case runs the same
chain at the right chart with FILE 1's §4 value computation
`chartReading_ratio_eq_zero_of_mem` (a section whose image point swallows
the left chart variable reads the right chart's ratio as `0`).  The full
spellings are used throughout (the wave-68 full-spelling discipline: no
`have`-bound locals in matching positions — a `have`-bound local is opaque to
defeq). -/
theorem coordPoint_finiteLinePointsGateForward (M : ℕ) [NeZero M] :
    ∀ p : ComplexPoint (finiteLineWorld M),
      coordPoint M (finiteLinePointsGateForward M p) = p := by
  intro p
  by_cases hcond : lineQuotientMap M (MvPolynomial.X
      (lineLeftChart M (finiteLinePointsGateForwardIndex M p))) ∉
    (finiteLineComplexPointImage M p (default : complexBase)).asHomogeneousIdeal.toIdeal
  · -- THE SOME-CASE: the branch fired, so the forward coordinate is the left
    -- chart's reading and the section is the left chart point at it.
    rw [show finiteLinePointsGateForward M p =
        ⟨finiteLinePointsGateForwardIndex M p,
          finiteLinePointsGateForwardOption M
            (finiteLinePointsGateForwardIndex M p) p⟩ from rfl]
    rw [show finiteLinePointsGateForwardOption M
        (finiteLinePointsGateForwardIndex M p) p =
        (if h : lineQuotientMap M (MvPolynomial.X
            (lineLeftChart M (finiteLinePointsGateForwardIndex M p))) ∉
            (finiteLineComplexPointImage M p (default : complexBase)).asHomogeneousIdeal.toIdeal
          then some (chartReading M
            (lineLeftChart M (finiteLinePointsGateForwardIndex M p)) p
            (left_preimage_of_avoids M p (default : complexBase)
              (finiteLinePointsGateForwardIndex M p) h)
            (chartRatio M (lineLeftChart M
              (finiteLinePointsGateForwardIndex M p))))
          else none) from rfl]
    simp only [dif_pos hcond]
    show chartPoint M (lineLeftChart M (finiteLinePointsGateForwardIndex M p))
        (chartReading M (lineLeftChart M (finiteLinePointsGateForwardIndex M p)) p
          (left_preimage_of_avoids M p (default : complexBase)
            (finiteLinePointsGateForwardIndex M p) hcond)
          (chartRatio M (lineLeftChart M
            (finiteLinePointsGateForwardIndex M p)))) = p
    apply Subtype.ext
    have e1 : (chartPoint M (lineLeftChart M (finiteLinePointsGateForwardIndex M p))
        (chartReading M (lineLeftChart M (finiteLinePointsGateForwardIndex M p)) p
          (left_preimage_of_avoids M p (default : complexBase)
            (finiteLinePointsGateForwardIndex M p) hcond)
          (chartRatio M (lineLeftChart M
            (finiteLinePointsGateForwardIndex M p))))).1 =
        Spec.map (CommRingCat.ofHom (chartEvalRingHom M
          (lineLeftChart M (finiteLinePointsGateForwardIndex M p))
          (chartReading M (lineLeftChart M (finiteLinePointsGateForwardIndex M p)) p
            (left_preimage_of_avoids M p (default : complexBase)
              (finiteLinePointsGateForwardIndex M p) hcond)
            (chartRatio M (lineLeftChart M
              (finiteLinePointsGateForwardIndex M p)))))) ≫
        Proj.awayι (lineGrading M)
          (lineQuotientMap M (MvPolynomial.X
            (lineLeftChart M (finiteLinePointsGateForwardIndex M p))))
          (lineCoverHomogeneousOneQ M
            (lineLeftChart M (finiteLinePointsGateForwardIndex M p))) zero_lt_one := rfl
    have e2 : Spec.map (CommRingCat.ofHom (chartReading M
          (lineLeftChart M (finiteLinePointsGateForwardIndex M p)) p
          (left_preimage_of_avoids M p (default : complexBase)
            (finiteLinePointsGateForwardIndex M p) hcond))) ≫
        Proj.awayι (lineGrading M)
          (lineQuotientMap M (MvPolynomial.X
            (lineLeftChart M (finiteLinePointsGateForwardIndex M p))))
          (lineCoverHomogeneousOneQ M
            (lineLeftChart M (finiteLinePointsGateForwardIndex M p))) zero_lt_one =
      chartLeg M (lineLeftChart M (finiteLinePointsGateForwardIndex M p)) p
          (left_preimage_of_avoids M p (default : complexBase)
            (finiteLinePointsGateForwardIndex M p) hcond) ≫
        Proj.awayι (lineGrading M)
          (lineQuotientMap M (MvPolynomial.X
            (lineLeftChart M (finiteLinePointsGateForwardIndex M p))))
          (lineCoverHomogeneousOneQ M
            (lineLeftChart M (finiteLinePointsGateForwardIndex M p))) zero_lt_one :=
      congrArg (fun g => g ≫ Proj.awayι (lineGrading M)
          (lineQuotientMap M (MvPolynomial.X
            (lineLeftChart M (finiteLinePointsGateForwardIndex M p))))
          (lineCoverHomogeneousOneQ M
            (lineLeftChart M (finiteLinePointsGateForwardIndex M p))) zero_lt_one)
        (chartLeg_map M (lineLeftChart M (finiteLinePointsGateForwardIndex M p)) p
          (left_preimage_of_avoids M p (default : complexBase)
            (finiteLinePointsGateForwardIndex M p) hcond)).symm
    exact e1.trans ((congrArg (fun g => Spec.map (CommRingCat.ofHom g) ≫
          Proj.awayι (lineGrading M)
            (lineQuotientMap M (MvPolynomial.X
              (lineLeftChart M (finiteLinePointsGateForwardIndex M p))))
            (lineCoverHomogeneousOneQ M
              (lineLeftChart M (finiteLinePointsGateForwardIndex M p))) zero_lt_one)
          ((chartReading_eval M (lineLeftChart M (finiteLinePointsGateForwardIndex M p)) p
            (left_preimage_of_avoids M p (default : complexBase)
              (finiteLinePointsGateForwardIndex M p) hcond)).symm)).trans
        (e2.trans (chartLeg_awayι M (lineLeftChart M
            (finiteLinePointsGateForwardIndex M p)) p
          (left_preimage_of_avoids M p (default : complexBase)
            (finiteLinePointsGateForwardIndex M p) hcond))))
  · -- THE NONE-CASE: the branch failed, so the section's image point swallows
    -- the left chart variable; the right chart covers it and the section is
    -- the right chart point at the origin.
    have hmem : lineQuotientMap M (MvPolynomial.X
        (lineLeftChart M (finiteLinePointsGateForwardIndex M p))) ∈
      (finiteLineComplexPointImage M p (default : complexBase)).asHomogeneousIdeal.toIdeal := by
      by_contra hne
      exact hcond hne
    rw [show finiteLinePointsGateForward M p =
        ⟨finiteLinePointsGateForwardIndex M p,
          finiteLinePointsGateForwardOption M
            (finiteLinePointsGateForwardIndex M p) p⟩ from rfl]
    rw [show finiteLinePointsGateForwardOption M
        (finiteLinePointsGateForwardIndex M p) p =
        (if h : lineQuotientMap M (MvPolynomial.X
            (lineLeftChart M (finiteLinePointsGateForwardIndex M p))) ∉
            (finiteLineComplexPointImage M p (default : complexBase)).asHomogeneousIdeal.toIdeal
          then some (chartReading M
            (lineLeftChart M (finiteLinePointsGateForwardIndex M p)) p
            (left_preimage_of_avoids M p (default : complexBase)
              (finiteLinePointsGateForwardIndex M p) h)
            (chartRatio M (lineLeftChart M
              (finiteLinePointsGateForwardIndex M p))))
          else none) from rfl]
    simp only [dif_neg hcond]
    show chartPoint M (lineRightChart M (finiteLinePointsGateForwardIndex M p)) 0 = p
    apply Subtype.ext
    have e1 : (chartPoint M (lineRightChart M (finiteLinePointsGateForwardIndex M p)) 0).1 =
        Spec.map (CommRingCat.ofHom (chartEvalRingHom M
          (lineRightChart M (finiteLinePointsGateForwardIndex M p)) 0)) ≫
        Proj.awayι (lineGrading M)
          (lineQuotientMap M (MvPolynomial.X
            (lineRightChart M (finiteLinePointsGateForwardIndex M p))))
          (lineCoverHomogeneousOneQ M
            (lineRightChart M (finiteLinePointsGateForwardIndex M p))) zero_lt_one := rfl
    have e2 : Spec.map (CommRingCat.ofHom (chartReading M
          (lineRightChart M (finiteLinePointsGateForwardIndex M p)) p
          (right_preimage_of_left_mem M p hmem))) ≫
        Proj.awayι (lineGrading M)
          (lineQuotientMap M (MvPolynomial.X
            (lineRightChart M (finiteLinePointsGateForwardIndex M p))))
          (lineCoverHomogeneousOneQ M
            (lineRightChart M (finiteLinePointsGateForwardIndex M p))) zero_lt_one =
      chartLeg M (lineRightChart M (finiteLinePointsGateForwardIndex M p)) p
          (right_preimage_of_left_mem M p hmem) ≫
        Proj.awayι (lineGrading M)
          (lineQuotientMap M (MvPolynomial.X
            (lineRightChart M (finiteLinePointsGateForwardIndex M p))))
          (lineCoverHomogeneousOneQ M
            (lineRightChart M (finiteLinePointsGateForwardIndex M p))) zero_lt_one :=
      congrArg (fun g => g ≫ Proj.awayι (lineGrading M)
          (lineQuotientMap M (MvPolynomial.X
            (lineRightChart M (finiteLinePointsGateForwardIndex M p))))
          (lineCoverHomogeneousOneQ M
            (lineRightChart M (finiteLinePointsGateForwardIndex M p))) zero_lt_one)
        (chartLeg_map M (lineRightChart M (finiteLinePointsGateForwardIndex M p)) p
          (right_preimage_of_left_mem M p hmem)).symm
    exact e1.trans ((congrArg (fun g => Spec.map (CommRingCat.ofHom g) ≫
          Proj.awayι (lineGrading M)
            (lineQuotientMap M (MvPolynomial.X
              (lineRightChart M (finiteLinePointsGateForwardIndex M p))))
            (lineCoverHomogeneousOneQ M
              (lineRightChart M (finiteLinePointsGateForwardIndex M p))) zero_lt_one)
          ((chartReading_eval M (lineRightChart M (finiteLinePointsGateForwardIndex M p)) p
              (right_preimage_of_left_mem M p hmem)).trans
            (congrArg (chartEvalRingHom M (lineRightChart M
                (finiteLinePointsGateForwardIndex M p)))
              (chartReading_ratio_eq_zero_of_mem M
                (finiteLinePointsGateForwardIndex M p) p (default : complexBase) hmem
                (right_preimage_of_left_mem M p hmem)))).symm).trans
        (e2.trans (chartLeg_awayι M (lineRightChart M
            (finiteLinePointsGateForwardIndex M p)) p
          (right_preimage_of_left_mem M p hmem))))


end GSTFiniteLinePointsGateDischarge

end -- noncomputable section
