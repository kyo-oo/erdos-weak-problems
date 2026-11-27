import Mathlib
import HCUniverse2.GSTFiniteLineOverBase
import HCUniverse2.GSTFiniteLineRiemann
import HCUniverse2.GSTGeometricRealizationStage2F

/-!
# THE FINITE-LINE ANALYTIFICATION (wave 3-C — GATE-A: the chart classification)

The analytification identification of the finite-line world — the disjoint
union of M projective lines, `finiteLineWorld M`
(`GSTFiniteLineOverBase.lean:331`) — against the honest sphere-union `Σ _ :
Fin M, unitSphereType` (M disjoint copies of the 2-sphere,
`GSTSphereUnionComponents.lean:169`).

## What this module proves unconditionally

* **§1 THE SPACE**: the analytification space `finiteLineSpace M :=
  TopCat.of (sphereUnionSpace M)` with the definitional carrier receipt
  (`finiteLineSpace_coe`) and the path-component receipt
  (`finiteLineSpace_components` — the green sphere-union component machine
  re-exported at the world's analytification: the components are exactly
  the M slices).
* **§2 THE TWO-CHART COORDINATE MODEL**: the type-level identification
  `sphereUnionSpace M ≃ Σ _ : Fin M, Option ℂ` (`sphereUnionCoordEquiv`) —
  slice-by-slice through the Riemann-sphere coordinate equivalence
  `riemannSphereEquiv` (`GSTFiniteLineRiemann.lean:318`, the wave-3-A green
  module): per line, the ℙ¹-points are the extended complex plane (the
  two-chart coordinate model of the projective line).
* **§3 THE CHART ARITHMETIC**: the chart ring's polynomial reading — the
  constants (`chartMap_C`), the variable (`chartMap_X0`), the chart ratio
  (`chartRetracts_chartRatio`), and the one-variable universal property
  (`polyEval_ext`: a ring homomorphism of `ℂ[T]` is determined by its
  constants and its variable).
* **§4 THE CHART POINT-SECTIONS AND THE AFFINE CLASSIFICATION**: every
  ℂ-linear ring homomorphism of every chart ring lifts to a GENUINE
  complex point of the world (`chartPointHomOf` +
  `chartPointHomOf_section` — the chart square discharge, the finite-point
  template's section-calculus (`GSTFinitePointAnalytification.lean:143`)
  transplanted onto the green chart square `chart_awayι_comp'`
  (`GSTFiniteLineSmoothness.lean:377`)); the chart-point space of every
  chart is classified as `ℂ` (`chartPointSpace_eval` +
  `chartPointSpaceEquiv` — the affine half of GATE-A); every two-chart
  coordinate is a genuine complex point (`coordPoint` — the constructive
  surjective-direction half: the `some`-coordinates through the line's left
  chart at the coordinate, the `none`-coordinate through the right chart
  at the origin).
* **§5 THE GATE AND THE ASSEMBLED ANALYTIFICATION**: the assembled
  `AnalytificationData (finiteLineWorld M)` whose space is the
  sphere-union, GIVEN the scheme-level classification as an explicit gate
  (`FiniteLinePointsGate` → `finiteLineAnalytificationOfGate` + the space
  receipt) — the same gate-form discipline the general-M law module (wave
  68) uses for its GATE-A input, so the law lane can already consume this
  module's assembly once the gate is discharged.

## The honest residual (the disclosed gap)

The scheme-level classification itself — `FiniteLinePointsGate M` — is NOT
proved here.  Discharging it requires (i) every section's image point lies
in some away-chart (the cover twin `iSup_basicOpen_eq_top'` + the
image-point analysis on the prime lattice of
`GSTFiniteLinePointAlgebra.lean` — the coheight-zero/component machinery
`lineIndexOfGeneric`/`lineComponentOf` and the no-intermediate law are
already green there), (ii) the per-line two-chart consistency
(a section read through the two charts of its line carries reciprocal
coordinates — the transition-function glueing of the two-chart model), and
(iii) the assembled full equiv (the coordinate-point family `coordPoint`
below is the constructive surjective-direction half; its injectivity is the
remaining half).  This is the next wave's battle; the present module is the
honest maximum below it.

Binder discipline of the lane (the finite-point template's own law):
every declaration below that mentions `M` takes `(M : ℕ) [NeZero M]` as
its leading binders.

Honesty ledger: zero `sorry`, zero new axioms, zero `native_decide`.  The
GitHub CI lane `gst-finite-line-analytification.yml` owns the kernel check.
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicTopology
open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTFiniteLineOverBase
open GSTFiniteLineWorldCarrier
open GSTFiniteLineRing
open GSTFiniteLineSmoothness
open GSTFiniteLineRiemann
open GSTSphereUnionComponents

namespace GSTFiniteLineAnalytification

variable (M : ℕ) [NeZero M]
-- Lane binder discipline (the finite-point template's own law): every
-- declaration below that mentions `M` re-binds `(M : ℕ) [NeZero M]`
-- explicitly at its head (the section variable above is kept per the lane
-- law and shadowed by the explicit binders, so the shipped signatures are
-- fully deterministic).

/-! ## §1 THE SPACE — the honest sphere-union -/

/-- **THE ANALYTIFICATION SPACE OF THE FINITE-LINE WORLD** — the honest
sphere-union: M disjoint copies of the 2-sphere (the sigma-typed disjoint
union `sphereUnionSpace M` of the green component machine), packaged as a
`TopCat` through the canonical `TopCat.of`. -/
def finiteLineSpace (M : ℕ) [NeZero M] : TopCat :=
  TopCat.of (sphereUnionSpace M)

/-- The underlying type of the analytification space is definitionally the
sphere-union (the `TopCat.of` Sort-coe is the identity carrier — the same
`rfl` receipt shape as the finite-point lane's `finitePointSpace_coe`). -/
theorem finiteLineSpace_coe (M : ℕ) [NeZero M] :
    ↥(finiteLineSpace M) = sphereUnionSpace M := rfl

/-- **THE PATH-COMPONENT RECEIPT** — the components of the analytification
space are exactly the M slices (the green sphere-union component machine
`sphereUnionZerothHomotopyEquiv`, accepted at the bundled space through the
definitional carrier — the same acceptance the green
`sphereUnion_cohomology_zero` exercises at `TopCat.of`). -/
noncomputable def finiteLineSpace_components (M : ℕ) [NeZero M] :
    ZerothHomotopy ↥(finiteLineSpace M) ≃ Fin M :=
  sphereUnionZerothHomotopyEquiv M

/-! ## §2 THE TWO-CHART COORDINATE MODEL -/

/-- **THE COORDINATE MODEL OF THE SPHERE-UNION** — the type-level
identification of the sphere-union with the two-chart coordinate model:
slice-by-slice, each 2-sphere is the extended complex plane `Option ℂ`
through the Riemann-sphere coordinate equivalence `riemannSphereEquiv`
(the `none`-coordinate is the point at infinity of the line's left
chart). -/
noncomputable def sphereUnionCoordEquiv (M : ℕ) [NeZero M] :
    sphereUnionSpace M ≃ (Sigma (fun _ : Fin M => Option ℂ)) where
  toFun z := ⟨z.1, riemannSphereEquiv z.2⟩
  invFun z := ⟨z.1, riemannSphereEquiv.symm z.2⟩
  left_inv z := by
    obtain ⟨i, s⟩ := z
    exact congrArg (Sigma.mk (β := fun _ : Fin M => unitSphereType) i)
      (riemannSphereEquiv.symm_apply_apply s)
  right_inv z := by
    obtain ⟨i, t⟩ := z
    exact congrArg (Sigma.mk (β := fun _ : Fin M => Option ℂ) i)
      (riemannSphereEquiv.apply_symm_apply t)

/-! ## §3 THE CHART ARITHMETIC (the polynomial reading of the chart ring) -/

/-- **THE CONSTANTS RECEIPT** — the chart map reads the constant polynomials
exactly as the chart's ℂ-structure fractions (the chart square's ring map
`chartRingHom` is definitionally the constants-into-the-away composite, the
W67-C certification). -/
theorem chartMap_C (M : ℕ) [NeZero M] (j : Fin (2 * M)) (c : ℂ) :
    chartMap M j (MvPolynomial.C c) = chartRingHom M j c := by
  show MvPolynomial.aeval (fun _ : Fin 1 => chartRatio M j)
      (MvPolynomial.C c) = chartRingHom M j c
  rw [MvPolynomial.aeval_C]
  rfl

/-- **THE VARIABLE RECEIPT** — the chart map reads the one variable exactly
as the chart ratio (the chart's transcendental generator). -/
theorem chartMap_X0 (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    chartMap M j (MvPolynomial.X (0 : Fin 1)) = chartRatio M j := by
  show MvPolynomial.aeval (fun _ : Fin 1 => chartRatio M j)
      (MvPolynomial.X (0 : Fin 1)) = chartRatio M j
  rw [MvPolynomial.aeval_X]

/-- **THE RATIO RECEIPT** — the green chart retraction reads the chart ratio
back as the one variable (the coordinate-reading half of the chart
equivalence). -/
theorem chartRetracts_chartRatio (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    chartRetracts M j (chartRatio M j) = MvPolynomial.X (0 : Fin 1) := by
  rw [show chartRatio M j = HomogeneousLocalization.Away.mk (lineGrading M)
      (lineCoverHomogeneousOneQ M j) 1
      (lineQuotientMap M (MvPolynomial.X (linePartner M j)))
      (linePartner_mem_smul_one M j) from rfl,
    chartRetracts_mk M j 1 _ _, blockEvalQuot_mk, blockEval_X,
    if_neg (linePartner_ne M j), if_pos rfl]

/-- **THE ONE-VARIABLE UNIVERSAL PROPERTY** — a ring homomorphism of the
one-variable polynomial algebra over ℂ is determined by its constants (both
read the constants through their own ℂ-structure) and its variable.  The
induction is the corpus's own `MvPolynomial.induction_on` workhorse; the
index collapses by `Subsingleton (Fin 1)`. -/
theorem polyEval_ext (f g : MvPolynomial (Fin 1) ℂ →+* ℂ)
    (hC : ∀ a : ℂ, f (MvPolynomial.C a) = g (MvPolynomial.C a))
    (hX : f (MvPolynomial.X (0 : Fin 1)) = g (MvPolynomial.X (0 : Fin 1))) :
    f = g := by
  refine MvPolynomial.ringHom_ext hC fun i => ?_
  rw [Subsingleton.elim i 0]
  exact hX

/-! ## §4 THE CHART POINT-SECTIONS AND THE AFFINE CLASSIFICATION -/

/-- **THE CHART EVALUATION** — the ring-level evaluation of the chart ring at
a coordinate `c ∈ ℂ`: the polynomial evaluation (at the constant family)
after the green chart retraction. -/
noncomputable def chartEvalRingHom (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (c : ℂ) :
    HomogeneousLocalization.Away (lineGrading M)
      (lineQuotientMap M (MvPolynomial.X j)) →+* ℂ :=
  (MvPolynomial.eval (fun _ : Fin 1 => c)).comp (chartRetracts M j)

/-- **THE EVALUATION IS ℂ-LINEAR** — the chart evaluation reads the chart's
ℂ-structure fractions back to the scalars: the retraction of the constant
fraction is the constant polynomial (the green `chart_retract` receipt at
the constants bridge `chartMap_C`), whose evaluation at `c` is the scalar
(the pinned `MvPolynomial.eval_C`). -/
theorem chartEval_chartRingHom (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (c c' : ℂ) :
    chartEvalRingHom M j c (chartRingHom M j c') = c' := by
  show (MvPolynomial.eval (fun _ : Fin 1 => c))
      (chartRetracts M j (chartRingHom M j c')) = c'
  rw [← chartMap_C M j c', chart_retract M j (MvPolynomial.C c'),
    MvPolynomial.eval_C]

/-- **THE COORDINATE READING** — the chart evaluation at `c` reads the chart
ratio as `c`: the retraction reads the ratio as the variable
(`chartRetracts_chartRatio`), whose evaluation is the coordinate (the
pinned `MvPolynomial.eval_X`). -/
theorem chartEvalRingHom_chartRatio (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (c : ℂ) :
    chartEvalRingHom M j c (chartRatio M j) = c := by
  show (MvPolynomial.eval (fun _ : Fin 1 => c))
      (chartRetracts M j (chartRatio M j)) = c
  rw [chartRetracts_chartRatio, MvPolynomial.eval_X]

/-- **THE HONEST CHART-POINT SPACE** — the affine ℂ-points of the chart:
ring homomorphisms of the chart ring that read the chart's ℂ-structure back
to the scalars (the Spec-side point space of the chart, the per-chart half
of the classification). -/
def chartPointSpace (M : ℕ) [NeZero M] (j : Fin (2 * M)) : Type :=
  { h : HomogeneousLocalization.Away (lineGrading M)
        (lineQuotientMap M (MvPolynomial.X j)) →+* ℂ //
    ∀ c : ℂ, h (chartRingHom M j c) = c }

/-- **THE EVALUATION POINT** — the chart evaluation at `c` is a chart point
(the pointwise ℂ-linearity receipt). -/
noncomputable def chartPointSpaceEval (M : ℕ) [NeZero M]
    (j : Fin (2 * M)) (c : ℂ) : chartPointSpace M j where
  val := chartEvalRingHom M j c
  property := fun c' => chartEval_chartRingHom M j c c'

/-- The comp-form receipt of the chart-point property (the ring-hom
composition is the identity — consumed by the chart square discharge
below). -/
theorem chartPointSpace_comp (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (h : chartPointSpace M j) :
    RingHom.comp h.val (chartRingHom M j) = RingHom.id ℂ := by
  ext c
  exact h.2 c

/-- The left (even) chart index of the i-th line. -/
def lineLeftChart (M : ℕ) [NeZero M] (i : Fin M) : Fin (2 * M) :=
  ⟨2 * i.val, by have hi := i.isLt; omega⟩

/-- The right (odd) chart index of the i-th line. -/
def lineRightChart (M : ℕ) [NeZero M] (i : Fin M) : Fin (2 * M) :=
  ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩

/-- **THE CHART POINT-SECTION** — every affine chart point lifts to a
morphism from the complex base into the world, through the chart's open
immersion `Proj.awayι`. -/
noncomputable def chartPointHomOf (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (h : chartPointSpace M j) : complexBase ⟶ (finiteLineWorld M).X :=
  Spec.map (CommRingCat.ofHom h.val) ≫
    Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
      (lineCoverHomogeneousOneQ M j) zero_lt_one

/-- **THE SECTION PROPERTY** — the chart point-section is a genuine complex
point: composing with the world's structure map returns the identity on the
complex base.  The calculation is the finite-point template's
section-calculus (`pointSection_section`,
`GSTFinitePointAnalytification.lean:143-163`) transplanted onto the green
chart square `chart_awayι_comp'`: the associativity regroup, the chart
square (the away-chart of the structure map is the `Spec` of the chart's
ℂ-structure ring hom — supplied through the definitional
`chartRingHom`-form), the contravariant `Spec.map` fusion, the ℂ-linearity
of the chart point, and `Spec.map_id`. -/
theorem chartPointHomOf_section (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (h : chartPointSpace M j) :
    chartPointHomOf M j h ≫ (finiteLineWorld M).structureMap =
      𝟙 complexBase := by
  have hchart : Proj.awayι (lineGrading M)
      (lineQuotientMap M (MvPolynomial.X j))
      (lineCoverHomogeneousOneQ M j) zero_lt_one ≫
      finiteLineStructureMap M =
      Spec.map (CommRingCat.ofHom (chartRingHom M j)) := chart_awayι_comp' M j
  have hring : (CommRingCat.ofHom (chartRingHom M j)) ≫
      (CommRingCat.ofHom h.val) =
      CommRingCat.ofHom (RingHom.id ℂ) := by
    apply CommRingCat.hom_ext
    exact chartPointSpace_comp M j h
  show (Spec.map (CommRingCat.ofHom h.val) ≫
      Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
        (lineCoverHomogeneousOneQ M j) zero_lt_one) ≫
      finiteLineStructureMap M = 𝟙 complexBase
  calc (Spec.map (CommRingCat.ofHom h.val) ≫
        Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
          (lineCoverHomogeneousOneQ M j) zero_lt_one) ≫
        finiteLineStructureMap M
      = Spec.map (CommRingCat.ofHom h.val) ≫
          (Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
            (lineCoverHomogeneousOneQ M j) zero_lt_one ≫
            finiteLineStructureMap M) :=
          CategoryTheory.Category.assoc _ _ _
    _ = Spec.map (CommRingCat.ofHom h.val) ≫
          Spec.map (CommRingCat.ofHom (chartRingHom M j)) := by rw [hchart]
    _ = Spec.map
          ((CommRingCat.ofHom (chartRingHom M j)) ≫
            (CommRingCat.ofHom h.val)) :=
          (Spec.map_comp _ _).symm
    _ = Spec.map (CommRingCat.ofHom (RingHom.id ℂ)) := by rw [hring]
    _ = 𝟙 complexBase := Spec.map_id _

/-- **THE CHART POINT-SECTION IS A COMPLEX POINT** — the `c`-indexed family
of genuine complex points of the world, one per coordinate of the chart. -/
noncomputable def chartPoint (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (c : ℂ) : ComplexPoint (finiteLineWorld M) :=
  ⟨chartPointHomOf M j (chartPointSpaceEval M j c),
    chartPointHomOf_section M j (chartPointSpaceEval M j c)⟩

/-- **THE CONSTRUCTIVE COORDINATE-POINT FAMILY** — the surjective-direction
half of the classification: every two-chart coordinate (line index + extended
coordinate) is a genuine complex point of the world.  The `some`-coordinates
ride the line's left chart at the coordinate; the `none`-coordinate (the
point at infinity of the left chart) rides the right chart at the origin
(the point `[0 : 1]` of the line, where the left coordinate vanishes). -/
noncomputable def coordPoint (M : ℕ) [NeZero M] :
    (Sigma (fun _ : Fin M => Option ℂ)) →
      ComplexPoint (finiteLineWorld M) :=
  fun z =>
    match z.2 with
    | some c => chartPoint M (lineLeftChart M z.1) c
    | none => chartPoint M (lineRightChart M z.1) 0

/-- **THE AFFINE CHART CLASSIFICATION (GATE-A's constructive core)** — every
chart point is the evaluation at its own coordinate (the value on the chart
ratio): the two polynomial-level readings of a chart element (through the
point and through the evaluation at the point's own coordinate) agree on
the constants (the ℂ-structure) and the variable (the chart ratio) — the
`C`/`add`/`mul_X` block induction of the corpus's own `chart_retract` /
`block_identity` battles (`GSTFiniteLineSmoothness.lean:962/:879`) — and
the chart's surjectivity (`chartMap_surjective`) transports the
identification to every chart element through the green retraction receipt
`chart_retract`.  WAVE-3-C repair: the block induction is stated POINTWISE
(`∀ q, h.val (chartMap M j q) = eval ... q`); the previous draft's
`RingHom.comp h.val (chartMap M j)` spliced an `AlgHom` into a `RingHom`
argument position (the corpus's own lanes always write `.toRingHom`
explicitly there — `GSTFinitePointShiftWord.lean` — and the automatic
`AlgHom → RingHom` coercion is not corpus-verified), so the honest route is
the induction the green corpus already exercises. -/
theorem chartPointSpace_eval (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (h : chartPointSpace M j) :
    h.val = chartEvalRingHom M j (h.val (chartRatio M j)) := by
  ext z
  obtain ⟨p, hp⟩ := chartMap_surjective M j z
  rw [show z = chartMap M j p from hp.symm]
  have hcomp : ∀ q : MvPolynomial (Fin 1) ℂ,
      h.val (chartMap M j q) =
      MvPolynomial.eval (fun _ : Fin 1 => h.val (chartRatio M j)) q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a =>
        rw [chartMap_C M j a, h.2 a, MvPolynomial.eval_C]
    | add a b ha hb =>
        simp only [map_add]
        rw [ha, hb]
    | mul_X a k ha =>
        have hk : k = (0 : Fin 1) := Subsingleton.elim k 0
        subst hk
        simp only [map_mul]
        rw [ha, chartMap_X0 M j, MvPolynomial.eval_X]
  rw [hcomp p]
  show MvPolynomial.eval (fun _ : Fin 1 => h.val (chartRatio M j)) p =
    (MvPolynomial.eval (fun _ : Fin 1 => h.val (chartRatio M j)))
      (chartRetracts M j (chartMap M j p))
  rw [chart_retract M j p]

/-- **THE CHART-POINT EQUIVALENCE** — the honest chart-point space of every
chart is `ℂ`: the coordinate reading (the value on the chart ratio) is the
classification, with the evaluation at `c` as its inverse (the coordinate
reading receipt `chartEvalRingHom_chartRatio`). -/
noncomputable def chartPointSpaceEquiv (M : ℕ) [NeZero M]
    (j : Fin (2 * M)) : chartPointSpace M j ≃ ℂ where
  toFun h := h.val (chartRatio M j)
  invFun c := chartPointSpaceEval M j c
  left_inv h := Subtype.ext (chartPointSpace_eval M j h).symm
  right_inv c := chartEvalRingHom_chartRatio M j c

/-! ## §5 THE GATE AND THE ASSEMBLED ANALYTIFICATION -/

/-- **THE SCHEME-LEVEL CLASSIFICATION GATE** — the honest residual
interface: the classification of the world's complex points over the
two-chart coordinate model (the module documentation's disclosed gap: the
image-point chart-covering, the per-line two-chart consistency, and the
assembled full equiv).  The gate is deliberately stated over the SAME
coordinate model that §2 identifies with the sphere-union, so the assembled
analytification below carries the honest space definitionally. -/
abbrev FiniteLinePointsGate (M : ℕ) [NeZero M] : Type _ :=
  ComplexPoint (finiteLineWorld M) ≃ (Sigma (fun _ : Fin M => Option ℂ))

/-- **THE ASSEMBLED ANALYTIFICATION (GATE FORM)** — given the scheme-level
classification (the gate), the finite-line world's analytification is the
honest sphere-union: the space is `TopCat.of (sphereUnionSpace M)` and the
points ride the gate through the two-chart coordinate model and the
Riemann-sphere identification slice-by-slice.  This is the same gate-form
discipline the general-M law module uses for its GATE-A input. -/
noncomputable def finiteLineAnalytificationOfGate (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M) :
    AnalytificationData (finiteLineWorld M) where
  space := finiteLineSpace M
  pointsEquiv :=
    (Equiv.trans gate (sphereUnionCoordEquiv M).symm).trans
      (Equiv.cast (finiteLineSpace_coe M).symm)

/-- **THE SPACE RECEIPT (the hspace gate)** — the assembled analytification's
space IS the honest sphere-union (the wave-68 law architecture's GATE-A
interface, discharged definitionally at the assembled data). -/
theorem finiteLineAnalytificationOfGate_space (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M) :
    (finiteLineAnalytificationOfGate M gate).space =
      TopCat.of (sphereUnionSpace M) := rfl

/-- **THE COMPONENT RECEIPT** — the assembled analytification's path
components are the M lines (the green sphere-union component machine,
consumed at the assembled space through the space receipt — the green
`sphereUnion_cohomology_zero` acceptance pattern).  WAVE-2 note: stated as
a DEF (the `≃`-shaped statement is data, not a Prop — the green corpus's
own `sphereUnion_cohomology_zero` form). -/
noncomputable def finiteLineAnalytificationOfGate_components (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M) :
    ZerothHomotopy ↥(finiteLineAnalytificationOfGate M gate).space ≃ Fin M := by
  rw [finiteLineAnalytificationOfGate_space M gate]
  exact sphereUnionZerothHomotopyEquiv M

/-! ## Receipts -/

#check finiteLineSpace
#check finiteLineSpace_coe
#check finiteLineSpace_components
#check sphereUnionCoordEquiv
#check chartMap_C
#check chartMap_X0
#check chartRetracts_chartRatio
#check polyEval_ext
#check chartEvalRingHom
#check chartEval_chartRingHom
#check chartEvalRingHom_chartRatio
#check chartPointSpace
#check chartPointSpaceEval
#check chartPointSpace_comp
#check lineLeftChart
#check lineRightChart
#check chartPointHomOf
#check chartPointHomOf_section
#check chartPoint
#check coordPoint
#check chartPointSpace_eval
#check chartPointSpaceEquiv
#check FiniteLinePointsGate
#check finiteLineAnalytificationOfGate
#check finiteLineAnalytificationOfGate_space
#check finiteLineAnalytificationOfGate_components

#print axioms sphereUnionCoordEquiv
#print axioms chartMap_C
#print axioms chartMap_X0
#print axioms chartRetracts_chartRatio
#print axioms polyEval_ext
#print axioms chartEval_chartRingHom
#print axioms chartEvalRingHom_chartRatio
#print axioms chartPointSpace_comp
#print axioms chartPointHomOf_section
#print axioms chartPointSpace_eval
#print axioms chartPointSpaceEquiv
#print axioms finiteLineAnalytificationOfGate
#print axioms finiteLineAnalytificationOfGate_space
#print axioms finiteLineAnalytificationOfGate_components

end GSTFiniteLineAnalytification

/-! DRAFT STATUS (wave 3-C, the finite-line analytification lane's Task 2;
the wave-2 draft body repaired and finalized):
* Source: the assault on the 19-line stub (the stub receipt is superseded
  by this body; no corpus file references it — verified by grep).  Template:
  `GSTFinitePointAnalytification.lean` (the finite-point lane's CI-green
  analytification) — the section-calculus, the carrier-X defeq, the
  Equiv.cast assembly and the binder discipline are its transplants; the
  chart-level content is new mathematics on the green F3 corpus
  (`GSTFiniteLineSmoothness.lean`) and the wave-3-A Riemann module.
* WAVE-3-C REPAIR: `chartPointSpace_eval`'s composition step was rebuilt
  POINTWISE (the `C`/`add`/`mul_X` induction) — the previous draft's
  `RingHom.comp h.val (chartMap M j)` spliced the `AlgHom` `chartMap` into
  a `RingHom` argument position (the corpus's lanes always write
  `.toRingHom` explicitly there, `GSTFinitePointShiftWord.lean`; the
  automatic coercion is not corpus-verified), so the honest route is the
  induction the green corpus itself exercises (`chart_retract`'s and
  `block_identity`'s own `C`/`add`/`mul_X` spines).
* Declarations: 26 (14 defs, 1 abbrev, 11 theorems), in dependency order;
  every M-mentioning declaration re-binds `(M : ℕ) [NeZero M]`
  (`polyEval_ext`, the M-free one-variable universal property, is exempt).
* External names, every one verified against its providing module (or the
  pinned Mathlib): `finiteLineWorld` (GSTFiniteLineOverBase.lean:331),
  `ComplexPoint`/`AnalytificationData` (GSTGeometricRealizationStage2F.lean:51/:60),
  `sphereUnionSpace`/`unitSphereType`/`sphereUnionZerothHomotopyEquiv`
  (GSTSphereUnionComponents.lean:169/:161/:227), `riemannSphereEquiv`
  (GSTFiniteLineRiemann.lean:318), `chartRingHom`/`chart_awayι_comp'`/
  `chartMap`/`chartRatio`/`chartRetracts`/`chartRetracts_mk`/
  `chart_retract`/`chartMap_surjective`/`blockEvalQuot_mk`/`blockEval_X`/
  `linePartner_ne`/`linePartner_mem_smul_one`/`lineCoverHomogeneousOneQ`
  (GSTFiniteLineSmoothness.lean:417/:377/:488/:469/:925/:943/:960/:907/:322/
  :262/:149/:458/:201), `finiteLineStructureMap`
  (GSTFiniteLineWorldCarrier.lean:77), `lineGrading`/`lineQuotientMap`
  (GSTFiniteLineRing.lean:155/:126), `complexBase`
  (GSTProjectiveOverC.lean:37), `MvPolynomial.eval`/`eval_C`/`eval_X`
  (the pin's Algebra/MvPolynomial/Eval.lean:257/:273/:276),
  `MvPolynomial.aeval_C`/`aeval_X`/`induction_on` (corpus-green usages:
  GSTFiniteLineSmoothness.lean:971/:871/:887), `Spec.map`/`map_comp`/
  `map_id`, `CommRingCat.ofHom`/`hom_ext`, `CategoryTheory.Category.assoc`
  (template-green), `Equiv.symm_apply_apply`/`apply_symm_apply`/`cast`,
  `Subtype.ext` (template-green), `ZerothHomotopy` (the pin's
  Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy), `Subsingleton.elim`
  (corpus-green, GSTFiniteLineSmoothness.lean:986).
* Every opened namespace is transitively imported: `CategoryTheory`,
  `AlgebraicGeometry`, `AlgebraicTopology` (`import Mathlib`);
  `GSTProjectiveOverC`, `GSTFiniteLineWorldCarrier`, `GSTFiniteLineRing`,
  `GSTFiniteLineSmoothness` (via `GSTFiniteLineOverBase`);
  `GSTSphereUnionComponents` (via `GSTFiniteLineRiemann`);
  `GSTFiniteLineOverBase`, `GSTFiniteLineRiemann`,
  `GSTGeometricRealizationStage2F` (direct imports) — the wave-5-A law.
* The honest residual: the scheme-level classification gate
  (`FiniteLinePointsGate`) — the image-point chart-covering on the prime
  lattice, the per-line two-chart consistency, and the full equiv.  The
  present module is the honest maximum below it: the space, the coordinate
  model, the full constructive chart side (every chart point of every chart
  is a genuine complex point; the chart-point space of every chart is
  classified as ℂ; every two-chart coordinate is a genuine complex point),
  and the gate-formed assembly with the space receipt.
* Static verification: no `sorry`/`admit`/`native_decide`/new axioms
  (grep-checked); parenthesis balance depth 0 (docstring-excluded); no
  stub names survive.  NOT COMPILED (no local Lean by repo law) — the
  designated CI repair points are the defeq `show`-bridges that unfold the
  `RingHom.comp`-application delta of `chartEvalRingHom` (the
  `chartEval_chartRingHom`/`chartEvalRingHom_chartRatio`/
  `chartPointSpace_eval` sites — the same `comp`-unfold the corpus's own
  `RingHom.comp_apply`-by-`rfl` class exercises) and the carrier defeqs of
  `chartPointHomOf`/`chartPointHomOf_section` (the `.X`/`.structureMap`
  delta of `finiteLineWorld`, the template's own CI-green PORT RISK class).
* NEXT-WAVE BATTLE MAP (discharging `FiniteLinePointsGate M`):
  (1) COVER — every section's underlying image point lies in some
  `D₊(q (X j))` (the twins `lineCoverHomogeneousQ`/`lineCoverAdjoin` feed
  Mathlib's `Proj.iSup_basicOpen_eq_top'`; then the prime-lattice machinery
  of `GSTFiniteLinePointAlgebra.lean` — `lineIndexOfGeneric`,
  `lineComponentOf`, the no-intermediate law — pins the component and the
  chart pair of the line); (2) TWO-CHART CONSISTENCY — the section's ring
  homomorphism, read through the two charts of its line, carries reciprocal
  coordinates (the `Away.mk`-arithmetic of
  `GSTFiniteLineSmoothness.lean` §7.A at the partner ratio
  `chartRetracts_chartRatio`'s witnesses); (3) ASSEMBLY — the full equiv
  `ComplexPoint (finiteLineWorld M) ≃ Σ _ : Fin M, Option ℂ` from the
  per-chart classification `chartPointSpaceEquiv` + injectivity of
  `coordPoint`, then `finiteLineAnalytification :=
  finiteLineAnalytificationOfGate M gate` with the space receipt — the
  unconditional `finiteLineAnalytification` name stays reserved for that
  wave (the route-H capstone's GATE-A consumes `A` + `hspace` as inputs,
  which `finiteLineAnalytificationOfGate` +
  `finiteLineAnalytificationOfGate_space` already discharge).
-/
end -- noncomputable section
