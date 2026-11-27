import Mathlib
import HCUniverse2.GSTFiniteLineAnalytification
import HCUniverse2.GSTFiniteLinePointAlgebra
import HCUniverse2.GSTFiniteLineSmoothness
import HCUniverse2.GSTFiniteLineRiemann
import HCUniverse2.GSTFiniteLineOverBase

/-!
# THE FINITE-LINE POINTS GATE — THE COVER STRIKE (wave 7-B, GATE-A)

The discharge assault on the last open gate of Task 2 —
`FiniteLinePointsGate M` (`GSTFiniteLineAnalytification.lean:403`), the
classification of the finite-line world's complex points
`ComplexPoint (finiteLineWorld M) ≃ Σ _ : Fin M, Option ℂ`.

This module delivers the maximal coherent PREFIX of the prior wave's
NEXT-WAVE BATTLE MAP (`GSTFiniteLineAnalytification.lean:553-571`), with
zero `sorry` and zero new axioms:

* **§1 THE COVER STRIKE (battle-map step 1, the point level)** — every
  complex point of the world has its image point covered by the
  variables: some `q (X j)` does not vanish at the section's underlying
  image point (`finiteLineComplexPoint_cover`, the frozen name, riding
  the green `exists_variable_not_mem` of the prime-lattice module), with
  the `D₊`-membership form at the pinned `Proj.basicOpen`
  (`finiteLineComplexPoint_cover_basicOpen`, through the pinned
  `Proj.mem_basicOpen` and `HomogeneousIdeal.mem_iff`).  The supporting
  cross-block law (`finiteLinePoint_avoids_crossBlock_mem`) is the
  prime-lattice module's own `eq_lineGenericPoint_of_le` core pattern
  (the cross-product vanishing `crossMul_eq_zero` plus the point's
  primality), and the same-block law
  (`finiteLinePoint_avoids_same_block`) is the exactly-one-line
  uniqueness at the avoidance level.
* **§2 THE UNIQUE LINE (battle-map step 1, the component level)** — the
  line index `finiteLinePointLineIndex` of a world point (the `choose`
  of the cover witness, the `lineIndexOfGeneric` discipline of the
  prime-lattice module transplanted at the general point level), with
  the well-definedness receipt
  (`finiteLinePointLineIndex_of_avoids`: every avoided variable's block
  IS the line index), the generic-ideal containment
  (`finiteLinePoint_lineGenericIdeal_le`: the point's ideal contains its
  line's generic ideal — the span-induction of the green corpus), the
  ON-LINE law (`finiteLinePoint_on_line`: every point of the world
  lies on its line, through the green order bridge `le_iff_ideal`), the
  EXACTLY-ONE-LINE law (`finiteLinePoint_line_unique`: a point cannot
  lie on two distinct lines — the all-variables/irrelevant contradiction
  of the green `exists_unique_generic_above` core), the packaged
  characterization (`finiteLinePoint_on_line_iff`), and the line's
  CHART PAIR territory (`finiteLinePoint_avoids_chartPair`: the point
  avoids the left or the right chart variable of its own line — the
  parity split of the cover witness).
* **§3 THE SECTION-SIDE LINE MACHINERY** — the image point of a complex
  point (`finiteLineComplexPointImage`, with the definitional receipt
  `finiteLineComplexPointImage_eq`), the section's line index
  (`finiteLineComplexPointLineIndex`, the first component of the gate's
  forward reading), the section's ON-LINE law and its packaged
  characterization, and the section's chart-pair territory in the
  `D₊`-membership form (`finiteLineComplexPoint_line_chart`).

## The honest residual (the disclosed gap)

The gate itself — `finiteLinePointsGate M`, the full equiv
`ComplexPoint (finiteLineWorld M) ≃ Σ _ : Fin M, Option ℂ`, and
consequently the frozen unconditional exports
`finiteLineAnalytificationUnconditional` /
`finiteLineAnalytificationUnconditional_space` — is NOT stated in this
module, per the honesty law (a stated-but-unproved declaration is a
death penalty; the piece that is out of reach is not stated).
STATUS RECEIPT (wave 8, superseding the prior wave's battle map): the
gate named below was subsequently CONSTRUCTED and DISCHARGED in
`GSTFiniteLinePointsGateDischarge.lean` -- the explicit `Equiv.mk`
of that file, CI-green at `2152f70` and `26e0c81` (all eight
finite-line lanes SUCCESS, zero sorry).  The residual list below is
the pre-wave-8 honesty ledger, retained verbatim; it carries no
current status.  The pre-wave-8 residual was:

* **battle-map step (2) TWO-CHART CONSISTENCY and step (3) ASSEMBLY**
  both require the DECOMPOSITION direction: reading an arbitrary
  section `p : complexBase ⟶ Proj (lineGrading M)` through the away
  charts — i.e. factoring `p` through `Proj.awayι`, the universal
  property of `Proj` for morphisms INTO `Proj`.  The pinned Mathlib
  (`research/pin/mathlib-51e6992/Basic.lean`) provides only the
  CONSTRUCTION direction (`Proj.fromOfGlobalSections` and its
  glueing), with no converse or extensional characterization, and the
  corpus has never decomposed an arbitrary `complexBase ⟶ Proj`
  (the corpus's only constructions are the chart-side ones of the
  green `chartPointHomOf`).  The residue therefore also needs: the
  per-line two-chart coordinate consistency, the coordinate reading
  (the second component of the gate's forward map), and the two
  inverse laws of the equiv.
* The SURJECTIVE direction of the classification remains green in the
  prior module (`coordPoint`, `GSTFiniteLineAnalytification.lean:332`
  — every two-chart coordinate is a genuine complex point), and the
  per-chart affine classification of chart points is green there
  (`chartPointSpaceEquiv`).  This module's §1-§3 add the cover and the
  unique-line pinning that the decomposition wave will consume.

## What rides which green corpus theorem

`exists_variable_not_mem`, `crossMul_eq_zero`, `mem_lineGenericIdeal`,
`lineGenericIdeal` (with its definitional `rw`-unfold),
`lineGenericPoint_asIdeal`, `le_iff_ideal`,
`irrelevant_le_of_mem_variables`, the point fields
`asHomogeneousIdeal`/`isPrime`/`not_irrelevant_le` and the local
`specializationOrder` instance (the prime-lattice module's own §3
discipline, `GSTFiniteLinePointAlgebra.lean:802`); the chart pair
`lineLeftChart`/`lineRightChart` and the gate interface
`FiniteLinePointsGate`/`finiteLineAnalytificationOfGate`/
`finiteLineAnalytificationOfGate_space`/`coordPoint`
(`GSTFiniteLineAnalytification.lean:257/:261/:403/:412/:423/:332`); the
pinned Mathlib `Proj.basicOpen`/`Proj.mem_basicOpen`
(`research/pin/mathlib-51e6992/Basic.lean:54/:58`) and
`HomogeneousIdeal.mem_iff`
(`research/pin/mathlib-51e6992/GradedAlgebra_Homogeneous_Ideal.lean:102`,
corpus-green at `GSTClassicalHodgePointClosureRelativeCut.lean:219`).

Binder discipline of the lane (the finite-point template's own law):
every declaration below that mentions `M` takes `(M : ℕ) [NeZero M]`
as its leading binders.

Honesty ledger: zero `sorry`, zero new axioms, zero `native_decide`.
The GitHub CI lane of this module owns the kernel check.
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 20000
set_option trace.profiler true

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
open GSTFiniteLineAnalytification
open GSTFiniteLinePointAlgebra

-- The prime-lattice module's own §3 discipline: the specialization
-- order on the world's points (reverse inclusion of homogeneous
-- ideals, `le_iff_ideal`), activated locally so that every `≤` below
-- is the order `GSTFiniteLinePointAlgebra` states its lemmas against.
attribute [local instance] specializationOrder

namespace GSTFiniteLinePointsGate

variable (M : ℕ) [NeZero M]
-- Lane binder discipline (the finite-point template's own law): every
-- declaration below that mentions `M` re-binds `(M : ℕ) [NeZero M]`
-- explicitly at its head (the section variable above is kept per the lane
-- law and shadowed by the explicit binders, so the shipped signatures are
-- fully deterministic).

/-! ## §0 THE SECTION IMAGE POINT -/

/-- **THE IMAGE POINT OF A COMPLEX POINT** — the point of the line world
hit by the section's underlying map at a base point (the complex base
is the one-point `Spec ℂ`, so this is the section's unique image
point; the statement is honestly quantified over the base point).  The
carrier-`X` defeq (`(finiteLineWorld M).X` vs `finiteLineScheme M`,
the wave-3-C `finiteLineWorld_hWX` `rfl` class) is discharged inside
this single definition, with the definitional receipt below. -/
noncomputable def finiteLineComplexPointImage (M : ℕ) [NeZero M]
    (p : ComplexPoint (finiteLineWorld M)) (x : complexBase) :
    finiteLineScheme M :=
  p.1 x

/-- The definitional receipt: the image point IS the section's
underlying map applied at the base point. -/
theorem finiteLineComplexPointImage_eq (M : ℕ) [NeZero M]
    (p : ComplexPoint (finiteLineWorld M)) (x : complexBase) :
    finiteLineComplexPointImage M p x = p.1 x := rfl

/-! ## §1 THE COVER STRIKE (battle-map step 1, the point level) -/

/-- **THE CROSS-BLOCK LAW** — a point that avoids some block's variable
(`q (X a) ∉` its ideal) contains every other-block variable: the
cross-monomial product vanishes (`crossMul_eq_zero`, the defining
relation of the M disjoint lines) and the point's ideal is prime, so
one factor must be inside.  The proof is the prime-lattice module's
own `eq_lineGenericPoint_of_le` core pattern
(`GSTFiniteLinePointAlgebra.lean:905-914`), verbatim in lemma calls. -/
theorem finiteLinePoint_avoids_crossBlock_mem (M : ℕ) [NeZero M]
    (y : finiteLineScheme M) {a b : Fin (2 * M)}
    (ha : lineQuotientMap M (MvPolynomial.X a) ∉
      y.asHomogeneousIdeal.toIdeal)
    (hab : a.val / 2 ≠ b.val / 2) :
    lineQuotientMap M (MvPolynomial.X b) ∈
      y.asHomogeneousIdeal.toIdeal := by
  have hzero : lineQuotientMap M (MvPolynomial.X a) *
      lineQuotientMap M (MvPolynomial.X b) = 0 :=
    crossMul_eq_zero M hab
  have hmem : lineQuotientMap M (MvPolynomial.X a) *
      lineQuotientMap M (MvPolynomial.X b) ∈
      y.asHomogeneousIdeal.toIdeal := by
    rw [hzero]; exact Submodule.zero_mem _
  rcases y.isPrime.mem_or_mem hmem with h | h
  · exact absurd h ha
  · exact h

/-- **THE SAME-BLOCK LAW (the exactly-one-line uniqueness at the
avoidance level)** — two variables both avoided by one point share
their block: otherwise the cross-block law would put the second inside
the ideal. -/
theorem finiteLinePoint_avoids_same_block (M : ℕ) [NeZero M]
    (y : finiteLineScheme M) {a b : Fin (2 * M)}
    (ha : lineQuotientMap M (MvPolynomial.X a) ∉
      y.asHomogeneousIdeal.toIdeal)
    (hb : lineQuotientMap M (MvPolynomial.X b) ∉
      y.asHomogeneousIdeal.toIdeal) :
    a.val / 2 = b.val / 2 := by
  by_contra hne
  exact hb (finiteLinePoint_avoids_crossBlock_mem M y ha hne)

/-- **THE COVER (the frozen name)** — every complex point of the finite
line world has its image point covered by the variables: some `q (X j)`
does not vanish at the section's image point, i.e. the image point lies
in the chart territory `D₊(q (X j))` of some line's chart.  The proof
is the green prime-lattice cover `exists_variable_not_mem`
(`GSTFiniteLinePointAlgebra.lean:885`) consumed at the image point. -/
theorem finiteLineComplexPoint_cover (M : ℕ) [NeZero M]
    (p : ComplexPoint (finiteLineWorld M)) (x : complexBase) :
    ∃ j : Fin (2 * M), lineQuotientMap M (MvPolynomial.X j) ∉
      (finiteLineComplexPointImage M p x).asHomogeneousIdeal.toIdeal :=
  exists_variable_not_mem M (finiteLineComplexPointImage M p x)

/-- The `D₊`-membership bridge: a non-vanishing variable puts the point
inside the pinned basic open (the pinned `Proj.mem_basicOpen`, an
`Iff.rfl` simp lemma, plus the pinned `HomogeneousIdeal.mem_iff`
degree-cast between the homogeneous-ideal and plain-ideal readings). -/
private theorem basicOpen_of_avoids (M : ℕ) [NeZero M] (y : finiteLineScheme M)
    {j : Fin (2 * M)} (hj : lineQuotientMap M (MvPolynomial.X j) ∉
      y.asHomogeneousIdeal.toIdeal) :
    y ∈ Proj.basicOpen (lineGrading M)
      (lineQuotientMap M (MvPolynomial.X j)) := by
  rw [Proj.mem_basicOpen]
  intro hmem
  exact hj (HomogeneousIdeal.mem_iff.mpr hmem)

/-- **THE COVER, THE `D₊`-MEMBERSHIP FORM** — the section's image
point lies in the chart territory `D₊(q (X j))` of some chart of some
line: the battle map's own cover statement. -/
theorem finiteLineComplexPoint_cover_basicOpen (M : ℕ) [NeZero M]
    (p : ComplexPoint (finiteLineWorld M)) (x : complexBase) :
    ∃ j : Fin (2 * M), finiteLineComplexPointImage M p x ∈
      Proj.basicOpen (lineGrading M)
        (lineQuotientMap M (MvPolynomial.X j)) := by
  obtain ⟨j, hj⟩ := finiteLineComplexPoint_cover M p x
  exact ⟨j, basicOpen_of_avoids M _ hj⟩

/-! ## §2 THE UNIQUE LINE (battle-map step 1, the component level) -/

/-- **THE LINE INDEX OF A WORLD POINT** — the block of the cover
witness: the `choose` of the green cover
`exists_variable_not_mem`, halved into `Fin M`.  This is the
`lineIndexOfGeneric` discipline (`GSTFiniteLinePointAlgebra.lean:1317`)
transplanted at the general point level: the index of the unique line
carrying the point. -/
noncomputable def finiteLinePointLineIndex (M : ℕ) [NeZero M]
    (y : finiteLineScheme M) : Fin M :=
  ⟨(Classical.choose (exists_variable_not_mem M y)).val / 2, by
    have ha := (Classical.choose (exists_variable_not_mem M y)).isLt
    omega⟩

/-- The definitional receipt of the index's value (the block of the
witness). -/
theorem finiteLinePointLineIndex_val (M : ℕ) [NeZero M]
    (y : finiteLineScheme M) :
    (finiteLinePointLineIndex M y).val =
      (Classical.choose (exists_variable_not_mem M y)).val / 2 := rfl

/-- **THE WITNESS RECEIPT** — the chosen cover variable does not
vanish at the point (the `choose_spec` receipt, the
`lineIndexOfGeneric_spec` pattern). -/
theorem finiteLinePointLineIndex_choose (M : ℕ) [NeZero M]
    (y : finiteLineScheme M) :
    lineQuotientMap M (MvPolynomial.X
      (Classical.choose (exists_variable_not_mem M y))) ∉
      y.asHomogeneousIdeal.toIdeal :=
  Classical.choose_spec (exists_variable_not_mem M y)

/-- **THE WELL-DEFINEDNESS RECEIPT** — every variable avoided by the
point has the line index as its block (the cover witnesses all live in
one block, by the same-block law). -/
theorem finiteLinePointLineIndex_of_avoids (M : ℕ) [NeZero M]
    (y : finiteLineScheme M) {a : Fin (2 * M)}
    (ha : lineQuotientMap M (MvPolynomial.X a) ∉
      y.asHomogeneousIdeal.toIdeal) :
    a.val / 2 = (finiteLinePointLineIndex M y).val := by
  rw [finiteLinePointLineIndex_val]
  exact (@finiteLinePoint_avoids_same_block M _ y
    (Classical.choose (exists_variable_not_mem M y)) a
    (finiteLinePointLineIndex_choose M y) ha).symm

/-- **THE GENERIC-IDEAL CONTAINMENT** — the point's ideal contains its
line's generic ideal: the span-induction of the green corpus (the
`hgen` core of `eq_lineGenericPoint_of_le`,
`GSTFiniteLinePointAlgebra.lean:903-914` — the generic ideal's span
generators are the other-block variables, and the cross-block law puts
each of them inside the point's ideal through the witness). -/
theorem finiteLinePoint_lineGenericIdeal_le (M : ℕ) [NeZero M]
    (y : finiteLineScheme M) :
    lineGenericIdeal M (finiteLinePointLineIndex M y) ≤
      y.asHomogeneousIdeal.toIdeal := by
  rw [lineGenericIdeal, Ideal.span_le]
  rintro _ ⟨b, rfl⟩
  refine @finiteLinePoint_avoids_crossBlock_mem M _ y
    (Classical.choose (exists_variable_not_mem M y)) (b : Fin (2 * M))
    (finiteLinePointLineIndex_choose M y) ?_
  intro hcon
  exact b.2 (hcon.symm.trans (finiteLinePointLineIndex_val M y).symm)

/-- **THE ON-LINE LAW** — every point of the line world lies on its
line: below the line's generic point in the specialization order
(the green order bridge `le_iff_ideal` at the containment above). -/
theorem finiteLinePoint_on_line (M : ℕ) [NeZero M]
    (y : finiteLineScheme M) :
    y ≤ lineGenericPoint M (finiteLinePointLineIndex M y) :=
  (le_iff_ideal M y
    (lineGenericPoint M (finiteLinePointLineIndex M y))).mpr
    (by
      rw [lineGenericPoint_asIdeal]
      exact finiteLinePoint_lineGenericIdeal_le M y)

/-- **THE EXACTLY-ONE-LINE LAW** — a point cannot lie on two distinct
lines: if the point were below two generic points, then every variable
would be inside its ideal (each variable is outside one of the two
blocks), so the irrelevant ideal would be inside — contradicting the
point's relevance.  The proof is the green
`exists_unique_generic_above` core
(`GSTFiniteLinePointAlgebra.lean:1361-1370`), verbatim in lemma calls. -/
theorem finiteLinePoint_line_unique (M : ℕ) [NeZero M]
    (y : finiteLineScheme M) {i i' : Fin M}
    (hi : y ≤ lineGenericPoint M i) (hi' : y ≤ lineGenericPoint M i') :
    i = i' := by
  by_contra hne
  have hIi : lineGenericIdeal M i ≤ y.asHomogeneousIdeal.toIdeal := by
    have h := (le_iff_ideal M y (lineGenericPoint M i)).mp hi
    rwa [lineGenericPoint_asIdeal] at h
  have hIi' : lineGenericIdeal M i' ≤ y.asHomogeneousIdeal.toIdeal := by
    have h := (le_iff_ideal M y (lineGenericPoint M i')).mp hi'
    rwa [lineGenericPoint_asIdeal] at h
  apply y.not_irrelevant_le
  show (HomogeneousIdeal.irrelevant (lineGrading M)).toIdeal ≤
    y.asHomogeneousIdeal.toIdeal
  exact irrelevant_le_of_mem_variables M _ (fun a => by
    rcases eq_or_ne (a.val / 2) i.val with hblock | hblock
    · exact hIi' (mem_lineGenericIdeal M i'
        (fun hcon => hne (Fin.ext (hcon.symm.trans hblock).symm)))
    · exact hIi (mem_lineGenericIdeal M i hblock))

/-- **THE PACKAGED LINE CHARACTERIZATION** — lying on line `i` is the
same as `i` being the point's line index (the on-line law plus the
exactly-one-line law). -/
theorem finiteLinePoint_on_line_iff (M : ℕ) [NeZero M]
    (y : finiteLineScheme M) (i : Fin M) :
    y ≤ lineGenericPoint M i ↔ i = finiteLinePointLineIndex M y := by
  constructor
  · intro hi
    exact finiteLinePoint_line_unique M y hi (finiteLinePoint_on_line M y)
  · intro h
    rw [h]
    exact finiteLinePoint_on_line M y

/-- **THE CHART-PAIR TERRITORY OF THE LINE** — the point avoids the
left or the right chart variable of its own line: the cover witness
lives in the index's block, and its parity puts it at the block's left
or right chart index (the world's chart pair
`lineLeftChart`/`lineRightChart`,
`GSTFiniteLineAnalytification.lean:257-261`). -/
theorem finiteLinePoint_avoids_chartPair (M : ℕ) [NeZero M]
    (y : finiteLineScheme M) :
    lineQuotientMap M (MvPolynomial.X
        (lineLeftChart M (finiteLinePointLineIndex M y))) ∉
      y.asHomogeneousIdeal.toIdeal ∨
    lineQuotientMap M (MvPolynomial.X
        (lineRightChart M (finiteLinePointLineIndex M y))) ∉
      y.asHomogeneousIdeal.toIdeal := by
  obtain ⟨a, ha⟩ := exists_variable_not_mem M y
  have hidx : a.val / 2 = (finiteLinePointLineIndex M y).val :=
    finiteLinePointLineIndex_of_avoids M y ha
  have hmod : a.val % 2 = 0 ∨ a.val % 2 = 1 := by omega
  rcases hmod with h0 | h1
  · refine Or.inl ?_
    have hL : (lineLeftChart M (finiteLinePointLineIndex M y)).val =
        2 * (finiteLinePointLineIndex M y).val := rfl
    rw [show lineLeftChart M (finiteLinePointLineIndex M y) = a from
      Fin.ext (by omega)]
    exact ha
  · refine Or.inr ?_
    have hR : (lineRightChart M (finiteLinePointLineIndex M y)).val =
        2 * (finiteLinePointLineIndex M y).val + 1 := rfl
    rw [show lineRightChart M (finiteLinePointLineIndex M y) = a from
      Fin.ext (by omega)]
    exact ha

/-! ## §3 THE SECTION-SIDE LINE MACHINERY (the first component of the
gate's forward reading) -/

/-- **THE LINE INDEX OF A COMPLEX POINT** — the line index of the
section's image point: the first component of the gate's forward
coordinate reading (the second component — the chart coordinate — is
the decomposition wave's residue). -/
noncomputable def finiteLineComplexPointLineIndex (M : ℕ) [NeZero M]
    (p : ComplexPoint (finiteLineWorld M)) (x : complexBase) : Fin M :=
  finiteLinePointLineIndex M (finiteLineComplexPointImage M p x)

/-- **THE SECTION'S ON-LINE LAW** — the image point of every complex
point of the world lies on its line. -/
theorem finiteLineComplexPoint_on_line (M : ℕ) [NeZero M]
    (p : ComplexPoint (finiteLineWorld M)) (x : complexBase) :
    finiteLineComplexPointImage M p x ≤
      lineGenericPoint M (finiteLineComplexPointLineIndex M p x) :=
  finiteLinePoint_on_line M (finiteLineComplexPointImage M p x)

/-- **THE SECTION'S PACKAGED LINE CHARACTERIZATION** — the image point
of the section lies on line `i` exactly when `i` is the section's line
index. -/
theorem finiteLineComplexPoint_on_line_iff (M : ℕ) [NeZero M]
    (p : ComplexPoint (finiteLineWorld M)) (x : complexBase)
    (i : Fin M) :
    finiteLineComplexPointImage M p x ≤ lineGenericPoint M i ↔
      i = finiteLineComplexPointLineIndex M p x :=
  finiteLinePoint_on_line_iff M (finiteLineComplexPointImage M p x) i

/-- **THE SECTION'S CHART-PAIR TERRITORY** — the image point of every
complex point of the world lies in the chart territory
(`D₊`-membership) of the left or the right chart of its own line: the
cover strike's chart landing, the honest maximal form of the battle
map's step (1). -/
theorem finiteLineComplexPoint_line_chart (M : ℕ) [NeZero M]
    (p : ComplexPoint (finiteLineWorld M)) (x : complexBase) :
    finiteLineComplexPointImage M p x ∈
      Proj.basicOpen (lineGrading M)
        (lineQuotientMap M (MvPolynomial.X
          (lineLeftChart M (finiteLineComplexPointLineIndex M p x)))) ∨
    finiteLineComplexPointImage M p x ∈
      Proj.basicOpen (lineGrading M)
        (lineQuotientMap M (MvPolynomial.X
          (lineRightChart M (finiteLineComplexPointLineIndex M p x)))) := by
  rcases finiteLinePoint_avoids_chartPair M
    (finiteLineComplexPointImage M p x) with h | h
  · exact Or.inl (basicOpen_of_avoids M _ h)
  · exact Or.inr (basicOpen_of_avoids M _ h)

/-! ## §4 THE GATE STATUS (the residual interface, re-checked) -/

#check FiniteLinePointsGate
#check finiteLineAnalytificationOfGate
#check finiteLineAnalytificationOfGate_space
#check coordPoint

/-! ## Receipts -/

#check finiteLineComplexPointImage
#check finiteLineComplexPointImage_eq
#check finiteLinePoint_avoids_crossBlock_mem
#check finiteLinePoint_avoids_same_block
#check finiteLineComplexPoint_cover
#check finiteLineComplexPoint_cover_basicOpen
#check finiteLinePointLineIndex
#check finiteLinePointLineIndex_val
#check finiteLinePointLineIndex_choose
#check finiteLinePointLineIndex_of_avoids
#check finiteLinePoint_lineGenericIdeal_le
#check finiteLinePoint_on_line
#check finiteLinePoint_line_unique
#check finiteLinePoint_on_line_iff
#check finiteLinePoint_avoids_chartPair
#check finiteLineComplexPointLineIndex
#check finiteLineComplexPoint_on_line
#check finiteLineComplexPoint_on_line_iff
#check finiteLineComplexPoint_line_chart

#print axioms finiteLineComplexPointImage
#print axioms finiteLineComplexPointImage_eq
#print axioms finiteLinePoint_avoids_crossBlock_mem
#print axioms finiteLinePoint_avoids_same_block
#print axioms finiteLineComplexPoint_cover
#print axioms finiteLineComplexPoint_cover_basicOpen
#print axioms finiteLinePointLineIndex
#print axioms finiteLinePointLineIndex_val
#print axioms finiteLinePointLineIndex_choose
#print axioms finiteLinePointLineIndex_of_avoids
#print axioms finiteLinePoint_lineGenericIdeal_le
#print axioms finiteLinePoint_on_line
#print axioms finiteLinePoint_line_unique
#print axioms finiteLinePoint_on_line_iff
#print axioms finiteLinePoint_avoids_chartPair
#print axioms finiteLineComplexPointLineIndex
#print axioms finiteLineComplexPoint_on_line
#print axioms finiteLineComplexPoint_on_line_iff
#print axioms finiteLineComplexPoint_line_chart

end GSTFiniteLinePointsGate

/-! DRAFT STATUS (wave 7-B, the finite-line points gate lane's cover
strike; the first assault on the last open gate of Task 2):
* Source: the prior wave's NEXT-WAVE BATTLE MAP
  (`GSTFiniteLineAnalytification.lean:553-571`) — this module delivers
  its step (1) COVER in full (at the point level: the variable cover
  of the section's image point, the `D₊`-membership form, the unique
  line with its well-definedness, on-line/exactly-one-line laws and the
  chart-pair territory), and NOTHING of steps (2)/(3) — see the honest
  residual below.  Template: `GSTFiniteLinePointAlgebra.lean` (the
  prime-lattice module whose lemma calls the proofs ride verbatim) and
  `GSTFiniteLineAnalytification.lean` (the lane's binder discipline and
  the chart pair).
* Declarations: 20 (3 noncomputable defs, 17 theorems; 1 of the theorems
  private), in dependency order; every M-mentioning declaration re-binds
  `(M : ℕ) [NeZero M]`.
* External names, every one verified against its providing module (or
  the pinned Mathlib): `ComplexPoint`
  (GSTGeometricRealizationStage2F.lean:51), `finiteLineWorld`
  (GSTFiniteLineOverBase.lean:331), `finiteLineScheme`
  (GSTFiniteLineWorldCarrier.lean:65), `complexBase`
  (GSTProjectiveOverC.lean:37), `lineQuotientMap`/`lineGrading`
  (GSTFiniteLineRing.lean:126/:155), `exists_variable_not_mem`
  `crossMul_eq_zero` `mem_lineGenericIdeal` `lineGenericIdeal`
  `lineGenericPoint_asIdeal` `le_iff_ideal`
  `irrelevant_le_of_mem_variables` and the point fields
  `asHomogeneousIdeal`/`isPrime`/`not_irrelevant_le`
  (GSTFiniteLinePointAlgebra.lean:885/:71/:330/:326/:779/:807/:868 and
  the structure at the pin's
  research/pin/mathlib-51e6992/ProjectiveSpectrum_Topology.lean:54-57),
  the local `specializationOrder` instance command
  (GSTFiniteLinePointAlgebra.lean:802, verbatim), `lineLeftChart`
  `lineRightChart` `FiniteLinePointsGate`
  `finiteLineAnalytificationOfGate`
  `finiteLineAnalytificationOfGate_space` `coordPoint`
  (GSTFiniteLineAnalytification.lean:257/:261/:403/:412/:423/:332),
  `Proj.basicOpen`/`Proj.mem_basicOpen`
  (research/pin/mathlib-51e6992/Basic.lean:54/:58; corpus-green usage
  GSTFinitePointWorldCarrier.lean:570), `HomogeneousIdeal.mem_iff`
  (research/pin/mathlib-51e6992/GradedAlgebra_Homogeneous_Ideal.lean:102;
  corpus-green usages GSTClassicalHodgePointClosureRelativeCut.lean:219),
  `Submodule.zero_mem` (GSTFiniteLinePointAlgebra.lean:911), `absurd`
  (GSTFiniteLinePointAlgebra.lean:1309), `Classical.choose`/`choose_spec`
  (GSTFiniteLinePointAlgebra.lean:1317-1324 pattern), `eq_or_ne`
  (GSTFiniteLinePointAlgebra.lean:902), `Fin.ext`
  (GSTFiniteLineSmoothness.lean:189), `a.isLt`
  (GSTFiniteLinePointAlgebra.lean:881), `Ideal.span_le`
  (GSTFiniteLinePointAlgebra.lean:904), `omega`/`rcases`/`rintro`/
  `obtain`/`rwa`/`by_contra` (corpus-battle-tested tactics).
* Every opened namespace is transitively imported: `CategoryTheory`,
  `AlgebraicGeometry` (`import Mathlib`); `GSTProjectiveOverC`,
  `GSTFiniteLineWorldCarrier`, `GSTFiniteLineRing`,
  `GSTNativeCodimensionCyclePresentation`,
  `GSTGeometricRealizationStage2D` (via `GSTFiniteLinePointAlgebra`,
  whose own wave-5-A-audited opens certify the chain);
  `GSTGeometricRealizationStage2F` (via
  `GSTFiniteLineAnalytification`); `GSTFiniteLineOverBase`,
  `GSTFiniteLineAnalytification`, `GSTFiniteLinePointAlgebra` (direct
  imports) — the wave-5-A law.  `GSTFiniteLineSmoothness` and
  `GSTFiniteLineRiemann` are imported (the mission's frozen import
  list) but not opened (nothing is consumed from them by name).
* THE HONEST RESIDUAL (why `finiteLinePointsGate M` — the full equiv —
  and the frozen unconditional exports
  `finiteLineAnalytificationUnconditional`/
  `finiteLineAnalytificationUnconditional_space` are NOT stated here):
  the remaining battle-map steps (2) TWO-CHART CONSISTENCY and (3)
  ASSEMBLY both live on the DECOMPOSITION of an arbitrary section
  `p : complexBase ⟶ Proj (lineGrading M)` into chart data — factoring
  `p` through `Proj.awayι`, which is the universal property of `Proj`
  for morphisms INTO `Proj`: the pinned Mathlib
  (research/pin/mathlib-51e6992/Basic.lean:443) provides only the
  CONSTRUCTION direction (`Proj.fromOfGlobalSections`), with no
  converse, and the corpus has never decomposed an arbitrary section
  (its only `complexBase ⟶ (finiteLineWorld M).X` constructions are
  the chart-side `chartPointHomOf` — verified by repo-wide grep).
  Concretely, the pre-wave-8 residual (DISCHARGED by the wave-8 gate
  construction in `GSTFiniteLinePointsGateDischarge.lean`, CI-green
  at `2152f70`/`26e0c81`): (i) the section's chart-coordinate reading
  (the second component of the gate's forward map, i.e. pulling the
  section back through the away chart); (ii) the per-line two-chart
  coordinate consistency (reciprocal coordinates at the partner
  ratio); (iii) the two inverse laws of the equiv; (iv) the
  independence of the image point from the base point (the base is
  the one-point `Spec ℂ`, so the honest statements above quantify over
  the base point instead).
* Static verification: no `sorry`/`admit`/`native_decide`/new axioms
  (grep-checked); parenthesis balance depth 0 (docstring-excluded);
  namespace/end pairing; declaration-name uniqueness (repo-wide grep:
  all 20 names fresh).  NOT COMPILED (no local Lean by repo law) — the
  designated CI repair points are (a) the carrier-`X` defeq of
  `finiteLineComplexPointImage` (the wave-3-C `finiteLineWorld_hWX`
  `rfl` class, discharged inside the single def and receipted by
  `finiteLineComplexPointImage_eq`), (b) the `p.1 x` coercion shape
  (the corpus's own `finiteLineCycle M x` application class,
  GSTFiniteLineCycleCorrespondence.lean:87-95), and (c) the
  `rw [Proj.mem_basicOpen]` matching at the world's points (the pinned
  `Iff.rfl` simp lemma, first corpus consumption at this grading).
* NEXT-WAVE BATTLE MAP (unchanged from the prior wave, with this
  module's contributions slotted): (2) TWO-CHART CONSISTENCY — the
  section's ring homomorphism, read through the two charts of its
  line, carries reciprocal coordinates (needs the away-chart
  factorization of the section; the `Away.mk`-arithmetic of
  `GSTFiniteLineSmoothness.lean` §7.A at the partner ratio
  `chartRetracts_chartRatio`'s witnesses); (3) ASSEMBLY — the full
  equiv `ComplexPoint (finiteLineWorld M) ≃ Σ _ : Fin M, Option ℂ`
  from the per-chart classification `chartPointSpaceEquiv` + the
  coordinate reading, then `finiteLineAnalytificationUnconditional :=
  finiteLineAnalytificationOfGate M (finiteLinePointsGate M)` with the
  `rfl` space receipt — this module's §1-§3 provide the line-index
  component and the cover/unique-line machinery that wave consumes.
-/
end -- noncomputable section
