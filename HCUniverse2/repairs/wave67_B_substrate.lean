import Mathlib
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import HCUniverse2.GSTFiniteLineRing
import HCUniverse2.GSTProjectiveOverC
import HCUniverse2.GSTFiniteLineWorldCarrier

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# WAVE 67-B — F3 STAGE 0 + STAGE 2: the smoothness substrate (paste section)

The F3 (smoothness) substrate lemmas of the finite-line world, per the frozen
wave-67 route (`repairs/wave67_A_smoothness_route.md`, sections Stage 0 and
Stage 2).  This is a STANDALONE PASTE-SECTION file: the preamble and namespace
follow the `GSTFiniteLineClosedImmersion.lean` pattern; the assembler pastes
the body into `GSTFiniteLineSmoothness.lean` (the F3 module) behind Stage 1
(W67-C, the chart equivalence).

## Contents

STAGE 0 (the shared substrate, twins of CI-green corpus lemmas):

* `linePartner` (T1) — the partner involution on `Fin (2*M)`: the other
  element of `j`'s coordinate block `{2b, 2b+1}`, with the spec lemmas
  `linePartner_ne` (≠ j), `linePartner_block` (same block: j'/2 = j/2),
  `linePartner_involution` (j'' = j);
* `lineCoverHomogeneousOneQ` / `lineCoverHomogeneousQ` (T2/T2') — the
  variables are homogeneous of degree 1 (the ∃-form feeds
  `Proj.iSup_basicOpen_eq_top'`, the degree-1 form feeds `awayι`);
* `lineCoverAdjoin` (T3) — the variables adjoin-generate the quotient over
  its degree-0 piece (the twin of the green `span_cover`,
  GSTFinitePointWorldCarrier.lean:202-215, lifted through
  `lineQuotientMap_surjective`);
* `blockEval` / `blockEval_mem_ker` / `blockEvalQuot` (T4/T5) — the block
  projection `ℂ[x_0..x_{2M-1}] → ℂ[t]` (X j ↦ 1, X j' ↦ t, everything else
  ↦ 0), which kills the cross ideal and hence descends to the quotient;
* `hzero` (T6) — constants through degree zero (the
  `SetLike.GradeZero.coe_algebraMap` fold).

STAGE 2 (the chart square — `chartRingHom` is an EXTERNAL W67-C PLUG, see
the §5 contract):

* `chart_awayι_comp'` — the standalone form: the away-chart of the structure
  map is the `Spec` of the canonical ℂ-structure composite of the chart;
* `chart_awayι_comp` — the plug-facing form (chartRingHom + its defining
  equation as explicit binders).

## Deviations from the route-map draft (all pin-verified, see the report)

1. `linePartner` is defined by the parity split `if j.val % 2 = 0 then
   j.val + 1 else j.val - 1`, NOT by `j.val ^^^ 1`: the pin's `omega` frontend
   (lean4 v4.33.0-rc2, src/Lean/Elab/Tactic/Omega/Frontend.lean) has NO
   `Nat.xor` support (xor terms become opaque atoms), so the draft's
   `⟨j.val ^^^ 1, by omega⟩` cannot compile.  The spec lemmas (ne/block/
   involution) are unchanged — all downstream uses (Stage 1's `chartRatio`,
   `blockEval`) go through the INDEX `linePartner M j` and these lemmas only.
2. `blockEvalQuot` uses `Ideal.Quotient.liftₐ (crossIdeal M) (blockEval M j)
   (pointwise)`: at the pin (Mathlib/RingTheory/Ideal/Quotient/Operations.lean:471)
   `liftₐ` has NO explicit base-ring argument and takes the POINTWISE
   hypothesis `∀ a ∈ I, f a = 0` — the CI-green carrier spelling
   (GSTFiniteLineWorldCarrier.lean:285-288), not the draft's `liftₐ ℂ … ≤ ker`
   spelling.
3. `blockEval` writes `MvPolynomial.X (0 : Fin 1)` (corpus style,
   GSTTruncatedWorldCohomologyRing.lean:103) instead of the draft's
   `MvPolynomial.X ()`: the unit-notation does not elaborate at `Fin 1`.
4. The `hm : 0 < 1` argument of `awayι` is the term `zero_lt_one` (the green
   ClosedImmersion spelling, GSTFiniteLineClosedImmersion.lean:226) instead
   of `by norm_num`.
5. THE `chartRingHom` CONTRACT (§5 below): the correct type is
   `ℂ →+* Away (lineGrading M) (q (X j))` (the chart's ℂ-STRUCTURE ring hom,
   route map Stage 1: `(fromZeroRingHom 𝒜 (Submonoid.powers f)).comp
   (algebraMap ℂ (𝒜 0))`), NOT `MvPolynomial (Fin 1) ℂ →+* Away …`: with the
   latter the chart-square statement is ill-typed (its RHS would live in
   `Spec ℂ[t]` while the LHS lands in `Spec ℂ`).

Honesty ledger: zero `sorry`, zero new axioms, zero `native_decide`.  Every
non-local name is pin-verified at Mathlib 51e6992efd06126df61a496bebf8f49482a4e129
(reference copies under research/pin/mathlib-51e6992/) or CI-green in the
corpus (file:line in each docstring).
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry CategoryTheory
open GSTProjectiveOverC GSTFiniteLineRing GSTFiniteLineWorldCarrier
open MvPolynomial DirectSum

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GSTFiniteLineSmoothness

/-! ## §1 Stage 0 (T1) — the partner involution on the coordinate indices -/

/-- **THE PARTNER INVOLUTION (T1)** — `linePartner M j` is the OTHER element
of `j`'s coordinate block `{X (2b), X (2b+1)}` (block `b = j / 2`).  The
route map's spelling is `j.val ^^^ 1`; here it is the parity split, which is
`omega`-provable at the pin (see Deviation 1 in the header).  The spec is
carried entirely by `linePartner_ne`, `linePartner_block` and
`linePartner_involution` below. -/
def linePartner (M : ℕ) [NeZero M] (j : Fin (2 * M)) : Fin (2 * M) :=
  ⟨if j.val % 2 = 0 then j.val + 1 else j.val - 1, by
    have h : j.val < 2 * M := j.isLt
    by_cases hj : j.val % 2 = 0
    · rw [if_pos hj]
      omega
    · rw [if_neg hj]
      omega⟩

/-- The value bridge (the corpus's `blockRot_val` pattern,
GSTFiniteLineWorldCarrier.lean:122-123: a `rfl` unfolding of a `Fin`-valued
def through its `val`). -/
theorem linePartner_val (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    (linePartner M j).val = if j.val % 2 = 0 then j.val + 1 else j.val - 1 :=
  rfl

/-- The partner of an even index is the next index (the block's odd
element). -/
theorem linePartner_val_even (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (hj : j.val % 2 = 0) : (linePartner M j).val = j.val + 1 := by
  rw [linePartner_val, if_pos hj]

/-- The partner of an odd index is the previous index (the block's even
element). -/
theorem linePartner_val_odd (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (hj : ¬ j.val % 2 = 0) : (linePartner M j).val = j.val - 1 := by
  rw [linePartner_val, if_neg hj]

/-- **T1 (ne)** — the partner is the OTHER element of the block. -/
theorem linePartner_ne (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    linePartner M j ≠ j := by
  intro h
  have hv : (linePartner M j).val = j.val := by rw [h]
  rw [linePartner_val] at hv
  by_cases hj : j.val % 2 = 0
  · rw [if_pos hj] at hv
    omega
  · rw [if_neg hj] at hv
    omega

/-- **T1 (block)** — the partner lives in the same coordinate block:
`j' / 2 = j / 2`.  This is the block-combinatorics input of
`blockEval_mem_ker` (§3) and of Stage 1's cross-pair bookkeeping. -/
theorem linePartner_block (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    (linePartner M j).val / 2 = j.val / 2 := by
  rw [linePartner_val]
  by_cases hj : j.val % 2 = 0
  · rw [if_pos hj]
    omega
  · rw [if_neg hj]
    omega

/-- **T1 (involution)** — partnering twice is the identity. -/
theorem linePartner_involution (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    linePartner M (linePartner M j) = j := by
  have hval : (linePartner M (linePartner M j)).val = j.val := by
    by_cases hj : j.val % 2 = 0
    · have hp : (linePartner M j).val = j.val + 1 := linePartner_val_even M j hj
      have hp' : ¬ (linePartner M j).val % 2 = 0 := by
        rw [hp]
        omega
      rw [linePartner_val_odd M (linePartner M j) hp', hp]
      omega
    · have hp : (linePartner M j).val = j.val - 1 := linePartner_val_odd M j hj
      have hp' : (linePartner M j).val % 2 = 0 := by
        rw [hp]
        omega
      rw [linePartner_val_even M (linePartner M j) hp', hp]
      omega
  exact Fin.ext hval

/-! ## §2 Stage 0 (T2/T2'/T3) — the D₊(q (X j)) cover twins -/

/-- **THE COVER TWIN (DEGREE ONE, T2')** — every variable's image in the
quotient grading is homogeneous of degree 1: the `f_deg` argument of
`Proj.awayι` / `Proj.basicOpenIsoSpec` at `f := q (X j)`, `m := 1`.  The
membership core is the substrate's `lineQuotientMap_mem_lineGrading`
(GSTFiniteLineRing.lean:167-171) fed by `isHomogeneous_X`
(MvPolynomial/Homogeneous.lean:178, `R` explicit) through
`mem_homogeneousSubmodule` (:101, `Iff.rfl`) — the substrate's own
`crossMonomials_homogeneous` cascade (GSTFiniteLineRing.lean:93-94). -/
theorem lineCoverHomogeneousOneQ (M : ℕ) (j : Fin (2 * M)) :
    lineQuotientMap M (MvPolynomial.X j) ∈ lineGrading M 1 :=
  lineQuotientMap_mem_lineGrading M 1 (MvPolynomial.X j)
    ((MvPolynomial.mem_homogeneousSubmodule 1 (MvPolynomial.X j)).mpr
      (MvPolynomial.isHomogeneous_X ℂ j))

/-- **THE COVER TWIN (HOMOGENEITY, T2)** — the ∃-degree form: the `hfn` side
condition of `Proj.iSup_basicOpen_eq_top'`
(Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:97-99) at
`f := fun j => lineQuotientMap M (MvPolynomial.X j)` (the twin of the green
`variables_homogeneous`, GSTFinitePointWorldCarrier.lean:219-223). -/
theorem lineCoverHomogeneousQ (M : ℕ) (j : Fin (2 * M)) :
    ∃ n : ℕ, lineQuotientMap M (MvPolynomial.X j) ∈ lineGrading M n :=
  ⟨1, lineCoverHomogeneousOneQ M j⟩

/-- **THE COVER TWIN (ADJOIN, T3)** — the variables generate the quotient as
an algebra over its degree-0 piece: the `hf` side condition of
`Proj.iSup_basicOpen_eq_top'` (Basic.lean:97-99).  The twin of the green
`span_cover` (GSTFinitePointWorldCarrier.lean:202-215), with the induction
lifted through `lineQuotientMap_surjective` (GSTFiniteLineRing.lean:137-144):
the `C`-case rides `S.algebraMap_mem` on the degree-0 image (the
`SetLike.GradeZero` algebra instances,
Mathlib/Algebra/DirectSum/Internal.lean:364-415), the `mul_X` case rides
`Algebra.subset_adjoin ∘ Set.mem_range_self`. -/
theorem lineCoverAdjoin (M : ℕ) :
    Algebra.adjoin ↥(lineGrading M 0)
      (Set.range (fun j : Fin (2 * M) => lineQuotientMap M (MvPolynomial.X j))) = ⊤ := by
  set S := Algebra.adjoin ↥(lineGrading M 0)
      (Set.range (fun j : Fin (2 * M) => lineQuotientMap M (MvPolynomial.X j)))
  refine top_unique fun x hx => ?_
  obtain ⟨p, rfl⟩ := lineQuotientMap_surjective M x
  clear hx
  induction p using MvPolynomial.induction_on with
  | C a =>
      exact S.algebraMap_mem
        ⟨lineQuotientMap M (MvPolynomial.C a),
          lineQuotientMap_mem_lineGrading M 0 (MvPolynomial.C a)
            ((MvPolynomial.mem_homogeneousSubmodule 0 (MvPolynomial.C a)).mpr
              (MvPolynomial.isHomogeneous_C (σ := Fin (2 * M)) (R := ℂ) a))⟩
  | add p q hp hq =>
      rw [map_add]
      exact S.add_mem hp hq
  | mul_X p k hp =>
      rw [map_mul]
      exact S.mul_mem hp (Algebra.subset_adjoin (Set.mem_range_self k))

/-! ## §3 Stage 0 (T4/T5) — the block projection and its descent -/

/-- **THE BLOCK PROJECTION (T4)** — the ℂ-algebra retraction of the
coordinate ring onto block `j`: `X j ↦ 1`, `X j' ↦ t` (the partner), every
other variable ↦ 0 (`MvPolynomial.aeval`, MvPolynomial/Eval.lean:592).
Stage 1's retraction χ is `Localization.awayLift` of its quotient descent
(`blockEvalQuot`) below. -/
noncomputable def blockEval (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    lineRing M →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  MvPolynomial.aeval fun a =>
    if a = j then (1 : MvPolynomial (Fin 1) ℂ)
    else if a = linePartner M j then MvPolynomial.X (0 : Fin 1) else 0

/-- The computation rule of the block projection on variables
(`MvPolynomial.aeval_X`, MvPolynomial/Eval.lean:611). -/
theorem blockEval_X (M : ℕ) [NeZero M] (j k : Fin (2 * M)) :
    blockEval M j (MvPolynomial.X k) =
      (if k = j then (1 : MvPolynomial (Fin 1) ℂ)
        else if k = linePartner M j then MvPolynomial.X (0 : Fin 1) else 0) := by
  simp only [blockEval, MvPolynomial.aeval_X]

/-- **T5 (generators, pointwise)** — every cross-monomial generator
evaluates to zero on the block projection: `a`, `b` lie in different blocks
(T1 `linePartner_block`), so at most one of them lies in the block's pair
`{j, linePartner M j}`, and any variable outside the pair evaluates to 0. -/
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

/-- **T5** — the block projection kills the cross ideal: the `≤ ker` form.
`Ideal.span_le` + the generator lemma above (the green
`truncIdeal_le_ker_evalWorldPoly` shape,
GSTTruncatedWorldCohomologyRing.lean:141-145). -/
theorem blockEval_mem_ker (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    crossIdeal M ≤ RingHom.ker (blockEval M j).toRingHom := by
  rw [show crossIdeal M = Ideal.span (crossMonomials M) from rfl, Ideal.span_le]
  intro p hp
  exact (RingHom.mem_ker (blockEval M j).toRingHom).mpr
    (blockEval_crossMonomials M j p hp)

/-- **T5 (pointwise, ideal-level)** — every cross-ideal element evaluates to
zero on the block projection (the `hI` shape of `liftₐ`). -/
theorem blockEval_mem_crossIdeal (M : ℕ) [NeZero M] (j : Fin (2 * M))
    {p : lineRing M} (hp : p ∈ crossIdeal M) : blockEval M j p = 0 :=
  (RingHom.mem_ker (blockEval M j).toRingHom).mp (blockEval_mem_ker M j hp)

/-- **THE BLOCK PROJECTION'S DESCENT (T5)** — the retraction of the
cross-monomial quotient onto `ℂ[t]`: the universal property of the quotient
algebra (`Ideal.Quotient.liftₐ`, Operations.lean:471 — pointwise `hI`, no
explicit base ring; the CI-green carrier spelling,
GSTFiniteLineWorldCarrier.lean:285-288). -/
noncomputable def blockEvalQuot (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    lineQuotient M →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  Ideal.Quotient.liftₐ (crossIdeal M) (blockEval M j)
    (fun p hp => blockEval_mem_crossIdeal M j hp)

/-- The computation rule of the descent on quotient classes — the carrier's
`lineRotateHom_mk` pattern (GSTFiniteLineWorldCarrier.lean:291-292, `rfl`). -/
theorem blockEvalQuot_mk (M : ℕ) [NeZero M] (j : Fin (2 * M)) (t : lineRing M) :
    blockEvalQuot M j (lineQuotientMap M t) = blockEval M j t :=
  rfl

/-! ## §4 Stage 0 (T6) — constants through degree zero -/

/-- **T6** — the constants through the degree-zero piece: the doubly-embedded
constant equals the quotient's constant.  This IS the pin's
`SetLike.GradeZero.coe_algebraMap`
(Mathlib/Algebra/DirectSum/Internal.lean:414-415, `@[simp, norm_cast]`, proved
`rfl`), at `S := ℂ`, `A := lineGrading M`, `R := lineQuotient M`.  The
finite-point carrier's `finitePoint_over_base` STAGE-3 idiom
(GSTFinitePointWorldCarrier.lean:676-688). -/
theorem hzero (M : ℕ) (c : ℂ) :
    (algebraMap ℂ (lineGrading M 0) c : lineQuotient M) = algebraMap ℂ (lineQuotient M) c :=
  SetLike.GradeZero.coe_algebraMap (lineGrading M) c

/-! ## §5 Stage 2 — the chart square (the `chartRingHom` contract)

THE W67-C PLUG.  `chartRingHom M j` is EXTERNAL (W67-C owns it, route map
Stage 1); the expected final shape is

    noncomputable def chartRingHom (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
        ℂ →+* HomogeneousLocalization.Away (lineGrading M)
            (lineQuotientMap M (MvPolynomial.X j)) :=
      (HomogeneousLocalization.fromZeroRingHom (lineGrading M)
          (Submonoid.powers (lineQuotientMap M (MvPolynomial.X j)))).comp
        (algebraMap ℂ (lineGrading M 0))

— the chart's ℂ-STRUCTURE ring hom (`RingHom.smooth_algebraMap` unfolds
`RingHom.Smooth (chartRingHom M j)` against it).  NOTE: the type is
`ℂ →+* Away …`, NOT `MvPolynomial (Fin 1) ℂ →+* Away …` — with the latter the
square below is ill-typed (its RHS would be a morphism into `Spec ℂ[t]`,
while `awayι ≫ finiteLineStructureMap M` lands in `Spec ℂ`).  The
`MvPolynomial (Fin 1) ℂ`-side of the chart is W67-C's `chartMap`
(`MvPolynomial.aeval (chartRatio M j)`).

ASSEMBLY.  In the assembled F3 module, where `chartRingHom M j` is the real
definition above, the assembler may either
(a) keep `chart_awayι_comp` verbatim, passing `chartRingHom := chartRingHom M j`
    and `hdef := rfl`; or
(b) delete the two binders of `chart_awayι_comp` and its proof body, and use
    `chart_awayι_comp'` (the same square, stated directly on the canonical
    composite — `chartRingHom M j` is definitionally that composite).
-/

/-- **THE CHART SQUARE (STAGE 2, standalone form)** — the away-chart of the
structure map is the `Spec` of the canonical ℂ-structure composite of the
chart.  Route: unfold `finiteLineStructureMap` (the green retype-`rw`,
GSTFiniteLineClosedImmersion.lean:205-208), regroup
(`← CategoryTheory.Category.assoc`), the pin's per-chart square
`Proj.awayι_toSpecZero` (Basic.lean:206: `awayι ≫ toSpecZero = Spec.map
(ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f)))`), fuse the two `Spec.map`s
(`← Spec.map_comp`, the contravariant `Spec` — Scheme.lean:488), and close by
the `ofHom`-fusion `CommRingCat.ofHom_comp` (Ring/Basic.lean:646-651, `rfl`). -/
theorem chart_awayι_comp' (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
        (lineCoverHomogeneousOneQ M j) zero_lt_one ≫
      finiteLineStructureMap M =
    Spec.map (CommRingCat.ofHom
      ((HomogeneousLocalization.fromZeroRingHom (lineGrading M)
          (Submonoid.powers (lineQuotientMap M (MvPolynomial.X j)))).comp
        (algebraMap ℂ (lineGrading M 0)))) := by
  rw [show finiteLineStructureMap M =
      (Proj.toSpecZero (lineGrading M) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (lineGrading M 0)))) from rfl,
    ← CategoryTheory.Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  exact congrArg Spec.map
    (CommRingCat.ofHom_comp (algebraMap ℂ (lineGrading M 0))
      (HomogeneousLocalization.fromZeroRingHom (lineGrading M)
        (Submonoid.powers (lineQuotientMap M (MvPolynomial.X j))))).symm

/-- **THE CHART SQUARE (STAGE 2, plug-facing form)** — the same square
against the NAME `chartRingHom` (the W67-C plug, §5 contract): the binder
`chartRingHom` carries the expected type and `hdef` its defining equation.
In the assembled file both are discharged definitionally (`hdef := rfl`). -/
theorem chart_awayι_comp (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (chartRingHom : ℂ →+* HomogeneousLocalization.Away (lineGrading M)
      (lineQuotientMap M (MvPolynomial.X j)))
    (hdef : chartRingHom = (HomogeneousLocalization.fromZeroRingHom (lineGrading M)
        (Submonoid.powers (lineQuotientMap M (MvPolynomial.X j)))).comp
      (algebraMap ℂ (lineGrading M 0))) :
    Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
        (lineCoverHomogeneousOneQ M j) zero_lt_one ≫
      finiteLineStructureMap M =
    Spec.map (CommRingCat.ofHom chartRingHom) := by
  rw [hdef]
  exact chart_awayι_comp' M j

/-! ## Receipts -/

#check linePartner
#check linePartner_ne
#check linePartner_block
#check linePartner_involution
#check lineCoverHomogeneousOneQ
#check lineCoverHomogeneousQ
#check lineCoverAdjoin
#check blockEval
#check blockEval_mem_ker
#check blockEvalQuot
#check hzero
#check chart_awayι_comp'
#check chart_awayι_comp

#print axioms linePartner_ne
#print axioms linePartner_block
#print axioms linePartner_involution
#print axioms lineCoverHomogeneousOneQ
#print axioms lineCoverHomogeneousQ
#print axioms lineCoverAdjoin
#print axioms blockEval_mem_ker
#print axioms hzero
#print axioms chart_awayι_comp'
#print axioms chart_awayι_comp

end GSTFiniteLineSmoothness

/-! ## DRAFT STATUS

Wave 67-B (Task 67-B-retry): F3 Stage 0 + Stage 2, authored against the
frozen route map `repairs/wave67_A_smoothness_route.md` with every API
claim re-verified at the pin (see the header's deviation ledger).  Not yet
kernel-checked — per the campaign law, the CI lane owns compilation; the
assembler (W67-D or the F3 integrator) pastes this section into
`GSTFiniteLineSmoothness.lean` behind W67-C's Stage 1. -/
