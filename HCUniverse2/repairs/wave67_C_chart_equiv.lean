import Mathlib
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import HCUniverse2.GSTFiniteLineRing
import HCUniverse2.GSTProjectiveOverC
import HCUniverse2.GSTFiniteLineWorldCarrier

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE CHART EQUIVALENCE (Wave 67-C — Stage 1 of the F3 smoothness module)

THE BATTLE OF F3 STAGE 1: the chart ring map of the finite-line world at the
variable `X j` is the polynomial ring `ℂ[T]` in the partner ratio
`ρ := q (X j') / q (X j)`, and this identification is a ring isomorphism —
hence (by `RingHom.Smooth.of_bijective`) a SMOOTH ring map.

Executed from the wave-67-A recon (repairs/wave67_A_smoothness_route.md,
§2 "Stage 1 — the chart equivalence (THE battle)"):

* `§1 Stage 0` — the partner index `linePartner` (the same-block involution
  `j ↦ j ^± 1` on `Fin (2*M)`), the same-block classification `sameBlock_or`,
  and the degree-1 homogeneity of both block variables in the quotient
  grading;
* `§2 the chart data` — the constants map `chartConstHom` (the `fromZeroRingHom`
  composite, feeding the `ℂ`-algebra structure `chartAwayAlgebra` on the
  homogeneous localization `Away (lineGrading M) (q (X j))`), the ratio
  generator `chartGen` (the fraction `q (X j') / q (X j)`), the chart ring map
  `chartRingHom := aeval ρ`, and the fraction-arithmetic helpers
  (`mk_eq_of_eq`, `mk_sum`, `const_mul_mk` — the pinned Proper.lean:229-237
  idiom: `val` + `Localization.mk_eq_mk_iff` + `Localization.r_of_eq`);
* `§3 THE BATTLE` — `chart_monomial` (the trichotomy: a cross-block monomial
  or an other-block monomial dies against the denominator; a same-block
  monomial is a polynomial in ρ) and `chartRingHom_surjective` (every element
  of `Away` is a fraction `q t / (q (X j))ⁿ` with `t` homogeneous of degree
  `n`, decomposed into monomials by `MvPolynomial.as_sum`, each a polynomial
  in ρ);
* `§4 the retraction` — `blockEval`/`blockEvalQuot` (the ℂ-algebra
  retraction of the quotient onto the `j`-block polynomial ring, killing the
  cross ideal) and `chartRetracts` (its `Localization.awayLift` extension to
  the chart, sending `ρ ↦ T`), giving `chartRingHom_injective`;
* `§5 THE TARGET` — `chart_ringHom_smooth`: the chart ring map is smooth
  (`RingHom.Smooth.of_bijective` — RingHom/Smooth.lean:122).

Every Mathlib name is pin-verified at 51e6992efd06126df61a496bebf8f49482a4e129
(reference copies under research/pin/mathlib-51e6992/; the fetched tree of the
67-A recon). Zero sorry, zero new axioms.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry CategoryTheory
open GSTProjectiveOverC GSTFiniteLineRing GSTFiniteLineWorldCarrier
open MvPolynomial DirectSum

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GSTFiniteLineSmoothness

/-! ## §1 Stage 0 — the partner index (the same-block involution)

The partner of `j` is the OTHER index of `j`'s coordinate block
(the block is `{X j, X (linePartner M j)}`).  All block logic is kept behind
`linePartnerVal` (the raw value function) and its three lemmas, mirroring the
carrier's `blockRotFn` lemma family (GSTFiniteLineWorldCarrier.lean:86-127). -/

/-- **THE PARTNER VALUE FUNCTION** — toggles the last bit at the value level:
`2b + e ↦ 2b + (1 - e)`. -/
def linePartnerVal (v : ℕ) : ℕ := if v % 2 = 0 then v + 1 else v - 1

/-- The partner stays in the same block (`omega`-verified: halving the value
is unchanged by the last-bit toggle). -/
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

/-- **THE PARTNER INDEX** — the other index of `j`'s coordinate block. -/
def linePartner (M : ℕ) [NeZero M] (j : Fin (2 * M)) : Fin (2 * M) :=
  ⟨linePartnerVal j.val, linePartnerVal_lt M j.isLt⟩

theorem linePartner_val (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    (linePartner M j).val = linePartnerVal j.val := rfl

/-- The partner is in the same block as `j`. -/
theorem linePartner_block (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    (linePartner M j).val / 2 = j.val / 2 :=
  linePartnerVal_block j.val

/-- The partner is different from `j`. -/
theorem linePartner_ne (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    linePartner M j ≠ j := fun h =>
  linePartnerVal_ne j.val (by
    have hv : (linePartner M j).val = j.val := congrArg Fin.val h
    rw [← linePartner_val M j]
    exact hv)

/-- **THE SAME-BLOCK CLASSIFICATION** — two indices in the same block are `j`
and its partner (`omega`-verified parity bookkeeping). -/
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
`lineQuotientMap_mem_lineGrading`, GSTFiniteLineRing.lean:167). -/
theorem lineX_mem_one (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    lineQuotientMap M (MvPolynomial.X j) ∈ lineGrading M 1 :=
  lineQuotientMap_mem_lineGrading M 1 _
    ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X ℂ j))

/-- The partner variable `q (X j')` is homogeneous of degree `1` as well. -/
theorem linePartner_mem_one (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    lineQuotientMap M (MvPolynomial.X (linePartner M j)) ∈ lineGrading M 1 :=
  lineQuotientMap_mem_lineGrading M 1 _
    ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X ℂ _))

/-- The `Away.mk`-graded form of the partner's homogeneity
(at degree `1 • 1`, the shape `Away.mk` demands). -/
theorem linePartner_mem_smul_one (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    lineQuotientMap M (MvPolynomial.X (linePartner M j)) ∈ lineGrading M (1 • 1) := by
  have h := linePartner_mem_one M j
  have hone : (1 : ℕ) • (1 : ℕ) = 1 := one_nsmul 1
  rw [hone]
  exact h

/-- The powers of the partner variable are homogeneous of degree `k • 1`
(`SetLike.pow_mem_graded`, the pin's own `Away.mk` denominator law,
HomogeneousLocalization.lean:610). -/
theorem linePartner_pow_mem (M : ℕ) [NeZero M] (j : Fin (2 * M)) (k : ℕ) :
    (lineQuotientMap M (MvPolynomial.X (linePartner M j))) ^ k ∈ lineGrading M (k • 1) :=
  SetLike.pow_mem_graded k (linePartner_mem_one M j)
