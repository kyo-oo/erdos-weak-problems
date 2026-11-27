import Mathlib
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE CROSS-MONOMIAL RING (the finite-line carrier's graded ring)

THE RING MODULE of the finite-line world construction: the cross-monomial
quotient of the coordinate ring of `ℙ^{2M-1}`, carrying the hand-built
quotient grading — the highest-risk unlock of the carrier lane (there is
NO quotient-grading constructor anywhere in Mathlib at the pin
v4.33.0-rc2; the campaign's own `GSTClassicalHodgeHomogeneousQuotientNonunit`
header records the gap).

THE WORLD (the frozen wave-44/60 design): `finiteLineWorld M` is the
disjoint union of `M` projective lines, presented as the `Proj` of the
cross-monomial quotient

  R := ℂ[x₀, …, x_{2M-1}]  /  (x_a · x_b : a, b in different blocks),

the `M` coordinate lines inside `ℙ^{2M-1}` (the i-th line is the
coordinate block `{x_{2i}, x_{2i+1}}`).

THIS MODULE builds the graded-ring substrate:

* `lineRing M` — the full coordinate ring `MvPolynomial (Fin (2*M)) ℂ`;

* `crossIdeal M` — the cross-monomial ideal (homogeneous of degree 2:
  the pin's `Ideal.homogeneous_span` over the degree-2 cross
  generators);

* `lineGrading M n` — the quotient grading: the image of the n-th
  homogeneous submodule of the full ring under the quotient map
  (`Submodule.map` of the quotient algebra map);

* `SetLike.GradedMonoid (lineGrading M)` — the multiplication law:
  images of homogeneous pieces multiply into the image of the
  degree-sum piece (the `Submodule.mul_mem_mul` transport through the
  multiplicative surjection);

* `lineGrading_isInternal` — the decomposition law: every element of
  the quotient decomposes uniquely into its image-homogeneous pieces
  (the `homogeneousComponent` machinery, descended along the
  homogeneous ideal: `homogeneousComponent_mem_of_mem` for the
  well-definedness, `homogeneousComponent_of_mem` for the
  component-of-homogeneous collapse);

* `GradedAlgebra (lineGrading M)` — the full instance, assembled by
  the pin's `DirectSum.IsInternal.gradedAlgebra` constructor.

The `Proj` of this grading IS the finite-line world's scheme — the
next module's construction (`GSTFiniteLineWorldCarrier`).

Honesty ledger: every statement is proved unconditionally.  No `sorry`,
no new axioms, no `native_decide`.  The grading is the honest
degree-grading of the cross-monomial quotient — no stashing, no
reindexing.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

attribute [local instance] MvPolynomial.gradedAlgebra

open scoped Classical

noncomputable section

namespace GSTFiniteLineRing

open MvPolynomial DirectSum

/-! ## §1 The coordinate ring and the cross-monomial ideal -/

/-- **THE FULL COORDINATE RING of `ℙ^{2M-1}`** (the carrier's ambient
polynomial ring; the grading pieces are the degree-homogeneous
submodules). -/
abbrev lineRing (M : ℕ) : Type :=
  MvPolynomial (Fin (2 * M)) ℂ

/-- **The cross-monomial generators**: the products `X a * X b` with
`a`, `b` in different blocks (block index `a / 2 ≠ b / 2`).  Each is
homogeneous of degree `2` (`isHomogeneous_X` + `IsHomogeneous.mul`). -/
def crossMonomials (M : ℕ) : Set (lineRing M) :=
  {p | ∃ a b : Fin (2 * M), a.val / 2 ≠ b.val / 2 ∧ p = X a * X b}

/-- Every cross-monomial generator is homogeneous of degree two. -/
theorem crossMonomials_homogeneous {M : ℕ}
    {p : lineRing M} (hp : p ∈ crossMonomials M) :
    ∃ n, p ∈ MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ n := by
  obtain ⟨a, b, -, rfl⟩ := hp
  exact ⟨2, (mem_homogeneousSubmodule 2 (X a * X b)).mpr
    (IsHomogeneous.mul (isHomogeneous_X ℂ a) (isHomogeneous_X ℂ b))⟩

/-- **THE CROSS-MONOMIAL IDEAL** — the ideal of `ℙ^{2M-1}` cutting out
the `M` disjoint coordinate lines. -/
def crossIdeal (M : ℕ) : Ideal (lineRing M) :=
  Ideal.span (crossMonomials M)

/-- The cross-monomial ideal is homogeneous for the degree grading (the
pin's `Ideal.homogeneous_span` over the degree-2 generators). -/
theorem crossIdeal_isHomogeneous (M : ℕ) :
    (crossIdeal M).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ) := by
  refine Ideal.homogeneous_span
    (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ) (crossMonomials M) ?_
  rintro p hp
  obtain ⟨n, hn⟩ := crossMonomials_homogeneous hp
  exact ⟨n, hn⟩

/-! ## §2 The quotient grading -/

/-- **THE FINITE-LINE QUOTIENT RING** — the coordinate ring of the `M`
disjoint lines. -/
abbrev lineQuotient (M : ℕ) : Type :=
  lineRing M ⧸ crossIdeal M

instance (M : ℕ) : CommRing (lineQuotient M) := inferInstance

instance (M : ℕ) : Algebra ℂ (lineQuotient M) := inferInstance

instance (M : ℕ) : DecidableEq (lineQuotient M) := Classical.decEq _

/-- The quotient map, as a `ℂ`-algebra homomorphism (the grading's
carrier). -/
def lineQuotientMap (M : ℕ) : lineRing M →ₐ[ℂ] lineQuotient M :=
  Ideal.Quotient.mkₐ ℂ (crossIdeal M)

/-- The definitional bridge: the algebra quotient map IS the ring
quotient map (the pin's `Quotient.mkₐ_eq_mk`). -/
theorem lineQuotientMap_mk (M : ℕ) (x : lineRing M) :
    lineQuotientMap M x = Ideal.Quotient.mk (crossIdeal M) x := by
  show (⇑(Ideal.Quotient.mkₐ ℂ (crossIdeal M))) x =
    Ideal.Quotient.mk (crossIdeal M) x
  rw [Ideal.Quotient.mkₐ_eq_mk]

theorem lineQuotientMap_surjective (M : ℕ) :
    Function.Surjective (lineQuotientMap M) := by
  have h : Function.Surjective
      (Ideal.Quotient.mk (crossIdeal M) : lineRing M → lineQuotient M) :=
    Ideal.Quotient.mk_surjective (I := crossIdeal M)
  intro a
  obtain ⟨r, hr⟩ := h a
  exact ⟨r, by rw [lineQuotientMap_mk M r]; exact hr⟩

theorem lineQuotientMap_eq_zero_iff (M : ℕ) (x : lineRing M) :
    lineQuotientMap M x = 0 ↔ x ∈ crossIdeal M := by
  rw [lineQuotientMap_mk M x]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- **THE QUOTIENT GRADING**: the image of the n-th homogeneous
submodule of the full coordinate ring under the quotient map.  This is
the degree grading of the cross-monomial quotient — the honest grading
whose `Proj` is the finite-line world. -/
def lineGrading (M : ℕ) (n : ℕ) :
    Submodule ℂ (lineQuotient M) :=
  Submodule.map (lineQuotientMap M).toLinearMap
    (MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ n)

theorem mem_lineGrading (M : ℕ) (n : ℕ) (x : lineQuotient M) :
    x ∈ lineGrading M n ↔ ∃ t : lineRing M,
      t ∈ MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ n ∧
      lineQuotientMap M t = x := by
  unfold lineGrading
  exact Submodule.mem_map

theorem lineQuotientMap_mem_lineGrading (M : ℕ) (n : ℕ)
    (t : lineRing M)
    (ht : t ∈ MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ n) :
    lineQuotientMap M t ∈ lineGrading M n :=
  (mem_lineGrading M n _).mpr ⟨t, ht, rfl⟩

/-! ## §3 The graded-monoid law (multiplication) -/

/-- **THE MULTIPLICATION LAW OF THE QUOTIENT GRADING.**  The image of
the degree-`i` piece times the image of the degree-`j` piece lands in
the image of the degree-`(i+j)` piece: images of homogeneous elements
are homogeneous (the transport through the multiplicative
surjection). -/
instance lineGrading_gradedMonoid (M : ℕ) :
    SetLike.GradedMonoid (lineGrading M) where
  one_mem := by
    refine (mem_lineGrading M 0 _).mpr ⟨1, ?_, map_one _⟩
    exact SetLike.one_mem_graded (MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ)
  mul_mem := by
    intro i j gi gj hi hj
    obtain ⟨a, ha, rfl⟩ := (mem_lineGrading M i _).mp hi
    obtain ⟨b, hb, rfl⟩ := (mem_lineGrading M j _).mp hj
    refine (mem_lineGrading M (i + j) _).mpr ⟨a * b, ?_, map_mul _ _ _⟩
    exact SetLike.mul_mem_graded ha hb

/-! ## §4 The well-definedness of the component lift -/

/-- **THE WELL-DEFINEDNESS OF THE COMPONENT LIFT.**  Equal quotient
elements have equal image-components: the homogeneous components of a
difference in the cross ideal stay in the cross ideal (the ideal is
homogeneous — the pin's `homogeneousComponent_mem_of_mem`). -/
theorem lineQuotient_component_congr (M : ℕ)
    (r r' : lineRing M) (h : lineQuotientMap M r = lineQuotientMap M r')
    (n : ℕ) :
    lineQuotientMap M (homogeneousComponent n r) =
      lineQuotientMap M (homogeneousComponent n r') := by
  have hmem : r - r' ∈ crossIdeal M :=
    (lineQuotientMap_eq_zero_iff M (r - r')).mp (by rw [map_sub, h, sub_self])
  have hcomp := homogeneousComponent_mem_of_mem
    (crossIdeal_isHomogeneous M) hmem n
  have hzero : lineQuotientMap M (homogeneousComponent n (r - r')) = 0 :=
    (lineQuotientMap_eq_zero_iff M _).mpr hcomp
  -- the linearity of the component map
  have hlin : homogeneousComponent n (r - r') =
      homogeneousComponent n r - homogeneousComponent n r' := by
    rw [map_sub]
  -- the component of the representative splits through the difference
  have hsplit : homogeneousComponent n r =
      homogeneousComponent n (r - r') + homogeneousComponent n r' := by
    rw [hlin, sub_add_cancel]
  rw [hsplit, map_add, hzero, zero_add]

/-! ## §5 The internal decomposition -/

/-- **THE LIFT EQUATION.**  The direct-sum coe of a family of graded
elements equals the quotient map applied to the representative sum:
each graded piece lifts along the quotient map, and the coe-sum is the
map of the lifted sum. -/
theorem coeAddMonoidHom_eq_lineQuotientMap_sum (M : ℕ)
    (s : ⨁ n, lineGrading M n) :
    DirectSum.coeAddMonoidHom (lineGrading M) s =
      ∑ n ∈ s.support, (s n : lineQuotient M) := by
  rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum]
  rfl

private theorem zero_of_coe_zero (M : ℕ) (s : ⨁ n, lineGrading M n)
    (h : DirectSum.coeAddMonoidHom (lineGrading M) s = 0) : s = 0 := by
  -- the graded lifts: every graded piece lifts along the quotient map
  have hlift : ∀ n : ℕ, ∃ t : lineRing M,
      t ∈ MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ n ∧
      lineQuotientMap M t = (s n : lineQuotient M) := by
    intro n
    by_cases hn : n ∈ s.support
    · exact (mem_lineGrading M n _).mp (s n).2
    · refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [DFinsupp.notMem_support_iff.mp hn]
      exact map_zero _
  choose t ht hmk using hlift
  -- the quotient sum vanishes: the lifted representative lies in the ideal
  have hsum : ∑ n ∈ s.support, t n ∈ crossIdeal M := by
    refine (lineQuotientMap_eq_zero_iff M _).mp ?_
    have hcoe : lineQuotientMap M (∑ n ∈ s.support, t n) = 0 := by
      rw [map_sum, ← h, coeAddMonoidHom_eq_lineQuotientMap_sum]
      exact Finset.sum_congr rfl (fun n _ => hmk n)
    exact hcoe
  -- every component of the lifted sum lies in the homogeneous ideal
  have hcomp : ∀ n₀ : ℕ, homogeneousComponent n₀ (∑ n ∈ s.support, t n)
      ∈ crossIdeal M :=
    fun n₀ => homogeneousComponent_mem_of_mem (crossIdeal_isHomogeneous M)
      hsum n₀
  -- the graded pieces vanish: the component collapse
  ext n₀
  by_cases hn : n₀ ∈ s.support
  · -- the n₀-th component of the lifted sum is the lift itself
    have hcollapse : homogeneousComponent n₀ (∑ n ∈ s.support, t n) = t n₀ := by
      rw [map_sum]
      rw [Finset.sum_eq_single_of_mem n₀ hn (fun b _ hne => by
        show homogeneousComponent n₀ (t b) = 0
        rw [homogeneousComponent_of_mem (ht b)]
        exact if_neg (Ne.symm hne))]
      rw [homogeneousComponent_of_mem (ht n₀), if_pos rfl]
    have hzero : lineQuotientMap M (t n₀) = 0 :=
      (lineQuotientMap_eq_zero_iff M _).mpr (by rw [← hcollapse]; exact hcomp n₀)
    have hval : (s n₀ : lineQuotient M) = 0 := by rw [← hmk n₀, hzero]
    rw [hval]
    rfl
  · -- off the support the graded piece is already zero
    rw [DFinsupp.notMem_support_iff.mp hn]
    rfl

private theorem injective_coeAddMonoidHom (M : ℕ) :
    Function.Injective (DirectSum.coeAddMonoidHom (lineGrading M)) := by
  intro s₁ s₂ h
  have hsub : s₁ - s₂ = 0 := by
    refine zero_of_coe_zero M (s₁ - s₂) ?_
    rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp hsub

private theorem surjective_coeAddMonoidHom (M : ℕ) :
    Function.Surjective (DirectSum.coeAddMonoidHom (lineGrading M)) := by
  intro a
  obtain ⟨r, rfl⟩ := lineQuotientMap_surjective M a
  -- the full ring's decomposition of the representative
  set d : ⨁ n, MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ n :=
    DirectSum.Decomposition.decompose' r with hd
  -- the full ring's decomposition coe is the representative itself
  have hfull : DirectSum.coeAddMonoidHom
      (MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ) d = r := by
    rw [hd]
    exact DirectSum.Decomposition.left_inv r
  -- its image: the graded generator sum of the image pieces
  set w : ⨁ n, lineGrading M n :=
    ∑ n ∈ d.support, DirectSum.of (fun n => lineGrading M n) n
      ⟨lineQuotientMap M (d n : lineRing M),
        lineQuotientMap_mem_lineGrading M n (d n : lineRing M) (d n).2⟩ with hw
  refine ⟨w, ?_⟩
  -- each generator's coe is the image piece
  have hgen : ∀ n ∈ d.support,
      DirectSum.coeAddMonoidHom (lineGrading M)
        (DirectSum.of (fun n => lineGrading M n) n
          ⟨lineQuotientMap M (d n : lineRing M),
            lineQuotientMap_mem_lineGrading M n (d n : lineRing M) (d n).2⟩) =
        lineQuotientMap M (d n : lineRing M) := by
    intro n _
    exact DirectSum.coeAddMonoidHom_of (fun n => lineGrading M n) n _
  -- the image sum is the image of the full ring's decomposition coe
  have step1 : DirectSum.coeAddMonoidHom (lineGrading M) w =
      ∑ n ∈ d.support, lineQuotientMap M (d n : lineRing M) := by
    rw [hw, map_sum]
    exact Finset.sum_congr rfl (fun n hn => hgen n hn)
  have step2 : ∑ n ∈ d.support, lineQuotientMap M (d n : lineRing M) =
      lineQuotientMap M (∑ n ∈ d.support, (d n : lineRing M)) :=
    (map_sum _ _ _).symm
  have step3 : lineQuotientMap M (∑ n ∈ d.support, (d n : lineRing M)) =
      lineQuotientMap M r := by
    have h2 : ∑ n ∈ d.support, (d n : lineRing M) = r := by
      rw [← hfull, DirectSum.coeAddMonoidHom_eq_dfinsuppSum]
      rfl
    rw [h2]
  exact step1.trans (step2.trans step3)

/-- **THE INTERNAL DECOMPOSITION LAW.**  The quotient grading is an
internal direct sum: every quotient element decomposes uniquely into
its image-homogeneous pieces (the component machinery descended along
the homogeneous cross ideal). -/
theorem lineGrading_isInternal (M : ℕ) :
    DirectSum.IsInternal (lineGrading M) :=
  ⟨injective_coeAddMonoidHom M, surjective_coeAddMonoidHom M⟩

/-! ## §6 The graded-ring instance -/

/-- **THE GRADED-RING INSTANCE of the cross-monomial quotient** — the
pin's `DirectSum.IsInternal.gradedAlgebra` constructor applied to the
internal decomposition: the `Proj` of this grading is the finite-line
world's scheme carrier. -/
instance lineGrading_gradedAlgebra (M : ℕ) :
    GradedAlgebra (lineGrading M) :=
  DirectSum.IsInternal.gradedAlgebra (lineGrading_isInternal M)

/-! ## §7 Receipts -/

#check GSTFiniteLineRing.lineRing
#check GSTFiniteLineRing.crossIdeal
#check GSTFiniteLineRing.lineQuotient
#check GSTFiniteLineRing.lineGrading
#check GSTFiniteLineRing.lineGrading_gradedMonoid
#check GSTFiniteLineRing.lineGrading_isInternal
#check GSTFiniteLineRing.lineGrading_gradedAlgebra

#print axioms GSTFiniteLineRing.lineGrading_gradedMonoid
#print axioms GSTFiniteLineRing.lineGrading_isInternal
#print axioms GSTFiniteLineRing.lineGrading_gradedAlgebra

end GSTFiniteLineRing

/-! ## DRAFT STATUS

Ported 12/12 declarations; kernel-checked by the CI lane
`gst-finite-line-ring.yml` on push (repo law: no local Lean, CI owns
compilation).  The module is the substrate of the finite-line carrier
lane (`GSTFiniteLineWorldCarrier`, the next wave's construction). -/
