import Mathlib
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import HCUniverse2.GSTFiniteLineRing
import HCUniverse2.GSTProjectiveOverC
import HCUniverse2.GSTFiniteLineWorldCarrier
import HCUniverse2.GSTNativeCodimensionCyclePresentation

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE HONEST PRIME LATTICE OF THE FINITE-LINE WORLD (wave 4-A, repaired)

The component algebra of `Proj (lineGrading M)` — the honest prime lattice
behind the canonical cycle-class maps of the unconditional round:

* the M generic points `lineGenericPoint M i` (the ideals of the variables
  outside block i) — coheight ZERO (the maximal points of the
  specialization order, the generic points of the M lines);
* the per-line closed points `lineClosedPointAt M i` (the `X_{2i+1}`-image
  together with all the outside-block-i variables) — coheight ONE, strictly
  below the i-th generic point; the 0-th one is `lineClosedPoint M`;
* the component machinery: `lineIndexOfGeneric` (the coheight-zero points
  ARE the M generic points) and `lineComponentOf` (every coheight-one
  point lies below EXACTLY ONE generic point).

The engines, all unconditional:

1. THE BLOCK RETRACTIONS (§1): the two-variable dehomogenization
   `blockProjAt M i` (a ℂ-algebra map to ℂ[Y,Z] sending block i's pair to
   Y,Z and every other variable to 0) and its one-variable shadow
   `blockProjClosedAt M i` (X_{2i} ↦ X, else 0), with the KERNEL LAWS — the
   kernels are exactly the generic/closed ideals.  The kernel inclusion
   `aeval = 0 → crossIdeal ⊔ outside` rides the projector-congruence route
   (every polynomial is congruent to its projector modulo the projector
   ideal; the projector collapses to zero on the kernel).
2. THE NO-INTERMEDIATE LAW (§4): no point's ideal lies strictly between
   the i-th generic ideal and the closed ideal — the transported prime in
   ℂ[Y,Z] dies by ELEMENTARY DESCENT (every element of the prime is
   divisible by Z, primality pushes the division down one Z-degree at a
   time, and a nonzero polynomial has bounded Z-degree).  No Krull-height
   machinery anywhere.
3. THE ORDER BRIDGE (§3): the specialization order on the line world's
   points is reverse inclusion of homogeneous ideals (the corpus's green
   `prime_le_iff` pattern, restated at this carrier), which turns the
   prime-lattice computations into coheight receipts.

Honesty ledger: every statement is proved unconditionally.  No `sorry`,
no new axioms, no `native_decide`.  The GitHub CI lane
`gst-finite-line-point-algebra.yml` owns the kernel check.
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry CategoryTheory
open GSTProjectiveOverC GSTFiniteLineRing GSTFiniteLineWorldCarrier
open GSTNativeCodimensionCyclePresentation GSTGeometricRealizationStage2D
open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GSTFiniteLinePointAlgebra

/-! ## §0 The cross-product vanishing and the block arithmetic -/

/-- **THE CROSS-PRODUCT VANISHING** — different-block variables multiply
to zero in the cross-monomial quotient (the defining relation of the M
disjoint lines). -/
theorem crossMul_eq_zero (M : ℕ) {a b : Fin (2 * M)}
    (hab : a.val / 2 ≠ b.val / 2) :
    lineQuotientMap M (X a) * lineQuotientMap M (X b) = 0 := by
  rw [← map_mul, lineQuotientMap_eq_zero_iff]
  exact Ideal.subset_span ⟨a, b, hab, rfl⟩

/-- The block-characterization arithmetic: the two index tests are the
block membership. -/
theorem mem_block_iff (M : ℕ) (i : Fin M) (a : Fin (2 * M)) :
    (a.val = 2 * i.val ∨ a.val = 2 * i.val + 1) ↔ a.val / 2 = i.val := by
  have ha : a.val < 2 * M := a.isLt
  have hM : 0 < M := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hdm : a.val = 2 * (a.val / 2) + a.val % 2 := (Nat.div_add_mod a.val 2).symm
  have hmod : a.val % 2 < 2 := Nat.mod_lt _ (by omega)
  constructor
  · rintro (h | h) <;> omega
  · intro h
    omega

/-- The even variable index of block i. -/
def blockVarLeft (M : ℕ) (i : Fin M) : Fin (2 * M) :=
  ⟨2 * i.val, by have := i.isLt; omega⟩

/-- The odd variable index of block i. -/
def blockVarRight (M : ℕ) (i : Fin M) : Fin (2 * M) :=
  ⟨2 * i.val + 1, by have := i.isLt; omega⟩

theorem blockVarLeft_val (M : ℕ) (i : Fin M) :
    (blockVarLeft M i).val = 2 * i.val := rfl

theorem blockVarRight_val (M : ℕ) (i : Fin M) :
    (blockVarRight M i).val = 2 * i.val + 1 := rfl

theorem blockVarLeft_block (M : ℕ) (i : Fin M) :
    (blockVarLeft M i).val / 2 = i.val := by
  rw [blockVarLeft_val, Nat.mul_div_cancel_left _ two_pos]

theorem blockVarRight_block (M : ℕ) (i : Fin M) :
    (blockVarRight M i).val / 2 = i.val := by
  rw [blockVarRight_val]
  omega

theorem not_mem_block_left (M : ℕ) (i : Fin M) {a : Fin (2 * M)}
    (ha : a.val / 2 ≠ i.val) : a.val ≠ 2 * i.val ∧ a.val ≠ 2 * i.val + 1 := by
  constructor
  · intro h
    rw [h] at ha
    exact ha (Nat.mul_div_cancel_left _ two_pos)
  · intro h
    apply ha
    omega

/-! ## §1 The block retractions and the kernel laws -/

/-- The block-i variable family: `X_{2i} ↦ Y`, `X_{2i+1} ↦ Z`, all other
variables to zero. -/
def blockVarFamily (M : ℕ) (i : Fin M) :
    Fin (2 * M) → MvPolynomial (Fin 2) ℂ :=
  fun a => if a.val = 2 * i.val then (X ⟨0, by omega⟩ : MvPolynomial (Fin 2) ℂ)
    else if a.val = 2 * i.val + 1 then
      (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) else 0

/-- **THE BLOCK PROJECTION** — the dehomogenization retraction at block i
(a ℂ-algebra map from the coordinate ring to ℂ[Y,Z]). -/
def blockProjAt (M : ℕ) (i : Fin M) :
    lineRing M →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.aeval (blockVarFamily M i)

/-- The block-i substitution family: `Y ↦ X_{2i}`, `Z ↦ X_{2i+1}`. -/
def blockInclFamily (M : ℕ) (i : Fin M) : Fin 2 → lineRing M :=
  fun a => (X ⟨2 * i.val + a.val, by have := i.isLt; omega⟩ : lineRing M)

/-- **THE BLOCK SUBSTITUTION** — the section of the block projection. -/
def blockInclAt (M : ℕ) (i : Fin M) :
    MvPolynomial (Fin 2) ℂ →ₐ[ℂ] lineRing M :=
  MvPolynomial.aeval (blockInclFamily M i)

/-- The family values at the three index classes. -/
theorem blockVarFamily_left (M : ℕ) (i : Fin M) :
    blockVarFamily M i (blockVarLeft M i) = (X ⟨0, by omega⟩ : MvPolynomial (Fin 2) ℂ) := by
  simp [blockVarFamily, blockVarLeft_val]

theorem blockVarFamily_right (M : ℕ) (i : Fin M) :
    blockVarFamily M i (blockVarRight M i) = (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) := by
  simp [blockVarFamily, blockVarRight_val]

theorem blockVarFamily_outside (M : ℕ) (i : Fin M) {a : Fin (2 * M)}
    (ha : a.val / 2 ≠ i.val) :
    blockVarFamily M i a = 0 := by
  have hne1 : a.val ≠ 2 * i.val := by
    intro h
    exact ha (by rw [h]; exact Nat.mul_div_cancel_left _ two_pos)
  have hne2 : a.val ≠ 2 * i.val + 1 := by
    intro h
    apply ha
    omega
  rw [blockVarFamily, if_neg hne1, if_neg hne2]

theorem blockProjAt_X_left (M : ℕ) (i : Fin M) :
    blockProjAt M i (X (blockVarLeft M i)) = (X ⟨0, by omega⟩ : MvPolynomial (Fin 2) ℂ) := by
  rw [blockProjAt, aeval_X, blockVarFamily_left]

theorem blockProjAt_X_right (M : ℕ) (i : Fin M) :
    blockProjAt M i (X (blockVarRight M i)) = (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) := by
  rw [blockProjAt, aeval_X, blockVarFamily_right]

theorem blockProjAt_X_outside (M : ℕ) (i : Fin M) {a : Fin (2 * M)}
    (ha : a.val / 2 ≠ i.val) :
    blockProjAt M i (X a) = 0 := by
  rw [blockProjAt, aeval_X, blockVarFamily_outside M i ha]

theorem blockInclAt_X (M : ℕ) (i : Fin M) (a : Fin 2) :
    blockInclAt M i (X a) = blockInclFamily M i a := by
  rw [blockInclAt, aeval_X]

theorem blockProjAt_comp_blockInclAt (M : ℕ) (i : Fin M) :
    (blockProjAt M i).comp (blockInclAt M i) = AlgHom.id ℂ (MvPolynomial (Fin 2) ℂ) := by
  refine MvPolynomial.algHom_ext fun a => ?_
  show blockProjAt M i (blockInclAt M i (X a)) = X a
  rw [blockInclAt_X]
  show blockProjAt M i (blockInclFamily M i a) = X a
  rcases a with ⟨av, hav⟩
  rcases av with _ | av1
  · show blockProjAt M i
      (X (⟨2 * i.val + 0, _⟩ : Fin (2 * M)) : lineRing M) = (X (⟨0, _⟩ : Fin 2))
    rw [show ((⟨2 * i.val + 0, _⟩ : Fin (2 * M)) = blockVarLeft M i) from rfl,
      blockProjAt_X_left]
  · rcases av1 with _ | av2
    · show blockProjAt M i
        (X (⟨2 * i.val + 1, _⟩ : Fin (2 * M)) : lineRing M) = (X (⟨1, _⟩ : Fin 2))
      rw [show ((⟨2 * i.val + 1, _⟩ : Fin (2 * M)) = blockVarRight M i) from rfl,
        blockProjAt_X_right]
    · omega

/-- **THE OUTSIDE-VARIABLE IDEAL** (ring level): the span of the
variables outside block i. -/
def outsideIdealRing (M : ℕ) (i : Fin M) : Ideal (lineRing M) :=
  Ideal.span (Set.range fun b : {b : Fin (2 * M) // b.val / 2 ≠ i.val} =>
    (X b.1 : lineRing M))

theorem mem_outsideIdealRing (M : ℕ) (i : Fin M) {a : Fin (2 * M)}
    (ha : a.val / 2 ≠ i.val) :
    (X a : lineRing M) ∈ outsideIdealRing M i :=
  Ideal.subset_span ⟨⟨a, ha⟩, rfl⟩

/-- **THE PROJECTOR IDEAL** — generated by the variable-projector
differences. -/
def projectorIdeal (M : ℕ) (i : Fin M) : Ideal (lineRing M) :=
  Ideal.span (Set.range fun a : Fin (2 * M) =>
    (X a : lineRing M) - blockInclAt M i (blockProjAt M i (X a)))

/-- Every polynomial is congruent to its projector modulo the projector
ideal (the two algebra maps — the quotient and the projector-then-quotient
— agree on the variable generators). -/
theorem sub_projector_mem (M : ℕ) (i : Fin M) (q : lineRing M) :
    q - blockInclAt M i (blockProjAt M i q) ∈ projectorIdeal M i := by
  have hagree : (Ideal.Quotient.mkₐ ℂ (projectorIdeal M i)).comp
      ((blockInclAt M i).comp (blockProjAt M i)) =
      (Ideal.Quotient.mkₐ ℂ (projectorIdeal M i)) := by
    refine MvPolynomial.algHom_ext fun a => ?_
    have hgen : (X a : lineRing M) - blockInclAt M i (blockProjAt M i (X a)) ∈
        projectorIdeal M i := Ideal.subset_span ⟨a, rfl⟩
    have hq := (Ideal.Quotient.eq (I := projectorIdeal M i)).mpr hgen
    exact hq.symm
  have happ := DFunLike.congr_fun hagree q
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at happ
  have hz : (Ideal.Quotient.mkₐ ℂ (projectorIdeal M i)) (q -
      blockInclAt M i (blockProjAt M i q)) = 0 := by
    rw [map_sub, ← happ, sub_self]
  rw [← map_zero (Ideal.Quotient.mkₐ ℂ (projectorIdeal M i))] at hz
  have hmem := (Ideal.Quotient.eq (I := projectorIdeal M i)).mp hz
  rwa [sub_zero] at hmem

/-- The substitution-variables are the block variables. -/
theorem blockInclAt_X_zero (M : ℕ) (i : Fin M) :
    blockInclAt M i (X ⟨0, by omega⟩ : MvPolynomial (Fin 2) ℂ) =
      (X (blockVarLeft M i) : lineRing M) := by
  rw [blockInclAt_X]
  show (X (⟨2 * i.val + 0, by have := i.isLt; omega⟩ : Fin (2 * M)) : lineRing M) =
    (X (blockVarLeft M i) : lineRing M)
  rfl

theorem blockInclAt_X_one (M : ℕ) (i : Fin M) :
    blockInclAt M i (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) =
      (X (blockVarRight M i) : lineRing M) := by
  rw [blockInclAt_X]
  show (X (⟨2 * i.val + 1, by have := i.isLt; omega⟩ : Fin (2 * M)) : lineRing M) =
    (X (blockVarRight M i) : lineRing M)
  rfl

/-- The projector fixes the kept variables. -/
theorem projector_roundtrip_left (M : ℕ) (i : Fin M) :
    blockInclAt M i (blockProjAt M i (X (blockVarLeft M i))) =
      (X (blockVarLeft M i) : lineRing M) := by
  rw [blockProjAt_X_left, blockInclAt_X_zero]

theorem projector_roundtrip_right (M : ℕ) (i : Fin M) :
    blockInclAt M i (blockProjAt M i (X (blockVarRight M i))) =
      (X (blockVarRight M i) : lineRing M) := by
  rw [blockProjAt_X_right, blockInclAt_X_one]

/-- The projector ideal lies in the outside-variable ideal (the
differences vanish on the kept block and equal the outside variables
elsewhere). -/
theorem projectorIdeal_le_outside (M : ℕ) (i : Fin M) :
    projectorIdeal M i ≤ outsideIdealRing M i := by
  rw [projectorIdeal, Ideal.span_le]
  rintro _ ⟨a, rfl⟩
  show (X a : lineRing M) - blockInclAt M i (blockProjAt M i (X a)) ∈
    outsideIdealRing M i
  rcases eq_or_ne (a.val / 2) i.val with h | h
  · have hkept : a = blockVarLeft M i ∨ a = blockVarRight M i := by
      rcases (mem_block_iff M i a).mpr h with hval | hval
      · exact Or.inl (Fin.ext hval)
      · exact Or.inr (Fin.ext hval)
    have hround : blockInclAt M i (blockProjAt M i (X a)) = (X a : lineRing M) := by
      rcases hkept with h1 | h1
      · subst h1
        exact projector_roundtrip_left M i
      · subst h1
        exact projector_roundtrip_right M i
    rw [hround, sub_self]
    exact Submodule.zero_mem _
  · rw [blockProjAt_X_outside M i h, map_zero, sub_zero]
    exact mem_outsideIdealRing M i h

/-- **THE KERNEL LAW** — the kernel of the block projection is exactly the
outside-variable ideal: the substitution route (every polynomial is
congruent to its projector modulo the projector ideal; the projector
collapses to zero on the kernel). -/
theorem ker_blockProjAt (M : ℕ) (i : Fin M) :
    RingHom.ker (blockProjAt M i).toRingHom = outsideIdealRing M i := by
  apply le_antisymm
  · -- a kernel element: the projector is zero on it, so it lies in the
    -- projector ideal, hence in the outside ideal
    intro t ht
    rw [RingHom.mem_ker] at ht
    have hPzero : blockInclAt M i (blockProjAt M i t) = 0 := by
      have ht' : blockProjAt M i t = 0 := ht
      rw [ht', map_zero]
    have hmem : t - blockInclAt M i (blockProjAt M i t) ∈ projectorIdeal M i :=
      sub_projector_mem M i t
    rw [hPzero, sub_zero] at hmem
    exact projectorIdeal_le_outside M i hmem
  · rw [outsideIdealRing, Ideal.span_le]
    rintro _ ⟨b, rfl⟩
    show (X (b : Fin (2 * M)) : lineRing M) ∈ RingHom.ker (blockProjAt M i).toRingHom
    rw [RingHom.mem_ker]
    show blockProjAt M i (X (b : Fin (2 * M))) = 0
    exact blockProjAt_X_outside M i b.2

/-! ### The generic ideal and the descended retraction -/

/-- **THE GENERIC IDEAL** — the span of the outside-block-i variable
images in the quotient: the prime of the i-th line's generic point. -/
def lineGenericIdeal (M : ℕ) (i : Fin M) : Ideal (lineQuotient M) :=
  Ideal.span (Set.range fun b : {b : Fin (2 * M) // b.val / 2 ≠ i.val} =>
    lineQuotientMap M (X b.1))

theorem mem_lineGenericIdeal (M : ℕ) (i : Fin M) {a : Fin (2 * M)}
    (ha : a.val / 2 ≠ i.val) :
    lineQuotientMap M (X a) ∈ lineGenericIdeal M i :=
  Ideal.subset_span ⟨⟨a, ha⟩, rfl⟩

/-- The block projection kills the cross ideal: different-block products
have a zero family factor. -/
theorem blockProjAt_crossIdeal_le_ker (M : ℕ) (i : Fin M) :
    crossIdeal M ≤ RingHom.ker (blockProjAt M i).toRingHom := by
  rw [crossIdeal, Ideal.span_le]
  rintro _ ⟨a, b, hab, rfl⟩
  show blockProjAt M i (X a * X b) = 0
  rw [map_mul]
  rcases eq_or_ne (a.val / 2) i.val with ha | ha
  · have hb : b.val / 2 ≠ i.val := fun h => hab (ha.trans h.symm)
    rw [blockProjAt_X_outside M i hb, mul_zero]
  · rw [blockProjAt_X_outside M i ha, zero_mul]

/-- **THE DESCENDED BLOCK PROJECTION** — the retraction on the quotient
ring. -/
noncomputable def blockProjQuotAt (M : ℕ) (i : Fin M) :
    lineQuotient M →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
  Ideal.Quotient.liftₐ (crossIdeal M) (blockProjAt M i)
    (fun p hp => by
      have hk : p ∈ RingHom.ker (blockProjAt M i).toRingHom :=
        blockProjAt_crossIdeal_le_ker M i hp
      rwa [RingHom.mem_ker] at hk)

theorem blockProjQuotAt_mk (M : ℕ) (i : Fin M) (t : lineRing M) :
    blockProjQuotAt M i (lineQuotientMap M t) = blockProjAt M i t := rfl

theorem blockProjQuotAt_X_left (M : ℕ) (i : Fin M) :
    blockProjQuotAt M i (lineQuotientMap M (X (blockVarLeft M i))) =
      (X ⟨0, by omega⟩ : MvPolynomial (Fin 2) ℂ) := by
  rw [blockProjQuotAt_mk, blockProjAt_X_left]

theorem blockProjQuotAt_X_right (M : ℕ) (i : Fin M) :
    blockProjQuotAt M i (lineQuotientMap M (X (blockVarRight M i))) =
      (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) := by
  rw [blockProjQuotAt_mk, blockProjAt_X_right]

theorem blockProjQuotAt_X_outside (M : ℕ) (i : Fin M) {a : Fin (2 * M)}
    (ha : a.val / 2 ≠ i.val) :
    blockProjQuotAt M i (lineQuotientMap M (X a)) = 0 := by
  rw [blockProjQuotAt_mk, blockProjAt_X_outside M i ha]

/-- **THE KERNEL CHARACTERIZATION AT THE GENERIC IDEAL** — membership in
the i-th generic ideal IS vanishing under the block-i retraction (the
kernel law transported along the quotient). -/
theorem mem_lineGenericIdeal_iff (M : ℕ) (i : Fin M) (y : lineQuotient M) :
    y ∈ lineGenericIdeal M i ↔ blockProjQuotAt M i y = 0 := by
  obtain ⟨t, rfl⟩ := lineQuotientMap_surjective M y
  constructor
  · intro hy
    have hle : lineGenericIdeal M i ≤
        RingHom.ker (blockProjQuotAt M i).toRingHom := by
      rw [lineGenericIdeal, Ideal.span_le]
      rintro _ ⟨b, rfl⟩
      show lineQuotientMap M (X (b : Fin (2 * M))) ∈
        RingHom.ker (blockProjQuotAt M i).toRingHom
      rw [RingHom.mem_ker]
      show blockProjQuotAt M i (lineQuotientMap M (X (b : Fin (2 * M)))) = 0
      exact blockProjQuotAt_X_outside M i b.2
    have hk := hle hy
    rwa [RingHom.mem_ker] at hk
  · intro hy
    rw [blockProjQuotAt_mk] at hy
    have hker : t ∈ RingHom.ker (blockProjAt M i).toRingHom := by
      rw [RingHom.mem_ker]
      have ht' : blockProjAt M i t = 0 := hy
      exact ht'
    have hout : t ∈ outsideIdealRing M i := by
      have hke := ker_blockProjAt M i
      rw [hke] at hker
      exact hker
    have hmap : lineQuotientMap M t ∈
        Ideal.map (lineQuotientMap M).toRingHom (outsideIdealRing M i) :=
      Ideal.mem_map_of_mem _ hout
    rw [outsideIdealRing, Ideal.map_span, ← Set.range_comp] at hmap
    simp only [Function.comp_def] at hmap
    exact hmap

/-- **THE GENERIC IDEAL IS PRIME.** -/
theorem lineGenericIdeal_isPrime (M : ℕ) (i : Fin M) :
    (lineGenericIdeal M i).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro htop
    have h1 : (1 : lineQuotient M) ∈ lineGenericIdeal M i := by
      rw [htop]; trivial
    have hz := (mem_lineGenericIdeal_iff M i 1).mp h1
    rw [map_one] at hz
    exact one_ne_zero hz
  · intro x y hxy
    have hx : blockProjQuotAt M i (x * y) = 0 :=
      (mem_lineGenericIdeal_iff M i _).mp hxy
    rw [map_mul, mul_eq_zero] at hx
    rcases hx with h | h
    · exact Or.inl ((mem_lineGenericIdeal_iff M i _).mpr h)
    · exact Or.inr ((mem_lineGenericIdeal_iff M i _).mpr h)

theorem lineQuotientMap_X_pair_not_mem (M : ℕ) (i : Fin M) :
    lineQuotientMap M (X (blockVarLeft M i)) ∉ lineGenericIdeal M i := by
  intro hmem
  have hz := (mem_lineGenericIdeal_iff M i _).mp hmem
  rw [blockProjQuotAt_X_left M i] at hz
  exact X_ne_zero (s := (⟨0, by omega⟩ : Fin 2)) hz

theorem lineQuotientMap_X_pair_not_mem' (M : ℕ) (i : Fin M) :
    lineQuotientMap M (X (blockVarRight M i)) ∉ lineGenericIdeal M i := by
  intro hmem
  have hz := (mem_lineGenericIdeal_iff M i _).mp hmem
  rw [blockProjQuotAt_X_right M i] at hz
  exact X_ne_zero (s := (⟨1, by omega⟩ : Fin 2)) hz

/-! ### The per-line closed ideal and its retraction -/

/-- The line-i closed-point variable family: `X_{2i} ↦ X`, all other
variables to zero. -/
def closedVarFamilyAt (M : ℕ) (i : Fin M) :
    Fin (2 * M) → MvPolynomial (Fin 1) ℂ :=
  fun a => if a.val = 2 * i.val then (X ⟨0, by omega⟩ : MvPolynomial (Fin 1) ℂ) else 0

/-- **THE CLOSED PROJECTION AT LINE i** — the one-variable retraction. -/
def blockProjClosedAt (M : ℕ) (i : Fin M) :
    lineRing M →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  MvPolynomial.aeval (closedVarFamilyAt M i)

/-- The closed substitution family: `X ↦ X_{2i}`. -/
def closedInclFamilyAt (M : ℕ) (i : Fin M) : Fin 1 → lineRing M :=
  fun _ => (X (blockVarLeft M i) : lineRing M)

/-- **THE CLOSED SUBSTITUTION AT LINE i.** -/
def blockInclClosedAt (M : ℕ) (i : Fin M) :
    MvPolynomial (Fin 1) ℂ →ₐ[ℂ] lineRing M :=
  MvPolynomial.aeval (closedInclFamilyAt M i)

theorem blockProjClosedAt_X_left (M : ℕ) (i : Fin M) :
    blockProjClosedAt M i (X (blockVarLeft M i)) =
      (X ⟨0, by omega⟩ : MvPolynomial (Fin 1) ℂ) := by
  rw [blockProjClosedAt, aeval_X]
  show (if (blockVarLeft M i).val = 2 * i.val then
      (X ⟨0, _⟩ : MvPolynomial (Fin 1) ℂ) else 0) = _
  rw [blockVarLeft_val, if_pos rfl]

theorem blockProjClosedAt_X_ne (M : ℕ) (i : Fin M) {a : Fin (2 * M)}
    (ha : a.val ≠ 2 * i.val) :
    blockProjClosedAt M i (X a) = 0 := by
  rw [blockProjClosedAt, aeval_X, closedVarFamilyAt, if_neg ha]

theorem blockInclClosedAt_X (M : ℕ) (i : Fin M) (a : Fin 1) :
    blockInclClosedAt M i (X a) = closedInclFamilyAt M i a := by
  rw [blockInclClosedAt, aeval_X]

theorem blockProjClosedAt_comp_blockInclClosedAt (M : ℕ) (i : Fin M) :
    (blockProjClosedAt M i).comp (blockInclClosedAt M i) =
      AlgHom.id ℂ (MvPolynomial (Fin 1) ℂ) := by
  refine MvPolynomial.algHom_ext fun a => ?_
  show blockProjClosedAt M i (blockInclClosedAt M i (X a)) = X a
  rcases a with ⟨av, hav⟩
  rcases av with _ | av1
  · rw [blockInclClosedAt_X, closedInclFamilyAt, blockProjClosedAt_X_left]
  · omega

/-- **THE CLOSED PROJECTOR IDEAL AT LINE i.** -/
def closedProjectorIdealAt (M : ℕ) (i : Fin M) : Ideal (lineRing M) :=
  Ideal.span (Set.range fun a : Fin (2 * M) =>
    (X a : lineRing M) - blockInclClosedAt M i (blockProjClosedAt M i (X a)))

/-- **THE CLOSED OUTSIDE IDEAL AT LINE i** — the span of all variables
except `X_{2i}`. -/
def closedOutsideIdealRingAt (M : ℕ) (i : Fin M) : Ideal (lineRing M) :=
  Ideal.span (Set.range fun b : {b : Fin (2 * M) // b.val ≠ 2 * i.val} =>
    (X b.1 : lineRing M))

theorem mem_closedOutsideIdealRingAt (M : ℕ) (i : Fin M) {a : Fin (2 * M)}
    (ha : a.val ≠ 2 * i.val) :
    (X a : lineRing M) ∈ closedOutsideIdealRingAt M i :=
  Ideal.subset_span ⟨⟨a, ha⟩, rfl⟩

/-- Every polynomial is congruent to its line-i closed projector modulo
the line-i closed projector ideal. -/
theorem sub_closedProjectorAt_mem (M : ℕ) (i : Fin M) (q : lineRing M) :
    q - blockInclClosedAt M i (blockProjClosedAt M i q) ∈ closedProjectorIdealAt M i := by
  have hagree : (Ideal.Quotient.mkₐ ℂ (closedProjectorIdealAt M i)).comp
      ((blockInclClosedAt M i).comp (blockProjClosedAt M i)) =
      (Ideal.Quotient.mkₐ ℂ (closedProjectorIdealAt M i)) := by
    refine MvPolynomial.algHom_ext fun a => ?_
    have hgen : (X a : lineRing M) -
        blockInclClosedAt M i (blockProjClosedAt M i (X a)) ∈
        closedProjectorIdealAt M i := Ideal.subset_span ⟨a, rfl⟩
    have hq := (Ideal.Quotient.eq (I := closedProjectorIdealAt M i)).mpr hgen
    exact hq.symm
  have happ := DFunLike.congr_fun hagree q
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at happ
  have hz : (Ideal.Quotient.mkₐ ℂ (closedProjectorIdealAt M i)) (q -
      blockInclClosedAt M i (blockProjClosedAt M i q)) = 0 := by
    rw [map_sub, ← happ, sub_self]
  rw [← map_zero (Ideal.Quotient.mkₐ ℂ (closedProjectorIdealAt M i))] at hz
  have hmem := (Ideal.Quotient.eq (I := closedProjectorIdealAt M i)).mp hz
  rwa [sub_zero] at hmem

theorem closedProjectorIdealAt_le_closedOutsideAt (M : ℕ) (i : Fin M) :
    closedProjectorIdealAt M i ≤ closedOutsideIdealRingAt M i := by
  rw [closedProjectorIdealAt, Ideal.span_le]
  rintro _ ⟨a, rfl⟩
  show (X a : lineRing M) -
    blockInclClosedAt M i (blockProjClosedAt M i (X a)) ∈ closedOutsideIdealRingAt M i
  by_cases h : a.val = 2 * i.val
  · have haidx : a = blockVarLeft M i := by
      apply Fin.ext
      show a.val = (blockVarLeft M i).val
      rw [blockVarLeft_val]
      omega
    subst haidx
    rw [blockProjClosedAt_X_left, blockInclClosedAt_X, closedInclFamilyAt]
    rw [sub_self]
    exact Submodule.zero_mem _
  · rw [blockProjClosedAt_X_ne M i h, map_zero, sub_zero]
    exact mem_closedOutsideIdealRingAt M i h

/-- **THE CLOSED KERNEL LAW AT LINE i.** -/
theorem ker_blockProjClosedAt (M : ℕ) (i : Fin M) :
    RingHom.ker (blockProjClosedAt M i).toRingHom = closedOutsideIdealRingAt M i := by
  apply le_antisymm
  · intro t ht
    rw [RingHom.mem_ker] at ht
    have hPzero : blockInclClosedAt M i (blockProjClosedAt M i t) = 0 := by
      have ht' : blockProjClosedAt M i t = 0 := ht
      rw [ht', map_zero]
    have hmem : t - blockInclClosedAt M i (blockProjClosedAt M i t) ∈
        closedProjectorIdealAt M i := sub_closedProjectorAt_mem M i t
    rw [hPzero, sub_zero] at hmem
    exact closedProjectorIdealAt_le_closedOutsideAt M i hmem
  · rw [closedOutsideIdealRingAt, Ideal.span_le]
    rintro _ ⟨b, rfl⟩
    show (X (b : Fin (2 * M)) : lineRing M) ∈
      RingHom.ker (blockProjClosedAt M i).toRingHom
    rw [RingHom.mem_ker]
    show blockProjClosedAt M i (X (b : Fin (2 * M))) = 0
    exact blockProjClosedAt_X_ne M i b.2

/-- The closed projection at line i kills the cross ideal. -/
theorem blockProjClosedAt_crossIdeal_le_ker (M : ℕ) (i : Fin M) :
    crossIdeal M ≤ RingHom.ker (blockProjClosedAt M i).toRingHom := by
  rw [crossIdeal, Ideal.span_le]
  rintro _ ⟨a, b, hab, rfl⟩
  show blockProjClosedAt M i (X a * X b) = 0
  rw [map_mul]
  rcases eq_or_ne a.val (2 * i.val) with ha | ha
  · have hb : b.val ≠ 2 * i.val := by
      intro hcon
      exact hab (by rw [ha, hcon])
    have haL : a = blockVarLeft M i := by
      apply Fin.ext
      show a.val = (blockVarLeft M i).val
      rw [blockVarLeft_val]
      exact ha
    subst haL
    rw [blockProjClosedAt_X_left, blockProjClosedAt_X_ne M i hb, mul_zero]
  · rw [blockProjClosedAt_X_ne M i ha, zero_mul]

/-- **THE DESCENDED CLOSED PROJECTION AT LINE i.** -/
noncomputable def blockProjClosedQuotAt (M : ℕ) (i : Fin M) :
    lineQuotient M →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  Ideal.Quotient.liftₐ (crossIdeal M) (blockProjClosedAt M i)
    (fun p hp => by
      have hk : p ∈ RingHom.ker (blockProjClosedAt M i).toRingHom :=
        blockProjClosedAt_crossIdeal_le_ker M i hp
      rwa [RingHom.mem_ker] at hk)

theorem blockProjClosedQuotAt_mk (M : ℕ) (i : Fin M) (t : lineRing M) :
    blockProjClosedQuotAt M i (lineQuotientMap M t) = blockProjClosedAt M i t := rfl

/-- **THE CLOSED IDEAL AT LINE i** — the span of the images of all
variables except `X_{2i}`: the prime of the closed point `[1:0]` on the
i-th line. -/
def lineClosedIdealAt (M : ℕ) (i : Fin M) : Ideal (lineQuotient M) :=
  Ideal.span (Set.range fun b : {b : Fin (2 * M) // b.val ≠ 2 * i.val} =>
    lineQuotientMap M (X b.1))

theorem mem_lineClosedIdealAt (M : ℕ) (i : Fin M) {a : Fin (2 * M)}
    (ha : a.val ≠ 2 * i.val) :
    lineQuotientMap M (X a) ∈ lineClosedIdealAt M i :=
  Ideal.subset_span ⟨⟨a, ha⟩, rfl⟩

/-- **THE KERNEL CHARACTERIZATION AT THE LINE-i CLOSED IDEAL.** -/
theorem mem_lineClosedIdealAt_iff (M : ℕ) (i : Fin M) (y : lineQuotient M) :
    y ∈ lineClosedIdealAt M i ↔ blockProjClosedQuotAt M i y = 0 := by
  obtain ⟨t, rfl⟩ := lineQuotientMap_surjective M y
  constructor
  · intro hy
    have hle : lineClosedIdealAt M i ≤
        RingHom.ker (blockProjClosedQuotAt M i).toRingHom := by
      rw [lineClosedIdealAt, Ideal.span_le]
      rintro _ ⟨b, rfl⟩
      show lineQuotientMap M (X (b : Fin (2 * M))) ∈
        RingHom.ker (blockProjClosedQuotAt M i).toRingHom
      rw [RingHom.mem_ker]
      show blockProjClosedQuotAt M i (lineQuotientMap M (X (b : Fin (2 * M)))) = 0
      rw [blockProjClosedQuotAt_mk, blockProjClosedAt_X_ne M i b.2]
    have hk := hle hy
    rwa [RingHom.mem_ker] at hk
  · intro hy
    rw [blockProjClosedQuotAt_mk] at hy
    have hker : t ∈ RingHom.ker (blockProjClosedAt M i).toRingHom := by
      rw [RingHom.mem_ker]
      have ht' : blockProjClosedAt M i t = 0 := hy
      exact ht'
    have hout : t ∈ closedOutsideIdealRingAt M i := by
      have hke := ker_blockProjClosedAt M i
      rw [hke] at hker
      exact hker
    have hmap : lineQuotientMap M t ∈
        Ideal.map (lineQuotientMap M).toRingHom (closedOutsideIdealRingAt M i) :=
      Ideal.mem_map_of_mem _ hout
    rw [closedOutsideIdealRingAt, Ideal.map_span, ← Set.range_comp] at hmap
    simp only [Function.comp_def] at hmap
    exact hmap

/-- **THE LINE-i CLOSED IDEAL IS PRIME.** -/
theorem lineClosedIdealAt_isPrime (M : ℕ) (i : Fin M) :
    (lineClosedIdealAt M i).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro htop
    have h1 : (1 : lineQuotient M) ∈ lineClosedIdealAt M i := by
      rw [htop]; trivial
    have hz := (mem_lineClosedIdealAt_iff M i 1).mp h1
    rw [map_one] at hz
    exact one_ne_zero hz
  · intro x y hxy
    have hx : blockProjClosedQuotAt M i (x * y) = 0 :=
      (mem_lineClosedIdealAt_iff M i _).mp hxy
    rw [map_mul, mul_eq_zero] at hx
    rcases hx with h | h
    · exact Or.inl ((mem_lineClosedIdealAt_iff M i _).mpr h)
    · exact Or.inr ((mem_lineClosedIdealAt_iff M i _).mpr h)

theorem lineQuotientMap_X_left_not_mem_lineClosedIdealAt (M : ℕ) (i : Fin M) :
    lineQuotientMap M (X (blockVarLeft M i)) ∉ lineClosedIdealAt M i := by
  intro hmem
  have hz := (mem_lineClosedIdealAt_iff M i _).mp hmem
  rw [blockProjClosedQuotAt_mk, blockProjClosedAt_X_left] at hz
  exact X_ne_zero (s := (⟨0, by omega⟩ : Fin 1)) hz

theorem lineQuotientMap_X_right_mem_lineClosedIdealAt (M : ℕ) (i : Fin M) :
    lineQuotientMap M (X (blockVarRight M i)) ∈ lineClosedIdealAt M i := by
  refine mem_lineClosedIdealAt M i ?_
  intro hcon
  rw [blockVarRight_val] at hcon
  omega

/-- The generic-i ideal is contained in the line-i closed ideal. -/
theorem lineGenericIdeal_le_lineClosedIdealAt (M : ℕ) (i : Fin M) :
    lineGenericIdeal M i ≤ lineClosedIdealAt M i := by
  rw [lineGenericIdeal, lineClosedIdealAt, Ideal.span_le]
  rintro _ ⟨b, rfl⟩
  show lineQuotientMap M (X (b : Fin (2 * M))) ∈ lineClosedIdealAt M i
  refine Ideal.subset_span ⟨⟨b, ?_⟩, rfl⟩
  intro hcon
  have hb := b.2
  omega

/-! ## §2 The homogeneous ideals and the points -/

/-- The degree-one membership of a variable image (the green substrate
receipt). -/
theorem lineQuotientMap_X_mem_lineGrading_one (M : ℕ) (a : Fin (2 * M)) :
    lineQuotientMap M (X a) ∈ lineGrading M 1 :=
  lineQuotientMap_mem_lineGrading M 1 (X a)
    ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X ℂ a))

/-- **THE GENERIC HOMOGENEOUS IDEAL** — the generic ideal as a
`HomogeneousIdeal` of the quotient grading (a span of degree-one
elements). -/
noncomputable def lineGenericHomogeneousIdeal (M : ℕ) (i : Fin M) :
    HomogeneousIdeal (lineGrading M) where
  toSubmodule := lineGenericIdeal M i
  is_homogeneous' := by
    rw [lineGenericIdeal]
    exact Ideal.homogeneous_span (𝒜 := lineGrading M)
      (Set.range fun b : {b : Fin (2 * M) // b.val / 2 ≠ i.val} =>
        lineQuotientMap M (X b.1))
      (by
        rintro p ⟨b, hb, rfl⟩
        exact ⟨1, lineQuotientMap_X_mem_lineGrading_one M b.1⟩)

theorem lineGenericHomogeneousIdeal_toIdeal (M : ℕ) (i : Fin M) :
    (lineGenericHomogeneousIdeal M i).toIdeal = lineGenericIdeal M i := rfl

/-- **THE LINE-i CLOSED HOMOGENEOUS IDEAL.** -/
noncomputable def lineClosedHomogeneousIdealAt (M : ℕ) (i : Fin M) :
    HomogeneousIdeal (lineGrading M) where
  toSubmodule := lineClosedIdealAt M i
  is_homogeneous' := by
    rw [lineClosedIdealAt]
    exact Ideal.homogeneous_span (𝒜 := lineGrading M)
      (Set.range fun b : {b : Fin (2 * M) // b.val ≠ 2 * i.val} =>
        lineQuotientMap M (X b.1))
      (by
        rintro p ⟨b, hb, rfl⟩
        exact ⟨1, lineQuotientMap_X_mem_lineGrading_one M b.1⟩)

theorem lineClosedHomogeneousIdealAt_toIdeal (M : ℕ) (i : Fin M) :
    (lineClosedHomogeneousIdealAt M i).toIdeal = lineClosedIdealAt M i := rfl

/-- **THE GENERIC POINT OF THE i-TH LINE** — the Proj-point of the i-th
generic ideal. -/
noncomputable def lineGenericPoint (M : ℕ) (i : Fin M) :
    finiteLineScheme M where
  asHomogeneousIdeal := lineGenericHomogeneousIdeal M i
  isPrime := lineGenericIdeal_isPrime M i
  not_irrelevant_le := by
    intro hle
    have hmem : lineQuotientMap M (X (blockVarLeft M i)) ∈
        lineGenericIdeal M i := by
      have h1 : lineQuotientMap M (X (blockVarLeft M i)) ∈
          (HomogeneousIdeal.irrelevant (lineGrading M)).toIdeal :=
        HomogeneousIdeal.mem_irrelevant_of_mem (lineGrading M) (by omega)
          (lineQuotientMap_X_mem_lineGrading_one M _)
      have h2 : (HomogeneousIdeal.irrelevant (lineGrading M)).toIdeal ≤
          lineGenericIdeal M i := by
        show (HomogeneousIdeal.irrelevant (lineGrading M)).toIdeal ≤
          (lineGenericHomogeneousIdeal M i).toIdeal
        exact (toIdeal_le_toIdeal_iff).mpr hle
      exact h2 h1
    exact lineQuotientMap_X_pair_not_mem M i hmem

/-- **THE CLOSED POINT OF THE i-TH LINE** — `[1:0]` on the i-th line (the
Proj-point of the line-i closed ideal). -/
noncomputable def lineClosedPointAt (M : ℕ) (i : Fin M) :
    finiteLineScheme M where
  asHomogeneousIdeal := lineClosedHomogeneousIdealAt M i
  isPrime := lineClosedIdealAt_isPrime M i
  not_irrelevant_le := by
    intro hle
    have hmem : lineQuotientMap M (X (blockVarLeft M i)) ∈
        lineClosedIdealAt M i := by
      have h1 : lineQuotientMap M (X (blockVarLeft M i)) ∈
          (HomogeneousIdeal.irrelevant (lineGrading M)).toIdeal :=
        HomogeneousIdeal.mem_irrelevant_of_mem (lineGrading M) (by omega)
          (lineQuotientMap_X_mem_lineGrading_one M _)
      have h2 : (HomogeneousIdeal.irrelevant (lineGrading M)).toIdeal ≤
          lineClosedIdealAt M i := by
        show (HomogeneousIdeal.irrelevant (lineGrading M)).toIdeal ≤
          (lineClosedHomogeneousIdealAt M i).toIdeal
        exact (toIdeal_le_toIdeal_iff).mpr hle
      exact h2 h1
    exact lineQuotientMap_X_left_not_mem_lineClosedIdealAt M i hmem

theorem lineGenericPoint_asIdeal (M : ℕ) (i : Fin M) :
    (lineGenericPoint M i).asHomogeneousIdeal.toIdeal = lineGenericIdeal M i :=
  rfl

theorem lineClosedPointAt_asIdeal (M : ℕ) (i : Fin M) :
    (lineClosedPointAt M i).asHomogeneousIdeal.toIdeal = lineClosedIdealAt M i :=
  rfl

/-- Points with equal homogeneous ideals are equal (proof irrelevance on
the propositional fields). -/
theorem projectiveSpectrum_ext {R : Type*} [CommRing R] {σ : Type*}
    [SetLike σ R] [AddSubgroupClass σ R] {𝒜 : ℕ → σ} [GradedRing 𝒜]
    {x y : ProjectiveSpectrum 𝒜}
    (h : x.asHomogeneousIdeal = y.asHomogeneousIdeal) : x = y := by
  obtain ⟨I, h1, h2⟩ := x
  obtain ⟨J, k1, k2⟩ := y
  have hIJ : I = J := h
  subst hIJ
  rfl

/-! ## §3 The specialization-order bridge and the maximality of the
generic points -/

attribute [local instance] specializationOrder

/-- **THE ORDER BRIDGE** — the specialization order on the line world's
points is reverse inclusion of homogeneous ideals (the corpus's green
`prime_le_iff` pattern at this carrier). -/
theorem le_iff_ideal (M : ℕ) (x y : finiteLineScheme M) :
    x ≤ y ↔ y.asHomogeneousIdeal.toIdeal ≤ x.asHomogeneousIdeal.toIdeal := by
  have key : ∀ a b : ProjectiveSpectrum (lineGrading M),
      a ∈ closure ({b} : Set (ProjectiveSpectrum (lineGrading M))) ↔
        b.asHomogeneousIdeal.toIdeal ≤ a.asHomogeneousIdeal.toIdeal := by
    intro a b
    rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      ProjectiveSpectrum.vanishingIdeal_singleton]
    exact ProjectiveSpectrum.mem_zeroLocus _ _ _
  constructor
  · intro h
    have hc : x ∈ closure ({y} : Set (finiteLineScheme M)) :=
      (specializes_iff_mem_closure (x := y) (y := x)).mp h
    exact (key x y).mp hc
  · intro h
    have hc : x ∈ closure ({y} : Set (finiteLineScheme M)) := (key x y).mpr h
    exact (specializes_iff_mem_closure (x := y) (y := x)).mpr hc

/-- A positive-degree homogeneous polynomial lies in the ideal generated
by the variables (the support decomposition: each support monomial of a
degree-`n ≥ 1` homogeneous polynomial has a positive exponent, hence
factors through the corresponding variable). -/
theorem homogeneous_pos_mem_span_X {M : ℕ} {n : ℕ} (hn : 0 < n)
    (t : lineRing M) (ht : IsHomogeneous t n) :
    t ∈ Ideal.span (Set.range (X : Fin (2 * M) → lineRing M)) := by
  rw [MvPolynomial.as_sum t]
  refine Submodule.sum_mem _ fun e he => ?_
  have hce : MvPolynomial.coeff e t ≠ 0 :=
    (MvPolynomial.mem_support_iff).mp he
  have hwe : Finsupp.weight 1 e = n := ht hce
  obtain ⟨a, ha⟩ : ∃ a : Fin (2 * M), 0 < e a := by
    by_contra hcon
    have hcon' : ∀ j : Fin (2 * M), ¬(0 < e j) := fun j h' => hcon ⟨j, h'⟩
    have he0 : e = 0 := Finsupp.ext fun j => by
      have := hcon' j
      simp only [Finsupp.zero_apply]
      omega
    rw [he0, map_zero] at hwe
    omega
  have hsplit : e = Finsupp.erase a e + Finsupp.single a (e a) := by
    ext j
    by_cases hja : j = a
    · subst hja
      simp [Finsupp.add_apply, Finsupp.erase_same, Finsupp.single_eq_same]
    · simp [Finsupp.add_apply, Finsupp.erase_ne hja, Finsupp.single_eq_of_ne hja]
  have hmul : ∀ c : ℂ,
      MvPolynomial.monomial (Finsupp.erase a e + Finsupp.single a (e a)) c =
      (X a ^ (e a - 1) * MvPolynomial.monomial (Finsupp.erase a e) c) *
        (X a : lineRing M) := by
    intro c
    rw [MvPolynomial.monomial_add_single]
    conv_lhs => rw [← Nat.sub_add_cancel ha, pow_succ]
    ring
  have hX : (X a : lineRing M) ∈
      Ideal.span (Set.range (X : Fin (2 * M) → lineRing M)) :=
    Submodule.subset_span (Set.mem_range_self a)
  rw [hsplit, hmul]
  exact Ideal.mul_mem_left _ _ hX

/-- If every variable image lies in an ideal, the irrelevant ideal lies in
it (the positive-degree homogeneous elements lie in the variable span). -/
theorem irrelevant_le_of_mem_variables (M : ℕ) (I : Ideal (lineQuotient M))
    (h : ∀ a : Fin (2 * M), lineQuotientMap M (X a) ∈ I) :
    (HomogeneousIdeal.irrelevant (lineGrading M)).toIdeal ≤ I := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi u hu
  obtain ⟨t, ht, rfl⟩ := (mem_lineGrading M i u).mp hu
  have hring : t ∈ Ideal.span (Set.range (X : Fin (2 * M) → lineRing M)) :=
    homogeneous_pos_mem_span_X hi t ((mem_homogeneousSubmodule _ _).mp ht)
  have hmaple : Ideal.map (lineQuotientMap M).toRingHom
      (Ideal.span (Set.range (X : Fin (2 * M) → lineRing M))) ≤ I := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨a, ⟨b, rfl⟩, rfl⟩
    show (lineQuotientMap M) (X b) ∈ I
    exact h b
  exact hmaple (Ideal.mem_map_of_mem _ hring)

/-- Every point of the line world has a variable avoiding its ideal. -/
theorem exists_variable_not_mem (M : ℕ) (y : finiteLineScheme M) :
    ∃ a : Fin (2 * M), lineQuotientMap M (X a) ∉
      y.asHomogeneousIdeal.toIdeal := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  apply y.not_irrelevant_le
  show (HomogeneousIdeal.irrelevant (lineGrading M)).toIdeal ≤
    y.asHomogeneousIdeal.toIdeal
  exact irrelevant_le_of_mem_variables M _ (fun a => hcon a)

/-- **THE GENERIC POINTS ARE MAXIMAL** — a relevant point whose ideal is
contained in the i-th generic ideal IS the i-th generic point. -/
theorem eq_lineGenericPoint_of_le (M : ℕ) (i : Fin M)
    (y : finiteLineScheme M)
    (hy : y.asHomogeneousIdeal.toIdeal ≤ lineGenericIdeal M i) :
    y = lineGenericPoint M i := by
  obtain ⟨a, ha⟩ := exists_variable_not_mem M y
  rcases eq_or_ne (a.val / 2) i.val with hblock | hblock
  · have hgen : lineGenericIdeal M i ≤ y.asHomogeneousIdeal.toIdeal := by
      rw [lineGenericIdeal, Ideal.span_le]
      rintro _ ⟨b, rfl⟩
      have hzero : lineQuotientMap M (X a) * lineQuotientMap M (X (b : Fin (2 * M))) = 0 :=
        crossMul_eq_zero M (fun hcon => b.2 (hcon.symm.trans hblock))
      have hmem : lineQuotientMap M (X a) *
          lineQuotientMap M (X (b : Fin (2 * M))) ∈
          y.asHomogeneousIdeal.toIdeal := by
        rw [hzero]; exact Submodule.zero_mem _
      rcases y.isPrime.mem_or_mem hmem with h1 | h2
      · exact absurd h1 ha
      · exact h2
    have hideal : y.asHomogeneousIdeal.toIdeal = lineGenericIdeal M i :=
      le_antisymm hy hgen
    refine projectiveSpectrum_ext ?_
    refine HomogeneousIdeal.ext ?_
    rw [lineGenericPoint_asIdeal M i]
    exact hideal
  · have hyin : lineQuotientMap M (X (blockVarLeft M i)) ∈
        y.asHomogeneousIdeal.toIdeal := by
      have hzero : lineQuotientMap M (X a) *
          lineQuotientMap M (X (blockVarLeft M i)) = 0 :=
        crossMul_eq_zero M (fun hcon => hblock (hcon.trans (blockVarLeft_block M i)))
      have hmem : lineQuotientMap M (X a) *
          lineQuotientMap M (X (blockVarLeft M i)) ∈
          y.asHomogeneousIdeal.toIdeal := by
        rw [hzero]; exact Submodule.zero_mem _
      rcases y.isPrime.mem_or_mem hmem with h1 | h2
      · exact absurd h1 ha
      · exact h2
    exact absurd (hy hyin) (lineQuotientMap_X_pair_not_mem M i)

/-- **THE COHEIGHT-ZERO RECEIPT** — the i-th generic point is maximal in
the specialization order. -/
theorem lineGenericPoint_coheight (M : ℕ) (i : Fin M) :
    Order.coheight (lineGenericPoint M i) = 0 := by
  refine Order.coheight_eq_zero.mpr (fun z hle => ?_)
  have hzle : z.asHomogeneousIdeal.toIdeal ≤ lineGenericIdeal M i :=
    (le_iff_ideal M (lineGenericPoint M i) z).mp hle
  rw [eq_lineGenericPoint_of_le M i z hzle]

/-- The line-i closed ideal is the join of the i-th generic ideal and the
`X_{2i+1}`-image principal ideal. -/
theorem lineClosedIdealAt_eq_supAt (M : ℕ) (i : Fin M) :
    lineClosedIdealAt M i = lineGenericIdeal M i ⊔
      Ideal.span {lineQuotientMap M (X (blockVarRight M i))} := by
  apply le_antisymm
  · rw [lineClosedIdealAt, Ideal.span_le]
    rintro _ ⟨b, rfl⟩
    show lineQuotientMap M (X (b : Fin (2 * M))) ∈
      lineGenericIdeal M i ⊔ Ideal.span {lineQuotientMap M (X (blockVarRight M i))}
    by_cases hb : (b : Fin (2 * M)).val = 2 * i.val + 1
    · have hbidx : (b : Fin (2 * M)) = blockVarRight M i := by
        apply Fin.ext
        show (b : Fin (2 * M)).val = (blockVarRight M i).val
        rw [blockVarRight_val]
        omega
      rw [hbidx]
      exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
    · refine Submodule.mem_sup_left (mem_lineGenericIdeal M i ?_)
      have hb2 := b.2
      omega
  · refine sup_le_iff.mpr ⟨lineGenericIdeal_le_lineClosedIdealAt M i, ?_⟩
    rw [Ideal.span_le]
    rintro _ rfl
    exact lineQuotientMap_X_right_mem_lineClosedIdealAt M i

/-! ## §4 The no-intermediate law (the elementary descent) -/

/-- **THE NO-INTERMEDIATE LAW AT LINE i** — no point's ideal lies strictly
between the i-th generic ideal and the line-i closed ideal.  The route:
transport to ℂ[Y,Z] through the surjective block-i retraction (a prime
mapping into the principal ideal `(Z)`), then ELEMENTARY DESCENT — every
element of the transported prime is divisible by `Z`, primality pushes the
division down one `Z`-degree at a time, and a nonzero polynomial has
bounded total degree.  No Krull-height machinery anywhere. -/
theorem no_intermediate_pointAt (M : ℕ) (i : Fin M) (y : finiteLineScheme M)
    (hgen : lineGenericIdeal M i < y.asHomogeneousIdeal.toIdeal)
    (hstrict : y.asHomogeneousIdeal.toIdeal < lineClosedIdealAt M i) :
    False := by
  -- the block-i retraction roundtrip and surjectivity
  have hround : ∀ g : MvPolynomial (Fin 2) ℂ,
      blockProjQuotAt M i (lineQuotientMap M (blockInclAt M i g)) = g := by
    intro g
    rw [blockProjQuotAt_mk]
    simpa using DFunLike.congr_fun (blockProjAt_comp_blockInclAt M i) g
  have hsurj : Function.Surjective (blockProjQuotAt M i) := by
    intro g
    refine ⟨lineQuotientMap M (blockInclAt M i g), hround g⟩
  -- the transported prime
  set ybar : Ideal (MvPolynomial (Fin 2) ℂ) :=
    Ideal.map (blockProjQuotAt M i).toRingHom y.asHomogeneousIdeal.toIdeal
    with hybardef
  have hybarprime : ybar.IsPrime := by
    refine ⟨?_, ?_⟩
    · intro htop
      have h1 : (1 : MvPolynomial (Fin 2) ℂ) ∈ ybar := by
        rw [htop]; trivial
      obtain ⟨w, hw, hw1⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp h1
      have hwker : w - 1 ∈ lineGenericIdeal M i := by
        rw [mem_lineGenericIdeal_iff M i]
        rw [map_sub, hw1, map_one, sub_self]
      have hgoal : (1 : lineQuotient M) ∈ y.asHomogeneousIdeal.toIdeal := by
        have hsub : w - (w - 1) ∈ y.asHomogeneousIdeal.toIdeal :=
          Submodule.sub_mem _ hw (hgen.le hwker)
        have hsum : w - (w - 1) = (1 : lineQuotient M) := by ring
        rw [hsum] at hsub
        exact hsub
      exact y.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hgoal)
    · intro a b hab
      obtain ⟨ã, hã⟩ := hsurj a
      obtain ⟨bbar, hbbar⟩ := hsurj b
      obtain ⟨w, hw, hwab⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp hab
      have hd : w - ã * bbar ∈ lineGenericIdeal M i := by
        rw [mem_lineGenericIdeal_iff M i]
        rw [map_sub, map_mul, hã, hbbar, hwab, sub_self]
      have hwmem : w - (w - ã * bbar) ∈ y.asHomogeneousIdeal.toIdeal :=
        Submodule.sub_mem _ hw (hgen.le hd)
      have hdm : w - (w - ã * bbar) = ã * bbar := by ring
      rw [hdm] at hwmem
      rcases y.isPrime.mem_or_mem hwmem with h1 | h2
      · exact Or.inl
          ((Ideal.mem_map_iff_of_surjective _ hsurj).mpr ⟨ã, h1, hã⟩)
      · exact Or.inr
          ((Ideal.mem_map_iff_of_surjective _ hsurj).mpr ⟨bbar, h2, hbbar⟩)
  -- ybar is nonzero: y strictly contains the generic ideal
  have hybarne : ybar ≠ ⊥ := by
    intro hbot
    obtain ⟨f, hf, hfne⟩ : ∃ f ∈ y.asHomogeneousIdeal.toIdeal,
        f ∉ lineGenericIdeal M i := by
      by_contra hcon
      push_neg at hcon
      exact absurd (le_antisymm hcon hgen.le).symm (ne_of_lt hgen)
    have hfimg : blockProjQuotAt M i f ∈ ybar :=
      (Ideal.mem_map_iff_of_surjective _ hsurj).mpr ⟨f, hf, rfl⟩
    have hf0 : blockProjQuotAt M i f ≠ 0 := by
      intro h0
      exact hfne ((mem_lineGenericIdeal_iff M i f).mpr h0)
    rw [hbot] at hfimg
    exact hf0 ((Submodule.mem_bot _).mp hfimg)
  -- the closed ideal's image is the principal ideal (Z)
  have hmapclosed : Ideal.map (blockProjQuotAt M i).toRingHom
      (lineClosedIdealAt M i) =
      Ideal.span {(X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ)} := by
    rw [lineClosedIdealAt, Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨z, ⟨b, rfl⟩, rfl⟩
      show blockProjQuotAt M i (lineQuotientMap M (X (b : Fin (2 * M)))) ∈
        Ideal.span {(X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ)}
      by_cases hb : (b : Fin (2 * M)).val = 2 * i.val + 1
      · have hbidx : (b : Fin (2 * M)) = blockVarRight M i := by
          apply Fin.ext
          show (b : Fin (2 * M)).val = (blockVarRight M i).val
          rw [blockVarRight_val]
          omega
        rw [hbidx, blockProjQuotAt_X_right M i]
        exact Ideal.subset_span (Set.mem_singleton _)
      · have hout : (b : Fin (2 * M)).val / 2 ≠ i.val := by
          have hb2 := b.2
          omega
        rw [blockProjQuotAt_mk, blockProjAt_X_outside M i hout]
        exact Submodule.zero_mem _
    · rw [Ideal.span_le]
      rintro _ rfl
      have hmem : blockProjQuotAt M i
          (lineQuotientMap M (X (blockVarRight M i))) ∈
          Ideal.map (blockProjQuotAt M i).toRingHom (lineClosedIdealAt M i) :=
        Ideal.mem_map_of_mem _ (lineQuotientMap_X_right_mem_lineClosedIdealAt M i)
      rw [blockProjQuotAt_mk, blockProjAt_X_right, lineClosedIdealAt,
        Ideal.map_span] at hmem
      exact hmem
  -- ybar lies inside (Z)
  have hybarle : ybar ≤ Ideal.span {(X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ)} := by
    rw [hybardef]
    calc Ideal.map (blockProjQuotAt M i).toRingHom y.asHomogeneousIdeal.toIdeal ≤
        Ideal.map (blockProjQuotAt M i).toRingHom (lineClosedIdealAt M i) :=
          Ideal.map_mono hstrict.le
      _ = Ideal.span {(X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ)} := hmapclosed
  -- ybar is strictly below (Z) (else the closed ideal would lie in y's)
  have hybarneZ : ybar ≠ Ideal.span {(X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ)} := by
    intro heq
    have hZmem : (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) ∈ ybar := by
      rw [heq]; exact Ideal.subset_span (Set.mem_singleton _)
    obtain ⟨w, hw, hwZ⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp hZmem
    have hker : w - lineQuotientMap M (X (blockVarRight M i)) ∈
        lineGenericIdeal M i := by
      rw [mem_lineGenericIdeal_iff M i]
      rw [map_sub, blockProjQuotAt_mk, blockProjAt_X_right M i, hwZ, sub_self]
    have hqmem : lineQuotientMap M (X (blockVarRight M i)) ∈
        y.asHomogeneousIdeal.toIdeal := by
      have hdiff : w - lineQuotientMap M (X (blockVarRight M i)) ∈
          y.asHomogeneousIdeal.toIdeal := hgen.le hker
      have hcalc : lineQuotientMap M (X (blockVarRight M i)) =
          w - (w - lineQuotientMap M (X (blockVarRight M i))) := by ring
      rw [hcalc]
      exact Submodule.sub_mem _ hw hdiff
    refine (ne_of_lt hstrict) ?_
    exact le_antisymm hstrict.le (by
      rw [lineClosedIdealAt_eq_supAt M i]
      exact sup_le hgen.le (by
        rw [Ideal.span_le]
        rintro _ rfl
        exact hqmem))
  -- Z is not in ybar (else ybar = (Z))
  have hZnotin : ¬ ((X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) ∈ ybar) := by
    intro hZ
    refine hybarneZ (le_antisymm hybarle ?_)
    rw [Ideal.span_singleton_le_iff_mem]
    exact hZ
  -- THE DEGREE-SHIFT RECEIPT: multiplying by the second variable raises the
  -- total degree by one (the support shifts through the monomial factor)
  have hge : ∀ g : MvPolynomial (Fin 2) ℂ, g ≠ 0 →
      MvPolynomial.totalDegree g + 1 ≤
        MvPolynomial.totalDegree ((X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) * g) := by
    intro g hg
    have hsupp : (MvPolynomial.support g).Nonempty := by
      rw [MvPolynomial.support_nonempty]
      exact hg
    obtain ⟨t, ht, htsup⟩ := Finset.exists_mem_eq_sup
      (MvPolynomial.support g) hsupp
      (fun s : Fin 2 →₀ ℕ => s.sum fun _ e => e :
        (Fin 2 →₀ ℕ) → ℕ)
    have hmem : (Finsupp.single (⟨1, by omega⟩ : Fin 2) 1 + t) ∈
        MvPolynomial.support ((X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) * g) := by
      rw [MvPolynomial.mem_support_iff,
        show (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) =
          MvPolynomial.monomial (Finsupp.single (⟨1, by omega⟩ : Fin 2) 1) 1 from rfl,
        MvPolynomial.coeff_monomial_mul, one_mul]
      exact (MvPolynomial.mem_support_iff.mp ht)
    have hwt : (Finsupp.single (⟨1, by omega⟩ : Fin 2) 1 + t).sum (fun _ e => e) =
        t.sum (fun _ e => e) + 1 := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_single_index]
      · omega
      · rfl
    rw [show MvPolynomial.totalDegree g = t.sum (fun _ e => e) from htsup]
    calc t.sum (fun _ e => e) + 1 =
          (Finsupp.single (⟨1, by omega⟩ : Fin 2) 1 + t).sum (fun _ e => e) := hwt.symm
      _ ≤ MvPolynomial.totalDegree
            ((X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) * g) :=
            MvPolynomial.le_totalDegree hmem
  -- THE ELEMENTARY DESCENT: every element of ybar is zero
  have hkill : ∀ n : ℕ, ∀ f : MvPolynomial (Fin 2) ℂ,
      MvPolynomial.totalDegree f ≤ n → f ∈ ybar → f = 0 := by
    intro n
    induction n with
    | zero =>
        intro f hfD hmem
        obtain ⟨g, hgf⟩ :=
          (Ideal.mem_span_singleton.mp (hybarle hmem) :
            (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) ∣ f)
        by_cases hg0 : g = 0
        · rw [hgf, hg0, mul_zero]
        · exfalso
          have h1 := hge g hg0
          rw [← hgf] at h1
          omega
    | succ m ih =>
        intro f hfD hmem
        obtain ⟨g, hgf⟩ :=
          (Ideal.mem_span_singleton.mp (hybarle hmem) :
            (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) ∣ f)
        have hmem' : (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) * g ∈ ybar := by
          rw [← hgf]; exact hmem
        rcases hybarprime.mem_or_mem hmem' with h1 | h2
        · exact absurd h1 hZnotin
        · by_cases hg0 : g = 0
          · rw [hgf, hg0, mul_zero]
          · rw [hgf, ih g (by
              have h1 := hge g hg0
              rw [← hgf] at h1
              omega) h2, mul_zero]
  have hybarbot : ybar = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr ?_
    intro f hmem
    exact hkill (MvPolynomial.totalDegree f) f (Nat.le_refl _) hmem
  exact hybarne hybarbot

/-- **THE CLOSED POINT AT LINE i LIES STRICTLY BELOW THE i-TH GENERIC
POINT.** -/
theorem lineClosedPointAt_lt (M : ℕ) (i : Fin M) :
    lineClosedPointAt M i < lineGenericPoint M i := by
  refine ⟨(le_iff_ideal M (lineClosedPointAt M i) (lineGenericPoint M i)).mpr ?_, ?_⟩
  · rw [lineClosedPointAt_asIdeal, lineGenericPoint_asIdeal]
    exact lineGenericIdeal_le_lineClosedIdealAt M i
  · intro heq
    have h1 : lineQuotientMap M (X (blockVarRight M i)) ∈ lineClosedIdealAt M i :=
      lineQuotientMap_X_right_mem_lineClosedIdealAt M i
    have h2 : lineQuotientMap M (X (blockVarRight M i)) ∉ lineGenericIdeal M i :=
      lineQuotientMap_X_pair_not_mem' M i
    apply h2
    have hI : (lineClosedPointAt M i).asHomogeneousIdeal.toIdeal =
        (lineGenericPoint M i).asHomogeneousIdeal.toIdeal :=
      le_antisymm ((le_iff_ideal M (lineGenericPoint M i) (lineClosedPointAt M i)).mp heq)
        ((le_iff_ideal M (lineClosedPointAt M i) (lineGenericPoint M i)).mp
          ((le_iff_ideal M (lineClosedPointAt M i) (lineGenericPoint M i)).mpr
            (by rw [lineClosedPointAt_asIdeal, lineGenericPoint_asIdeal];
                exact lineGenericIdeal_le_lineClosedIdealAt M i)))
    rw [lineClosedPointAt_asIdeal, lineGenericPoint_asIdeal] at hI
    rw [← hI]
    exact h1

/-- **THE LINE-i CLOSED POINT HAS COHEIGHT ONE.**  The lower bound is the
strict specialization below the generic point; the upper bound is the
no-intermediate law. -/
theorem lineClosedPointAt_coheight (M : ℕ) (i : Fin M) :
    Order.coheight (lineClosedPointAt M i) = 1 := by
  have hlower : (1 : ℕ∞) ≤ Order.coheight (lineClosedPointAt M i) := by
    have h := Order.coheight_add_one_le (lineClosedPointAt_lt M i)
    rw [lineGenericPoint_coheight M i] at h
    simpa using h
  have hupper : Order.coheight (lineClosedPointAt M i) ≤ ((1 : ℕ) : ℕ∞) := by
    rw [Order.coheight_le_coe_iff]
    intro w hw
    have hwle : w.asHomogeneousIdeal.toIdeal ≤ lineClosedIdealAt M i :=
      (le_iff_ideal M (lineClosedPointAt M i) w).mp hw.le
    have hwne : w.asHomogeneousIdeal.toIdeal ≠ lineClosedIdealAt M i := by
      intro heq
      have hwceq : w = lineClosedPointAt M i := by
        refine projectiveSpectrum_ext ?_
        refine HomogeneousIdeal.ext ?_
        rw [lineClosedPointAt_asIdeal]
        exact heq
      exact (ne_of_lt hw) hwceq.symm
    have hgen : lineGenericIdeal M i ≤ w.asHomogeneousIdeal.toIdeal := by
      rw [lineGenericIdeal, Ideal.span_le]
      rintro _ ⟨b, rfl⟩
      have hzero : lineQuotientMap M (X (blockVarLeft M i)) *
          lineQuotientMap M (X (b : Fin (2 * M))) = 0 :=
        crossMul_eq_zero M (fun hcon => b.2 (hcon.symm.trans
          (blockVarLeft_block M i)))
      have hX0 : lineQuotientMap M (X (blockVarLeft M i)) ∉
          w.asHomogeneousIdeal.toIdeal := fun hmem =>
        lineQuotientMap_X_left_not_mem_lineClosedIdealAt M i (hwle hmem)
      have hmem : lineQuotientMap M (X (blockVarLeft M i)) *
          lineQuotientMap M (X (b : Fin (2 * M))) ∈ w.asHomogeneousIdeal.toIdeal := by
        rw [hzero]; exact Submodule.zero_mem _
      rcases w.isPrime.mem_or_mem hmem with h1 | h2
      · exact absurd h1 hX0
      · exact h2
    rcases eq_or_ne w.asHomogeneousIdeal.toIdeal (lineGenericIdeal M i) with heq | hne
    · have hwgen : w = lineGenericPoint M i :=
        eq_lineGenericPoint_of_le M i w (by rw [heq])
      rw [hwgen, lineGenericPoint_coheight M i]
      norm_num
    · exact absurd
        (no_intermediate_pointAt M i w
          ⟨hgen, fun hle => hne (le_antisymm hle hgen)⟩
          ⟨hwle, fun hle => hwne (le_antisymm hwle hle)⟩) False.elim
  have hne : Order.coheight (lineClosedPointAt M i) ≠ ⊤ := by
    intro htop
    rw [htop] at hupper
    exact absurd hupper (by simp)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hn] at hupper hlower ⊢
  have hn1 : n ≤ 1 := ENat.natCast_le_natCast.mp hupper
  have hn2 : 1 ≤ n := ENat.natCast_le_natCast.mp hlower
  rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl]
  exact congrArg ((↑) : ℕ → ℕ∞) (le_antisymm (α := ℕ) hn1 hn2)

/-! ## §5 The component machinery -/

/-- The generic points are distinguished by their ideals. -/
theorem lineGenericPoint_injective (M : ℕ) :
    Function.Injective (lineGenericPoint M) := by
  intro i k hik
  by_contra hne
  have hne' : i.val ≠ k.val := fun h => hne (Fin.ext h)
  have hmem : lineQuotientMap M (X (blockVarLeft M i)) ∈
      lineGenericIdeal M k := by
    refine mem_lineGenericIdeal M k ?_
    show (blockVarLeft M i).val / 2 ≠ k.val
    rw [blockVarLeft_val]
    omega
  have hnot : lineQuotientMap M (X (blockVarLeft M i)) ∉
      lineGenericIdeal M i :=
    lineQuotientMap_X_pair_not_mem M i
  apply hnot
  have hII : (lineGenericPoint M i).asHomogeneousIdeal =
      (lineGenericPoint M k).asHomogeneousIdeal :=
    congrArg ProjectiveSpectrum.asHomogeneousIdeal hik
  have h1 := congrArg HomogeneousIdeal.toIdeal hII
  rw [lineGenericPoint_asIdeal, lineGenericPoint_asIdeal] at h1
  rw [h1]
  exact hmem

/-- **THE COHEIGHT-ZERO POINTS ARE THE GENERIC POINTS.** -/
theorem exists_eq_lineGenericPoint (M : ℕ) (η : finiteLineScheme M)
    (hη : Order.coheight η = 0) :
    ∃ i : Fin M, η = lineGenericPoint M i := by
  obtain ⟨a, ha⟩ := exists_variable_not_mem M η
  have hmax : IsMax η := (Order.coheight_eq_zero).mp hη
  refine ⟨⟨a.val / 2, by have := a.isLt; omega⟩, ?_⟩
  have hgen : lineGenericIdeal M ⟨a.val / 2, by have := a.isLt; omega⟩ ≤
      η.asHomogeneousIdeal.toIdeal := by
    rw [lineGenericIdeal, Ideal.span_le]
    rintro _ ⟨b, rfl⟩
    have hzero : lineQuotientMap M (X a) *
        lineQuotientMap M (X (b : Fin (2 * M))) = 0 :=
      crossMul_eq_zero M (fun hcon => b.2 hcon.symm)
    have hmem : lineQuotientMap M (X a) *
        lineQuotientMap M (X (b : Fin (2 * M))) ∈
        η.asHomogeneousIdeal.toIdeal := by
      rw [hzero]; exact Submodule.zero_mem _
    rcases η.isPrime.mem_or_mem hmem with h1 | h2
    · exact absurd h1 ha
    · exact h2
  have hle : η ≤ lineGenericPoint M ⟨a.val / 2, by have := a.isLt; omega⟩ :=
    (le_iff_ideal M η
      (lineGenericPoint M ⟨a.val / 2, by have := a.isLt; omega⟩)).mpr hgen
  exact le_antisymm hle (hmax hle)

/-- **THE GENERIC INDEX** — the coheight-zero points indexed by `Fin M`. -/
noncomputable def lineIndexOfGeneric (M : ℕ)
    (η : CodimensionPoint (finiteLineScheme M) 0) : Fin M :=
  Classical.choose (exists_eq_lineGenericPoint M η.1 η.2)

theorem lineIndexOfGeneric_spec (M : ℕ)
    (η : CodimensionPoint (finiteLineScheme M) 0) :
    lineGenericPoint M (lineIndexOfGeneric M η) = η.1 :=
  (Classical.choose_spec (exists_eq_lineGenericPoint M η.1 η.2)).symm

theorem lineIndexOfGeneric_lineGenericPoint (M : ℕ) (i : Fin M) :
    lineIndexOfGeneric M ⟨lineGenericPoint M i, lineGenericPoint_coheight M i⟩ = i :=
  lineGenericPoint_injective M (lineIndexOfGeneric_spec M _)

/-- **THE UNIQUE GENERIC ABOVE A COHEIGHT-ONE POINT.** -/
theorem exists_unique_generic_above (M : ℕ)
    (x : CodimensionPoint (finiteLineScheme M) 1) :
    ∃ η₀ : CodimensionPoint (finiteLineScheme M) 0, x.1 < η₀.1 ∧
      ∀ η : CodimensionPoint (finiteLineScheme M) 0, x.1 < η.1 → η = η₀ := by
  have hfin : Order.coheight x.1 < ⊤ := by
    rw [x.2]
    first
    | exact ENat.natCast_lt_top 1
    | simp
  have hlt : (0 : ℕ) < Order.coheight x.1 := by
    rw [x.2]
    first
    | exact_mod_cast (by norm_num : (0:ℕ) < (1:ℕ))
    | simp
    | norm_num
  obtain ⟨η, hxη, hη⟩ :=
    (Order.coe_lt_coheight_iff (x := x.1) (n := 0) hfin).mp hlt
  refine ⟨⟨η, hη⟩, hxη, ?_⟩
  rintro ⟨η'v, hη'⟩ hxη'
  have hxη'' : x.1 < η'v := hxη'
  obtain ⟨k, hk⟩ := exists_eq_lineGenericPoint M η hη
  obtain ⟨k', hk'⟩ := exists_eq_lineGenericPoint M η'v hη'
  have hkx : lineGenericIdeal M k ≤ x.1.asHomogeneousIdeal.toIdeal := by
    rw [hk] at hxη
    rw [← lineGenericPoint_asIdeal]
    exact (le_iff_ideal M x.1 (lineGenericPoint M k)).mp (le_of_lt hxη)
  have hkx' : lineGenericIdeal M k' ≤ x.1.asHomogeneousIdeal.toIdeal := by
    rw [hk'] at hxη''
    rw [← lineGenericPoint_asIdeal]
    exact (le_iff_ideal M x.1 (lineGenericPoint M k')).mp (le_of_lt hxη'')
  have hkk : k = k' := by
    by_contra hne
    apply x.1.not_irrelevant_le
    show (HomogeneousIdeal.irrelevant (lineGrading M)).toIdeal ≤
      x.1.asHomogeneousIdeal.toIdeal
    exact irrelevant_le_of_mem_variables M _ (fun a => by
      rcases eq_or_ne (a.val / 2) k.val with hblock | hblock
      · exact hkx' (mem_lineGenericIdeal M k'
          (fun hcon => hne (Fin.ext (hcon.symm.trans hblock).symm)))
      · exact hkx (mem_lineGenericIdeal M k hblock))
  have hηeq : η = η'v := by rw [hk, hk', hkk]
  exact Subtype.ext hηeq.symm

/-- **THE COMPONENT MAP** — the unique generic point above a coheight-one
point. -/
noncomputable def lineComponentOf (M : ℕ)
    (x : CodimensionPoint (finiteLineScheme M) 1) :
    CodimensionPoint (finiteLineScheme M) 0 :=
  Classical.choose (exists_unique_generic_above M x)

theorem lineComponentOf_above (M : ℕ)
    (x : CodimensionPoint (finiteLineScheme M) 1) :
    x.1 < (lineComponentOf M x).1 :=
  (Classical.choose_spec (exists_unique_generic_above M x)).1

theorem lineComponentOf_unique (M : ℕ) (x : CodimensionPoint (finiteLineScheme M) 1)
    (η : CodimensionPoint (finiteLineScheme M) 0) (hη : x.1 < η.1) :
    η = lineComponentOf M x :=
  (Classical.choose_spec (exists_unique_generic_above M x)).2 η hη

/-- **THE LINE-i CLOSED POINT LIES ON THE i-TH LINE.** -/
theorem lineClosedPointAt_component (M : ℕ) (i : Fin M) :
    lineComponentOf M ⟨lineClosedPointAt M i, lineClosedPointAt_coheight M i⟩ =
      ⟨lineGenericPoint M i, lineGenericPoint_coheight M i⟩ :=
  (lineComponentOf_unique M _ _ (lineClosedPointAt_lt M i)).symm

/-! ## §6 The honest seed cycles -/

/-- The unit point-cycle is nonzero (its coefficient at the point is
one). -/
theorem codimensionPointCycle_ne_zero {X : Scheme} {p : Nat}
    (x : CodimensionPoint X p) :
    codimensionPointCycle X p x ≠ 0 := by
  intro h
  have h2 : ((codimensionPointCycle X p x : AlgebraicCycle X ℚ) : X → ℚ) x.1 = 1 := by
    simp [codimensionPointCycle, Function.locallyFinsuppWithin.single_apply]
  rw [h] at h2
  simpa using h2

/-- **THE HONEST WEIGHT-ZERO SEED** — the atom at the 0-th generic point. -/
noncomputable def lineHonestSeedZero (M : ℕ) [NeZero M] :
    codimensionCycles (finiteLineScheme M) 0 :=
  codimensionPointCycle (finiteLineScheme M) 0
    ⟨lineGenericPoint M ⟨0, Nat.pos_of_neZero ‹_›⟩,
      lineGenericPoint_coheight M ⟨0, Nat.pos_of_neZero ‹_›⟩⟩

theorem lineHonestSeedZero_ne (M : ℕ) [NeZero M] : lineHonestSeedZero M ≠ 0 :=
  codimensionPointCycle_ne_zero _

/-- **THE HONEST WEIGHT-ONE SEED** — the atom at the 0-th line's closed
point. -/
noncomputable def lineHonestSeedOne (M : ℕ) [NeZero M] :
    codimensionCycles (finiteLineScheme M) 1 :=
  codimensionPointCycle (finiteLineScheme M) 1
    ⟨lineClosedPointAt M ⟨0, Nat.pos_of_neZero ‹_›⟩,
      lineClosedPointAt_coheight M ⟨0, Nat.pos_of_neZero ‹_›⟩⟩

theorem lineHonestSeedOne_ne (M : ℕ) [NeZero M] : lineHonestSeedOne M ≠ 0 :=
  codimensionPointCycle_ne_zero _

/-! ## Receipts -/

#check lineGenericPoint
#check lineGenericPoint_coheight
#check lineClosedPointAt
#check lineClosedPointAt_coheight
#check lineClosedPointAt_lt
#check lineClosedPointAt_component
#check le_iff_ideal
#check lineComponentOf
#check lineComponentOf_above
#check lineComponentOf_unique
#check lineIndexOfGeneric
#check lineIndexOfGeneric_lineGenericPoint
#check lineHonestSeedZero
#check lineHonestSeedZero_ne
#check lineHonestSeedOne
#check lineHonestSeedOne_ne
#check crossMul_eq_zero
#check no_intermediate_pointAt

#print axioms lineGenericPoint
#print axioms lineGenericPoint_coheight
#print axioms lineClosedPointAt
#print axioms lineClosedPointAt_coheight
#print axioms no_intermediate_pointAt
#print axioms lineComponentOf
#print axioms lineHonestSeedZero_ne
#print axioms lineHonestSeedOne_ne

end GSTFiniteLinePointAlgebra

end -- noncomputable section

