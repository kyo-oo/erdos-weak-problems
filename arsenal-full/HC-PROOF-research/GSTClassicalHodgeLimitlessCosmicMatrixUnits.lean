import GSTGlobalPureHodgeCosmology
import GSTUniversalAddressBridge
import GSTDimensionFreeHodgeDiagonal
import GSTUniversalLefschetzPathFormula
import GSTWorldPoincareDuality
import GSTWorldRecoordinationGroupoid
import GSTTransferBridgeV2

/-!
# GST CLASSICAL HODGE — LIMITLESS COSMIC MATRIX-UNIT ARTERY

This file uses the completed/compact GST cosmos directly.  No finite `Fin 12`
carrier and no fixed Hodge rank appears.

The key limitless operation is read/write on the diagonal:

* read weight `i` by the nondegenerate cosmic Poincare probe at `(i,i)`;
* write that coefficient into the genuine compact cosmic Hodge generator at
  `(j,j)`.

This produces an honest matrix-unit algebra on the unbounded pure-Hodge
cosmology.  Finite GST projector/Lefschetz/Poincare words are therefore finite
observations of an intrinsically limitless read/write mechanism rather than
independent finite constructions.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators

namespace GSTClassicalHodgeLimitlessCosmicMatrixUnits

open GSTWorldCosmology
open GSTUniversalAddressBridge
open GSTDimensionFreeHodgeDiagonal
open GSTGlobalPureHodgeCosmology
open GSTWorldPoincareDuality
open GSTUniversalLefschetzPathFormula
open GSTTransferBridgeV2

/-- The integral limitless diagonal matrix unit: read the `i`-th cosmic Hodge
weight by Poincare duality and write it into weight `j`. -/
def cosmicDiagonalMatrixUnit (i j : ℕ) : Module.End ℤ CompactCosmos where
  toFun f := Finsupp.single (j,j) (cosmicPairing f (cosmicProbe (i,i)))
  map_add' := by
    intro f g
    ext c
    simp [cosmicPairing_probe, Finsupp.single_add, Finsupp.add_apply]
  map_smul' := by
    intro z f
    ext c
    simp [cosmicPairing_probe, Finsupp.smul_single, smul_eq_mul]

@[simp]
theorem cosmicDiagonalMatrixUnit_apply
    (i j : ℕ) (f : CompactCosmos) :
    cosmicDiagonalMatrixUnit i j f =
      Finsupp.single (j,j) (f (i,i)) := by
  simp [cosmicDiagonalMatrixUnit, cosmicPairing_probe]

/-- The operator is literally `Poincare read at i` followed by `Hodge write at
j`. -/
theorem cosmicDiagonalMatrixUnit_read_write
    (i j : ℕ) (f : CompactCosmos) :
    cosmicDiagonalMatrixUnit i j f =
      cosmicPairing f (cosmicProbe (i,i)) • cosmicDiagonalClass j := by
  rw [cosmicDiagonalMatrixUnit_apply]
  simp [cosmicDiagonalClass]

/-- Exact action on every limitless Hodge basis generator. -/
theorem cosmicDiagonalMatrixUnit_on_generator
    (i j k : ℕ) :
    cosmicDiagonalMatrixUnit i j (cosmicDiagonalClass k) =
      if k = i then cosmicDiagonalClass j else 0 := by
  by_cases h : k = i
  · subst k
    simp [cosmicDiagonalMatrixUnit_apply, cosmicDiagonalClass]
  · ext c
    simp [cosmicDiagonalMatrixUnit_apply, cosmicDiagonalClass, h]

/-- Diagonal matrix units compose with the exact matrix-unit law. -/
theorem cosmicDiagonalMatrixUnit_comp
    (i j k : ℕ) :
    (cosmicDiagonalMatrixUnit j k).comp
        (cosmicDiagonalMatrixUnit i j) =
      cosmicDiagonalMatrixUnit i k := by
  apply LinearMap.ext
  intro f
  simp [cosmicDiagonalMatrixUnit_apply]

/-- Matrix units with a mismatched intermediate weight annihilate. -/
theorem cosmicDiagonalMatrixUnit_comp_zero
    (i j k l : ℕ) (h : j ≠ k) :
    (cosmicDiagonalMatrixUnit k l).comp
        (cosmicDiagonalMatrixUnit i j) = 0 := by
  apply LinearMap.ext
  intro f
  ext c
  simp [cosmicDiagonalMatrixUnit_apply, h]

/-- Every cosmic matrix unit preserves the compact pure-Hodge sector. -/
theorem cosmicDiagonalMatrixUnit_preserves_pure
    (i j : ℕ) (f : compactPureHodge) :
    ∀ c, c.1 ≠ c.2 → cosmicDiagonalMatrixUnit i j f.1 c = 0 := by
  intro c hc
  rw [cosmicDiagonalMatrixUnit_apply]
  have hne : c ≠ (j, j) := fun heq => hc (by simp [heq])
  simp [hne]

/-- The universal address dictionary reads a cosmic matrix unit as one exact
address basis vector. -/
theorem compactAddress_cosmicDiagonalMatrixUnit
    (i j : ℕ) (f : CompactCosmos) :
    compactAddressEquiv (cosmicDiagonalMatrixUnit i j f) =
      Finsupp.single (cosmicAddressEquiv (j,j)) (f (i,i)) := by
  rw [cosmicDiagonalMatrixUnit_apply]
  ext n
  simp [compactAddressEquiv]

/-- The limitless transfer generator is exactly the address image of the
write-basis used by the matrix-unit artery. -/
theorem transfer_generator_is_matrixUnit_write_basis
    (p : ℕ) :
    compactClMono p =
      compactAddressEquiv (cosmicDiagonalClass p) := by
  exact compactClMono_eq_cosmicDiagonalAddress p

/-- Finite windows see the matrix-unit output as the expected scalar multiple
of the finite diagonal generator whenever the target weight is visible. -/
theorem observe_cosmicDiagonalMatrixUnit
    {A B : ℕ} (i j : ℕ)
    (hjA : j < A) (hjB : j < B)
    (f : CompactCosmos) :
    observe A B (cosmicDiagonalMatrixUnit i j f) =
      f (i,i) • worldDiagonalClass hjA hjB := by
  rw [cosmicDiagonalMatrixUnit_apply]
  have hobs := observe_cosmicDiagonalClass (A:=A) (B:=B) hjA hjB
  have hlin : observe A B (Finsupp.single (j, j) (f (i, i))) =
      f (i, i) • observe A B (cosmicDiagonalClass j) := by
    funext c
    have hsmul : (f (i, i) • observe A B (cosmicDiagonalClass j)) c
        = f (i, i) * observe A B (cosmicDiagonalClass j) c := rfl
    rw [hsmul]
    by_cases hc : (j, j) = (↑c.1, ↑c.2)
    · simp [observe, cosmicDiagonalClass, Finsupp.single_apply, hc, mul_one]
    · simp [observe, cosmicDiagonalClass, Finsupp.single_apply, hc, mul_zero]
  rw [hlin]
  exact congrArg (fun g : WorldCoef A B => f (i,i) • g) hobs

/-- If the target weight lies outside a finite observation window, the same
limitless matrix-unit action becomes invisible rather than ceasing to exist. -/
theorem observe_cosmicDiagonalMatrixUnit_invisible
    {A B : ℕ} (i j : ℕ)
    (hout : A ≤ j ∨ B ≤ j)
    (f : CompactCosmos) :
    observe A B (cosmicDiagonalMatrixUnit i j f) = 0 := by
  rw [cosmicDiagonalMatrixUnit_apply]
  have hzero := cosmic_weight_invisible (A:=A) (B:=B) (p:=j) hout
  have hlin : observe A B (Finsupp.single (j, j) (f (i, i))) =
      f (i, i) • observe A B (cosmicDiagonalClass j) := by
    funext c
    have hsmul : (f (i, i) • observe A B (cosmicDiagonalClass j)) c
        = f (i, i) * observe A B (cosmicDiagonalClass j) c := rfl
    rw [hsmul]
    by_cases hc : (j, j) = (↑c.1, ↑c.2)
    · simp [observe, cosmicDiagonalClass, Finsupp.single_apply, hc, mul_one]
    · simp [observe, cosmicDiagonalClass, Finsupp.single_apply, hc, mul_zero]
  rw [hlin, hzero, smul_zero]

/-! ## Rational limitless pure-address algebra

The classical Hodge fiber is rational.  Its limitless GST shadow therefore
uses the rationalization of the compact pure-address universe, namely
finitely-supported rational functions on all natural Hodge weights.
-/

abbrev RationalPureCosmos := ℕ →₀ ℚ

/-- Rational limitless basis vector at weight `p`. -/
def rationalCosmicBasis (p : ℕ) : RationalPureCosmos :=
  Finsupp.single p 1

/-- Rank-free rational cosmic matrix unit. -/
def rationalCosmicMatrixUnit (i j : ℕ) : Module.End ℚ RationalPureCosmos where
  toFun f := Finsupp.single j (f i)
  map_add' := by intro f g; ext k; simp
  map_smul' := by intro q f; ext k; simp

@[simp]
theorem rationalCosmicMatrixUnit_apply
    (i j : ℕ) (f : RationalPureCosmos) :
    rationalCosmicMatrixUnit i j f = Finsupp.single j (f i) := rfl

@[simp]
theorem rationalCosmicMatrixUnit_basis
    (i j k : ℕ) :
    rationalCosmicMatrixUnit i j (rationalCosmicBasis k) =
      if k = i then rationalCosmicBasis j else 0 := by
  by_cases h : k = i
  · subst k
    simp [rationalCosmicMatrixUnit, rationalCosmicBasis]
  · ext n
    simp [rationalCosmicMatrixUnit, rationalCosmicBasis, h]

/-- Rational limitless matrix-unit composition. -/
theorem rationalCosmicMatrixUnit_comp
    (i j k : ℕ) :
    (rationalCosmicMatrixUnit j k).comp
        (rationalCosmicMatrixUnit i j) =
      rationalCosmicMatrixUnit i k := by
  apply LinearMap.ext
  intro f
  simp [rationalCosmicMatrixUnit]

/-- Coordinate extraction is complete on the rational compact cosmos. -/
theorem exists_nonzero_rationalCosmicCoordinate
    {f : RationalPureCosmos} (hf : f ≠ 0) :
    ∃ i : ℕ, f i ≠ 0 := by
  by_contra h
  push_neg at h
  apply hf
  ext i
  exact h i

/-- **LIMITLESS PURE-HODGE IRREDUCIBILITY.**
A nonzero rational submodule invariant under every cosmic diagonal matrix unit
is the entire finitely-supported pure-Hodge cosmos. -/
theorem rationalCosmic_invariant_eq_top
    (S : Submodule ℚ RationalPureCosmos)
    (hstable : ∀ i j f, f ∈ S → rationalCosmicMatrixUnit i j f ∈ S)
    (hne : S ≠ ⊥) :
    S = ⊤ := by
  apply top_unique
  intro g hg
  obtain ⟨f, hfS, hf0⟩ : ∃ f : RationalPureCosmos, f ∈ S ∧ f ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    ext f
    constructor
    · intro hf
      simpa [h f hf]
    · intro hf
      rw [Submodule.mem_bot] at hf
      subst hf
      exact Submodule.zero_mem S
  obtain ⟨i, hi⟩ := exists_nonzero_rationalCosmicCoordinate hf0
  have hbasis : ∀ j : ℕ, rationalCosmicBasis j ∈ S := by
    intro j
    have hmove := hstable i j f hfS
    have hscaled : f i • rationalCosmicBasis j ∈ S := by
      simpa [rationalCosmicMatrixUnit, rationalCosmicBasis] using hmove
    have hinv := S.smul_mem ((f i)⁻¹) hscaled
    simpa [hi, smul_smul] using hinv
  rw [← g.sum_single]
  refine S.sum_mem fun j _ => ?_
  simpa [rationalCosmicBasis, Finsupp.smul_single, smul_eq_mul, mul_one] using
    S.smul_mem (g j) (hbasis j)

/-- Crown collecting the actual limitless Hodge artery: unbounded generators,
universal addresses, Poincare read/write matrix units, and rational
irreducibility are one system. -/
theorem limitless_cosmic_matrix_unit_crown :
    (∀ p : ℕ, cosmicDiagonalClass p (p,p) = 1)
    ∧ (∀ i j k : ℕ,
        cosmicDiagonalMatrixUnit i j (cosmicDiagonalClass k) =
          if k = i then cosmicDiagonalClass j else 0)
    ∧ (∀ p : ℕ,
        compactClMono p = compactAddressEquiv (cosmicDiagonalClass p))
    ∧ (∀ S : Submodule ℚ RationalPureCosmos,
        (∀ i j f, f ∈ S → rationalCosmicMatrixUnit i j f ∈ S) →
        S ≠ ⊥ → S = ⊤) := by
  exact ⟨cosmicDiagonalClass_self,
    cosmicDiagonalMatrixUnit_on_generator,
    transfer_generator_is_matrixUnit_write_basis,
    rationalCosmic_invariant_eq_top⟩

#check cosmicDiagonalMatrixUnit
#check cosmicDiagonalMatrixUnit_read_write
#check cosmicDiagonalMatrixUnit_on_generator
#check cosmicDiagonalMatrixUnit_comp
#check compactAddress_cosmicDiagonalMatrixUnit
#check observe_cosmicDiagonalMatrixUnit
#check rationalCosmicMatrixUnit
#check rationalCosmic_invariant_eq_top
#check limitless_cosmic_matrix_unit_crown

#print axioms cosmicDiagonalMatrixUnit_on_generator
#print axioms cosmicDiagonalMatrixUnit_comp
#print axioms compactAddress_cosmicDiagonalMatrixUnit
#print axioms observe_cosmicDiagonalMatrixUnit
#print axioms rationalCosmic_invariant_eq_top
#print axioms limitless_cosmic_matrix_unit_crown

end GSTClassicalHodgeLimitlessCosmicMatrixUnits
