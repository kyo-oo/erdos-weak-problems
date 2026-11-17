import GSTClassicalHodgeExplicitArsenalGeneration
import GSTClassicalHodgePrimitiveArsenalRationalization
import GSTPureHodgeLefschetzKernel
import GSTSquarePureHodgeDuality

/-!
# GST CLASSICAL HODGE — LEFSCHETZ/POINCARE MATRIX GENERATION

The spectral code projector is not actually needed to generate the finite
pure-Hodge matrix algebra.

The universal pure-Hodge Lefschetz kernel proves that the diagonal part of
`L^2` sends one pure sheet to the next with coefficient exactly 2 and has no
other diagonal matrix entries.  After dividing by 2 we obtain the one-step
forward shift `S`.  Poincare reversal conjugates `S` to the one-step backward
shift `T`.

Then

  P₀ = I - S T

is the bottom-sheet projector, and every matrix unit is

  E_pq = S^q P₀ T^p.

Therefore *Lefschetz plus Poincare alone* generate the complete finite matrix
algebra.  Code-sector spectral projectors are a redundant convenience, not a
primitive ingredient of the final irreducibility mechanism.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open GSTWorldCosmology
open GSTWorldPoincareDuality
open GSTDimensionFreeHodgeDiagonal
open GSTGlobalPureHodgeCosmology
open GSTTruncatedWorldCohomologyRing
open GSTUniversalLefschetzKernel
open GSTPureHodgeLefschetzKernel
open GSTSquarePureHodgeDuality
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgeExplicitArsenalGeneration
open GSTClassicalHodgePrimitiveArsenalRationalization

namespace GSTClassicalHodgeLefschetzPoincareMatrixGeneration

/-- Normalized diagonal part of the genuine GST operator `L^2`. -/
noncomputable def pureForwardShift
    (N : Nat) : Module.End ℚ (RationalPureWindow N) :=
  (2 : ℚ)⁻¹ • diagonalLefschetzQ N 2

/-- Poincare conjugate of the normalized forward shift. -/
noncomputable def pureBackwardShift
    (N : Nat) : Module.End ℚ (RationalPureWindow N) :=
  poincareConjugate (pureForwardShift N)

/-- `L^2/2` is exactly the one-step forward shift on a pure basis sheet. -/
theorem pureForwardShift_basis
    {N : Nat} (p : Fin N) :
    pureForwardShift N (rationalPureBasis p) =
      if h : p.1 + 1 < N then
        rationalPureBasis (⟨p.1 + 1, h⟩ : Fin N)
      else 0 := by
  funext q
  unfold pureForwardShift
  simp only [LinearMap.smul_apply, Pi.smul_apply]
  rw [diagonalLefschetzQ_basis]
  rw [pure_diagonal_lefschetz_kernel]
  by_cases hsucc : p.1 + 1 < N
  · rw [dif_pos hsucc]
    let s : Fin N := ⟨p.1 + 1, hsucc⟩
    by_cases hq : q = s
    · subst q
      show (2⁻¹ : ℚ) • ↑(if hpq : ↑(Fin.castLE (show N ≤ min N N by omega) p) ≤
              ↑(Fin.castLE (show N ≤ min N N by omega) s) then
          if htime : 2 = 2 * pureWeightGap
              (Fin.castLE (show N ≤ min N N by omega) p)
              (Fin.castLE (show N ≤ min N N by omega) s) then
            ((Nat.choose 2 (pureWeightGap
              (Fin.castLE (show N ≤ min N N by omega) p)
              (Fin.castLE (show N ≤ min N N by omega) s)) : ℕ) : ℤ)
          else (0 : ℤ)
        else (0 : ℤ)) = rationalPureBasis ⟨p.1 + 1, hsucc⟩ s
      have hpq : ↑(Fin.castLE (show N ≤ min N N by omega) p) ≤
          ↑(Fin.castLE (show N ≤ min N N by omega) s) := Nat.le_succ p.1
      rw [dif_pos hpq]
      have htime : 2 = 2 * pureWeightGap
          (Fin.castLE (show N ≤ min N N by omega) p)
          (Fin.castLE (show N ≤ min N N by omega) s) := by
        show 2 = 2 * (s.1 - p.1)
        have hs : s.1 = p.1 + 1 := rfl
        omega
      rw [dif_pos htime]
      have hgap : pureWeightGap
          (Fin.castLE (show N ≤ min N N by omega) p)
          (Fin.castLE (show N ≤ min N N by omega) s) = 1 := by
        show s.1 - p.1 = 1
        have hs : s.1 = p.1 + 1 := rfl
        omega
      rw [hgap]
      simp [rationalPureBasis, s]
    · by_cases hpq : p.1 ≤ q.1
      · show (2⁻¹ : ℚ) • ↑(if hpq : ↑(Fin.castLE (show N ≤ min N N by omega) p) ≤
              ↑(Fin.castLE (show N ≤ min N N by omega) q) then
          if htime : 2 = 2 * pureWeightGap
              (Fin.castLE (show N ≤ min N N by omega) p)
              (Fin.castLE (show N ≤ min N N by omega) q) then
            ((Nat.choose 2 (pureWeightGap
              (Fin.castLE (show N ≤ min N N by omega) p)
              (Fin.castLE (show N ≤ min N N by omega) q)) : ℕ) : ℤ)
          else (0 : ℤ)
        else (0 : ℤ)) = rationalPureBasis ⟨p.1 + 1, hsucc⟩ q
        have hpq' : ↑(Fin.castLE (show N ≤ min N N by omega) p) ≤
            ↑(Fin.castLE (show N ≤ min N N by omega) q) := hpq
        rw [dif_pos hpq']
        have hgap : pureWeightGap
            (Fin.castLE (show N ≤ min N N by omega) p)
            (Fin.castLE (show N ≤ min N N by omega) q) = q.1 - p.1 := rfl
        have htime : 2 ≠ 2 * pureWeightGap
            (Fin.castLE (show N ≤ min N N by omega) p)
            (Fin.castLE (show N ≤ min N N by omega) q) := by
          rw [hgap]
          intro ht
          have : q.1 = p.1 + 1 := by omega
          exact hq (Fin.ext this)
        rw [dif_neg htime]
        have hq' : q.1 ≠ p.1 + 1 := fun hval => hq (Fin.ext hval)
        have hqne : ¬ q = ⟨p.1 + 1, hsucc⟩ := by
          intro hqeq
          exact hq' (congrArg Fin.val hqeq)
        simp [rationalPureBasis, hqne]
      · show (2⁻¹ : ℚ) • ↑(if hpq : ↑(Fin.castLE (show N ≤ min N N by omega) p) ≤
              ↑(Fin.castLE (show N ≤ min N N by omega) q) then
          if htime : 2 = 2 * pureWeightGap
              (Fin.castLE (show N ≤ min N N by omega) p)
              (Fin.castLE (show N ≤ min N N by omega) q) then
            ((Nat.choose 2 (pureWeightGap
              (Fin.castLE (show N ≤ min N N by omega) p)
              (Fin.castLE (show N ≤ min N N by omega) q)) : ℕ) : ℤ)
          else (0 : ℤ)
        else (0 : ℤ)) = rationalPureBasis ⟨p.1 + 1, hsucc⟩ q
        have hpq' : ¬ ↑(Fin.castLE (show N ≤ min N N by omega) p) ≤
            ↑(Fin.castLE (show N ≤ min N N by omega) q) := hpq
        rw [dif_neg hpq']
        have hq' : q.1 ≠ p.1 + 1 := fun hval => hq (Fin.ext hval)
        have hqne : ¬ q = ⟨p.1 + 1, hsucc⟩ := by
          intro hqeq
          exact hq' (congrArg Fin.val hqeq)
        simp [rationalPureBasis, hqne]
  · rw [dif_neg hsucc]
    show (2⁻¹ : ℚ) • ↑(if hpq : ↑(Fin.castLE (show N ≤ min N N by omega) p) ≤
          ↑(Fin.castLE (show N ≤ min N N by omega) q) then
        if htime : 2 = 2 * pureWeightGap
            (Fin.castLE (show N ≤ min N N by omega) p)
            (Fin.castLE (show N ≤ min N N by omega) q) then
          ((Nat.choose 2 (pureWeightGap
            (Fin.castLE (show N ≤ min N N by omega) p)
            (Fin.castLE (show N ≤ min N N by omega) q)) : ℕ) : ℤ)
        else (0 : ℤ)
      else (0 : ℤ)) = (0 : ℚ)
    by_cases hpq : p.1 ≤ q.1
    · have hpq' : ↑(Fin.castLE (show N ≤ min N N by omega) p) ≤
          ↑(Fin.castLE (show N ≤ min N N by omega) q) := hpq
      rw [dif_pos hpq']
      have hgap : pureWeightGap
          (Fin.castLE (show N ≤ min N N by omega) p)
          (Fin.castLE (show N ≤ min N N by omega) q) = q.1 - p.1 := rfl
      have htime : 2 ≠ 2 * pureWeightGap
          (Fin.castLE (show N ≤ min N N by omega) p)
          (Fin.castLE (show N ≤ min N N by omega) q) := by
        rw [hgap]
        intro ht
        have : p.1 + 1 ≤ q.1 := by omega
        exact hsucc (lt_of_le_of_lt this q.2)
      rw [dif_neg htime]
      simp
    · have hpq' : ¬ ↑(Fin.castLE (show N ≤ min N N by omega) p) ≤
          ↑(Fin.castLE (show N ≤ min N N by omega) q) := hpq
      rw [dif_neg hpq']
      simp

/-- Poincare conjugation turns the forward shift into the exact one-step
backward shift. -/
theorem pureBackwardShift_basis
    {N : Nat} (p : Fin N) :
    pureBackwardShift N (rationalPureBasis p) =
      if h : 0 < p.1 then
        rationalPureBasis (⟨p.1 - 1, by omega⟩ : Fin N)
      else 0 := by
  rw [show pureBackwardShift N (rationalPureBasis p) =
      poincareReverseQ N ((pureForwardShift N) (poincareReverseQ N (rationalPureBasis p))) from
    poincareConjugate_apply (pureForwardShift N) (rationalPureBasis p)]
  rw [poincareReverseQ_basis]
  rw [pureForwardShift_basis]
  by_cases hp : 0 < p.1
  · rw [dif_pos hp]
    by_cases hsucc : (windowMirror p).1 + 1 < N
    · rw [dif_pos hsucc]
      rw [poincareReverseQ_basis]
      apply congrArg rationalPureBasis
      apply Fin.ext
      unfold windowMirror
      simp only
      have := p.2
      omega
    · exfalso
      have hwm : (windowMirror p).1 = N - 1 - p.1 := by
        unfold windowMirror
        simp only
      omega
  · rw [dif_neg hp]
    by_cases hsucc : (windowMirror p).1 + 1 < N
    · exfalso
      have hwm : (windowMirror p).1 = N - 1 - p.1 := by
        unfold windowMirror
        simp only
      omega
    · rw [dif_neg hsucc]
      simp

/-- Bottom-sheet projector constructed only from the two Lefschetz/Poincare
shifts. -/
noncomputable def bottomProjectorLP
    (N : Nat) : Module.End ℚ (RationalPureWindow N) :=
  LinearMap.id - (pureForwardShift N).comp (pureBackwardShift N)

/-- The derived endpoint projector fixes the bottom sheet. -/
theorem bottomProjectorLP_bottom
    {N : Nat} (hN : 0 < N) :
    bottomProjectorLP N
        (rationalPureBasis (⟨0, hN⟩ : Fin N)) =
      rationalPureBasis (⟨0, hN⟩ : Fin N) := by
  simp [bottomProjectorLP, pureBackwardShift_basis]

/-- The derived endpoint projector kills every non-bottom pure sheet. -/
theorem bottomProjectorLP_other
    {N : Nat} (p : Fin N) (hp : 0 < p.1) :
    bottomProjectorLP N (rationalPureBasis p) = 0 := by
  rw [bottomProjectorLP]
  simp only [LinearMap.sub_apply, LinearMap.id_apply]
  show rationalPureBasis p -
      pureForwardShift N (pureBackwardShift N (rationalPureBasis p)) = 0
  rw [pureBackwardShift_basis, dif_pos hp]
  rw [pureForwardShift_basis]
  have hsucc : p.1 - 1 + 1 < N := by omega
  rw [dif_pos hsucc]
  have heq : (⟨p.1 - 1 + 1, hsucc⟩ : Fin N) = p := by
    apply Fin.ext
    show p.1 - 1 + 1 = p.1
    omega
  rw [heq]
  simp

/-- Repeated forward shift moves a basis sheet by exactly k positions while
it remains in the finite window. -/
theorem pureForwardShift_pow_basis
    {N : Nat} (p : Fin N) (k : Nat)
    (hk : p.1 + k < N) :
    ((pureForwardShift N)^k) (rationalPureBasis p) =
      rationalPureBasis (⟨p.1 + k, hk⟩ : Fin N) := by
  revert hk
  revert p
  induction k with
  | zero =>
      intro p hk
      rfl
  | succ k ih =>
      intro p hk
      rw [pow_succ, Module.End.mul_apply]
      rw [pureForwardShift_basis, dif_pos (show p.1 + 1 < N by omega)]
      rw [ih ⟨p.1 + 1, by omega⟩ (show p.1 + 1 + k < N by omega)]
      apply congrArg rationalPureBasis
      apply Fin.ext
      show p.1 + 1 + k = p.1 + (k + 1)
      omega

/-- Repeated backward shift moves a basis sheet down by exactly k positions. -/
theorem pureBackwardShift_pow_basis
    {N : Nat} (p : Fin N) (k : Nat)
    (hk : k ≤ p.1) :
    ((pureBackwardShift N)^k) (rationalPureBasis p) =
      rationalPureBasis (⟨p.1 - k, by omega⟩ : Fin N) := by
  revert hk
  revert p
  induction k with
  | zero =>
      intro p hk
      rfl
  | succ k ih =>
      intro p hk
      rw [pow_succ, Module.End.mul_apply]
      rw [pureBackwardShift_basis, dif_pos (show 0 < p.1 by omega)]
      rw [ih ⟨p.1 - 1, by omega⟩ (show k ≤ p.1 - 1 by omega)]
      apply congrArg rationalPureBasis
      apply Fin.ext
      show p.1 - 1 - k = p.1 - (k + 1)
      omega

/-- Matrix-unit word using Lefschetz and Poincare only. -/
noncomputable def lefschetzPoincareMatrixWord
    {N : Nat} (p q : Fin N) :
    Module.End ℚ (RationalPureWindow N) :=
  ((pureForwardShift N)^q.1).comp
    ((bottomProjectorLP N).comp ((pureBackwardShift N)^p.1))

/-- **LEFSCHETZ + POINCARE GENERATE EVERY MATRIX UNIT.** -/
theorem lefschetzPoincareMatrixWord_eq
    {N : Nat} (p q : Fin N) :
    lefschetzPoincareMatrixWord p q = pureMatrixUnit p q := by
  apply LinearMap.ext
  intro a
  rw [rationalPureWindow_eq_sum_basis a]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hrp : r = p
  · subst r
    rw [lefschetzPoincareMatrixWord]
    simp only [LinearMap.comp_apply]
    rw [pureBackwardShift_pow_basis p p.1 (by omega)]
    simp only [Nat.sub_self]
    have hN : 0 < N := Nat.pos_of_ne_zero (by
      intro hN0
      subst N
      exact Fin.elim0 p)
    rw [bottomProjectorLP_bottom hN]
    rw [pureForwardShift_pow_basis
      (⟨0, hN⟩ : Fin N) q.1 (by simpa using q.2)]
    simp [pureMatrixUnit_basis_source]
  · have hdown :
      ((pureBackwardShift N)^p.1) (rationalPureBasis r) = 0 ∨
      ∃ s : Fin N, s.1 ≠ 0 ∧
        ((pureBackwardShift N)^p.1) (rationalPureBasis r) =
          rationalPureBasis s := by
      by_cases hpr : p.1 ≤ r.1
      · right
        refine ⟨⟨r.1 - p.1, by omega⟩, ?_, ?_⟩
        · show r.1 - p.1 ≠ 0
          have hrne : r.1 ≠ p.1 := fun h => hrp (Fin.ext h)
          omega
        · exact pureBackwardShift_pow_basis r p.1 hpr
      · left
        have hlt : r.1 < p.1 := by omega
        have vanishing : ∀ (k : Nat) (r : Fin N), r.1 < k →
            ((pureBackwardShift N)^k) (rationalPureBasis r) = 0 := by
          intro k
          induction k with
          | zero =>
              intro r hr
              exact absurd hr (by omega)
          | succ k ih =>
              intro r hr
              rw [pow_succ, Module.End.mul_apply]
              by_cases hr0 : 0 < r.1
              · rw [pureBackwardShift_basis, dif_pos hr0]
                have hrlt : r.1 - 1 < k := by omega
                exact ih ⟨r.1 - 1, by omega⟩ hrlt
              · rw [pureBackwardShift_basis, dif_neg hr0]
                simp
        exact vanishing p.1 r hlt
    rcases hdown with hzero | ⟨s, hs0, hs⟩
    · simp [lefschetzPoincareMatrixWord, hzero,
        pureMatrixUnit_basis_other p q r hrp]
    · rw [lefschetzPoincareMatrixWord]
      simp only [LinearMap.comp_apply]
      rw [hs]
      rw [bottomProjectorLP_other s (Nat.pos_of_ne_zero hs0)]
      simp [pureMatrixUnit_basis_other p q r hrp]

/-- Full finite matrix algebra generation using only the two native global GST
operations `L` and Poincare reversal. -/
theorem lefschetz_poincare_full_matrix_crown :
    ∀ N (p q : Fin N),
      lefschetzPoincareMatrixWord p q = pureMatrixUnit p q :=
  fun _ p q => lefschetzPoincareMatrixWord_eq p q

#check pureForwardShift
#check pureBackwardShift
#check bottomProjectorLP
#check pureForwardShift_basis
#check pureBackwardShift_basis
#check lefschetzPoincareMatrixWord
#check lefschetzPoincareMatrixWord_eq
#check lefschetz_poincare_full_matrix_crown

#print axioms pureForwardShift_basis
#print axioms pureBackwardShift_basis
#print axioms bottomProjectorLP_bottom
#print axioms bottomProjectorLP_other
#print axioms lefschetzPoincareMatrixWord_eq
#print axioms lefschetz_poincare_full_matrix_crown

end GSTClassicalHodgeLefschetzPoincareMatrixGeneration
