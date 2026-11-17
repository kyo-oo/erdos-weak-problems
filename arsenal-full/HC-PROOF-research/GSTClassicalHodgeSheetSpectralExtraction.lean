import GSTClassicalHodgeIntegralSquareLocalization
import GSTWorldRecoordinationGroupoid
import GSTDimensionFreeHodgeDiagonal
import GSTSquarePureHodgeDuality

/-!
# GST CLASSICAL HODGE — SINGLE-SHEET SPECTRAL EXTRACTION

After denominator clearing, every hypothetical separator witness lives inside
one finite integral pure GST square.  The world-recoordination theory already
contains exact invariant code-sector projectors, and every such projector is
an explicit integer spectral polynomial.

On a pure square, only diagonal code sectors can be live.  Hence the full
state decomposes into independent diagonal multiplicity sheets.  A nonzero
Poincare pairing forces at least one complementary pair of individual sheets
to pair nontrivially.

This reduces any global classical witness to one spectrally isolated sheet
atom, while retaining the original classical codimension as an external base
label rather than confusing it with the local sheet coordinate.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open GSTProjectiveOverC
open GSTWorldRecoordinationGroupoid
open GSTWorldPoincareDuality
open GSTDimensionFreeHodgeDiagonal
open GSTGlobalPureHodgeCosmology
open GSTSquarePureHodgeDuality
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeSeparatorProbe
open GSTClassicalHodgeSquareStrandLocalization
open GSTClassicalHodgeIntegralSquareLocalization
open GSTWorldCosmology
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiniteSupportChart

namespace GSTClassicalHodgeSheetSpectralExtraction

/-- Invariant world code of the i-th multiplicity-sheet diagonal cell. -/
def sheetCode {N : Nat} (i : Fin N) : Nat :=
  worldCode (outputShape N N) (i,i)

/-- Exact numeric sheet code in the row-major square chart. -/
theorem sheetCode_val
    {N : Nat} (i : Fin N) :
    sheetCode i = (N + 1) * i.1 := by
  unfold sheetCode
  rw [worldCode_expanded]
  show i.1 + (outputShape N N).cols * i.1 = (N + 1) * i.1
  have hcols : (outputShape N N).cols = N := rfl
  rw [hcols]
  ring

/-- The world-code observable is injective on every shaped world because its
underlying coding map is an equivalence. -/
theorem worldCode_injective
    {M : Nat} (S : GSTWorldShape M) :
    Function.Injective (worldCode S) := by
  intro x y h
  apply (shapeCodeEquiv S).injective
  apply Fin.ext
  exact h

/-- Integral diagonal atom carried by one local multiplicity sheet. -/
def sheetDiagonalAtom
    {N : Nat} (i : Fin N) (z : ℤ) :
    ShapeCoef (outputShape N N) :=
  fun c => z * worldDiagonalClass i.2 i.2 c

/-- Spectral projector onto one local multiplicity-sheet code. -/
def sheetSpectralProj
    {N : Nat} (i : Fin N)
    (f : ShapeCoef (outputShape N N)) :
    ShapeCoef (outputShape N N) :=
  codeSectorProj (outputShape N N) (sheetCode i) f

/-- A sheet projector is exactly an explicit integer polynomial spectral
operator, up to its nonzero normalization scalar. -/
theorem sheetSpectralProj_is_polynomial
    {N : Nat} (i : Fin N) :
    ∃ (P : Polynomial ℤ) (c : ℤ), c ≠ 0 ∧
      ∀ (f : ShapeCoef (outputShape N N))
        (x : ShapeState (outputShape N N)),
        codePolyOp (outputShape N N) P f x =
          c * sheetSpectralProj i f x := by
  apply codeSector_projector_polynomial
  unfold sheetCode
  exact worldCode_lt (outputShape N N) (i,i)

/-- On a pure integral square, the i-th spectral sector is exactly the i-th
coefficient times its single diagonal sheet atom. -/
theorem sheetSpectralProj_pure_eq_atom
    {N : Nat} (i : Fin N)
    (f : ShapeCoef (outputShape N N))
    (hf : isWorldPureHodge f) :
    sheetSpectralProj i f =
      sheetDiagonalAtom i (f (i,i)) := by
  funext x
  by_cases hcode : worldCode (outputShape N N) x = sheetCode i
  · have hx : x = (i,i) :=
      worldCode_injective (outputShape N N) hcode
    subst x
    have hcond : worldCode (outputShape N N) (i,i) = sheetCode i := rfl
    have hdiag : worldDiagonalClass i.2 i.2 (i,i) = 1 := by
      simp [worldDiagonalClass, GSTUniversalAddressBridge.worldBasis]
      rfl
    show (if worldCode (outputShape N N) (i,i) = sheetCode i
        then f (i,i) else 0) =
      f (i,i) * worldDiagonalClass i.2 i.2 (i,i)
    rw [if_pos hcond]
    exact ((congrArg (fun z : ℤ => f (i, i) * z) hdiag).trans (mul_one _)).symm
  · have hxne : x ≠ (i,i) := by
      intro hx
      subst x
      exact hcode rfl
    have hdiagOr : x.1.1 ≠ x.2.1 ∨
        (x.1.1 = x.2.1 ∧ x.1 ≠ i) := by
      by_cases hd : x.1.1 = x.2.1
      · right
        refine ⟨hd, ?_⟩
        intro hxi
        have hyi : x.2 = i := by
          apply Fin.ext
          simpa [hxi] using hd.symm
        exact hxne (Prod.ext hxi hyi)
      · exact Or.inl hd
    have hzero : sheetSpectralProj i f x = 0 := by
      show (if worldCode (outputShape N N) x = sheetCode i
        then f x else 0) = 0
      exact if_neg hcode
    rw [hzero]
    rcases hdiagOr with hoff | ⟨hdiag,hxi⟩
    · have hoff' : x.1.1 ≠ i.1 ∨ x.2.1 ≠ i.1 := by
        by_cases hxi : x.1.1 = i.1
        · exact Or.inr (fun h => hoff (hxi.trans h.symm))
        · exact Or.inl hxi
      have hvw : worldDiagonalClass i.2 i.2 x = 0 :=
        worldDiagonalClass_off_diagonal i.2 i.2 x hoff'
      show (0 : ℤ) = f (i,i) * worldDiagonalClass i.2 i.2 x
      rw [hvw]
      simp
    · have hoffWeight : x.1.1 ≠ i.1 ∨ x.2.1 ≠ i.1 := by
        left
        intro hval
        apply hxi
        exact Fin.ext hval
      have hvw : worldDiagonalClass i.2 i.2 x = 0 :=
        worldDiagonalClass_off_diagonal i.2 i.2 x hoffWeight
      show (0 : ℤ) = f (i,i) * worldDiagonalClass i.2 i.2 x
      rw [hvw]
      simp

/-- Different local sheet projectors are orthogonal. -/
theorem sheetSpectralProj_orthogonal
    {N : Nat} (i j : Fin N) (hij : i ≠ j)
    (f : ShapeCoef (outputShape N N)) :
    sheetSpectralProj i (sheetSpectralProj j f) = 0 := by
  apply codeSectorProj_orthogonal
  intro hcode
  have hdiag : (i,i) = (j,j) :=
    worldCode_injective (outputShape N N) hcode
  exact hij (congrArg Prod.fst hdiag)

/-- Every integral pure square is the finite sum of its independent sheet
atoms. -/
theorem pureWorld_sheet_decomposition
    {N : Nat}
    (f : ShapeCoef (outputShape N N))
    (hf : isWorldPureHodge f) :
    f = ∑ i : Fin N, sheetDiagonalAtom i (f (i,i)) := by
  funext x
  by_cases hdiag : x.1.1 = x.2.1
  · have hx : x = (x.1, x.1) := by
      apply Prod.ext
      · rfl
      · apply Fin.ext
        exact hdiag.symm
    rw [hx]
    classical
    have happlied : ∀ y : ShapeState (outputShape N N),
        (∑ i : Fin N, sheetDiagonalAtom i (f (i, i))) y
        = ∑ i : Fin N, sheetDiagonalAtom i (f (i, i)) y :=
      fun y => Finset.sum_apply _ _ _
    have hsingle : ∑ i : Fin N, sheetDiagonalAtom i (f (i, i)) (x.1, x.1)
        = sheetDiagonalAtom (x.1 : Fin N) (f (x.1, x.1)) (x.1, x.1) :=
      Finset.sum_eq_single (x.1 : Fin N)
        (fun b _ hne => by
          have hoff' : (x.1, x.1).1.1 ≠ b.1 ∨ (x.1, x.1).2.1 ≠ b.1 :=
            Or.inl (fun hval => hne (Fin.ext hval.symm))
          have hvw : worldDiagonalClass b.2 b.2 (x.1, x.1) = 0 :=
            worldDiagonalClass_off_diagonal b.2 b.2 (x.1, x.1) hoff'
          show f (b, b) * worldDiagonalClass b.2 b.2 (x.1, x.1) = 0
          rw [hvw, mul_zero])
        (fun hnomem => absurd (Finset.mem_univ _) hnomem)
    have hz : sheetDiagonalAtom (x.1 : Fin N) (f (x.1, x.1)) (x.1, x.1)
        = f (x.1, x.1) * worldDiagonalClass (x.1).2 (x.1).2 (x.1, x.1) := rfl
    have hdiagval : worldDiagonalClass (x.1).2 (x.1).2 (x.1, x.1) = 1 := by
      simp [worldDiagonalClass, GSTUniversalAddressBridge.worldBasis]
      rfl
    have hf : f (x.1, x.1) * worldDiagonalClass (x.1).2 (x.1).2 (x.1, x.1)
        = f (x.1, x.1) :=
      (congrArg (fun z : ℤ => f (x.1, x.1) * z) hdiagval).trans (mul_one _)
    exact (((happlied (x.1, x.1)).trans hsingle).trans (hz.trans hf)).symm
  · rw [hf x hdiag]
    have happlied : (∑ i : Fin N, sheetDiagonalAtom i (f (i, i))) x
        = ∑ i : Fin N, sheetDiagonalAtom i (f (i, i)) x :=
      Finset.sum_apply _ _ _
    rw [happlied]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    have hoff' : x.1.1 ≠ i.1 ∨ x.2.1 ≠ i.1 := by
      by_cases hxi : x.1.1 = i.1
      · exact Or.inr (fun h => hdiag (hxi.trans h.symm))
      · exact Or.inl hxi
    have hvw : worldDiagonalClass i.2 i.2 x = 0 :=
      worldDiagonalClass_off_diagonal i.2 i.2 x hoff'
    show f (i,i) * worldDiagonalClass i.2 i.2 x = 0
    rw [hvw]
    simp

/-- Complementary local multiplicity-sheet index under square Poincare
reflection. -/
def sheetMirror {N : Nat} (i : Fin N) : Fin N :=
  complementFin i

@[simp]
theorem worldDual_sheetDiagonal
    {N : Nat} (i : Fin N) :
    worldDual ((i,i) : WorldCell N N) =
      (sheetMirror i, sheetMirror i) := by
  rfl

/-- A nonzero pure-vs-pure integral Poincare pairing contains one nonzero
complementary sheet product. -/
theorem nonzero_purePairing_yields_nonzero_sheet_product
    {N : Nat}
    (A B : ShapeCoef (outputShape N N))
    (hA : isWorldPureHodge A)
    (hpair : worldTopPairing A B ≠ 0) :
    ∃ i : Fin N,
      A (i,i) * B (sheetMirror i, sheetMirror i) ≠ 0 := by
  unfold worldTopPairing at hpair
  by_contra hnone
  push_neg at hnone
  apply hpair
  apply Finset.sum_eq_zero
  intro c hc
  by_cases hdiag : c.1.1 = c.2.1
  · have hcdiag : c = (c.1, c.1) := by
      apply Prod.ext
      · rfl
      · apply Fin.ext
        exact hdiag.symm
    rw [hcdiag]
    exact hnone c.1
  · simp [hA c hdiag]

/-- The corresponding single-sheet spectral projectors already retain a
nonzero Poincare pairing. -/
theorem nonzero_purePairing_yields_nonzero_projected_pairing
    {N : Nat}
    (A B : ShapeCoef (outputShape N N))
    (hA : isWorldPureHodge A)
    (hB : isWorldPureHodge B)
    (hpair : worldTopPairing A B ≠ 0) :
    ∃ i : Fin N,
      worldTopPairing
        (sheetSpectralProj i A)
        (sheetSpectralProj (sheetMirror i) B) ≠ 0 := by
  obtain ⟨i,hi⟩ :=
    nonzero_purePairing_yields_nonzero_sheet_product A B hA hpair
  refine ⟨i, ?_⟩
  rw [sheetSpectralProj_pure_eq_atom i A hA]
  rw [sheetSpectralProj_pure_eq_atom (sheetMirror i) B hB]
  have hsingle : worldTopPairing (sheetDiagonalAtom i (A (i,i)))
      (sheetDiagonalAtom (sheetMirror i) (B (sheetMirror i, sheetMirror i)))
      ≠ 0 := by
    classical
    unfold worldTopPairing sheetDiagonalAtom
    rw [Finset.sum_eq_single (diagonalState i.2 i.2)]
    · show A (i,i) * worldDiagonalClass i.2 i.2 (diagonalState i.2 i.2)
          * (B (sheetMirror i, sheetMirror i)
            * worldDiagonalClass (sheetMirror i).2 (sheetMirror i).2
              (worldDual (diagonalState i.2 i.2)))
          ≠ 0
      rw [worldDiagonalClass_at_diagonal]
      have hB1 : worldDiagonalClass (sheetMirror i).2 (sheetMirror i).2
          (worldDual (diagonalState i.2 i.2)) = 1 :=
        worldDiagonalClass_at_diagonal (sheetMirror i).2 (sheetMirror i).2
      rw [hB1, mul_one, mul_one]
      exact hi
    · intro c hc hci
      have hoff' : c.1.1 ≠ i.1 ∨ c.2.1 ≠ i.1 := by
        by_contra hcon
        push_neg at hcon
        exact hci (Prod.ext (Fin.ext hcon.1) (Fin.ext hcon.2))
      have hvw : worldDiagonalClass i.2 i.2 c = 0 :=
        worldDiagonalClass_off_diagonal i.2 i.2 c hoff'
      show A (i,i) * worldDiagonalClass i.2 i.2 c
          * (B (sheetMirror i, sheetMirror i)
            * worldDiagonalClass (sheetMirror i).2 (sheetMirror i).2 (worldDual c)) = 0
      rw [hvw, mul_zero, zero_mul]
    · simp
  exact hsingle



/-- **SINGLE-SHEET REDUCTION OF CLASSICAL HODGE FAILURE.**
Any Stage-2G failure witness yields a finite integral pure square and one
spectrally isolated multiplicity sheet whose complementary projected pairing
is nonzero.  The original classical codimension p is retained separately. -/
theorem not_hodge_yields_single_sheet_spectral_witness
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hnot : ¬ GSTGeometricRealizationStage2G.BigradedBettiHodgeStatement V H) :
    ∃ p : Nat,
    ∃ S : AtomicSeparatorProbe V H p,
    ∃ N : Nat,
    ∃ A B : ShapeCoef (outputShape N N),
    ∃ i : Fin N,
      isWorldPureHodge A ∧
      isWorldPureHodge B ∧
      worldTopPairing
        (sheetSpectralProj i A)
        (sheetSpectralProj (sheetMirror i) B) ≠ 0 := by
  obtain ⟨p,S,a,b,ha,hb,hpair⟩ :=
    not_hodge_yields_nonzero_pureSquare_pairing V H hnot
  let IA := canonicalIntegralPureSquareModel a ha
  let IB := canonicalIntegralPureSquareModel b hb
  have hIntegral : worldTopPairing IA.world IB.world ≠ 0 :=
    nonzero_rationalPairing_yields_nonzero_integralPairing
      a b ha hb hpair
  obtain ⟨i,hi⟩ :=
    nonzero_purePairing_yields_nonzero_projected_pairing
      IA.world IB.world IA.world_pure IB.world_pure hIntegral
  exact ⟨p,S,
    fiberedSupportSize (fiberedWeightCoordinates V H p S.alpha),
    IA.world, IB.world, i,
    IA.world_pure, IB.world_pure, hi⟩

#check sheetCode
#check sheetCode_val
#check worldCode_injective
#check sheetDiagonalAtom
#check sheetSpectralProj
#check sheetSpectralProj_is_polynomial
#check sheetSpectralProj_pure_eq_atom
#check sheetSpectralProj_orthogonal
#check pureWorld_sheet_decomposition
#check sheetMirror
#check nonzero_purePairing_yields_nonzero_sheet_product
#check nonzero_purePairing_yields_nonzero_projected_pairing
#check not_hodge_yields_single_sheet_spectral_witness

#print axioms sheetSpectralProj_is_polynomial
#print axioms sheetSpectralProj_pure_eq_atom
#print axioms pureWorld_sheet_decomposition
#print axioms nonzero_purePairing_yields_nonzero_projected_pairing
#print axioms not_hodge_yields_single_sheet_spectral_witness

end GSTClassicalHodgeSheetSpectralExtraction
