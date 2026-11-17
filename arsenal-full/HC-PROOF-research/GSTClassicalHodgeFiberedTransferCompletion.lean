import GSTClassicalHodgeLefschetzTomography
import GSTTransferBridgeV2

/-!
# GST CLASSICAL HODGE — FIBERED TRANSFER COMPLETION

The original limitless GST transfer layer has one diagonal generator at every
weight.  A genuine classical rational `(p,p)` Hodge fiber can have arbitrary
multiplicity.  The correct rank-free completion is therefore a family of
independent sheets above each GST base weight.

A sheet is indexed by `(p,i)`, where p is the limitless GST diagonal weight
and i is one basis direction in the genuine classical Hodge fiber.  Each sheet
projects to the already-proved GST diagonal generator at weight p, but before
that projection all sheets remain linearly independent.

Every genuine Hodge class has finite basis support, so it is exactly a finite
rational sum of these independent transformed-cycle sheet generators.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open GSTProjectiveOverC
open GSTClassicalHodgeFiberedCosmology
open GSTGeometricRealizationStage2G

namespace GSTClassicalHodgeFiberedTransferCompletion

/-- One independent transformed GST sheet generator. -/
def fiberedSheetGenerator
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (s : FiberedHodgeIndex V H) :
    FiberedHodgeAddress V H :=
  Finsupp.single s 1

/-- Weight-p transformed Hodge addresses have no support over any other
GST base weight. -/
def IsFiberedTransferHodge
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (p : Nat)
    (φ : FiberedHodgeAddress V H) : Prop :=
  ∀ s : FiberedHodgeIndex V H, s.1 ≠ p → φ s = 0

/-- One sheet over p is a weight-p transformed Hodge generator. -/
theorem fiberedSheetGenerator_isHodge
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H p) :
    IsFiberedTransferHodge p
      (fiberedSheetGenerator V H ⟨p,i⟩) := by
  intro s hs
  classical
  simp only [fiberedSheetGenerator]
  have hne : ¬(⟨p, i⟩ = s) := by
    intro heq
    exact hs (congrArg Sigma.fst heq).symm
  rw [Finsupp.single_apply, if_neg hne]

/-- Distinct sheets are linearly distinct before multiplicity is forgotten. -/
theorem fiberedSheetGenerator_injective
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    Function.Injective (fiberedSheetGenerator V H) := by
  intro s t h
  by_contra hst
  have hs := congrArg (fun φ : FiberedHodgeAddress V H => φ s) h
  simp [fiberedSheetGenerator, hst] at hs

/-- The chosen classical basis vector is literally its corresponding sheet
generator in the total fibered Hodge universe. -/
theorem classicalBasis_eq_fiberedSheetGenerator
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H p) :
    fiberedWeightCoordinates V H p (classicalHodgeBasis V H p i) =
      fiberedSheetGenerator V H ⟨p,i⟩ := by
  simp [fiberedSheetGenerator]

/-- Every sheet above p projects to the same established limitless GST base
generator at the cosmic diagonal address `(p,p)`. -/
theorem fiberedSheet_projects_to_cosmicGenerator
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H p) :
    forgetMultiplicityToGST (fiberedSheetGenerator V H ⟨p,i⟩) =
      Finsupp.single
        (GSTUniversalAddressBridge.cosmicAddressEquiv (p,p)) 1 := by
  rw [← classicalBasis_eq_fiberedSheetGenerator V H p i]
  exact classical_basis_projects_to_cosmic_diagonal V H p i

/-- A genuine weight-p classical Hodge class lands entirely in the weight-p
sheet family. -/
theorem fiberedWeightCoordinates_isHodge
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    IsFiberedTransferHodge p (fiberedWeightCoordinates V H p alpha) := by
  intro s hs
  classical
  simp only [fiberedWeightCoordinates, weightFiberEmbedding]
  refine Finsupp.embDomain_of_notMem_range _ _ _ ?_
  intro hin
  rcases Set.mem_range.mp hin with ⟨i, hi⟩
  exact hs (by rw [← hi]; rfl)

/-- **EXACT SHEET DECOMPOSITION.**  Every finite fibered address is the
finite sum of its scalar multiples of independent sheet generators. -/
theorem fiberedAddress_sheet_decomposition
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (φ : FiberedHodgeAddress V H) :
    φ = φ.sum (fun s q => q • fiberedSheetGenerator V H s) := by
  classical
  apply Finsupp.ext
  intro t
  simp [fiberedSheetGenerator]

/-- **FIBERED TRANSFORMED HODGE THEOREM.**  Every genuine rational Hodge
class is exactly a finite rational combination of independent transformed GST
sheet generators, all lying above its single GST base weight. -/
theorem fibered_transformed_hodge
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    ∃ coeff : ClassicalHodgeBasisIndex V H p →₀ ℚ,
      fiberedWeightCoordinates V H p alpha =
        coeff.sum (fun i q =>
          q • fiberedSheetGenerator V H ⟨p,i⟩) := by
  let coeff := (classicalHodgeBasis V H p).repr alpha
  refine ⟨coeff, ?_⟩
  classical
  unfold fiberedWeightCoordinates coeff
  apply Finsupp.ext
  intro s
  rcases s with ⟨q,j⟩
  by_cases hqp : q = p
  · subst q
    classical
    have hgoalL : Finsupp.embDomain (weightFiberEmbedding V H p)
        ((classicalHodgeBasis V H p).repr alpha) ⟨p, j⟩ =
        ((classicalHodgeBasis V H p).repr alpha) j :=
      Finsupp.embDomain_apply_self (weightFiberEmbedding V H p)
        ((classicalHodgeBasis V H p).repr alpha) j
    rw [hgoalL]
    simp [fiberedSheetGenerator,
      Finsupp.single_apply, Finsupp.sum]
  · classical
    have hL : Finsupp.embDomain (weightFiberEmbedding V H p)
        ((classicalHodgeBasis V H p).repr alpha) ⟨q, j⟩ = 0 := by
      refine Finsupp.embDomain_of_notMem_range _ _ _ ?_
      intro hin
      rcases Set.mem_range.mp hin with ⟨i, hi⟩
      exact hqp (congrArg Sigma.fst hi).symm
    have hR : (((classicalHodgeBasis V H p).repr alpha).sum
        (fun i q => q • fiberedSheetGenerator V H ⟨p, i⟩)) ⟨q, j⟩ = 0 := by
      simp [fiberedSheetGenerator, Finsupp.sum, Finsupp.single_apply,
        Ne.symm hqp]
    rw [hL, hR]

/-- Uniqueness of the sheet coefficients: the fibered completion introduces
no artificial relations between independent classical multiplicity sheets. -/
theorem fibered_transformed_hodge_coeff_unique
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (a b : ClassicalHodgeBasisIndex V H p →₀ ℚ)
    (ha : fiberedWeightCoordinates V H p alpha =
      a.sum (fun i q => q • fiberedSheetGenerator V H ⟨p,i⟩))
    (hb : fiberedWeightCoordinates V H p alpha =
      b.sum (fun i q => q • fiberedSheetGenerator V H ⟨p,i⟩)) :
    a = b := by
  apply Finsupp.ext
  intro i
  have h := ha.symm.trans hb
  have hi := congrArg
    (fun φ : FiberedHodgeAddress V H => φ ⟨p,i⟩) h
  classical
  simp [fiberedSheetGenerator, Finsupp.single_apply, Finsupp.sum] at hi
  split_ifs at hi <;> simp_all

/-- The unique coefficients are exactly the genuine basis coordinates. -/
theorem fibered_transformed_hodge_coeff_exact
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (a : ClassicalHodgeBasisIndex V H p →₀ ℚ)
    (ha : fiberedWeightCoordinates V H p alpha =
      a.sum (fun i q => q • fiberedSheetGenerator V H ⟨p,i⟩)) :
    a = (classicalHodgeBasis V H p).repr alpha := by
  apply fibered_transformed_hodge_coeff_unique V H p alpha
  · exact ha
  · rcases fibered_transformed_hodge V H p alpha with ⟨b,hb⟩
    have hbexact : b = (classicalHodgeBasis V H p).repr alpha := by
      apply Finsupp.ext
      intro i
      have hi := congrArg
        (fun φ : FiberedHodgeAddress V H => φ ⟨p,i⟩) hb
      classical
      have hself : Finsupp.embDomain (Function.Embedding.sigmaMk p)
          ((classicalHodgeBasis V H p).repr alpha) ⟨p, i⟩ =
          ((classicalHodgeBasis V H p).repr alpha) i :=
        Finsupp.embDomain_apply_self (Function.Embedding.sigmaMk p)
          ((classicalHodgeBasis V H p).repr alpha) i
      simp only [fiberedSheetGenerator, fiberedWeightCoordinates,
        weightFiberEmbedding] at hi
      rw [hself] at hi
      simp [Finsupp.single_apply, Finsupp.sum] at hi
      split_ifs at hi <;> simp_all
    simpa [hbexact] using hb

/-- Summing singleton carriers at one fixed address aggregates the
coefficients into one singleton carrier at that address. -/
theorem sum_single_address
    {ι : Type*} {κ : Type*}
    (f : ι →₀ ℚ) (c : κ) :
    f.sum (fun _ q => Finsupp.single c q) =
      Finsupp.single c (f.sum fun _ q => q) :=
  (Finsupp.single_sum f (fun _ q => q) c).symm

/-- The projection to the GST base is the finite sum of the coefficients at
the single limitless diagonal generator.  Multiplicity is deliberately
retained in the sheet universe until this final projection. -/
theorem forgetMultiplicity_fiberedWeightCoordinates
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    forgetMultiplicityToGST (fiberedWeightCoordinates V H p alpha) =
      Finsupp.single
        (GSTUniversalAddressBridge.cosmicAddressEquiv (p,p))
        (((classicalHodgeBasis V H p).repr alpha).sum (fun _ q => q)) := by
  classical
  simp only [forgetMultiplicityToGST, fiberedWeightCoordinates,
    weightFiberEmbedding]
  rw [Finsupp.sum_embDomain]
  have haddr : ∀ a : ClassicalHodgeBasisIndex V H p,
      ((Function.Embedding.sigmaMk p) a).1 = p := fun _ => rfl
  simp only [haddr]
  rw [sum_single_address]
  rfl

/-- Fibered transfer crown: independent sheets, exact finite decomposition,
unique coefficients, and exact projection to the established limitless GST
cosmic generator. -/
theorem fibered_transfer_completion_crown
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    Function.Injective (fiberedSheetGenerator V H)
    ∧ (∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
      ∃ coeff : ClassicalHodgeBasisIndex V H p →₀ ℚ,
        fiberedWeightCoordinates V H p alpha =
          coeff.sum (fun i q =>
            q • fiberedSheetGenerator V H ⟨p,i⟩))
    ∧ (∀ p : Nat, ∀ i : ClassicalHodgeBasisIndex V H p,
      forgetMultiplicityToGST (fiberedSheetGenerator V H ⟨p,i⟩) =
        Finsupp.single
          (GSTUniversalAddressBridge.cosmicAddressEquiv (p,p)) 1) := by
  exact ⟨
    fiberedSheetGenerator_injective V H,
    fibered_transformed_hodge V H,
    fiberedSheet_projects_to_cosmicGenerator V H⟩

#check fiberedSheetGenerator
#check IsFiberedTransferHodge
#check fiberedSheetGenerator_isHodge
#check fiberedSheetGenerator_injective
#check classicalBasis_eq_fiberedSheetGenerator
#check fiberedSheet_projects_to_cosmicGenerator
#check fiberedWeightCoordinates_isHodge
#check fiberedAddress_sheet_decomposition
#check fibered_transformed_hodge
#check fibered_transformed_hodge_coeff_unique
#check fibered_transformed_hodge_coeff_exact
#check sum_single_address
#check forgetMultiplicity_fiberedWeightCoordinates
#check fibered_transfer_completion_crown

#print axioms fiberedSheetGenerator_injective
#print axioms fiberedAddress_sheet_decomposition
#print axioms fibered_transformed_hodge
#print axioms fibered_transformed_hodge_coeff_unique
#print axioms forgetMultiplicity_fiberedWeightCoordinates
#print axioms fibered_transfer_completion_crown

end GSTClassicalHodgeFiberedTransferCompletion
