import GSTClassicalHodgeAugmentedTargetWindow
import GSTClassicalHodgeTotalSheetMatrixUnit
import GSTClassicalHodgeRankFreeArsenalIrreducibility

/-!
# GST CLASSICAL HODGE — CONCRETE RANK-FREE GENERATION

The finite GST arsenal now reaches the unrestricted classical Hodge fiber.
Given one nonzero genuine Hodge class `alpha` and any arbitrary target basis
direction `j`:

1. choose one genuinely live source basis coordinate of `alpha`;
2. adjoin the arbitrary target `j` to the finite observation window;
3. clear denominators to obtain one integral pure GST square;
4. apply the total projector/Lefschetz/Poincare matrix unit from the live
   source slot to the target slot;
5. read the rationalized output back through the genuine Hodge basis;
6. divide by the denominator scale and the nonzero source coefficient.

The result is exactly the target basis vector.  Therefore every nonzero Hodge
class is a concrete cyclic vector for actual finite GST operator words, even
when the requested target direction was absent from its original support.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeAugmentedTargetWindow
open GSTClassicalHodgeTotalSheetMatrixUnit
open GSTClassicalHodgeLocalCyclicCriterion

namespace GSTClassicalHodgeConcreteRankFreeGeneration

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Choose one live source basis direction of a nonzero Hodge class. -/
noncomputable def chosenLiveSource
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) : HodgeSupportIndex alpha := by
  have hsupp : ((classicalHodgeBasis V H p).repr alpha).support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    intro hzero
    apply halpha
    exact (classicalHodgeBasis V H p).repr.injective (by simpa using hzero)
  exact ⟨hsupp.choose, hsupp.choose_spec⟩

/-- The chosen live source coefficient is nonzero. -/
theorem chosenLiveSource_coefficient_ne_zero
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    (classicalHodgeBasis V H p).repr alpha
      (chosenLiveSource alpha halpha).1 ≠ 0 :=
  support_coefficient_ne_zero alpha (chosenLiveSource alpha halpha)

/-- Raw rational GST output for one arbitrary target basis direction. -/
noncomputable def arbitraryTargetGSTOutput
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (j : ClassicalHodgeBasisIndex V H p) :
    GSTClassicalHodgeConcreteSheetMatrixUnit.RationalSquareCoef
      (augmentedRank alpha j) :=
  totalSheetMatrixUnit
    (liveSourceSlot alpha j (chosenLiveSource alpha halpha))
    (targetSlot alpha j)
    (augmentedIntegralSquare alpha j).world

/-- The concrete GST word has exactly the denominator-scaled live source
coefficient on the arbitrary target sheet and nowhere else. -/
theorem arbitraryTargetGSTOutput_exact
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (j : ClassicalHodgeBasisIndex V H p) :
    arbitraryTargetGSTOutput alpha halpha j =
      fun x =>
        if x = (targetSlot alpha j, targetSlot alpha j) then
          (((augmentedIntegralSquare alpha j).scale : ℚ) *
            ((classicalHodgeBasis V H p).repr alpha
              (chosenLiveSource alpha halpha).1))
        else 0 := by
  unfold arbitraryTargetGSTOutput
  rw [totalSheetMatrixUnit_exact
    (liveSourceSlot alpha j (chosenLiveSource alpha halpha))
    (targetSlot alpha j)
    (augmentedIntegralSquare alpha j).world
    (augmentedIntegralSquare alpha j).world_pure]
  funext x
  by_cases hx : x = (targetSlot alpha j, targetSlot alpha j)
  · subst x
    simp
    have hdiag := (augmentedIntegralSquare alpha j).scaled_eq
      (liveSourceSlot alpha j (chosenLiveSource alpha halpha),
       liveSourceSlot alpha j (chosenLiveSource alpha halpha))
    refine hdiag.symm.trans ?_
    simp [augmentedRationalSquare, augmentedCoordinateVector,
      augmentedCoordinate_liveSource]
  · simp [hx]

/-- Reading the concrete GST output back into the genuine Hodge fiber gives
exactly the scaled arbitrary target basis vector. -/
theorem read_arbitraryTargetGSTOutput
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (j : ClassicalHodgeBasisIndex V H p) :
    readAugmentedSquare alpha j
        (arbitraryTargetGSTOutput alpha halpha j) =
      (((augmentedIntegralSquare alpha j).scale : ℚ) *
        ((classicalHodgeBasis V H p).repr alpha
          (chosenLiveSource alpha halpha).1)) •
        classicalHodgeBasis V H p j := by
  rw [arbitraryTargetGSTOutput_exact]
  exact readAugmentedSquare_target alpha j _

/-- The total normalization coefficient is nonzero. -/
theorem arbitraryTarget_normalization_ne_zero
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (j : ClassicalHodgeBasisIndex V H p) :
    ((augmentedIntegralSquare alpha j).scale : ℚ) *
      ((classicalHodgeBasis V H p).repr alpha
        (chosenLiveSource alpha halpha).1) ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast Nat.ne_of_gt (augmentedIntegralSquare alpha j).scale_pos
  · exact chosenLiveSource_coefficient_ne_zero alpha halpha

/-- Normalize the concrete finite GST word to produce exactly one arbitrary
genuine Hodge basis vector. -/
noncomputable def concreteBasisGenerator
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (j : ClassicalHodgeBasisIndex V H p) :
    ClassicalHodgeFiber V H p :=
  let c : ℚ :=
    ((augmentedIntegralSquare alpha j).scale : ℚ) *
      ((classicalHodgeBasis V H p).repr alpha
        (chosenLiveSource alpha halpha).1)
  c⁻¹ • readAugmentedSquare alpha j
    (arbitraryTargetGSTOutput alpha halpha j)

/-- **CONCRETE RANK-FREE BASIS GENERATION.** Every arbitrary genuine Hodge
basis vector is produced by one finite GST projector/Lefschetz/Poincare word
applied to an augmented integral observation of any fixed nonzero Hodge class. -/
theorem concreteBasisGenerator_eq_basis
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (j : ClassicalHodgeBasisIndex V H p) :
    concreteBasisGenerator alpha halpha j =
      classicalHodgeBasis V H p j := by
  unfold concreteBasisGenerator
  rw [read_arbitraryTargetGSTOutput]
  rw [smul_smul]
  have h1 :
      (((↑(augmentedIntegralSquare alpha j).scale *
      ((classicalHodgeBasis V H p).repr alpha) ↑(chosenLiveSource alpha halpha))⁻¹ *
      (↑(augmentedIntegralSquare alpha j).scale *
      ((classicalHodgeBasis V H p).repr alpha) ↑(chosenLiveSource alpha halpha))) •
      (classicalHodgeBasis V H p) j) =
      (classicalHodgeBasis V H p) j := by
    have hscale : ((augmentedIntegralSquare alpha j).scale : ℚ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (augmentedIntegralSquare alpha j).scale_pos
    have hlive : ((classicalHodgeBasis V H p).repr alpha)
        (chosenLiveSource alpha halpha).1 ≠ 0 :=
      chosenLiveSource_coefficient_ne_zero alpha halpha
    rw [inv_mul_cancel₀ (mul_ne_zero hscale hlive), one_smul]
  exact h1

/-- Every Hodge class is therefore a finite rational linear combination of
concrete GST-generated basis vectors from one fixed nonzero source state. -/
theorem hodgeClass_eq_sum_concreteGenerators
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (beta : ClassicalHodgeFiber V H p) :
    beta =
      ((classicalHodgeBasis V H p).repr beta).sum
        (fun j q => q • concreteBasisGenerator alpha halpha j) := by
  calc beta
      = Finsupp.linearCombination ℚ (classicalHodgeBasis V H p)
          ((classicalHodgeBasis V H p).repr beta) :=
        ((classicalHodgeBasis V H p).linearCombination_repr beta).symm
    _ = ((classicalHodgeBasis V H p).repr beta).sum
        (fun j q => q • concreteBasisGenerator alpha halpha j) := by
        rw [Finsupp.linearCombination_apply]
        apply Finsupp.sum_congr
        intro j hj
        rw [concreteBasisGenerator_eq_basis]

/-- **UNRESTRICTED CONCRETE CYCLICITY CROWN.** One nonzero genuine Hodge state
concretely generates the entire unrestricted Hodge fiber through finite GST
operator words, with no countability assumption and no restriction to its
original live support. -/
theorem concrete_rank_free_generation_crown
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    (∀ j : ClassicalHodgeBasisIndex V H p,
      concreteBasisGenerator alpha halpha j =
        classicalHodgeBasis V H p j)
    ∧ (∀ beta : ClassicalHodgeFiber V H p,
      beta = ((classicalHodgeBasis V H p).repr beta).sum
        (fun j q => q • concreteBasisGenerator alpha halpha j)) := by
  exact ⟨concreteBasisGenerator_eq_basis alpha halpha,
    hodgeClass_eq_sum_concreteGenerators alpha halpha⟩

#check chosenLiveSource
#check arbitraryTargetGSTOutput
#check arbitraryTargetGSTOutput_exact
#check read_arbitraryTargetGSTOutput
#check concreteBasisGenerator
#check concreteBasisGenerator_eq_basis
#check hodgeClass_eq_sum_concreteGenerators
#check concrete_rank_free_generation_crown

#print axioms arbitraryTargetGSTOutput_exact
#print axioms read_arbitraryTargetGSTOutput
#print axioms concreteBasisGenerator_eq_basis
#print axioms hodgeClass_eq_sum_concreteGenerators
#print axioms concrete_rank_free_generation_crown

end GSTClassicalHodgeConcreteRankFreeGeneration
