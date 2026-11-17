import GSTTargetWordRecovery
import GSTClassicalHodgeFiniteSourceCorrection

/-!
# Ordered source words on the prescribed original-X Hodge target
Uncompiled proof draft. This uses the prior genuine source-cycle constructor.
The tails act on the Hodge fiber; no native tail action or algebraic seed
for alpha is requested. Actual source geometry is still an explicit input.
-/

open scoped BigOperators
noncomputable section
open GSTProjectiveOverC GSTGeometricRealizationStage2D GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology GSTClassicalHodgeFiniteSourceCorrection

namespace GSTClassicalHodgeWordSourceRecovery
variable {X : SmoothProjectiveComplexScheme} {H : HodgeBigradedBettiData X}
variable {p : ℕ} {ι κ J : Type*} [Fintype κ]

theorem source_step_class_frame (S : SourceSystem X H p κ)
    (hS : S.SourceAlgebraicity) (alpha : ClassicalHodgeFiber X H p) :
    H.cycleClass p (S.oneCorrection hS alpha)=(S.frame alpha).1 := by
  rw [S.oneCorrection_class hS]
  have h : alpha-S.error alpha=S.frame alpha := by
    change alpha-(alpha-S.frame alpha)=S.frame alpha
    abel
  rw [h]

/-- All original-X output cycles are finite sums of actual source returns. -/
def targetWordCycle (S : ι → SourceSystem X H p κ)
    (hS : ∀ i,(S i).SourceAlgebraicity)
    (s : Finset J) (word : J → GSTTargetWordRecovery.NonemptyWord ι)
    (coeff : J → ℚ) (alpha : ClassicalHodgeFiber X H p) : codimensionCycles X.X p :=
  GSTTargetWordRecovery.finiteWordCycle (fun i => (S i).frame)
    (fun i => (S i).oneCorrection (hS i)) s word coeff alpha

theorem targetWordCycle_exact (S : ι → SourceSystem X H p κ)
    (hS : ∀ i,(S i).SourceAlgebraicity)
    (s : Finset J) (word : J → GSTTargetWordRecovery.NonemptyWord ι)
    (coeff : J → ℚ) (alpha : ClassicalHodgeFiber X H p)
    (hword : (∑ j ∈ s, coeff j • GSTTargetWordRecovery.wordOperator
      (fun i => (S i).frame) ((word j).1::(word j).2) alpha)=alpha) :
    H.cycleClass p (targetWordCycle S hS s word coeff alpha)=alpha.1 := by
  exact GSTTargetWordRecovery.exact_target_of_word_relation (H.cycleClass p)
    (rationalHodgeSubspace (H.hodgeBigrading p)).subtype (fun i => (S i).frame)
    (fun i => (S i).oneCorrection (hS i))
    (fun i x => source_step_class_frame (S i) (hS i) x) s word coeff alpha hword

/-- No division is used in the three-word cycle formula. -/
theorem originalX_fourth_order_recovery
    (SA SB SC : SourceSystem X H p κ)
    (hA : SA.SourceAlgebraicity) (hB : SB.SourceAlgebraicity)
    (hidentity : SA.frame*SA.frame*SB.frame*SB.frame +
      SA.frame*SA.frame*SC.frame*SC.frame + SB.frame*SB.frame*SC.frame*SC.frame=1)
    (alpha : ClassicalHodgeFiber X H p) :
    H.cycleClass p
      (GSTTargetWordRecovery.fourthOrderCycle SA.frame SB.frame SC.frame
        (SA.oneCorrection hA) (SB.oneCorrection hB) alpha)=alpha.1 := by
  exact GSTTargetWordRecovery.fourthOrderCycle_class (H.cycleClass p)
    (rationalHodgeSubspace (H.hodgeBigrading p)).subtype SA.frame SB.frame SC.frame
    (SA.oneCorrection hA) (SB.oneCorrection hB)
    (source_step_class_frame SA hA) (source_step_class_frame SB hB) hidentity alpha

#print axioms targetWordCycle_exact
#print axioms originalX_fourth_order_recovery
end GSTClassicalHodgeWordSourceRecovery
