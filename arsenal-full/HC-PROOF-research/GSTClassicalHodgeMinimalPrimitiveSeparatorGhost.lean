import GSTClassicalHodgeOmniversalSeparatorGhostCrown
import GSTClassicalHodgeGradedSeparatorBackpropagation

/-!
# GST CLASSICAL HODGE — MINIMAL PRIMITIVE SEPARATOR GHOST

The graded backpropagation theorem lets us sharpen an arbitrary classical
failure by well-founded descent on the Hodge weight.

Choose the least weight p admitting a microscopic basis separator.  Any
verified graded geometric program from a strictly smaller Hodge weight into the
detected sheet must then be invisible to the separator on every source Hodge
basis vector: a nonzero read would pull the separator back to the smaller
weight, contradicting minimality.

Thus every genuine Hodge failure has a *primitive* obstruction in an intrinsic
sense determined by the entire mixed projective/principal-cut program algebra,
not merely by one Lefschetz operator.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeMinimalPrimitiveSeparatorGhost

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeSingleSheetCrown
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeGradedSeparatorBackpropagation
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeLimitlessSeparatorGhost

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- There is a microscopic separator in weight p. -/
def HasBasisSeparator (p : Nat) : Prop :=
  ∃ i : ClassicalHodgeBasisIndex V H p,
    Nonempty (BasisAtomicSeparator V H p i)

/-- A Stage-2G failure gives at least one separator weight. -/
theorem exists_separator_weight
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ p : Nat, HasBasisSeparator (V := V) (H := H) p := by
  rw [not_bigradedBettiHodgeStatement_iff_exists_basis_separator V H] at hnot
  rcases hnot with ⟨p,i,hS⟩
  exact ⟨p,i,hS⟩

/-- Least codimension in which a separator exists. -/
noncomputable def minimalSeparatorWeight
    (hnot : ¬ BigradedBettiHodgeStatement V H) : Nat :=
  Nat.find (exists_separator_weight (V := V) (H := H) hnot)

/-- The least separator weight actually carries a separator. -/
theorem minimalSeparatorWeight_spec
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    HasBasisSeparator (V := V) (H := H) (minimalSeparatorWeight hnot) :=
  Nat.find_spec (exists_separator_weight (V := V) (H := H) hnot)

/-- No smaller weight carries any basis separator. -/
theorem no_separator_below_minimal
    (hnot : ¬ BigradedBettiHodgeStatement V H)
    {q : Nat} (hq : q < minimalSeparatorWeight hnot) :
    ¬ HasBasisSeparator (V := V) (H := H) q := by
  exact Nat.find_min' (exists_separator_weight (V := V) (H := H) hnot) q hq

/-- Choose one exact separator at the minimal bad weight. -/
noncomputable def minimalSeparatorSheet
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ClassicalHodgeBasisIndex V H (minimalSeparatorWeight hnot) :=
  Classical.choose (minimalSeparatorWeight_spec (V := V) (H := H) hnot)

/-- The chosen minimal sheet carries a genuine separator. -/
noncomputable def minimalSeparator
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    BasisAtomicSeparator V H (minimalSeparatorWeight hnot)
      (minimalSeparatorSheet hnot) :=
  Classical.choice
    (Classical.choose_spec
      (minimalSeparatorWeight_spec (V := V) (H := H) hnot))

/-- **MINIMAL-WEIGHT PRIMITIVITY.**
No verified graded geometric program from a smaller Hodge weight can be read
nontrivially by the minimal separator on any genuine source Hodge basis sheet. -/
theorem minimalSeparator_kills_lower_basis_programs
    (G : GeometricCycleClassSpine V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H)
    {q : Nat}
    (hq : q < minimalSeparatorWeight hnot)
    (P : GradedGeometricProgram V q (minimalSeparatorWeight hnot))
    (i : ClassicalHodgeBasisIndex V H q) :
    (minimalSeparator hnot).detector
      (P.cohomologyEval G (classicalHodgeBasis V H q i).1) = 0 := by
  by_contra hne
  have hback :
      Nonempty (BasisAtomicSeparator V H q i) :=
    exists_backpropagated_separator_of_basis_transport
      G P i (minimalSeparator hnot) 1 one_ne_zero (by
        simpa using
          (show P.cohomologyEval G (classicalHodgeBasis V H q i).1 =
              1 • P.cohomologyEval G (classicalHodgeBasis V H q i).1 by simp))
  exact no_separator_below_minimal (V := V) (H := H) hnot hq ⟨i,hback⟩

/-- Direct formulation avoiding the scalar transport wrapper: a nonzero pullback
of the minimal detector on any lower basis would itself be a smaller basis
separator, contradiction. -/
theorem minimalSeparator_pullback_basis_zero
    (G : GeometricCycleClassSpine V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H)
    {q : Nat}
    (hq : q < minimalSeparatorWeight hnot)
    (P : GradedGeometricProgram V q (minimalSeparatorWeight hnot))
    (i : ClassicalHodgeBasisIndex V H q) :
    pullbackDetector G P (minimalSeparator hnot).detector
      (classicalHodgeBasis V H q i).1 = 0 := by
  unfold pullbackDetector
  exact minimalSeparator_kills_lower_basis_programs G hnot hq P i

/-- The entire pullback detector through any program from a smaller weight is
zero on the genuine Hodge fiber. -/
theorem minimalSeparator_pullback_zero_on_hodge
    (G : GeometricCycleClassSpine V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H)
    {q : Nat}
    (hq : q < minimalSeparatorWeight hnot)
    (P : GradedGeometricProgram V q (minimalSeparatorWeight hnot))
    (alpha : ClassicalHodgeFiber V H q) :
    pullbackDetector G P (minimalSeparator hnot).detector alpha.1 = 0 := by
  classical
  rw [show alpha =
      ∑ i ∈ ((classicalHodgeBasis V H q).repr alpha).support,
        ((classicalHodgeBasis V H q).repr alpha i) •
          classicalHodgeBasis V H q i by
    exact (classicalHodgeBasis V H q).sum_repr alpha]
  simp only [map_sum, LinearMap.map_smul]
  apply Finset.sum_eq_zero
  intro i hi
  simp [minimalSeparator_pullback_basis_zero G hnot hq P i]

/-- A minimal failure therefore yields an omniversal separator ghost with the
extra primitive law against every lower-weight geometric program. -/
structure MinimalPrimitiveGhost
    (G : GeometricCycleClassSpine V H) where
  weight : Nat
  sheet : ClassicalHodgeBasisIndex V H weight
  separator : BasisAtomicSeparator V H weight sheet
  minimal : ∀ q < weight, ¬ HasBasisSeparator (V := V) (H := H) q
  ghost : FiberedCompletedAddress V H :=
    separatorFiberedProbe (V := V) (H := H) weight separator.detector
  ghost_ne_zero : ghost ≠ 0
  primitive :
    ∀ q : Nat, q < weight →
    ∀ P : GradedGeometricProgram V q weight,
    ∀ alpha : ClassicalHodgeFiber V H q,
      separator.detector (P.cohomologyEval G alpha.1) = 0

/-- Every genuine Stage-2G failure contains a least-weight primitive ghost. -/
noncomputable def minimalPrimitiveGhostOfFailure
    (G : GeometricCycleClassSpine V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    MinimalPrimitiveGhost G where
  weight := minimalSeparatorWeight hnot
  sheet := minimalSeparatorSheet hnot
  separator := minimalSeparator hnot
  minimal := fun q hq => no_separator_below_minimal hnot hq
  ghost := separatorFiberedProbe (V := V) (H := H)
    (minimalSeparatorWeight hnot) (minimalSeparator hnot).detector
  ghost_ne_zero := basisSeparator_ghost_ne_zero (minimalSeparator hnot)
  primitive := by
    intro q hq P alpha
    exact minimalSeparator_pullback_zero_on_hodge G hnot hq P alpha

/-- **FAILURE -> MINIMAL PRIMITIVE LIMITLESS GHOST.** -/
theorem not_hodge_yields_minimalPrimitiveGhost
    (G : GeometricCycleClassSpine V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    Nonempty (MinimalPrimitiveGhost G) :=
  ⟨minimalPrimitiveGhostOfFailure G hnot⟩

#check HasBasisSeparator
#check minimalSeparatorWeight
#check minimalSeparator
#check minimalSeparator_kills_lower_basis_programs
#check minimalSeparator_pullback_zero_on_hodge
#check MinimalPrimitiveGhost
#check minimalPrimitiveGhostOfFailure
#check not_hodge_yields_minimalPrimitiveGhost

#print axioms minimalSeparator_kills_lower_basis_programs
#print axioms minimalSeparator_pullback_zero_on_hodge
#print axioms not_hodge_yields_minimalPrimitiveGhost

end GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
