import GSTClassicalHodgeSheetSpectralExtraction
import GSTClassicalHodgeFiberedTransferCompletion
import GSTClassicalHodgeAtomicAnnihilator
import GSTHodgeBigradedCosmology
import GSTHodgeAssaultV2

/-!
# GST CLASSICAL HODGE — SINGLE-SHEET CROWN

The full classical target can be reduced to its smallest possible obstruction:
one genuine classical Hodge basis direction at one codimension, together with
one rational detector that annihilates every genuine algebraic point-cycle
class but detects that basis direction.

Eliminating these single-basis separators is equivalent to the complete
Stage-2G Hodge statement.  Each such basis direction is simultaneously:

* one independent fibered GST sheet;
* one exact finite-support coordinate atom;
* one limitless cosmic diagonal generator after forgetting multiplicity.

This module therefore isolates the exact microscopic object on which the
remaining transport machinery must act, without collapsing multiplicity or
confusing the classical codimension with the local sheet coordinate.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedTransferCompletion
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeAtomicAnnihilator

namespace GSTClassicalHodgeSingleSheetCrown

/-- One microscopic classical obstruction: a detector annihilating every
native codimension-p point-cycle class while detecting one chosen genuine
rational Hodge basis vector. -/
structure BasisAtomicSeparator
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H p) where
  detector :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ
  annihilates_atoms :
    AnnihilatesPointCycleClasses p (H.cycleClass p) detector
  detects_basis :
    detector (classicalHodgeBasis V H p i).1 ≠ 0

/-- Membership of one classical Hodge basis vector in the atomic algebraic
span is exactly the nonexistence of a separator detecting that vector. -/
theorem basis_mem_atomicSpan_iff_no_separator
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H p) :
    (classicalHodgeBasis V H p i).1 ∈
        pointCycleClassSpan p (H.cycleClass p) ↔
      IsEmpty (BasisAtomicSeparator V H p i) := by
  constructor
  · intro hmem
    refine ⟨?_⟩
    intro S
    have hker :
        pointCycleClassSpan p (H.cycleClass p) ≤
          LinearMap.ker S.detector :=
      (annihilatesPointCycles_iff_atomicSpan_le_ker
        p (H.cycleClass p) S.detector).mp S.annihilates_atoms
    exact S.detects_basis (hker hmem)
  · intro hnone
    by_contra hnot
    obtain ⟨ell, hellSpan, hellBasis⟩ :=
      exists_linearFunctional_separating_submodule
        (pointCycleClassSpan p (H.cycleClass p))
        (classicalHodgeBasis V H p i).1 hnot
    have hatoms :
        AnnihilatesPointCycleClasses p (H.cycleClass p) ell := by
      intro x
      apply hellSpan
      exact Submodule.subset_span ⟨x, rfl⟩
    exact isEmpty_iff.mp hnone
      ⟨ell, hatoms, hellBasis⟩

/-- Vanishing of the atomic defect on one chosen basis vector is the same
single-sheet no-separator statement. -/
theorem basis_atomicDefect_zero_iff_no_separator
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H p) :
    atomicDefectLinearMap V H p (classicalHodgeBasis V H p i) = 0 ↔
      IsEmpty (BasisAtomicSeparator V H p i) := by
  rw [atomicDefectLinearMap_apply]
  constructor
  · intro hzero
    exact (basis_mem_atomicSpan_iff_no_separator V H p i).mp
      ((Submodule.Quotient.mk_eq_zero
        (pointCycleClassSpan p (H.cycleClass p))).mp hzero)
  · intro hsep
    exact (Submodule.Quotient.mk_eq_zero
      (pointCycleClassSpan p (H.cycleClass p))).mpr
      ((basis_mem_atomicSpan_iff_no_separator V H p i).mpr hsep)

/-- **SINGLE-SHEET FORM OF THE CLASSICAL HODGE TARGET.**
The complete Stage-2G statement is equivalent to the nonexistence of a
separator for every individual genuine Hodge basis sheet. -/
theorem bigradedBettiHodgeStatement_iff_no_basis_separator
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    BigradedBettiHodgeStatement V H ↔
      ∀ p : Nat, ∀ i : ClassicalHodgeBasisIndex V H p,
        IsEmpty (BasisAtomicSeparator V H p i) := by
  rw [bigradedBettiHodgeStatement_iff_basis_atomicDefect_zero V H]
  constructor
  · intro h p i
    exact (basis_atomicDefect_zero_iff_no_separator V H p i).mp (h p i)
  · intro h p i
    exact (basis_atomicDefect_zero_iff_no_separator V H p i).mpr (h p i)

/-- Every microscopic classical basis direction is literally one independent
fibered GST sheet before multiplicity is forgotten. -/
theorem classical_basis_is_single_fibered_sheet
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H p) :
    fiberedWeightCoordinates V H p (classicalHodgeBasis V H p i) =
      fiberedSheetGenerator V H ⟨p,i⟩ :=
  classicalBasis_eq_fiberedSheetGenerator V H p i

/-- The same microscopic sheet has the exact limitless GST cosmic diagonal
address at its classical base weight p. -/
theorem classical_basis_single_sheet_cosmic_address
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H p) :
    forgetMultiplicityToGST
      (fiberedSheetGenerator V H ⟨p,i⟩) =
        Finsupp.single
          (GSTUniversalAddressBridge.cosmicAddressEquiv (p,p)) 1 :=
  fiberedSheet_projects_to_cosmicGenerator V H p i

/-- A single-sheet separator therefore detects a class whose GST image is an
exact cosmic diagonal generator while annihilating every genuine classical
codimension-p algebraic atom. -/
theorem basisSeparator_cosmic_crown
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H p)
    (S : BasisAtomicSeparator V H p i) :
    S.detector (classicalHodgeBasis V H p i).1 ≠ 0
    ∧ AnnihilatesPointCycleClasses p (H.cycleClass p) S.detector
    ∧ forgetMultiplicityToGST
        (fiberedWeightCoordinates V H p
          (classicalHodgeBasis V H p i)) =
        Finsupp.single
          (GSTUniversalAddressBridge.cosmicAddressEquiv (p,p)) 1 := by
  exact ⟨S.detects_basis, S.annihilates_atoms,
    classical_basis_projects_to_cosmic_diagonal V H p i⟩

/-- Failure of the full classical target is equivalent to existence of one
single classical Hodge sheet carrying the microscopic separator. -/
theorem not_bigradedBettiHodgeStatement_iff_exists_basis_separator
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    ¬ BigradedBettiHodgeStatement V H ↔
      ∃ p : Nat,
      ∃ i : ClassicalHodgeBasisIndex V H p,
        Nonempty (BasisAtomicSeparator V H p i) := by
  constructor
  · intro hnot
    have h :=
      not_congr (bigradedBettiHodgeStatement_iff_no_basis_separator V H)
    rw [h] at hnot
    push_neg at hnot
    obtain ⟨p,i,hne⟩ := hnot
    have hnonempty : Nonempty (BasisAtomicSeparator V H p i) := by
      exact hne
    exact ⟨p,i,hnonempty⟩
  · rintro ⟨p,i,⟨S⟩⟩ hHodge
    have hnone :=
      (bigradedBettiHodgeStatement_iff_no_basis_separator V H).mp
        hHodge p i
    exact isEmpty_iff.mp hnone S

/-- **MICROSCOPIC CROWN.**  To prove the full classical target it is enough,
and necessary, to eliminate the single-sheet separator at every `(p,i)`;
every such sheet simultaneously carries its exact unrestricted classical
basis vector and exact limitless GST cosmic diagonal address. -/
theorem classical_hodge_single_sheet_crown
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    BigradedBettiHodgeStatement V H ↔
      ∀ p : Nat, ∀ i : ClassicalHodgeBasisIndex V H p,
        IsEmpty (BasisAtomicSeparator V H p i) :=
  bigradedBettiHodgeStatement_iff_no_basis_separator V H

#check BasisAtomicSeparator
#check basis_mem_atomicSpan_iff_no_separator
#check basis_atomicDefect_zero_iff_no_separator
#check bigradedBettiHodgeStatement_iff_no_basis_separator
#check classical_basis_is_single_fibered_sheet
#check classical_basis_single_sheet_cosmic_address
#check basisSeparator_cosmic_crown
#check not_bigradedBettiHodgeStatement_iff_exists_basis_separator
#check classical_hodge_single_sheet_crown

#print axioms basis_mem_atomicSpan_iff_no_separator
#print axioms bigradedBettiHodgeStatement_iff_no_basis_separator
#print axioms basisSeparator_cosmic_crown
#print axioms not_bigradedBettiHodgeStatement_iff_exists_basis_separator
#print axioms classical_hodge_single_sheet_crown

end GSTClassicalHodgeSingleSheetCrown
