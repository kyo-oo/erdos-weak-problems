import GSTClassicalHodgeClosedCorrespondenceGhostExtinction
import GSTClassicalHodgeAtomicSpan

/-!
# GST CLASSICAL HODGE — NATIVE-CYCLE CORRESPONDENCE GHOST ATTACK

The point-source restriction in the original closed-correspondence ghost
extinction theorem is unnecessary for the final attack.  A realized
correspondence word preserves the entire genuine cycle-class range, not merely
single point atoms.  Therefore a basis separator kills the image of EVERY
native algebraic codimension-p cycle under EVERY realized correspondence word.

This is the source form needed by the projective-degree / principal-cut
machinery: once that geometry manufactures one nonzero native Hodge source,
the only remaining task is one source-specific genuine correspondence word
whose cohomological action lands on a nonzero multiple of the target Hodge
basis sheet.

No Hodge surjectivity, matrix-unit descent, or arbitrary coordinate operator
is assumed here.
-/

set_option maxHeartbeats 80000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeNativeCycleCorrespondenceGhostAttack

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeSingleSheetCrown
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeClosedCorrespondenceGhostExtinction

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Every genuine native cycle class belongs to the atomic span. -/
theorem nativeCycle_class_mem_atomicSpan
    (Z : codimensionCycles V.X p) :
    H.cycleClass p Z ∈ pointCycleClassSpan p (H.cycleClass p) := by
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
  exact ⟨Z, rfl⟩

/-- **ARBITRARY NATIVE-CYCLE GHOST ANNIHILATION.**
A basis separator kills the image of every native algebraic cycle under every
genuine realized correspondence word. -/
theorem basisSeparator_kills_realizedWord_cycle
    {j : ClassicalHodgeBasisIndex V H p}
    (S : BasisAtomicSeparator V H p j)
    (W : RealizedCorrespondenceWord V H p)
    (Z : codimensionCycles V.X p) :
    S.detector
      ((realizedWordPair W).cohomologyOperator (H.cycleClass p Z)) = 0 := by
  have hZAtomic :
      H.cycleClass p Z ∈ pointCycleClassSpan p (H.cycleClass p) :=
    nativeCycle_class_mem_atomicSpan (V := V) (H := H) Z
  have hImage :
      (realizedWordPair W).cohomologyOperator (H.cycleClass p Z) ∈
        pointCycleClassSpan p (H.cycleClass p) :=
    realizedWord_atomic_stable W _ hZAtomic
  have hker :
      pointCycleClassSpan p (H.cycleClass p) ≤ LinearMap.ker S.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      p (H.cycleClass p) S.detector).mp S.annihilates_atoms
  exact hker hImage

/-- Source-specific genuine correspondence hit starting from an arbitrary
native codimension-p cycle rather than a single point atom. -/
def NativeCycleCorrespondenceHitsSheet
    (j : ClassicalHodgeBasisIndex V H p) : Prop :=
  ∃ Z : codimensionCycles V.X p,
  ∃ W : RealizedCorrespondenceWord V H p,
  ∃ c : ℚ,
    c ≠ 0 ∧
    (realizedWordPair W).cohomologyOperator (H.cycleClass p Z) =
      c • (classicalHodgeBasis V H p j).1

/-- A source-specific native-cycle correspondence hit puts the target basis
sheet in the actual cycle-class span. -/
theorem basis_mem_atomicSpan_of_nativeCycleCorrespondenceHit
    (j : ClassicalHodgeBasisIndex V H p)
    (hHit : NativeCycleCorrespondenceHitsSheet (V := V) (H := H) j) :
    (classicalHodgeBasis V H p j).1 ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  rcases hHit with ⟨Z,W,c,hc,hEq⟩
  have hZAtomic :
      H.cycleClass p Z ∈ pointCycleClassSpan p (H.cycleClass p) :=
    nativeCycle_class_mem_atomicSpan (V := V) (H := H) Z
  have hImage :
      (realizedWordPair W).cohomologyOperator (H.cycleClass p Z) ∈
        pointCycleClassSpan p (H.cycleClass p) :=
    realizedWord_atomic_stable W _ hZAtomic
  rw [hEq] at hImage
  have hscaled :=
    (pointCycleClassSpan p (H.cycleClass p)).smul_mem c⁻¹ hImage
  simpa [hc, smul_smul] using hscaled

/-- Therefore a source-specific hit from ANY native cycle destroys the ghost
separator at the target sheet. -/
theorem isEmpty_basisAtomicSeparator_of_nativeCycleCorrespondenceHit
    (j : ClassicalHodgeBasisIndex V H p)
    (hHit : NativeCycleCorrespondenceHitsSheet (V := V) (H := H) j) :
    IsEmpty (BasisAtomicSeparator V H p j) :=
  (basis_mem_atomicSpan_iff_no_separator V H p j).mp
    (basis_mem_atomicSpan_of_nativeCycleCorrespondenceHit j hHit)

/-- Exact Stage-2G Hodge statement from source-specific genuine correspondence
hits, allowing the source for each target sheet to be any native algebraic
cycle. -/
theorem bigradedBettiHodge_of_nativeCycleCorrespondenceHits
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hHit : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        NativeCycleCorrespondenceHitsSheet (V := V) (H := H) j) :
    BigradedBettiHodgeStatement V H := by
  apply (bigradedBettiHodgeStatement_iff_no_basis_separator V H).mpr
  intro q j
  exact isEmpty_basisAtomicSeparator_of_nativeCycleCorrespondenceHit j (hHit q j)

#check nativeCycle_class_mem_atomicSpan
#check basisSeparator_kills_realizedWord_cycle
#check NativeCycleCorrespondenceHitsSheet
#check basis_mem_atomicSpan_of_nativeCycleCorrespondenceHit
#check isEmpty_basisAtomicSeparator_of_nativeCycleCorrespondenceHit
#check bigradedBettiHodge_of_nativeCycleCorrespondenceHits

#print axioms nativeCycle_class_mem_atomicSpan
#print axioms basisSeparator_kills_realizedWord_cycle
#print axioms basis_mem_atomicSpan_of_nativeCycleCorrespondenceHit
#print axioms bigradedBettiHodge_of_nativeCycleCorrespondenceHits

end GSTClassicalHodgeNativeCycleCorrespondenceGhostAttack
