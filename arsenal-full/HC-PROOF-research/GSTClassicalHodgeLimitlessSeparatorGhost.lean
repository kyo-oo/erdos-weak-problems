import GSTClassicalHodgeSingleSheetCrown
import GSTClassicalHodgeAtomicDefectDuality
import GSTClassicalHodgeGradedGeometricOrbitAlgebra

/-!
# GST CLASSICAL HODGE — LIMITLESS SEPARATOR GHOST

A failure of the genuine Stage-2G Hodge statement is equivalent to one
microscopic basis separator: a rational cohomology functional which kills every
genuine codimension-p point-cycle class while detecting one genuine Hodge basis
sheet.  The limitless fibered Hodge universe already carries a perfect pairing
between compact finite-support addresses and unrestricted completed probes.

This file sends the classical separator itself into that completed limitless
dual universe.

For a fixed weight p and an ambient functional ell, define the completed probe
whose value on a fibered address (q,j) is zero unless q=p, and at weight p is
exactly ell evaluated on the genuine Hodge basis vector j.  The central theorem
is an exact pairing identity:

  < fiberedWeightCoordinates(alpha), separatorProbe(ell) > = ell(alpha).

Consequently a BasisAtomicSeparator becomes a nonzero limitless ghost probe
which

* detects its offending classical basis sheet;
* annihilates every Hodge class already in the genuine atomic point-cycle span;
* annihilates, a fortiori, every Hodge state in the verified graded geometric
  program orbit, because that orbit is already proved to lie in the actual
  cycle-class range.

This is a genuine bridge of the obstruction, not a sufficient-condition
wrapper and not an identification of multiplicity with native geometry.  It
converts every possible classical failure into a completed limitless dual
object orthogonal to the entire verified native/projective/cut cosmology while
remaining nonzero on one exact fibered sheet.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeLimitlessSeparatorGhost

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeSingleSheetCrown
open GSTClassicalHodgeGradedGeometricOrbitAlgebra

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Completed limitless probe induced by one ambient cohomology functional at
one fixed Hodge weight.  It remembers full classical multiplicity. -/
noncomputable def separatorFiberedProbe
    (p : Nat)
    (ell : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ) :
    FiberedCompletedAddress V H :=
  fun s =>
    if hsp : s.1 = p then
      ell ((classicalHodgeBasis V H p (hsp ▸ s.2)).1)
    else 0

/-- The separator probe reads a basis atom in its own weight exactly as the
original ambient functional reads that Hodge basis vector. -/
@[simp]
theorem separatorFiberedProbe_at_same_weight
    (p : Nat)
    (ell : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ)
    (i : ClassicalHodgeBasisIndex V H p) :
    separatorFiberedProbe (V := V) (H := H) p ell
      (⟨p,i⟩ : FiberedHodgeIndex V H) =
      ell (classicalHodgeBasis V H p i).1 := by
  simp [separatorFiberedProbe]

/-- The separator probe vanishes identically on every different Hodge weight. -/
@[simp]
theorem separatorFiberedProbe_at_other_weight
    (p q : Nat) (hpq : q ≠ p)
    (ell : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ)
    (j : ClassicalHodgeBasisIndex V H q) :
    separatorFiberedProbe (V := V) (H := H) p ell
      (⟨q,j⟩ : FiberedHodgeIndex V H) = 0 := by
  simp [separatorFiberedProbe, hpq]

/-- **EXACT SEPARATOR/PAIRING IDENTITY.**
Embedding a genuine weight-p Hodge vector into the limitless fibered address
universe and pairing against the completed separator probe gives exactly the
original ambient detector value. -/
theorem fiberedPairing_separatorProbe
    (p : Nat)
    (ell : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ)
    (alpha : ClassicalHodgeFiber V H p) :
    fiberedPairing
        (fiberedWeightCoordinates V H p alpha)
        (separatorFiberedProbe (V := V) (H := H) p ell) =
      ell alpha.1 := by
  classical
  have hlhs : fiberedPairing (fiberedWeightCoordinates V H p alpha)
      (separatorFiberedProbe (V := V) (H := H) p ell) =
      ∑ a ∈ ((classicalHodgeBasis V H p).repr alpha).support,
        ((classicalHodgeBasis V H p).repr alpha) a *
          ell ((classicalHodgeBasis V H p a).1) := by
    show (Finsupp.embDomain (weightFiberEmbedding V H p)
        ((classicalHodgeBasis V H p).repr alpha)).sum
        (fun s q => q * separatorFiberedProbe (V := V) (H := H) p ell s) = _
    rw [Finsupp.sum_embDomain]
    simp only [Finsupp.sum, weightFiberEmbedding,
      Function.Embedding.sigmaMk_apply, separatorFiberedProbe_at_same_weight,
      smul_eq_mul]
  have hrhs : ell alpha.1 =
      ∑ a ∈ ((classicalHodgeBasis V H p).repr alpha).support,
        ((classicalHodgeBasis V H p).repr alpha) a *
          ell ((classicalHodgeBasis V H p a).1) := by
    conv_lhs => rw [show alpha =
        Finsupp.linearCombination ℚ (classicalHodgeBasis V H p)
          ((classicalHodgeBasis V H p).repr alpha) from
        ((classicalHodgeBasis V H p).linearCombination_repr alpha).symm]
    rw [Finsupp.linearCombination_apply, Finsupp.sum,
      AddSubmonoidClass.coe_finsetSum]
    simp only [Submodule.coe_smul_of_tower, map_sum, LinearMap.map_smul,
      smul_eq_mul]
  rw [hlhs, hrhs]

/-- A genuine basis separator becomes a nonzero completed limitless probe: it
pairs nontrivially with the exact fibered address of the basis sheet it detects. -/
theorem basisSeparator_ghost_detects_sheet
    {p : Nat}
    {i : ClassicalHodgeBasisIndex V H p}
    (S : BasisAtomicSeparator V H p i) :
    fiberedPairing
        (fiberedWeightCoordinates V H p (classicalHodgeBasis V H p i))
        (separatorFiberedProbe (V := V) (H := H) p S.detector) ≠ 0 := by
  rw [fiberedPairing_separatorProbe]
  exact S.detects_basis

/-- Hence the completed probe associated to a basis separator is itself
nonzero in the limitless dual universe. -/
theorem basisSeparator_ghost_ne_zero
    {p : Nat}
    {i : ClassicalHodgeBasisIndex V H p}
    (S : BasisAtomicSeparator V H p i) :
    separatorFiberedProbe (V := V) (H := H) p S.detector ≠ 0 := by
  intro hz
  apply S.detects_basis
  have hp := congrFun hz (⟨p,i⟩ : FiberedHodgeIndex V H)
  simpa using hp

/-- Every algebraic Hodge vector is invisible to the separator ghost. -/
theorem basisSeparator_ghost_annihilates_algebraicHodge
    {p : Nat}
    {i : ClassicalHodgeBasisIndex V H p}
    (S : BasisAtomicSeparator V H p i)
    (alpha : ClassicalHodgeFiber V H p)
    (halg : alpha.1 ∈ pointCycleClassSpan p (H.cycleClass p)) :
    fiberedPairing
        (fiberedWeightCoordinates V H p alpha)
        (separatorFiberedProbe (V := V) (H := H) p S.detector) = 0 := by
  rw [fiberedPairing_separatorProbe]
  have hker :
      pointCycleClassSpan p (H.cycleClass p) ≤ LinearMap.ker S.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      p (H.cycleClass p) S.detector).mp S.annihilates_atoms
  exact hker halg

/-- The verified mixed projective/principal-cut program orbit is invisible to
any basis-separator ghost whenever the orbit state is viewed as a genuine
Hodge vector.  This uses only the already-proved fact that the whole graded
program orbit lies in the actual cycle-class range. -/
theorem basisSeparator_ghost_annihilates_programOrbit
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    {p : Nat}
    {i : ClassicalHodgeBasisIndex V H p}
    (S : BasisAtomicSeparator V H p i)
    (alpha : ClassicalHodgeFiber V H p)
    (horbit : alpha.1 ∈ geometricProgramOrbitModule G p) :
    fiberedPairing
        (fiberedWeightCoordinates V H p alpha)
        (separatorFiberedProbe (V := V) (H := H) p S.detector) = 0 := by
  apply basisSeparator_ghost_annihilates_algebraicHodge S alpha
  have hrange : alpha.1 ∈ LinearMap.range (H.cycleClass p) :=
    geometricProgramOrbitModule_le_cycleClass_range G p horbit
  rw [smoothProjective_cycleClass_range_eq_atomic_span V H p] at hrange
  exact hrange

/-- Package the exact limitless obstruction produced by one microscopic
classical failure. -/
structure LimitlessSeparatorGhost where
  weight : Nat
  sheet : ClassicalHodgeBasisIndex V H weight
  probe : FiberedCompletedAddress V H
  probe_ne_zero : probe ≠ 0
  detects_sheet :
    fiberedPairing
      (fiberedWeightCoordinates V H weight
        (classicalHodgeBasis V H weight sheet)) probe ≠ 0
  annihilates_atomic :
    ∀ alpha : ClassicalHodgeFiber V H weight,
      alpha.1 ∈ pointCycleClassSpan weight (H.cycleClass weight) →
      fiberedPairing (fiberedWeightCoordinates V H weight alpha) probe = 0

/-- Every microscopic basis separator canonically determines a limitless ghost. -/
noncomputable def BasisAtomicSeparator.toLimitlessGhost
    {p : Nat}
    {i : ClassicalHodgeBasisIndex V H p}
    (S : BasisAtomicSeparator V H p i) :
    LimitlessSeparatorGhost (V := V) (H := H) where
  weight := p
  sheet := i
  probe := separatorFiberedProbe (V := V) (H := H) p S.detector
  probe_ne_zero := basisSeparator_ghost_ne_zero S
  detects_sheet := basisSeparator_ghost_detects_sheet S
  annihilates_atomic := fun alpha halg =>
    basisSeparator_ghost_annihilates_algebraicHodge S alpha halg

/-- **CLASSICAL FAILURE -> LIMITLESS GHOST.**
Any failure of the genuine Stage-2G Hodge statement produces a nonzero
completed limitless fibered probe which detects one exact Hodge sheet while
annihilating every genuine algebraic Hodge class in that weight. -/
theorem not_hodge_yields_limitless_separatorGhost
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    Nonempty (LimitlessSeparatorGhost (V := V) (H := H)) := by
  rw [not_bigradedBettiHodgeStatement_iff_exists_basis_separator V H] at hnot
  rcases hnot with ⟨p,i,⟨S⟩⟩
  exact ⟨BasisAtomicSeparator.toLimitlessGhost S⟩

/-- A no-ghost theorem on the completed fibered dual universe is therefore
already sufficient to close the classical Hodge target.  The premise is stated
purely in terms of the obstruction object constructed above, making the final
cosmological attack explicit rather than hiding it in a basis-cycle package. -/
theorem bigradedBettiHodge_of_no_limitless_separatorGhost
    (hghost : IsEmpty (LimitlessSeparatorGhost (V := V) (H := H))) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  exact isEmpty_iff.mp hghost (Classical.choice
    (not_hodge_yields_limitless_separatorGhost (V := V) (H := H) hnot))

#check separatorFiberedProbe
#check fiberedPairing_separatorProbe
#check basisSeparator_ghost_detects_sheet
#check basisSeparator_ghost_ne_zero
#check basisSeparator_ghost_annihilates_algebraicHodge
#check basisSeparator_ghost_annihilates_programOrbit
#check LimitlessSeparatorGhost
#check BasisAtomicSeparator.toLimitlessGhost
#check not_hodge_yields_limitless_separatorGhost
#check bigradedBettiHodge_of_no_limitless_separatorGhost

#print axioms fiberedPairing_separatorProbe
#print axioms basisSeparator_ghost_annihilates_programOrbit
#print axioms not_hodge_yields_limitless_separatorGhost
#print axioms bigradedBettiHodge_of_no_limitless_separatorGhost

end GSTClassicalHodgeLimitlessSeparatorGhost
