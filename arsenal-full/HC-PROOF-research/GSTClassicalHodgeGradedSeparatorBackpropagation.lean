import GSTClassicalHodgeLimitlessSeparatorGhost
import GSTClassicalHodgeGradedGeometricProgramOrbit
import GSTClassicalHodgeAtomicAnnihilator
import GSTNativeCodimensionCyclePresentation

/-!
# GST CLASSICAL HODGE — GRADED SEPARATOR BACKPROPAGATION

The limitless separator ghost is not merely a static completed probe.  Every
verified graded geometric program has an exact native/cohomological commuting
square.  Therefore a detector annihilating the genuine cycle-class range at a
target weight can be pulled backward through any mixed projective/principal-cut
program, and the pulled detector still annihilates the genuine cycle-class
range at the source weight.

This file upgrades a hypothetical Hodge obstruction into a complete backward
cone through the genuine graded geometry cosmology.

The key consequence is sharp: a basis separator at weight q annihilates the
image of the canonical geometric origin under *every* verified program
0 -> q.  More generally, if one such program carries a source Hodge basis
vector with nonzero coefficient into the target basis direction detected by
the separator, then the separator backpropagates to a genuine basis separator
at the source weight.  Hence any surviving obstruction must be primitive with
respect to every available descending geometric channel.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGradedSeparatorBackpropagation

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeSingleSheetCrown
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeLimitlessSeparatorGhost

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Pull an ambient detector backward through one verified graded geometric
program. -/
noncomputable def pullbackDetector
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (P : GradedGeometricProgram V p q)
    (ell : RationalSingularCohomology H.analytification (2 * q) →ₗ[ℚ] ℚ) :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ :=
  ell.comp (P.cohomologyEval G)

/-- If the target detector kills the entire genuine cycle-class range, then
its pullback through any genuine graded program kills the entire source range. -/
theorem pullbackDetector_annihilates_range
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (P : GradedGeometricProgram V p q)
    (ell : RationalSingularCohomology H.analytification (2 * q) →ₗ[ℚ] ℚ)
    (hell : ∀ Z : codimensionCycles V.X q,
      ell (H.cycleClass q Z) = 0) :
    ∀ Z : codimensionCycles V.X p,
      pullbackDetector G P ell (H.cycleClass p Z) = 0 := by
  intro Z
  unfold pullbackDetector
  rw [LinearMap.comp_apply]
  rw [← P.cycleClass_cycleEval G Z]
  exact hell (P.cycleEval G Z)

/-- Point-atom annihilation is enough at the target because, on a smooth
projective carrier, the span of genuine point-cycle classes is exactly the
cycle-class range. -/
theorem pullbackDetector_annihilates_atoms
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (P : GradedGeometricProgram V p q)
    (ell : RationalSingularCohomology H.analytification (2 * q) →ₗ[ℚ] ℚ)
    (hell : AnnihilatesPointCycleClasses q (H.cycleClass q) ell) :
    AnnihilatesPointCycleClasses p (H.cycleClass p) (pullbackDetector G P ell) := by
  have hker :
      pointCycleClassSpan q (H.cycleClass q) ≤ LinearMap.ker ell :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      q (H.cycleClass q) ell).mp hell
  have hrange :
      ∀ Z : codimensionCycles V.X q,
        ell (H.cycleClass q Z) = 0 := by
    intro Z
    apply hker
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H q]
    exact ⟨Z, rfl⟩
  intro x
  exact pullbackDetector_annihilates_range G P ell hrange
    (codimensionPointCycle V.X p x)

/-- A target basis separator therefore pulls back through every verified mixed
geometric program to an atomic annihilator at the source weight. -/
theorem basisSeparator_pullback_annihilates_atoms
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (P : GradedGeometricProgram V p q)
    {j : ClassicalHodgeBasisIndex V H q}
    (S : BasisAtomicSeparator V H q j) :
    AnnihilatesPointCycleClasses p (H.cycleClass p)
      (pullbackDetector G P S.detector) :=
  pullbackDetector_annihilates_atoms G P S.detector S.annihilates_atoms

/-- If a program sends a source Hodge basis vector to a state detected
nontrivially by a target separator, then the obstruction genuinely descends to
that source basis sheet. -/
noncomputable def backpropagatedBasisSeparator
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (P : GradedGeometricProgram V p q)
    (i : ClassicalHodgeBasisIndex V H p)
    {j : ClassicalHodgeBasisIndex V H q}
    (S : BasisAtomicSeparator V H q j)
    (hdetect :
      S.detector
        (P.cohomologyEval G (classicalHodgeBasis V H p i).1) ≠ 0) :
    BasisAtomicSeparator V H p i where
  detector := pullbackDetector G P S.detector
  annihilates_atoms := basisSeparator_pullback_annihilates_atoms G P S
  detects_basis := by
    simpa [pullbackDetector] using hdetect

/-- Scalar-target form: if the source basis is transported to a nonzero scalar
multiple of the target basis detected by S, then S necessarily backpropagates. -/
theorem exists_backpropagated_separator_of_basis_transport
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (P : GradedGeometricProgram V p q)
    (i : ClassicalHodgeBasisIndex V H p)
    {j : ClassicalHodgeBasisIndex V H q}
    (S : BasisAtomicSeparator V H q j)
    (c : ℚ) (hc : c ≠ 0)
    (hP :
      P.cohomologyEval G (classicalHodgeBasis V H p i).1 =
        c • (classicalHodgeBasis V H q j).1) :
    Nonempty (BasisAtomicSeparator V H p i) := by
  have hdetect :
      S.detector
        (P.cohomologyEval G (classicalHodgeBasis V H p i).1) ≠ 0 := by
    rw [hP, LinearMap.map_smul]
    exact smul_ne_zero hc S.detects_basis
  exact ⟨backpropagatedBasisSeparator G P i S hdetect⟩

/-- Every basis separator annihilates the image of every actual source cycle
under every verified graded program. -/
theorem basisSeparator_kills_every_program_cycle
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (P : GradedGeometricProgram V p q)
    {j : ClassicalHodgeBasisIndex V H q}
    (S : BasisAtomicSeparator V H q j)
    (Z : codimensionCycles V.X p) :
    S.detector (P.cohomologyEval G (H.cycleClass p Z)) = 0 := by
  have h := basisSeparator_pullback_annihilates_atoms G P S
  have hker :
      pointCycleClassSpan p (H.cycleClass p) ≤
        LinearMap.ker (pullbackDetector G P S.detector) :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      p (H.cycleClass p) (pullbackDetector G P S.detector)).mp h
  have hmem : H.cycleClass p Z ∈ pointCycleClassSpan p (H.cycleClass p) := by
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
    exact ⟨Z, rfl⟩
  exact hker hmem

/-- **CANONICAL-ORIGIN GHOST LAW.**
A surviving basis separator is orthogonal to every state reachable from the
canonical codimension-zero geometric origin by any verified mixed program. -/
theorem basisSeparator_kills_geometricOrigin_orbit
    (G : GeometricCycleClassSpine V H)
    {q : Nat}
    {j : ClassicalHodgeBasisIndex V H q}
    (S : BasisAtomicSeparator V H q j)
    (P : GradedGeometricProgram V 0 q) :
    S.detector
      (P.cohomologyEval G (geometricOriginClass V H)) = 0 := by
  exact basisSeparator_kills_every_program_cycle G P S
    (GSTClassicalHodgeCodimensionZeroFundamentalCycle.codimensionZeroFundamentalCycle V)

/-- Consequently any geometric program which reaches the detected target
basis with a nonzero coefficient contradicts the existence of that separator. -/
theorem no_basisSeparator_of_origin_reaches_basis
    (G : GeometricCycleClassSpine V H)
    {q : Nat}
    (j : ClassicalHodgeBasisIndex V H q)
    (P : GradedGeometricProgram V 0 q)
    (c : ℚ) (hc : c ≠ 0)
    (hreach :
      P.cohomologyEval G (geometricOriginClass V H) =
        c • (classicalHodgeBasis V H q j).1) :
    IsEmpty (BasisAtomicSeparator V H q j) := by
  refine ⟨?_⟩
  intro S
  have hzero := basisSeparator_kills_geometricOrigin_orbit G S P
  rw [hreach, LinearMap.map_smul] at hzero
  exact S.detects_basis (by
    apply (smul_eq_zero.mp hzero).resolve_left hc)

#check pullbackDetector
#check pullbackDetector_annihilates_range
#check pullbackDetector_annihilates_atoms
#check backpropagatedBasisSeparator
#check exists_backpropagated_separator_of_basis_transport
#check basisSeparator_kills_every_program_cycle
#check basisSeparator_kills_geometricOrigin_orbit
#check no_basisSeparator_of_origin_reaches_basis

#print axioms pullbackDetector_annihilates_range
#print axioms pullbackDetector_annihilates_atoms
#print axioms exists_backpropagated_separator_of_basis_transport
#print axioms basisSeparator_kills_geometricOrigin_orbit
#print axioms no_basisSeparator_of_origin_reaches_basis

end GSTClassicalHodgeGradedSeparatorBackpropagation
