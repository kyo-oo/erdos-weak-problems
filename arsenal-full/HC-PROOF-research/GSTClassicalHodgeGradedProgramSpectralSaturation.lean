import GSTClassicalHodgeGradedGeometricOrbitAlgebra
import GSTClassicalHodgeCyclicSpectralGeneration
import GSTClassicalHodgeLocalCyclicCriterion

/-!
# GST CLASSICAL HODGE — GRADED PROGRAM SPECTRAL SATURATION

The graded geometric orbit is an intrinsic rational submodule and every mixed
program acts on it.  This makes the orbit itself the correct invariant space
for the cyclic spectral machinery.

At one fixed weight, take a finite family of genuine Hodge basis directions
which diagonalize one horizontal geometric program with pairwise distinct
rational eigenvalues.  No algebraicity-preservation hypothesis is needed:
program invariance of the graded orbit proves it automatically.

If every selected coordinate is merely *visible somewhere* in the orbit,
different coordinates may use different orbit states.  Rational hyperplane
avoidance assembles one orbit state with every selected coordinate nonzero.
Lagrange interpolation in the geometric program observable then isolates each
selected Hodge basis vector **inside the orbit itself**.

For one concrete Hodge class only its finite live support must be covered.
Thus the exact class becomes an element of the graded geometric orbit, and the
master program naturality theorem immediately supplies an actual native cycle.

This is stronger than the earlier projective spectral cover: spectral
extraction no longer lands merely in the large algebraic cycle-class span; it
lands in the much smaller program-generated cosmological orbit.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeGradedProgramSpectralSaturation

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeLocalCyclicCriterion
open GSTClassicalHodgeCyclicSpectralGeneration
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeGradedGeometricOrbitAlgebra

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Finite spectral chart carried by one horizontal element of the verified
graded geometric program algebra. -/
structure GradedProgramSpectralFamily
    (G : GeometricCycleClassSpine V H)
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  program : GradedGeometricProgram V p p
  basisIndex : ι → ClassicalHodgeBasisIndex V H p
  basisIndex_injective : Function.Injective basisIndex
  eigenvalue : ι → ℚ
  eigenvalue_injective : Function.Injective eigenvalue
  eigenvector : ∀ i,
    program.cohomologyEval G
        (classicalHodgeBasis V H p (basisIndex i)).1 =
      eigenvalue i • (classicalHodgeBasis V H p (basisIndex i)).1

namespace GradedProgramSpectralFamily

variable {G : GeometricCycleClassSpine V H}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Underlying finite spectral family of the geometric program. -/
noncomputable def toFiniteSpectralFamily
    (S : GradedProgramSpectralFamily (V := V) (H := H) (p := p) G ι) :
    FiniteSpectralFamily ι
      (RationalSingularCohomology H.analytification (2 * p)) where
  observable := S.program.cohomologyEval G
  vector := fun i => (classicalHodgeBasis V H p (S.basisIndex i)).1
  eigenvalue := S.eigenvalue
  eigenvector := S.eigenvector
  eigenvalue_injective := S.eigenvalue_injective

/-- One selected spectral coordinate is visible if some finite spectral
combination lying in the genuine graded program orbit has nonzero coefficient
in that coordinate. -/
def CoordinateVisible
    (S : GradedProgramSpectralFamily (V := V) (H := H) (p := p) G ι)
    (i : ι) : Prop :=
  S.toFiniteSpectralFamily.CoordinateVisible
    (geometricProgramOrbitModule G p) i

/-- The horizontal spectral program preserves the graded orbit automatically. -/
theorem program_orbit_stable
    (S : GradedProgramSpectralFamily (V := V) (H := H) (p := p) G ι) :
    ∀ x : RationalSingularCohomology H.analytification (2 * p),
      x ∈ geometricProgramOrbitModule G p →
      S.program.cohomologyEval G x ∈ geometricProgramOrbitModule G p := by
  intro x hx
  exact program_maps_geometricProgramOrbitModule G S.program hx

/-- Coordinatewise orbit visibility assembles one cyclic orbit seed whose
coefficient in every selected eigendirection is nonzero. -/
theorem exists_cyclic_orbit_seed
    (S : GradedProgramSpectralFamily (V := V) (H := H) (p := p) G ι)
    (hvisible : ∀ i, S.CoordinateVisible i) :
    ∃ a : ι → ℚ,
      (∀ i, a i ≠ 0) ∧
      S.toFiniteSpectralFamily.spectralCombination a ∈
        geometricProgramOrbitModule G p := by
  exact S.toFiniteSpectralFamily.exists_cyclic_seed_of_coordinatewise_visible
    (geometricProgramOrbitModule G p) hvisible

/-- **ORBIT SPECTRAL SATURATION.**
Every selected basis sheet lies in the graded geometric orbit itself. -/
theorem selected_basis_mem_orbit
    (S : GradedProgramSpectralFamily (V := V) (H := H) (p := p) G ι)
    (hvisible : ∀ i, S.CoordinateVisible i) :
    ∀ i : ι,
      (classicalHodgeBasis V H p (S.basisIndex i)).1 ∈
        geometricProgramOrbitModule G p := by
  obtain ⟨a, ha, hseed⟩ := S.exists_cyclic_orbit_seed hvisible
  exact S.toFiniteSpectralFamily.every_vector_mem_of_cyclic_seed
    (geometricProgramOrbitModule G p)
    S.program_orbit_stable a ha hseed

/-- Every selected basis sheet therefore has an actual native cycle
representative, but this is now a consequence of orbit membership rather than
an externally supplied basis-cycle bridge. -/
theorem selected_basis_has_native_cycle
    (S : GradedProgramSpectralFamily (V := V) (H := H) (p := p) G ι)
    (hvisible : ∀ i, S.CoordinateVisible i)
    (i : ι) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z =
        (classicalHodgeBasis V H p (S.basisIndex i)).1 := by
  have hrange :
      (classicalHodgeBasis V H p (S.basisIndex i)).1 ∈
        LinearMap.range (H.cycleClass p) :=
    (geometricProgramOrbitModule_le_cycleClass_range G p)
      (S.selected_basis_mem_orbit hvisible i)
  exact LinearMap.mem_range.mp hrange

end GradedProgramSpectralFamily

/-- Finite orbit-spectral cover for one concrete Hodge class.  A single
horizontal geometric program supplies the spectrum; only weak coordinatewise
visibility in the already-verified orbit is required. -/
structure FiniteGradedProgramSpectralCover
    (G : GeometricCycleClassSpine V H)
    (alpha : ClassicalHodgeFiber V H p) where
  rank : Nat
  spectral :
    GradedProgramSpectralFamily
      (V := V) (H := H) (p := p) G (Fin rank)
  covers_live_support :
    ∀ i : HodgeSupportIndex alpha,
      ∃ k : Fin rank, spectral.basisIndex k = i.1
  visible : ∀ k : Fin rank, spectral.CoordinateVisible k

namespace FiniteGradedProgramSpectralCover

variable {G : GeometricCycleClassSpine V H}
variable {alpha : ClassicalHodgeFiber V H p}

/-- Every live sheet of the requested class lies in the graded geometric
orbit. -/
theorem live_basis_mem_orbit
    (C : FiniteGradedProgramSpectralCover G alpha)
    (i : HodgeSupportIndex alpha) :
    (classicalHodgeBasis V H p i.1).1 ∈
      geometricProgramOrbitModule G p := by
  rcases C.covers_live_support i with ⟨k, hk⟩
  rw [← hk]
  exact C.spectral.selected_basis_mem_orbit C.visible k

/-- The whole concrete Hodge class lies in the graded geometric orbit by its
finite-support basis reconstruction. -/
theorem class_mem_orbit
    (C : FiniteGradedProgramSpectralCover G alpha) :
    alpha.1 ∈ geometricProgramOrbitModule G p := by
  rw [hodgeClass_eq_support_sum alpha]
  apply Submodule.sum_mem
  intro i hi
  exact (geometricProgramOrbitModule G p).smul_mem
    ((classicalHodgeBasis V H p).repr alpha i.1)
    (C.live_basis_mem_orbit i)

/-- **FINITE GRADED-PROGRAM SPECTRAL LANDING.**
The requested Hodge class has an exact native algebraic-cycle representative. -/
theorem exists_native_cycle
    (C : FiniteGradedProgramSpectralCover G alpha) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 := by
  have hrange :
      (alpha : ClassicalHodgeFiber V H p).1 ∈
        LinearMap.range (H.cycleClass p) :=
    (geometricProgramOrbitModule_le_cycleClass_range G p)
      C.class_mem_orbit
  exact LinearMap.mem_range.mp hrange

end FiniteGradedProgramSpectralCover

/-- Per-class finite graded-program spectral covers imply the full Stage-2G
Hodge statement. -/
theorem bigradedBettiHodge_of_finite_graded_program_spectral_covers
    (G : GeometricCycleClassSpine V H)
    (C : ∀ q : Nat,
      ∀ alpha : ClassicalHodgeFiber V H q,
        alpha ≠ 0 → Nonempty (FiniteGradedProgramSpectralCover G alpha)) :
    BigradedBettiHodgeStatement V H := by
  intro q x hx
  let alpha : ClassicalHodgeFiber V H q := ⟨x, hx⟩
  by_cases halpha : alpha = 0
  · have hx0 : x = 0 := congrArg Subtype.val halpha
    subst x
    exact ⟨0, by simp⟩
  · exact (Classical.choice (C q alpha halpha)).exists_native_cycle

#check GradedProgramSpectralFamily
#check GradedProgramSpectralFamily.program_orbit_stable
#check GradedProgramSpectralFamily.exists_cyclic_orbit_seed
#check GradedProgramSpectralFamily.selected_basis_mem_orbit
#check FiniteGradedProgramSpectralCover
#check FiniteGradedProgramSpectralCover.class_mem_orbit
#check FiniteGradedProgramSpectralCover.exists_native_cycle
#check bigradedBettiHodge_of_finite_graded_program_spectral_covers

#print axioms GradedProgramSpectralFamily.program_orbit_stable
#print axioms GradedProgramSpectralFamily.selected_basis_mem_orbit
#print axioms FiniteGradedProgramSpectralCover.exists_native_cycle
#print axioms bigradedBettiHodge_of_finite_graded_program_spectral_covers

end GSTClassicalHodgeGradedProgramSpectralSaturation