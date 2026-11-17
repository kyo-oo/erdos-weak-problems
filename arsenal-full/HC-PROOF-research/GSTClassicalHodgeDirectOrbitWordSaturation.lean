import GSTClassicalHodgeGradedProgramSpectralSaturation
import GSTClassicalHodgeProjectiveTwoGeneratorExternalization
import GSTClassicalHodgeProjectiveWordOrbit

/-!
# GST CLASSICAL HODGE — DIRECT ORBIT WORD SATURATION

This layer continues the geometry-first Hodge cosmology after the intrinsic
`geometricProgramOrbitModule` construction.

The key point is that a projective live-source word is not merely an external
basis-cycle extractor.  The normalized spine is itself already a graded
program from the genuine codimension-zero geometric origin.  Therefore a
live-source projective word can be composed directly after that spine program,
and the inverse live coefficient can be absorbed by the graded program's
rational scalar constructor.

The result is one finite genuine geometry program

  geometric origin -> normalized spine source -> projective word -> basis sheet.

So every target Hodge basis sheet reached by a live-source projective word lies
in the intrinsic graded geometric orbit itself.  Finite-support reconstruction
then places every rational Hodge class in that orbit.  The final Stage-2G Hodge
statement follows through the already-proved orbit algebraicity theorem.

This removes the intermediate basis-cycle bridge and the finite spectral-cover
wrapper from this route: projective words now saturate the actual graded
geometry orbit directly.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open scoped BigOperators

namespace GSTClassicalHodgeDirectOrbitWordSaturation

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeLocalCyclicCriterion
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeProjectiveWordOrbit
open GSTClassicalHodgeProjectiveTwoGeneratorExternalization
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeGradedGeometricOrbitAlgebra
open GSTGeometricRealizationStage2D

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {q : Nat}

/-- Compile one live-source projective target word directly into a graded
program from the genuine codimension-zero geometric origin. -/
noncomputable def directTargetProgram
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (q : Nat)
    (j : ClassicalHodgeBasisIndex V H q)
    (R : ProjectiveWordLiveSourceTarget G (conservedSpineOrbitSeed G D q) j) :
    GradedGeometricProgram V 0 q :=
  let S := conservedSpineOrbitSeed G D q
  let c := (classicalHodgeBasis V H q).repr S.hodge S.sourceIndex
  .smul c⁻¹
    (.comp (normalizedSpineProgram V q) (.word R.word))

/-- Exact execution law for the compiled program: it reaches the requested
Hodge basis sheet, not merely a scalar multiple of it. -/
theorem directTargetProgram_cohomologyEval
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (q : Nat)
    (j : ClassicalHodgeBasisIndex V H q)
    (R : ProjectiveWordLiveSourceTarget G (conservedSpineOrbitSeed G D q) j) :
    (directTargetProgram G D q j R).cohomologyEval G
        (geometricOriginClass V H) =
      (classicalHodgeBasis V H q j).1 := by
  let S := conservedSpineOrbitSeed G D q
  let c := (classicalHodgeBasis V H q).repr S.hodge S.sourceIndex
  have hc : c ≠ 0 := by
    simpa [S, c] using S.sourceCoefficient_ne_zero
  change
    c⁻¹ •
      (R.word.operatorPair G).cohomologyOperator
        ((normalizedSpineProgram V q).cohomologyEval G
          (geometricOriginClass V H)) =
      (classicalHodgeBasis V H q j).1
  rw [normalizedSpineProgram_cohomologyEval]
  change
    c⁻¹ • (R.word.operatorPair G).cohomologyOperator S.hodge.1 =
      (classicalHodgeBasis V H q j).1
  rw [R.source_action]
  exact inv_smul_smul₀ hc _

/-- Every live-source projective target word therefore puts its requested
basis sheet in the one-program orbit set itself. -/
theorem basis_mem_geometricProgramOrbitSet
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (q : Nat)
    (j : ClassicalHodgeBasisIndex V H q)
    (R : ProjectiveWordLiveSourceTarget G (conservedSpineOrbitSeed G D q) j) :
    (classicalHodgeBasis V H q j).1 ∈ geometricProgramOrbitSet G q := by
  refine ⟨directTargetProgram G D q j R, ?_⟩
  exact (directTargetProgram_cohomologyEval G D q j R).symm

/-- The same basis sheet lies in the intrinsic rational orbit module. -/
theorem basis_mem_geometricProgramOrbitModule
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (q : Nat)
    (j : ClassicalHodgeBasisIndex V H q)
    (R : ProjectiveWordLiveSourceTarget G (conservedSpineOrbitSeed G D q) j) :
    (classicalHodgeBasis V H q j).1 ∈ geometricProgramOrbitModule G q := by
  change (classicalHodgeBasis V H q j).1 ∈ geometricProgramOrbitSet G q
  exact basis_mem_geometricProgramOrbitSet G D q j R

/-- **DIRECT ORBIT SATURATION.**
If every basis direction at every weight is reachable from the canonical live
spine source by a genuine projective word, then the intrinsic graded geometric
orbit is the whole rational Hodge sector. -/
theorem gradedGeometricOrbitModuleCyclic_of_projective_words
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (R : ∀ q : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H q,
        ProjectiveWordLiveSourceTarget G (conservedSpineOrbitSeed G D q) j) :
    GradedGeometricOrbitModuleCyclic G := by
  intro q alpha halpha
  let alphaH : ClassicalHodgeFiber V H q := ⟨alpha, halpha⟩
  rw [show alpha = alphaH.1 by rfl]
  rw [hodgeClass_eq_support_sum alphaH]
  apply Submodule.sum_mem
  intro i hi
  exact (geometricProgramOrbitModule G q).smul_mem
    ((classicalHodgeBasis V H q).repr alphaH i.1)
    (basis_mem_geometricProgramOrbitModule G D q i.1 (R q i.1))

/-- **PROJECTIVE-WORD GEOMETRY HODGE CROWN.**
The exact Stage-2G Hodge statement now follows through direct graded-orbit
saturation; no spectral-cover package and no separately assembled basis-cycle
bridge occurs in the proof. -/
theorem bigradedBettiHodge_of_direct_orbit_projective_words
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (R : ∀ q : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H q,
        ProjectiveWordLiveSourceTarget G (conservedSpineOrbitSeed G D q) j) :
    BigradedBettiHodgeStatement V H := by
  exact bigradedBettiHodge_of_gradedGeometricOrbitModuleCyclic G
    (gradedGeometricOrbitModuleCyclic_of_projective_words G D R)

/-- Elementwise native-cycle witness produced by the direct orbit route. -/
theorem every_hodge_class_has_native_cycle_of_direct_orbit_projective_words
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (R : ∀ q : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H q,
        ProjectiveWordLiveSourceTarget G (conservedSpineOrbitSeed G D q) j)
    (q : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading q)) :
    ∃ Z : codimensionCycles V.X q,
      H.cycleClass q Z = alpha := by
  rcases bigradedBettiHodge_of_direct_orbit_projective_words G D R q halpha with ⟨Z, hZ⟩
  exact ⟨Z, hZ⟩

/-- Native-mass form: the conserved spine charge is manufactured internally
from the native mass bridge before direct orbit saturation. -/
theorem bigradedBettiHodge_of_native_mass_direct_orbit_words
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (R : ∀ q : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H q,
        ProjectiveWordLiveSourceTarget G
          (conservedSpineOrbitSeed G (M.toConservedCharge G) q) j) :
    BigradedBettiHodgeStatement V H := by
  exact bigradedBettiHodge_of_direct_orbit_projective_words
    G (M.toConservedCharge G) R

#check directTargetProgram
#check directTargetProgram_cohomologyEval
#check basis_mem_geometricProgramOrbitSet
#check basis_mem_geometricProgramOrbitModule
#check gradedGeometricOrbitModuleCyclic_of_projective_words
#check bigradedBettiHodge_of_direct_orbit_projective_words
#check every_hodge_class_has_native_cycle_of_direct_orbit_projective_words
#check bigradedBettiHodge_of_native_mass_direct_orbit_words

#print axioms directTargetProgram_cohomologyEval
#print axioms gradedGeometricOrbitModuleCyclic_of_projective_words
#print axioms bigradedBettiHodge_of_direct_orbit_projective_words
#print axioms bigradedBettiHodge_of_native_mass_direct_orbit_words

end GSTClassicalHodgeDirectOrbitWordSaturation
