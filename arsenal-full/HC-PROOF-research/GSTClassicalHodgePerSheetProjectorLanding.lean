import GSTClassicalHodgeProjectorSeedLanding

/-!
# GST CLASSICAL HODGE — PER-SHEET PROJECTOR LANDING

A common cyclic seed is not necessary once the spectral observable has been
lifted to native cycles from a point-transition kernel.

For each live Hodge basis direction i we may choose a completely independent
finite point seed s_i.  It is enough that the i-th Lagrange isolator sends the
class of s_i to a nonzero scalar multiple of basis_i.

The same native spectral operator then extracts an actual native cycle for
basis_i from the corresponding native seed.  Since every individual Hodge
class has finite basis support, those independently extracted cycles can be
recombined with the original Hodge coefficients.

This matches the microscopic GST architecture closely: single-sheet
projectors and single-sheet witnesses may be constructed independently; no
simultaneous all-sheet seed or hyperplane-avoidance assembly is required.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeCyclicSpectralGeneration
open GSTClassicalHodgeLocalCyclicCriterion
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeSpectralSeparatorCollision
open GSTClassicalHodgeGeneratorwiseAtomicStability
open GSTClassicalHodgePointKernelOperatorLift

namespace GSTClassicalHodgePerSheetProjectorLanding

/-- Independent projector witness for each live Hodge sheet. -/
structure PerSheetProjectorCertificate
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) where
  spectral :
    RawClassicalHodgeSpectralObservable
      V H p (HodgeSupportIndex alpha)
  spectral_basisIndex :
    spectral.basisIndex = HodgeSupportIndex.include
  transitions : spectral.PointTransitionKernel
  seedPresentation :
    HodgeSupportIndex alpha → FiniteCodimensionPresentation V.X p
  isolatedCoefficient : HodgeSupportIndex alpha → ℚ
  isolatedCoefficient_ne_zero : ∀ i, isolatedCoefficient i ≠ 0
  isolator_seed : ∀ i : HodgeSupportIndex alpha,
    let F := spectral.toFiniteSpectralFamily
    linearPolyEval spectral.observable (F.isolatorPolynomial i)
        (finitePointCycleClassMap p (H.cycleClass p)
          (seedPresentation i)) =
      (isolatedCoefficient i * F.isolatorScale i) •
        (classicalHodgeBasis V H p i.1).1

namespace PerSheetProjectorCertificate

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}
variable {alpha : ClassicalHodgeFiber V H p}

/-- The unique native spectral operator shared by all independently chosen
sheet seeds. -/
noncomputable def nativeSpectral
    (C : PerSheetProjectorCertificate V H p alpha) :
    SpectralCycleOperator V H p (HodgeSupportIndex alpha) :=
  C.spectral.toSpectralCycleOperatorViaPointKernel C.transitions

/-- Native realization of the seed chosen for one sheet. -/
noncomputable def seedCycle
    (C : PerSheetProjectorCertificate V H p alpha)
    (i : HodgeSupportIndex alpha) :
    codimensionCycles V.X p :=
  realizeFiniteCodimensionPresentation V.X p (C.seedPresentation i)

@[simp]
theorem seedCycle_class
    (C : PerSheetProjectorCertificate V H p alpha)
    (i : HodgeSupportIndex alpha) :
    H.cycleClass p (C.seedCycle i) =
      finitePointCycleClassMap p (H.cycleClass p)
        (C.seedPresentation i) := by
  unfold seedCycle
  exact (finitePointCycleClassMap_eq_cycleClass_realize
    p (H.cycleClass p) (C.seedPresentation i)).symm

/-- Native cycle obtained by applying the i-th projector to the independent
seed chosen for i. -/
noncomputable def extractedLiveBasisCycle
    (C : PerSheetProjectorCertificate V H p alpha)
    (i : HodgeSupportIndex alpha) :
    codimensionCycles V.X p :=
  let S := C.nativeSpectral
  let F := C.spectral.toFiniteSpectralFamily
  let c := C.isolatedCoefficient i * F.isolatorScale i
  c⁻¹ • S.cyclePolyEval (F.isolatorPolynomial i) (C.seedCycle i)

/-- **INDEPENDENT-SHEET EXTRACTION.**  Each sheet's own finite point seed
produces an exact native algebraic cycle for that Hodge basis direction. -/
theorem extractedLiveBasisCycle_spec
    (C : PerSheetProjectorCertificate V H p alpha)
    (i : HodgeSupportIndex alpha) :
    H.cycleClass p (C.extractedLiveBasisCycle i) =
      (classicalHodgeBasis V H p i.1).1 := by
  let S := C.nativeSpectral
  let F := C.spectral.toFiniteSpectralFamily
  let c := C.isolatedCoefficient i * F.isolatorScale i
  have hc : c ≠ 0 :=
    mul_ne_zero (C.isolatedCoefficient_ne_zero i)
      (F.isolatorScale_ne_zero i)
  have hproj := C.isolator_seed i
  unfold extractedLiveBasisCycle
  rw [LinearMap.map_smul]
  rw [S.cycleClass_cyclePolyEval]
  rw [C.seedCycle_class]
  change c⁻¹ •
      linearPolyEval C.spectral.observable
        (F.isolatorPolynomial i)
        (finitePointCycleClassMap p (H.cycleClass p)
          (C.seedPresentation i)) = _
  rw [hproj, smul_smul]
  have hone : c⁻¹ * (C.isolatedCoefficient i * F.isolatorScale i) = (1 : ℚ) :=
    inv_mul_cancel₀ hc
  rw [hone, one_smul]

/-- Reassemble the original Hodge class from the independently extracted
native basis cycles. -/
noncomputable def reconstructedCycle
    (C : PerSheetProjectorCertificate V H p alpha) :
    codimensionCycles V.X p :=
  ∑ i : HodgeSupportIndex alpha,
    ((classicalHodgeBasis V H p).repr alpha i.1) •
      C.extractedLiveBasisCycle i

/-- Exact class reconstruction. -/
theorem reconstructedCycle_spec
    (C : PerSheetProjectorCertificate V H p alpha) :
    H.cycleClass p C.reconstructedCycle = alpha.1 := by
  unfold reconstructedCycle
  rw [map_sum]
  simp_rw [LinearMap.map_smul, C.extractedLiveBasisCycle_spec]
  exact (hodgeClass_eq_support_sum alpha).symm

/-- Direct native-cycle consequence. -/
theorem exists_native_cycle
    (C : PerSheetProjectorCertificate V H p alpha) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 :=
  ⟨C.reconstructedCycle, C.reconstructedCycle_spec⟩

end PerSheetProjectorCertificate

/-- **PER-SHEET PROJECTOR HODGE CRITERION.**  Independent single-sheet finite
point witnesses for every live basis direction of each Hodge class suffice for
the full Stage-2G statement. -/
theorem bigradedBettiHodge_of_perSheetProjectorCertificates
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hcert :
      ∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
        Nonempty (PerSheetProjectorCertificate V H p alpha)) :
    BigradedBettiHodgeStatement V H := by
  intro p x hx
  let alpha : ClassicalHodgeFiber V H p := ⟨x, hx⟩
  exact (Classical.choice (hcert p alpha)).exists_native_cycle

#check PerSheetProjectorCertificate
#check PerSheetProjectorCertificate.nativeSpectral
#check PerSheetProjectorCertificate.seedCycle
#check PerSheetProjectorCertificate.extractedLiveBasisCycle
#check PerSheetProjectorCertificate.extractedLiveBasisCycle_spec
#check PerSheetProjectorCertificate.reconstructedCycle
#check PerSheetProjectorCertificate.reconstructedCycle_spec
#check PerSheetProjectorCertificate.exists_native_cycle
#check bigradedBettiHodge_of_perSheetProjectorCertificates

#print axioms PerSheetProjectorCertificate.extractedLiveBasisCycle_spec
#print axioms PerSheetProjectorCertificate.reconstructedCycle_spec
#print axioms PerSheetProjectorCertificate.exists_native_cycle
#print axioms bigradedBettiHodge_of_perSheetProjectorCertificates

end GSTClassicalHodgePerSheetProjectorLanding
