import GSTClassicalHodgePointKernelCyclicCrown

/-!
# GST CLASSICAL HODGE — PROJECTOR-SEED LANDING

The cyclic seed need not lie exactly in the span of the selected Hodge sheets.
That condition is stronger than the spectral argument actually uses.

For constructive extraction it is enough to have one algebraic seed class s
such that, for every selected live sheet i, the Lagrange isolator satisfies

  P_i(T) s = c_i * basis_i

with c_i nonzero.

The seed may contain arbitrary additional ambient components; they only need
to be annihilated by the relevant isolator.  This is precisely the shape of
the GST world-code / sheet-projector theorems, which isolate one sector from a
larger state.

If T has a point-transition kernel, the preceding operator-lift theorem
constructs a native cycle operator realizing T.  Therefore the same isolator
polynomial can be applied to an actual native seed cycle.  Normalizing by c_i
produces an explicit native cycle for basis_i.  Recombining with the original
Hodge coefficients produces an exact native cycle for the Hodge class.

This removes the exact-selected-span requirement from the cyclic landing.
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

namespace GSTClassicalHodgeProjectorSeedLanding

/-- A concrete local projector certificate.  The seed is an explicit finite
point presentation, but its cohomology class is not required to live purely in
the selected Hodge span.  Only its isolated sheets are prescribed. -/
structure ProjectorSeedCertificate
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
  seedPresentation : FiniteCodimensionPresentation V.X p
  isolatedCoefficient : HodgeSupportIndex alpha → ℚ
  isolatedCoefficient_ne_zero : ∀ i, isolatedCoefficient i ≠ 0
  isolator_seed : ∀ i : HodgeSupportIndex alpha,
    let F := spectral.toFiniteSpectralFamily
    linearPolyEval spectral.observable (F.isolatorPolynomial i)
        (finitePointCycleClassMap p (H.cycleClass p) seedPresentation) =
      (isolatedCoefficient i * F.isolatorScale i) •
        (classicalHodgeBasis V H p i.1).1

namespace ProjectorSeedCertificate

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}
variable {alpha : ClassicalHodgeFiber V H p}

/-- Full native spectral operator manufactured from the generator transition
kernel. -/
noncomputable def nativeSpectral
    (C : ProjectorSeedCertificate V H p alpha) :
    SpectralCycleOperator V H p (HodgeSupportIndex alpha) :=
  C.spectral.toSpectralCycleOperatorViaPointKernel C.transitions

/-- Actual native seed cycle obtained from the finite point presentation. -/
noncomputable def seedCycle
    (C : ProjectorSeedCertificate V H p alpha) :
    codimensionCycles V.X p :=
  realizeFiniteCodimensionPresentation V.X p C.seedPresentation

/-- The class of the native seed is exactly its finite point-class sum. -/
theorem seedCycle_class
    (C : ProjectorSeedCertificate V H p alpha) :
    H.cycleClass p C.seedCycle =
      finitePointCycleClassMap p (H.cycleClass p) C.seedPresentation := by
  unfold seedCycle
  exact (finitePointCycleClassMap_eq_cycleClass_realize
    p (H.cycleClass p) C.seedPresentation).symm

/-- Native cycle extracted from the seed by the i-th spectral projector. -/
noncomputable def extractedLiveBasisCycle
    (C : ProjectorSeedCertificate V H p alpha)
    (i : HodgeSupportIndex alpha) :
    codimensionCycles V.X p :=
  let S := C.nativeSpectral
  let F := C.spectral.toFiniteSpectralFamily
  let c := C.isolatedCoefficient i * F.isolatorScale i
  c⁻¹ • S.cyclePolyEval (F.isolatorPolynomial i) C.seedCycle

/-- **PROJECTOR-SEED EXTRACTION.**  Even though the seed may contain ambient
components outside the selected Hodge span, its isolated native cycle has
cycle class exactly the selected Hodge basis direction. -/
theorem extractedLiveBasisCycle_spec
    (C : ProjectorSeedCertificate V H p alpha)
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
        (finitePointCycleClassMap p (H.cycleClass p) C.seedPresentation) = _
  rw [hproj, smul_smul]
  have hone : c⁻¹ * (C.isolatedCoefficient i * F.isolatorScale i) = (1 : ℚ) :=
    inv_mul_cancel₀ hc
  rw [hone, one_smul]

/-- Reassemble the original Hodge class from the projector-extracted native
basis cycles on its finite live support. -/
noncomputable def reconstructedCycle
    (C : ProjectorSeedCertificate V H p alpha) :
    codimensionCycles V.X p :=
  ∑ i : HodgeSupportIndex alpha,
    ((classicalHodgeBasis V H p).repr alpha i.1) •
      C.extractedLiveBasisCycle i

/-- Exact reconstruction of the original Hodge class. -/
theorem reconstructedCycle_spec
    (C : ProjectorSeedCertificate V H p alpha) :
    H.cycleClass p C.reconstructedCycle = alpha.1 := by
  unfold reconstructedCycle
  rw [map_sum]
  simp_rw [LinearMap.map_smul, C.extractedLiveBasisCycle_spec]
  exact (hodgeClass_eq_support_sum alpha).symm

/-- Direct native-cycle existential consequence. -/
theorem exists_native_cycle
    (C : ProjectorSeedCertificate V H p alpha) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 :=
  ⟨C.reconstructedCycle, C.reconstructedCycle_spec⟩

end ProjectorSeedCertificate

/-- **PROJECTOR-SEED HODGE CRITERION.**  It is enough that every individual
Hodge class admit one finite point seed whose GST/Lagrange spectral projectors
isolate all of its live sheets with nonzero coefficients. -/
theorem bigradedBettiHodge_of_projectorSeedCertificates
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hcert :
      ∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
        Nonempty (ProjectorSeedCertificate V H p alpha)) :
    BigradedBettiHodgeStatement V H := by
  intro p x hx
  let alpha : ClassicalHodgeFiber V H p := ⟨x, hx⟩
  exact (Classical.choice (hcert p alpha)).exists_native_cycle

#check ProjectorSeedCertificate
#check ProjectorSeedCertificate.nativeSpectral
#check ProjectorSeedCertificate.seedCycle
#check ProjectorSeedCertificate.seedCycle_class
#check ProjectorSeedCertificate.extractedLiveBasisCycle
#check ProjectorSeedCertificate.extractedLiveBasisCycle_spec
#check ProjectorSeedCertificate.reconstructedCycle
#check ProjectorSeedCertificate.reconstructedCycle_spec
#check ProjectorSeedCertificate.exists_native_cycle
#check bigradedBettiHodge_of_projectorSeedCertificates

#print axioms ProjectorSeedCertificate.extractedLiveBasisCycle_spec
#print axioms ProjectorSeedCertificate.reconstructedCycle_spec
#print axioms ProjectorSeedCertificate.exists_native_cycle
#print axioms bigradedBettiHodge_of_projectorSeedCertificates

end GSTClassicalHodgeProjectorSeedLanding
