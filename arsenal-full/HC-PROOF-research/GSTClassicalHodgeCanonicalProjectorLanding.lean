import GSTClassicalHodgeZeroComplementSpectrum
import GSTClassicalHodgePointKernelOperatorLift

/-!
# GST CLASSICAL HODGE — CANONICAL PROJECTOR LANDING

The microscopic projector certificate can be stripped of all arbitrary
spectral data.  A finite Hodge-basis window canonically supplies:

* its rational spectrum;
* the zero-complement ambient observable;
* the augmented Lagrange projector `X * P_i(X)`;
* the exact nonzero normalization on the selected Hodge sheet.

Thus a local constructive certificate now consists only of genuinely
geometric/combinatorial information:

1. a point-transition kernel showing that the canonical observable is induced
   on native algebraic cycles;
2. one explicit finite codimension-p point-cycle seed;
3. the statement that the canonical augmented projector applied to that seed
   has a nonzero component on the selected genuine Hodge sheet.

Everything else is manufactured by the limitless spectral calculus.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeCyclicSpectralGeneration
open GSTClassicalHodgeSpectralSeparatorCollision
open GSTClassicalHodgeGeneratorwiseAtomicStability
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgePointKernelOperatorLift
open GSTClassicalHodgeCanonicalSpectralObservable
open GSTClassicalHodgeZeroComplementSpectrum

namespace GSTClassicalHodgeCanonicalProjectorLanding

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Fully canonical spectral certificate for one genuine Hodge basis sheet.
No observable, eigenvalue family, or projector polynomial is stored as data. -/
structure CanonicalProjectorCertificate
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H p) where
  window : FiniteHodgeBasisWindow V H p
  slot : Fin window.N
  targets_basis : window.basisIndex slot = i
  transitions :
    PointClassTransitionKernel
      (p := p) (cl := H.cycleClass p)
      window.zeroComplementObservable
  seedPresentation : FiniteCodimensionPresentation V.X p
  isolatedCoefficient : ℚ
  isolatedCoefficient_ne_zero : isolatedCoefficient ≠ 0
  augmented_projector_seed :
    linearPolyEval window.zeroComplementObservable
        (window.augmentedIsolatorPolynomial slot)
        (finitePointCycleClassMap p (H.cycleClass p) seedPresentation) =
      isolatedCoefficient • (classicalHodgeBasis V H p i).1

namespace CanonicalProjectorCertificate

/-- The canonical zero-complement raw spectral observable of the certificate. -/
noncomputable def rawSpectral
    {i : ClassicalHodgeBasisIndex V H p}
    (C : CanonicalProjectorCertificate V H p i) :
    RawClassicalHodgeSpectralObservable V H p (Fin C.window.N) :=
  C.window.toZeroComplementRawSpectralObservable

/-- Upgrade the point-transition law to a genuine native cycle operator. -/
noncomputable def nativeSpectral
    {i : ClassicalHodgeBasisIndex V H p}
    (C : CanonicalProjectorCertificate V H p i) :
    SpectralCycleOperator V H p (Fin C.window.N) :=
  C.rawSpectral.toSpectralCycleOperatorViaPointKernel C.transitions

/-- The finite point seed realized as an actual native codimension-p cycle. -/
noncomputable def seedCycle
    {i : ClassicalHodgeBasisIndex V H p}
    (C : CanonicalProjectorCertificate V H p i) :
    codimensionCycles V.X p :=
  realizeFiniteCodimensionPresentation V.X p C.seedPresentation

@[simp]
theorem seedCycle_class
    {i : ClassicalHodgeBasisIndex V H p}
    (C : CanonicalProjectorCertificate V H p i) :
    H.cycleClass p C.seedCycle =
      finitePointCycleClassMap p (H.cycleClass p) C.seedPresentation := by
  unfold seedCycle
  exact (finitePointCycleClassMap_eq_cycleClass_realize
    p (H.cycleClass p) C.seedPresentation).symm

/-- Native cycle produced by the canonical augmented projector. -/
noncomputable def extractedBasisCycle
    {i : ClassicalHodgeBasisIndex V H p}
    (C : CanonicalProjectorCertificate V H p i) :
    codimensionCycles V.X p :=
  C.isolatedCoefficient⁻¹ •
    C.nativeSpectral.cyclePolyEval
      (C.window.augmentedIsolatorPolynomial C.slot)
      C.seedCycle

/-- **CANONICAL PROJECTOR EXTRACTION.**
The cycle class of the extracted native cycle is exactly the targeted genuine
Hodge basis direction. -/
theorem extractedBasisCycle_spec
    {i : ClassicalHodgeBasisIndex V H p}
    (C : CanonicalProjectorCertificate V H p i) :
    H.cycleClass p C.extractedBasisCycle =
      (classicalHodgeBasis V H p i).1 := by
  unfold extractedBasisCycle
  rw [LinearMap.map_smul]
  rw [C.nativeSpectral.cycleClass_cyclePolyEval]
  rw [C.seedCycle_class]
  have hproj := C.augmented_projector_seed
  change C.isolatedCoefficient⁻¹ •
      linearPolyEval C.window.zeroComplementObservable
        (C.window.augmentedIsolatorPolynomial C.slot)
        (finitePointCycleClassMap p (H.cycleClass p) C.seedPresentation) = _
  rw [hproj]
  simp [C.isolatedCoefficient_ne_zero]

/-- The targeted basis direction lies in the actual native cycle-class range. -/
theorem basis_mem_cycleClass_range
    {i : ClassicalHodgeBasisIndex V H p}
    (C : CanonicalProjectorCertificate V H p i) :
    (classicalHodgeBasis V H p i).1 ∈ LinearMap.range (H.cycleClass p) :=
  ⟨C.extractedBasisCycle, C.extractedBasisCycle_spec⟩

/-- Explicit existential form. -/
theorem exists_native_basis_cycle
    {i : ClassicalHodgeBasisIndex V H p}
    (C : CanonicalProjectorCertificate V H p i) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = (classicalHodgeBasis V H p i).1 :=
  ⟨C.extractedBasisCycle, C.extractedBasisCycle_spec⟩

end CanonicalProjectorCertificate

/-- A canonical projector certificate at every genuine Hodge basis sheet
constructs every Hodge class by rank-free finite-support reconstruction. -/
theorem bigradedBettiHodge_of_canonicalProjectorCertificates
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hcert : ∀ p : Nat, ∀ i : ClassicalHodgeBasisIndex V H p,
      Nonempty (CanonicalProjectorCertificate V H p i)) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  let lift : ClassicalHodgeFiber V H p →ₗ[ℚ] codimensionCycles V.X p :=
    (classicalHodgeBasis V H p).constr ℚ
      (fun i => (Classical.choice (hcert p i)).extractedBasisCycle)
  refine ⟨lift alphaH, ?_⟩
  have hmaps :
      (H.cycleClass p).comp lift =
        (rationalHodgeSubspace (H.hodgeBigrading p)).subtype := by
    apply (classicalHodgeBasis V H p).ext
    intro i
    simp [lift,
      CanonicalProjectorCertificate.extractedBasisCycle_spec]
  change ((H.cycleClass p).comp lift) alphaH = alpha
  rw [hmaps]
  rfl

#check CanonicalProjectorCertificate
#check CanonicalProjectorCertificate.rawSpectral
#check CanonicalProjectorCertificate.nativeSpectral
#check CanonicalProjectorCertificate.extractedBasisCycle
#check CanonicalProjectorCertificate.extractedBasisCycle_spec
#check bigradedBettiHodge_of_canonicalProjectorCertificates

#print axioms CanonicalProjectorCertificate.extractedBasisCycle_spec
#print axioms CanonicalProjectorCertificate.exists_native_basis_cycle
#print axioms bigradedBettiHodge_of_canonicalProjectorCertificates

end GSTClassicalHodgeCanonicalProjectorLanding
