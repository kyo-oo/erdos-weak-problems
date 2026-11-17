import GSTClassicalHodgePerSheetProjectorLanding

/-!
# GST CLASSICAL HODGE — MICROSCOPIC PROJECTOR CRITERION

The Stage-2G Hodge statement is already equivalent to eliminating the atomic
separator on every individual genuine Hodge basis sheet.  Therefore the
constructive certificate can be localized to exactly one sheet as well.

A microscopic certificate for one basis direction `(p,i)` consists of:

* one finite spectral chart `Fin N` containing that direction;
* a raw cohomological observable with distinct spectral labels on the chart;
* a generatorwise finite point-transition kernel for the observable;
* one explicit finite codimension-p point seed;
* one nonzero projector equation saying that the selected Lagrange isolator
  sends the seed class to a nonzero scalar multiple of basis_i.

The point kernel manufactures a native cycle operator.  Applying the selected
projector polynomial to the native seed and normalizing constructs an actual
native cycle whose class is basis_i.  Hence the microscopic separator on that
sheet is impossible.

If every classical Hodge basis sheet has such a certificate, the full
Stage-2G statement follows immediately from the existing single-sheet crown.
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
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeCyclicSpectralGeneration
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeSingleSheetCrown
open GSTClassicalHodgeSpectralSeparatorCollision
open GSTClassicalHodgeGeneratorwiseAtomicStability
open GSTClassicalHodgePointKernelOperatorLift

namespace GSTClassicalHodgeMicroscopicProjectorCriterion

/-- One finite projector certificate for one genuine classical Hodge basis
sheet. -/
structure BasisProjectorCertificate
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H p) where
  N : Nat
  slot : Fin N
  spectral : RawClassicalHodgeSpectralObservable V H p (Fin N)
  targets_basis : spectral.basisIndex slot = i
  transitions : spectral.PointTransitionKernel
  seedPresentation : FiniteCodimensionPresentation V.X p
  isolatedCoefficient : ℚ
  isolatedCoefficient_ne_zero : isolatedCoefficient ≠ 0
  isolator_seed :
    let F := spectral.toFiniteSpectralFamily
    linearPolyEval spectral.observable (F.isolatorPolynomial slot)
        (finitePointCycleClassMap p (H.cycleClass p) seedPresentation) =
      (isolatedCoefficient * F.isolatorScale slot) •
        (classicalHodgeBasis V H p i).1

namespace BasisProjectorCertificate

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}
variable {i : ClassicalHodgeBasisIndex V H p}

/-- Full native spectral operator generated from the point-transition kernel. -/
noncomputable def nativeSpectral
    (C : BasisProjectorCertificate V H p i) :
    SpectralCycleOperator V H p (Fin C.N) :=
  C.spectral.toSpectralCycleOperatorViaPointKernel C.transitions

/-- Actual native seed cycle. -/
noncomputable def seedCycle
    (C : BasisProjectorCertificate V H p i) :
    codimensionCycles V.X p :=
  realizeFiniteCodimensionPresentation V.X p C.seedPresentation

@[simp]
theorem seedCycle_class
    (C : BasisProjectorCertificate V H p i) :
    H.cycleClass p C.seedCycle =
      finitePointCycleClassMap p (H.cycleClass p) C.seedPresentation := by
  unfold seedCycle
  exact (finitePointCycleClassMap_eq_cycleClass_realize
    p (H.cycleClass p) C.seedPresentation).symm

/-- Native cycle obtained by applying the selected spectral projector to the
native seed and dividing by the nonzero projector scalar. -/
noncomputable def extractedBasisCycle
    (C : BasisProjectorCertificate V H p i) :
    codimensionCycles V.X p :=
  let S := C.nativeSpectral
  let F := C.spectral.toFiniteSpectralFamily
  let c := C.isolatedCoefficient * F.isolatorScale C.slot
  c⁻¹ • S.cyclePolyEval (F.isolatorPolynomial C.slot) C.seedCycle

/-- **MICROSCOPIC NATIVE EXTRACTION.** -/
theorem extractedBasisCycle_spec
    (C : BasisProjectorCertificate V H p i) :
    H.cycleClass p C.extractedBasisCycle =
      (classicalHodgeBasis V H p i).1 := by
  let S := C.nativeSpectral
  let F := C.spectral.toFiniteSpectralFamily
  let c := C.isolatedCoefficient * F.isolatorScale C.slot
  have hc : c ≠ 0 :=
    mul_ne_zero C.isolatedCoefficient_ne_zero
      (F.isolatorScale_ne_zero C.slot)
  have hproj := C.isolator_seed
  unfold extractedBasisCycle
  rw [LinearMap.map_smul]
  rw [S.cycleClass_cyclePolyEval]
  rw [C.seedCycle_class]
  change c⁻¹ •
      linearPolyEval C.spectral.observable
        (F.isolatorPolynomial C.slot)
        (finitePointCycleClassMap p (H.cycleClass p) C.seedPresentation) = _
  rw [hproj, smul_smul]
  have hone : c⁻¹ * (C.isolatedCoefficient * F.isolatorScale C.slot) = (1 : ℚ) :=
    inv_mul_cancel₀ hc
  rw [hone, one_smul]

/-- Every microscopic certificate places the selected basis sheet in the
actual atomic point-cycle span. -/
theorem basis_mem_atomicSpan
    (C : BasisProjectorCertificate V H p i) :
    (classicalHodgeBasis V H p i).1 ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
  exact ⟨C.extractedBasisCycle, C.extractedBasisCycle_spec⟩

/-- Therefore the single-sheet atomic separator is impossible. -/
theorem no_basis_separator
    (C : BasisProjectorCertificate V H p i) :
    IsEmpty (BasisAtomicSeparator V H p i) :=
  (basis_mem_atomicSpan_iff_no_separator V H p i).mp C.basis_mem_atomicSpan

end BasisProjectorCertificate

/-- **MICROSCOPIC PROJECTOR FORM OF THE CLASSICAL HODGE LANDING.**
A projector certificate for every individual genuine Hodge basis sheet closes
the complete Stage-2G statement. -/
theorem bigradedBettiHodge_of_basisProjectorCertificates
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hcert :
      ∀ p : Nat, ∀ i : ClassicalHodgeBasisIndex V H p,
        Nonempty (BasisProjectorCertificate V H p i)) :
    BigradedBettiHodgeStatement V H := by
  apply (bigradedBettiHodgeStatement_iff_no_basis_separator V H).mpr
  intro p i
  exact (Classical.choice (hcert p i)).no_basis_separator

/-- Constructive family form: the same microscopic certificates directly
produce one native codimension-p algebraic cycle for every genuine Hodge basis
sheet. -/
theorem basisProjectorCertificates_construct_basis_cycles
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hcert :
      ∀ p : Nat, ∀ i : ClassicalHodgeBasisIndex V H p,
        Nonempty (BasisProjectorCertificate V H p i)) :
    ∀ p : Nat, ∀ i : ClassicalHodgeBasisIndex V H p,
      ∃ Z : codimensionCycles V.X p,
        H.cycleClass p Z = (classicalHodgeBasis V H p i).1 := by
  intro p i
  let C := Classical.choice (hcert p i)
  exact ⟨C.extractedBasisCycle, C.extractedBasisCycle_spec⟩

#check BasisProjectorCertificate
#check BasisProjectorCertificate.nativeSpectral
#check BasisProjectorCertificate.seedCycle
#check BasisProjectorCertificate.extractedBasisCycle
#check BasisProjectorCertificate.extractedBasisCycle_spec
#check BasisProjectorCertificate.basis_mem_atomicSpan
#check BasisProjectorCertificate.no_basis_separator
#check bigradedBettiHodge_of_basisProjectorCertificates
#check basisProjectorCertificates_construct_basis_cycles

#print axioms BasisProjectorCertificate.extractedBasisCycle_spec
#print axioms BasisProjectorCertificate.basis_mem_atomicSpan
#print axioms BasisProjectorCertificate.no_basis_separator
#print axioms bigradedBettiHodge_of_basisProjectorCertificates
#print axioms basisProjectorCertificates_construct_basis_cycles

end GSTClassicalHodgeMicroscopicProjectorCriterion
