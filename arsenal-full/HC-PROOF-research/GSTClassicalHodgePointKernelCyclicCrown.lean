import GSTClassicalHodgePointKernelOperatorLift
import GSTClassicalHodgeWeightedCyclicCriterion

/-!
# GST CLASSICAL HODGE — POINT-KERNEL CYCLIC CROWN

The preceding reductions allow the local constructive Hodge engine to be
stated entirely in finite generator-level data.

For one genuine rational `(p,p)` Hodge class alpha, it is enough to supply:

1. one raw rational spectral observable on the finitely many live basis
   directions of alpha, with distinct eigenvalues;
2. one finite point-transition kernel describing the observable on every
   genuine codimension-p point-cycle class;
3. one explicit finite codimension-p point presentation whose classical cycle
   class is a weighted combination of the live Hodge directions, with every
   live coefficient nonzero.

From (2), the point-kernel operator-lift theorem constructs the full native
cycle operator and commuting cycle-class square.  From (3), the finite
presentation realizes an actual native cyclic seed.  Lagrange spectral
extraction then constructs native cycles for every live basis direction and
reassembles the original Hodge class.

This is a completely generator-level certificate: no arbitrary-cycle operator,
no abstract atomic-span membership witness, and no separate basis-cycle family
is supplied.
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
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeLocalCyclicCriterion
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeConstructiveCyclicLanding
open GSTClassicalHodgeSpectralSeparatorCollision
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgeGeneratorwiseAtomicStability
open GSTClassicalHodgePointKernelOperatorLift

namespace GSTClassicalHodgePointKernelCyclicCrown

/-- Fully concrete local certificate for one genuine Hodge class. -/
structure PointKernelCyclicCertificate
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
  coefficient : HodgeSupportIndex alpha → ℚ
  coefficient_ne_zero : ∀ i, coefficient i ≠ 0
  seedPresentation : FiniteCodimensionPresentation V.X p
  seedClass_spec :
    finitePointCycleClassMap p (H.cycleClass p) seedPresentation =
      ∑ i : HodgeSupportIndex alpha,
        coefficient i • (classicalHodgeBasis V H p i.1).1

namespace PointKernelCyclicCertificate

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}
variable {alpha : ClassicalHodgeFiber V H p}

/-- The raw point-kernel spectral data manufacture the full native spectral
cycle operator. -/
noncomputable def nativeSpectral
    (C : PointKernelCyclicCertificate V H p alpha) :
    SpectralCycleOperator V H p (HodgeSupportIndex alpha) :=
  C.spectral.toSpectralCycleOperatorViaPointKernel C.transitions

/-- Realize the explicit finite point seed as one native codimension-p cycle. -/
noncomputable def seedCycle
    (C : PointKernelCyclicCertificate V H p alpha) :
    codimensionCycles V.X p :=
  realizeFiniteCodimensionPresentation V.X p C.seedPresentation

/-- Exact cycle-class formula for the realized seed. -/
theorem seedCycle_class
    (C : PointKernelCyclicCertificate V H p alpha) :
    H.cycleClass p C.seedCycle =
      ∑ i : HodgeSupportIndex alpha,
        C.coefficient i • (classicalHodgeBasis V H p i.1).1 := by
  unfold seedCycle
  rw [← finitePointCycleClassMap_eq_cycleClass_realize]
  exact C.seedClass_spec

/-- Convert the generator-level certificate to the existing constructive
local spectral realization. -/
noncomputable def toLocalCycleSpectralRealization
    (C : PointKernelCyclicCertificate V H p alpha) :
    LocalCycleSpectralRealization V H p alpha := by
  let S := C.nativeSpectral
  have hindex : S.basisIndex = HodgeSupportIndex.include := by
    exact C.spectral_basisIndex
  refine {
    spectral := S
    spectral_basisIndex := hindex
    seed := {
      cycle := C.seedCycle
      coefficient := C.coefficient
      coefficient_ne_zero := C.coefficient_ne_zero
      class_eq := ?_
    }
  }
  rw [hindex]
  exact C.seedCycle_class

/-- **LOCAL POINT-KERNEL LANDING.**  The certificate constructs an actual
native algebraic cycle with class equal to the original Hodge class. -/
theorem exists_native_cycle
    (C : PointKernelCyclicCertificate V H p alpha) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 :=
  C.toLocalCycleSpectralRealization.exists_native_cycle

/-- The same certificate produces an explicit finite point presentation of the
original Hodge class. -/
theorem exists_point_presentation
    (C : PointKernelCyclicCertificate V H p alpha) :
    ∃ φ : FiniteCodimensionPresentation V.X p,
      finitePointCycleClassMap p (H.cycleClass p) φ = alpha.1 := by
  let R := C.toLocalCycleSpectralRealization
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  refine ⟨R.reconstructedPresentation, ?_⟩
  rw [finitePointCycleClassMap_eq_cycleClass_realize]
  have hR : realizeFiniteCodimensionPresentation V.X p
      R.reconstructedPresentation = R.reconstructedCycle :=
    realize_presentationOfNativeCycle V.X p R.reconstructedCycle
  rw [hR]
  exact R.reconstructedCycle_spec

end PointKernelCyclicCertificate

/-- **GLOBAL POINT-KERNEL HODGE CRITERION.**
A generator-level cyclic certificate for each individual rational Hodge class
proves the complete Stage-2G statement. -/
theorem bigradedBettiHodge_of_pointKernelCyclicCertificates
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hcert :
      ∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
        Nonempty (PointKernelCyclicCertificate V H p alpha)) :
    BigradedBettiHodgeStatement V H := by
  intro p x hx
  let alpha : ClassicalHodgeFiber V H p := ⟨x, hx⟩
  exact (Classical.choice (hcert p alpha)).exists_native_cycle

/-- Constructive crown: the same finite certificates simultaneously produce
the Hodge statement, native algebraic cycles and explicit finite point
presentations. -/
theorem pointKernelCyclic_constructive_crown
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hcert :
      ∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
        Nonempty (PointKernelCyclicCertificate V H p alpha)) :
    BigradedBettiHodgeStatement V H
    ∧ (∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
      ∃ Z : codimensionCycles V.X p,
        H.cycleClass p Z = alpha.1)
    ∧ (∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
      ∃ φ : FiniteCodimensionPresentation V.X p,
        finitePointCycleClassMap p (H.cycleClass p) φ = alpha.1) := by
  refine ⟨bigradedBettiHodge_of_pointKernelCyclicCertificates V H hcert,
    ?_, ?_⟩
  · intro p alpha
    exact (Classical.choice (hcert p alpha)).exists_native_cycle
  · intro p alpha
    exact (Classical.choice (hcert p alpha)).exists_point_presentation

#check PointKernelCyclicCertificate
#check PointKernelCyclicCertificate.nativeSpectral
#check PointKernelCyclicCertificate.seedCycle
#check PointKernelCyclicCertificate.seedCycle_class
#check PointKernelCyclicCertificate.toLocalCycleSpectralRealization
#check PointKernelCyclicCertificate.exists_native_cycle
#check PointKernelCyclicCertificate.exists_point_presentation
#check bigradedBettiHodge_of_pointKernelCyclicCertificates
#check pointKernelCyclic_constructive_crown

#print axioms PointKernelCyclicCertificate.seedCycle_class
#print axioms PointKernelCyclicCertificate.toLocalCycleSpectralRealization
#print axioms PointKernelCyclicCertificate.exists_native_cycle
#print axioms PointKernelCyclicCertificate.exists_point_presentation
#print axioms bigradedBettiHodge_of_pointKernelCyclicCertificates
#print axioms pointKernelCyclic_constructive_crown

end GSTClassicalHodgePointKernelCyclicCrown
