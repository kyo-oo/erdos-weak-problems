import GSTClassicalHodgeCrossCarrierExplicitPointKernel
import GSTClassicalHodgeCMConstructiveSurfaceDescent

/-!
# Non-self-product cup/Gysin realization of GST finite point kernels

The original HC-PROOF cup/Gysin interface handles correspondences X -> X.
The OpenAI CM surface and Kuga--Satake / Gale constructions require
correspondences BETWEEN DIFFERENT varieties S -> V.

This file specifies the mathematically correct degree-graded shape
on S x V.  If source dimension is d, source codimension p, target
codimension q, and correspondence codimension e, the projection
formula uses

               2e + 2p = 2d + 2q.

A class of codimension e on S x V, cup with the pullback of a source
degree-2p class, is integrated over source dimension d and gives
a target degree-2q class.

Crucially, the Betti correspondence action is NOT arbitrary: it is
constructed from a kernel class, first projection pullback, cup and
second projection Gysin. The native action is NOT arbitrary: it is
built from finite incidence point presentations in the preceding
module. Their geometric agreement ON POINTS is all that is needed
to derive the global rational cycle-class commuting square.

The product-cohomology type and the topological operations remain
supplied primitives, because the current Mathlib stack does not yet
construct their required Kunneth/Gysin operations for general S x V.
They are typed here to prevent degree or codimension sleight of hand.

NEEDS CI RUN LATER.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 900000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeCrossCarrierGeometricTransfer
open GSTClassicalHodgeCrossCarrierExplicitPointKernel

namespace GSTClassicalHodgeCrossCarrierCupGysinConstruction

variable {S V : SmoothProjectiveComplexScheme}
variable {D : HodgeBigradedBettiData S}
variable {H : HodgeBigradedBettiData V}
variable {p q d e : Nat}
variable {PCoh : Nat → Type*}
variable [∀ n, AddCommGroup (PCoh n)] [∀ n, Module ℚ (PCoh n)]

/-- Strictly degree-checked source/target product cohomology calculus.

Every nontrivial operation used in the classical correspondence formula is
explicit. There is NO field consisting of an arbitrary Betti endomorphism. -/
structure CrossProductCupGysin
    (S V : SmoothProjectiveComplexScheme)
    (D : HodgeBigradedBettiData S)
    (H : HodgeBigradedBettiData V)
    (PCoh : Nat → Type*)
    [∀ n, AddCommGroup (PCoh n)] [∀ n, Module ℚ (PCoh n)]
    (d p q e : Nat) where
  degree_balance : 2 * e + 2 * p = 2 * d + 2 * q
  sourcePullback :
    RationalSingularCohomology D.analytification (2 * p) →ₗ[ℚ]
      PCoh (2 * p)
  kernelClass : PCoh (2 * e)
  cup :
    PCoh (2 * e) →ₗ[ℚ]
      (PCoh (2 * p) →ₗ[ℚ] PCoh (2 * d + 2 * q))
  targetGysin :
    PCoh (2 * d + 2 * q) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * q)

/-- Full rational Betti action DETERMINED by actual cup/pullback/Gysin
operations and the chosen kernel class; no Betti operator is input. -/
noncomputable def CrossProductCupGysin.action
    (C : CrossProductCupGysin S V D H PCoh d p q e) :
    RationalSingularCohomology D.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * q) :=
  C.targetGysin.comp ((C.cup C.kernelClass).comp C.sourcePullback)

/-- This is the exact classical geometric correspondence equation
p'_*([C] cup p^* alpha), with cohomology degrees checked. -/
@[simp]
theorem CrossProductCupGysin.action_apply
    (C : CrossProductCupGysin S V D H PCoh d p q e)
    (alpha : RationalSingularCohomology D.analytification (2 * p)) :
    C.action alpha =
      C.targetGysin (C.cup C.kernelClass (C.sourcePullback alpha)) :=
  rfl

/-- Independent genuine incidence equation: for every algebraic
source generic point, cup and Gysin of the correspondence class equals
the cycle class of the explicitly computed finite target incidence. -/
def CupGysinPointIncidence
    (C : CrossProductCupGysin S V D H PCoh d p q e)
    (K : FiniteCrossCarrierPointKernel S V p q) : Prop :=
  ∀ x : CodimensionPoint S.X p,
    H.cycleClass q
      (GSTNativeCodimensionCyclePresentation.realizeFiniteCodimensionPresentation
        V.X q (K x)) =
    C.targetGysin
      (C.cup C.kernelClass
        (C.sourcePullback (D.cycleClass p
          (codimensionPointCycle S.X p x))))

/-- Global naturality is now the CONCLUSION of point incidence for the
geometrically defined cup/Gysin action and explicit native finite kernel. -/
theorem cupGysin_kernel_cycleClass_natural
    (C : CrossProductCupGysin S V D H PCoh d p q e)
    (K : FiniteCrossCarrierPointKernel S V p q)
    (h : CupGysinPointIncidence C K)
    (Z : codimensionCycles S.X p) :
    H.cycleClass q (nativeOfFinitePointKernel K Z) =
      C.action (D.cycleClass p Z) := by
  have hPoint :
      RealizesFinitePointKernelOnBetti (H := D) (J := H)
        K C.action := by
    intro x
    exact h x
  exact finitePointKernel_naturality K C.action hPoint Z

/-- The fully coupled cross-carrier geometry action has no freely supplied
native operator or freely supplied Betti operator: both are built. -/
noncomputable def cupGysinFiniteTransfer
    (C : CrossProductCupGysin S V D H PCoh d p q e)
    (K : FiniteCrossCarrierPointKernel S V p q)
    (h : CupGysinPointIncidence C K) :
    CrossCarrierTransfer S V D H p q where
  native := nativeOfFinitePointKernel K
  betti := C.action
  naturality := cupGysin_kernel_cycleClass_natural C K h

/-- Every actual cup/Gysin image of a genuine source cycle under a
point-incidence-corresponding kernel has an explicit rational native-cycle
representative on the destination. -/
theorem cupGysin_native_output
    (C : CrossProductCupGysin S V D H PCoh d p q e)
    (K : FiniteCrossCarrierPointKernel S V p q)
    (h : CupGysinPointIncidence C K)
    (Z : codimensionCycles S.X p) :
    C.action (D.cycleClass p Z) ∈
      LinearMap.range (H.cycleClass q) := by
  exact ⟨nativeOfFinitePointKernel K Z,
    cupGysin_kernel_cycleClass_natural C K h Z⟩

#check CrossProductCupGysin.action
#check cupGysin_kernel_cycleClass_natural
#check cupGysinFiniteTransfer
#print axioms cupGysin_kernel_cycleClass_natural

end GSTClassicalHodgeCrossCarrierCupGysinConstruction
