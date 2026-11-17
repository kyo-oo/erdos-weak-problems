import GSTGraphV2CMNMCoupledUniverse
import GSTUniversalProjectiveProductPrimitive

/-!
# GST Graph V2: certified primitive CM–NM cycle channel

This is the TRUE primitive-property check for the new arithmetic/geometric
graph. It is intentionally not enough to simply label a CM–NM cycle
"primitive": geometric pushforwards need not commute with arbitrary ample
Lefschetz operators. We therefore require the two *actual input images*
to satisfy a supplied independently meaningful linear primitive test
(e.g. cup with L^(dim-2p+1) on the true Betti realization).

Under that exact geometric property, the CM–NM rational linear
combination automatically stays primitive, AND is a reachable
genuine native cycle in the combined original GST infinite graph.

The module also reuses the PREVIOUSLY KERNEL-VERIFIED unlimited-dimensional
codimension-two projective-product primitive coefficient theorem. It keeps
that separate algebraic cohomology-coordinate model distinct from a
new claimed actual Mathlib scheme intersection comparison.

No Hodge-surjectivity assumption or reverse Hodge-to-cycle arrow.
-/

set_option maxHeartbeats 50000000
noncomputable section

open AlgebraicGeometry

namespace GSTGraphV2CMNMPrimitiveLefschetzBridge

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeOmniversalConstructorGraph
open GSTClassicalHodgeProjectivePointTransport
open GSTGraphV2OmniversalCore
open GSTGraphV2ArithmeticOmniversalRealization
open GSTGraphV2CMNMPrimitiveUpgrade
open GSTGraphV2CMNMCoupledUniverse

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {W : Type*} [AddCommGroup W] [Module ℚ W]

/-- An actual graded cohomological primitive-test linear map (when
instantiated with a correctly typed ample Lefschetz cup power).
Unlike an abstract event, its application really tests cohomology. -/
theorem cmNMNativeGraphCycle_preserves_primitive_kernel
    (q : ℕ) (f g : V.X ⟶ V.X)
    (x y : GSTCMNumberManipulationTrace.CMQ) (m : ℕ)
    (Z : codimensionCycles V.X q)
    (L : RationalSingularCohomology H.analytification (2*q) →ₗ[ℚ] W)
    (hf : L (H.cycleClass q (smoothProjectiveNativePushforward V f q Z)) = 0)
    (hg : L (H.cycleClass q (smoothProjectiveNativePushforward V g q Z)) = 0) :
    L (H.cycleClass q (cmNMNativeGraphCycle q f g x y m Z)) = 0 := by
  rw [cmNMNativeGraphCycle_cycleClass]
  simp [map_add, map_smul, hf, hg]

/-- The genuine combined Graph V2 now constructs a new NATIVE cycle,
proves that it is in the desired primitive kernel, and certifies an
actual one-step event from its source at ANY physical arithmetic address. -/
theorem cmNMPrimitiveCycle_reachable_at_every_arithmetic_state
    (a : ArithmeticNode) (q : ℕ) (f g : V.X ⟶ V.X)
    (x y : GSTCMNumberManipulationTrace.CMQ) (m : ℕ)
    (Z : codimensionCycles V.X q)
    (L : RationalSingularCohomology H.analytification (2*q) →ₗ[ℚ] W)
    (hf : L (H.cycleClass q (smoothProjectiveNativePushforward V f q Z)) = 0)
    (hg : L (H.cycleClass q (smoothProjectiveNativePushforward V g q Z)) = 0) :
    OmniversalGraph.Reachable (coupledGraph (V := V) (H := H))
      ⟨a, .cycle q Z⟩
      ⟨a, .cycle q (cmNMNativeGraphCycle q f g x y m Z)⟩
      ∧ L (H.cycleClass q (cmNMNativeGraphCycle q f g x y m Z)) = 0 := by
  constructor
  · exact geometric_step_at_any_arithmetic_address (V := V) (H := H)
      a (CertifiedEvent.cmNM q f g x y m Z)
  · exact cmNMNativeGraphCycle_preserves_primitive_kernel
      q f g x y m Z L hf hg

/-- Existing universal p=2 product-cycle coefficient packet,
checked already by the independent exact Wolfram and Lean jobs.
This is a rational cohomology MODEL certificate, not an
unproved map from all X×P² scheme cycles. -/
def projectiveProductPrimitiveProfile (d : ℕ) :
    GSTUniversalProjectiveProductPrimitive.HodgeCodimTwo :=
  GSTUniversalProjectiveProductPrimitive.actualPrimitiveProductCycle d

/-- The imported universal primitive polynomial certificate is
unchanged by the CM–NM graph extension; it is valid at every d. -/
theorem projectiveProductPrimitiveProfile_exact (d : ℕ) :
    GSTUniversalProjectiveProductPrimitive.hyperplaneCupToNearTop d
      (projectiveProductPrimitiveProfile d) = (0,0) := by
  exact GSTUniversalProjectiveProductPrimitive.actualPrimitiveProductCycle_primitive d

#check cmNMNativeGraphCycle_preserves_primitive_kernel
#check cmNMPrimitiveCycle_reachable_at_every_arithmetic_state
#check projectiveProductPrimitiveProfile_exact

#print axioms cmNMNativeGraphCycle_preserves_primitive_kernel
#print axioms cmNMPrimitiveCycle_reachable_at_every_arithmetic_state
#print axioms projectiveProductPrimitiveProfile_exact

end GSTGraphV2CMNMPrimitiveLefschetzBridge
