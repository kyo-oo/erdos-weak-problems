import GSTClassicalHodgeGeometricSpineKernelReduction
import GSTClassicalHodgePointNormalForm

/-!
# GST CLASSICAL HODGE — POINT-REDUCED GEOMETRIC SPINE

The compact native-cycle normal form makes the whole-cycle Hodge-typing field
of the historical geometric spine redundant. It is enough to type genuine
codimension-point atoms; every native cycle is a finite rational combination
of those atoms, so submodule closure supplies Hodge type for every cycle.

Together with the earlier kernel reduction, this leaves only point-level
Hodge semantics and the genuine kernel laws as the non-packaging data.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgePointReducedGeometricSpine

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgeProjectivePointTransport
open GSTClassicalHodgeNativeOperatorCohomologyRealization
open GSTClassicalHodgeGeometricSpineKernelReduction
open GSTClassicalHodgeGeometricCycleClassSpine

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Point-level reduced geometric semantics. No whole-cycle Hodge field and no
cohomological operator pair is stored. -/
structure PointReducedGeometricCycleClassSpine where
  pointClass_is_hodge :
    ∀ p : Nat, ∀ x : CodimensionPoint V.X p,
      H.cycleClass p (codimensionPointCycle V.X p x) ∈
        rationalHodgeSubspace (H.hodgeBigrading p)
  pushforward_kernelStable :
    ∀ p : Nat, ∀ f : V.X ⟶ V.X,
      KernelStable (H := H) (smoothProjectiveNativePushforward V f p)
  principalCut : PrincipalCutKernelRealization (V := V) (H := H)

namespace PointReducedGeometricCycleClassSpine

/-- POINT NORMAL FORM UPGRADES POINT HODGE TYPE TO ALL NATIVE CYCLES. -/
theorem algebraic_is_hodge
    (R : PointReducedGeometricCycleClassSpine (V := V) (H := H))
    (p : Nat)
    (Z : codimensionCycles V.X p) :
    H.cycleClass p Z ∈ rationalHodgeSubspace (H.hodgeBigrading p) := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  let phi := presentationOfNativeCycle V.X p Z
  have hZ : realizeFiniteCodimensionPresentation V.X p phi = Z :=
    realize_presentationOfNativeCycle V.X p Z
  rw [← hZ]
  rw [linearMap_realizeFiniteCodimensionPresentation]
  apply Submodule.sum_mem
  intro x hx
  exact (rationalHodgeSubspace (H.hodgeBigrading p)).smul_mem
    (phi x) (R.pointClass_is_hodge p x)

/-- Manufacture the previous kernel-reduced spine. -/
noncomputable def toKernelReduced
    (R : PointReducedGeometricCycleClassSpine (V := V) (H := H)) :
    KernelReducedGeometricCycleClassSpine (V := V) (H := H) where
  algebraic_is_hodge := R.algebraic_is_hodge
  pushforward_kernelStable := R.pushforward_kernelStable
  principalCut := R.principalCut

/-- Manufacture the historical full geometric cycle-class spine. Every
operator pair and every whole-cycle Hodge law is now derived. -/
noncomputable def toGeometricCycleClassSpine
    (R : PointReducedGeometricCycleClassSpine (V := V) (H := H)) :
    GeometricCycleClassSpine V H :=
  R.toKernelReduced.toGeometricCycleClassSpine

/-- Exported point-class theorem agrees with the original spine interface. -/
theorem pointClass_is_hodge_export
    (R : PointReducedGeometricCycleClassSpine (V := V) (H := H))
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    H.cycleClass p (codimensionPointCycle V.X p x) ∈
      rationalHodgeSubspace (H.hodgeBigrading p) :=
  R.pointClass_is_hodge p x

#check PointReducedGeometricCycleClassSpine
#check PointReducedGeometricCycleClassSpine.algebraic_is_hodge
#check PointReducedGeometricCycleClassSpine.toKernelReduced
#check PointReducedGeometricCycleClassSpine.toGeometricCycleClassSpine

#print axioms PointReducedGeometricCycleClassSpine.algebraic_is_hodge
#print axioms PointReducedGeometricCycleClassSpine.toGeometricCycleClassSpine

end PointReducedGeometricCycleClassSpine
end GSTClassicalHodgePointReducedGeometricSpine
