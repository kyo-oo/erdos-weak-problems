import Mathlib.Algebra.Module.Projective
import GSTClassicalHodgeConcreteRankFreeGeneration
import GSTClassicalHodgePointKernelOperatorLift
import GSTClassicalHodgeRankFreeArsenalIrreducibility
import GSTClassicalHodgeNativeArsenalRepresentation

/-!
# GST CLASSICAL HODGE — CANONICAL AMBIENT ARSENAL

The rank-free GST matrix units are intrinsically defined on the genuine
rational `(p,p)` Hodge fiber.  No extra spectral observable is required to
extend them to ambient rational cohomology: over `Q`, a linear map defined on
a subspace extends to the whole vector space.

This module performs that extension once and for all.  Every pair of genuine
Hodge basis indices `(i,j)` therefore determines an ambient cohomological
operator whose restriction to the Hodge subspace is exactly the GST matrix
unit `E_{i,j}`.

Combined with the point-kernel lift, a finite point transition law for this
canonical ambient extension automatically produces the complete native cycle
operator and the commuting cycle-class square.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgePointKernelOperatorLift
open GSTClassicalHodgeGeneratorwiseAtomicStability

namespace GSTClassicalHodgeCanonicalAmbientArsenal

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

abbrev Coh (H : HodgeBigradedBettiData V) (p : Nat) :
    Type _ :=
  RationalSingularCohomology H.analytification (2 * p)
abbrev HFiber (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) (p : Nat) :
    Type _ :=
  ClassicalHodgeFiber V H p

/-- Hodge-fiber matrix unit followed by the inclusion into ambient cohomology. -/
noncomputable def hodgeMatrixUnitIntoAmbient
    (i j : ClassicalHodgeBasisIndex V H p) :
    HFiber V H p →ₗ[ℚ] Coh H p :=
  (rationalHodgeSubspace (H.hodgeBigrading p)).subtype.comp
    (hodgeMatrixUnit i j)

/-- Extend one Hodge matrix unit to an ambient cohomological endomorphism. -/
noncomputable def ambientHodgeMatrixUnit
    (i j : ClassicalHodgeBasisIndex V H p) :
    Coh H p →ₗ[ℚ] Coh H p :=
  Classical.choose (LinearMap.exists_extend (hodgeMatrixUnitIntoAmbient (V:=V) (H:=H) i j))

/-- The ambient extension agrees exactly with the rank-free GST matrix unit on
all genuine Hodge classes. -/
theorem ambientHodgeMatrixUnit_on_hodge
    (i j : ClassicalHodgeBasisIndex V H p)
    (alpha : HFiber V H p) :
    ambientHodgeMatrixUnit (V:=V) (H:=H) i j alpha.1 =
      (hodgeMatrixUnit i j alpha).1 := by
  have h := Classical.choose_spec
    (LinearMap.exists_extend (hodgeMatrixUnitIntoAmbient (V:=V) (H:=H) i j))
  have hf := LinearMap.congr_fun h alpha
  exact hf

/-- Source basis maps exactly to the chosen target basis in ambient cohomology. -/
theorem ambientHodgeMatrixUnit_basis_source
    (i j : ClassicalHodgeBasisIndex V H p) :
    ambientHodgeMatrixUnit (V:=V) (H:=H) i j
        (classicalHodgeBasis V H p i).1 =
      (classicalHodgeBasis V H p j).1 := by
  rw [ambientHodgeMatrixUnit_on_hodge]
  simp

/-- Every other Hodge basis direction is killed. -/
theorem ambientHodgeMatrixUnit_basis_other
    (i j k : ClassicalHodgeBasisIndex V H p)
    (hki : k ≠ i) :
    ambientHodgeMatrixUnit (V:=V) (H:=H) i j
        (classicalHodgeBasis V H p k).1 = 0 := by
  rw [ambientHodgeMatrixUnit_on_hodge]
  have hik : i ≠ k := Ne.symm hki
  simp [hik]

/-- Point-transition kernel required only for the canonical ambient matrix
unit.  There is no separately supplied cohomological observable anymore. -/
abbrev AmbientMatrixUnitPointKernel
    (i j : ClassicalHodgeBasisIndex V H p) :=
  PointClassTransitionKernel
    (p := p) (cl := H.cycleClass p)
    (ambientHodgeMatrixUnit (V:=V) (H:=H) i j)

/-- A point kernel for the canonical ambient matrix unit automatically
manufactures the full native cycle operator and exact naturality square. -/
noncomputable def nativeMatrixUnitOperatorPair
    (i j : ClassicalHodgeBasisIndex V H p)
    (K : AmbientMatrixUnitPointKernel (V:=V) (H:=H) i j) :
    GSTClassicalHodgeCycleOperatorNaturality.CycleClassOperatorPair V H p :=
  K.toCycleClassOperatorPair

/-- The derived native operator acts as the exact target matrix unit on every
actual Hodge class after applying cycle class. -/
theorem nativeMatrixUnitOperatorPair_hodge_action
    (i j : ClassicalHodgeBasisIndex V H p)
    (K : AmbientMatrixUnitPointKernel (V:=V) (H:=H) i j)
    (Z : codimensionCycles V.X p)
    (alpha : HFiber V H p)
    (hZ : H.cycleClass p Z = alpha.1) :
    H.cycleClass p ((nativeMatrixUnitOperatorPair i j K).cycleOperator Z) =
      (hodgeMatrixUnit i j alpha).1 := by
  rw [GSTClassicalHodgeCycleOperatorNaturality.CycleClassOperatorPair.cycleClass_cycleOperator, hZ]
  exact ambientHodgeMatrixUnit_on_hodge i j alpha

/-- Canonical matrix-unit point kernels at every pair produce the full native
rank-free arsenal representation without supplying any ambient observable. -/
noncomputable def nativeArsenalRepresentationOfPointKernels
    (K : ∀ i j : ClassicalHodgeBasisIndex V H p,
      AmbientMatrixUnitPointKernel (V:=V) (H:=H) i j) :
    GSTClassicalHodgeNativeArsenalRepresentation.NativeArsenalRepresentation
      V H p where
  operator := fun i j => nativeMatrixUnitOperatorPair i j (K i j)
  hodge_action := by
    intro i j alpha
    exact ambientHodgeMatrixUnit_on_hodge i j alpha

#check hodgeMatrixUnitIntoAmbient
#check ambientHodgeMatrixUnit
#check ambientHodgeMatrixUnit_on_hodge
#check ambientHodgeMatrixUnit_basis_source
#check ambientHodgeMatrixUnit_basis_other
#check AmbientMatrixUnitPointKernel
#check nativeMatrixUnitOperatorPair
#check nativeArsenalRepresentationOfPointKernels

#print axioms ambientHodgeMatrixUnit_on_hodge
#print axioms ambientHodgeMatrixUnit_basis_source
#print axioms nativeMatrixUnitOperatorPair_hodge_action
#print axioms nativeArsenalRepresentationOfPointKernels

end GSTClassicalHodgeCanonicalAmbientArsenal
