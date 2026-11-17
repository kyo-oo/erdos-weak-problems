import GSTClassicalHodgeGlobalSheetCosmos
import GSTClassicalHodgeLimitlessSpinePropagation
import GSTClassicalHodgeSynchronizedDefectOrbit

/-!
# GST CLASSICAL HODGE — CANONICAL SPINE AS GLOBAL GST SOURCE

The global sheet cosmos becomes useful only once it is fed by a genuine
algebraic source.  The limitless spine already constructs exactly such a
source at every weight from the codimension-zero fundamental cycle and genuine
principal cuts.

This file lifts that canonical spine into the total `(weight,basis-sheet)` GST
cosmos.  Native mass supplies nonvanishing.  The chosen live basis coordinate
therefore becomes a nonzero global GST probe.  Every same-weight global matrix
unit then sends that one canonical algebraic source address to a nonzero scalar
multiple of an arbitrary target sheet.

This is pure GST orbit mathematics: no target algebraicity and no target
geometric realization is assumed here.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGSTSpineGlobalSource

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedTransferCompletion
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeGlobalSheetCosmos

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The canonical synchronized algebraic orbit seed in weight `p`, manufactured
from the genuine projective spine and the native-mass bridge. -/
noncomputable def globalSpineOrbitSeed
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (p : Nat) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := p) where
  cycle := spineNativeTower G p
  hodge := spineHodgeSeed G p
  hodge_ne_zero := M.spineHodgeSeed_ne_zero G p
  class_eq := spineNativeTower_cycleClass G p

/-- Total GST sheet address of the canonical spine Hodge state. -/
noncomputable def globalSpineAddress
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (p : Nat) :
    FiberedHodgeAddress V H :=
  fiberedWeightCoordinates V H p (globalSpineOrbitSeed G M p).hodge

/-- Selected live total sheet of the canonical spine source. -/
noncomputable def globalSpineSourceSheet
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (p : Nat) :
    FiberedHodgeIndex V H :=
  ⟨p, (globalSpineOrbitSeed G M p).sourceIndex⟩

/-- The selected global sheet probe is literally the selected basis
coefficient of the canonical spine seed. -/
theorem globalSpineSourceProbe_eq_coefficient
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (p : Nat) :
    sheetProbe (globalSpineSourceSheet G M p)
        (globalSpineAddress G M p) =
      (classicalHodgeBasis V H p).repr
        (globalSpineOrbitSeed G M p).hodge
        (globalSpineOrbitSeed G M p).sourceIndex := by
  simp only [sheetProbe_fiberedWeightCoordinates, globalSpineSourceSheet,
    globalSpineAddress]
  simp [hodgeCoordinate]

/-- **GLOBAL GST SOURCE NONVANISHING.**  Native mass and projective spine
conservation force the selected global GST coordinate to be nonzero in every
weight. -/
theorem globalSpineSourceProbe_ne_zero
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (p : Nat) :
    sheetProbe (globalSpineSourceSheet G M p)
        (globalSpineAddress G M p) ≠ 0 := by
  rw [globalSpineSourceProbe_eq_coefficient]
  exact (globalSpineOrbitSeed G M p).sourceCoefficient_ne_zero

/-- Exact global GST action from the canonical live source to any target sheet
at the same Hodge weight. -/
theorem globalSpine_matrixUnit_hits_target
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (p : Nat)
    (j : ClassicalHodgeBasisIndex V H p) :
    sheetMatrixUnit
        (globalSpineSourceSheet G M p)
        (⟨p,j⟩ : FiberedHodgeIndex V H)
        (globalSpineAddress G M p) =
      sheetProbe (globalSpineSourceSheet G M p)
          (globalSpineAddress G M p) •
        fiberedSheetGenerator V H ⟨p,j⟩ := by
  exact sheetMatrixUnit_apply _ _ _

/-- The target coefficient in the global GST hit is nonzero. -/
theorem globalSpine_matrixUnit_target_scalar_ne_zero
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (p : Nat)
    (j : ClassicalHodgeBasisIndex V H p) :
    ∃ c : ℚ, c ≠ 0 ∧
      sheetMatrixUnit
          (globalSpineSourceSheet G M p)
          (⟨p,j⟩ : FiberedHodgeIndex V H)
          (globalSpineAddress G M p) =
        c • fiberedSheetGenerator V H ⟨p,j⟩ := by
  refine ⟨sheetProbe (globalSpineSourceSheet G M p)
      (globalSpineAddress G M p), ?_, ?_⟩
  · exact globalSpineSourceProbe_ne_zero G M p
  · exact globalSpine_matrixUnit_hits_target G M p j

/-- The same global GST move is exactly the old rank-free Hodge matrix unit on
the synchronized canonical Hodge source. -/
theorem globalSpine_matrixUnit_intertwines_hodge
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (p : Nat)
    (j : ClassicalHodgeBasisIndex V H p) :
    sheetMatrixUnit
        (globalSpineSourceSheet G M p)
        (⟨p,j⟩ : FiberedHodgeIndex V H)
        (globalSpineAddress G M p) =
      fiberedWeightCoordinates V H p
        (hodgeMatrixUnit
          (globalSpineOrbitSeed G M p).sourceIndex j
          (globalSpineOrbitSeed G M p).hodge) := by
  exact sheetMatrixUnit_intertwines_hodgeMatrixUnit
    p (globalSpineOrbitSeed G M p).sourceIndex j
    (globalSpineOrbitSeed G M p).hodge

/-- Crown: one actual algebraic spine state, manufactured rather than assumed,
has a nonzero GST coordinate and the unrestricted global GST sheet algebra can
move that coordinate to every target sheet in its weight. -/
theorem global_spine_source_crown
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H) :
    ∀ p : Nat,
      sheetProbe (globalSpineSourceSheet G M p)
          (globalSpineAddress G M p) ≠ 0
      ∧ ∀ j : ClassicalHodgeBasisIndex V H p,
        ∃ c : ℚ, c ≠ 0 ∧
          sheetMatrixUnit
              (globalSpineSourceSheet G M p)
              (⟨p,j⟩ : FiberedHodgeIndex V H)
              (globalSpineAddress G M p) =
            c • fiberedSheetGenerator V H ⟨p,j⟩ := by
  intro p
  exact ⟨globalSpineSourceProbe_ne_zero G M p,
    globalSpine_matrixUnit_target_scalar_ne_zero G M p⟩

#check globalSpineOrbitSeed
#check globalSpineAddress
#check globalSpineSourceSheet
#check globalSpineSourceProbe_ne_zero
#check globalSpine_matrixUnit_hits_target
#check globalSpine_matrixUnit_target_scalar_ne_zero
#check globalSpine_matrixUnit_intertwines_hodge
#check global_spine_source_crown

#print axioms globalSpineSourceProbe_ne_zero
#print axioms globalSpine_matrixUnit_target_scalar_ne_zero
#print axioms global_spine_source_crown

end GSTClassicalHodgeGSTSpineGlobalSource
