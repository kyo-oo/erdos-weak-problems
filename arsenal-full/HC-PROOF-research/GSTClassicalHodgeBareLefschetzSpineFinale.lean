import GSTClassicalHodgeLocalSeedBareLefschetzExtinction
import GSTClassicalHodgeLimitlessSpinePropagation

/-!
# GST CLASSICAL HODGE — BARE LEFSCHETZ SPINE FINALE

This module removes the branch-packet realization law from the active Hodge
route.

The canonical geometric spine already supplies, in every weight, a native
cycle whose class is the recursively generated Hodge seed.  A conserved
geometric charge proves that seed nonzero.  Therefore a hypothetical minimal
separator ghost automatically receives the exact local algebraic source
required by the one-motion extinction theorem.

The only fixed-weight motion used below is the bare universal two-slot GST
`L^2` operator.  No branch-packet carrier, common-class plane, matrix-unit
correspondence, code observable, spectral projector, catenarity statement, or
successor exact-stratum premise is used.

Mathematical chain:

  conserved charge
    -> nonzero canonical spine seed at the minimal bad weight
    -> algebraic local source
    -> bare two-slot L^2 native point-lift
    -> minimal ghost contradiction
    -> Hodge.

A `NativeMassCycleClassBridge` manufactures the conserved charge, giving the
second crown below.

This is a genuine reduction theorem.  It does not claim the remaining bare
`L^2` native point-lift law or the native-mass bridge is already constructed.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeBareLefschetzSpineFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgeNativeGeneratorNaturality
open GSTClassicalHodgeUniversalTwoSlotNativeClosure
open GSTClassicalHodgeLocalSeedBareLefschetzExtinction
open GSTClassicalHodgeLimitlessSpinePropagation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The canonical spine seed is a local minimal-ghost source as soon as a
conserved charge proves it nonzero.  Algebraicity is already a theorem of the
spine construction itself. -/
noncomputable def spineMinimalGhostLocalSeed
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge (V := V) (H := H) G)
    (M : MinimalPrimitiveGhost G) :
    MinimalGhostLocalSeed G M :=
  localSeedOfNonzeroAlgebraic
    G M
    (spineHodgeSeed G M.weight)
    (spineHodgeSeed_algebraic G M.weight)
    (D.spineHodgeSeed_ne_zero M.weight)

/-- The source stored in the canonical local packet is genuinely nonzero. -/
theorem spineMinimalGhostLocalSeed_source_ne_zero
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge (V := V) (H := H) G)
    (M : MinimalPrimitiveGhost G) :
    (spineMinimalGhostLocalSeed G D M).source ≠ 0 := by
  exact D.spineHodgeSeed_ne_zero M.weight

/-- **MINIMAL GHOST EXTINCTION FROM THE SPINE AND ONE BARE L² MOTION.**

No positive-weight separator packet is required.  The canonical spine itself
provides the nonzero algebraic source at the minimal bad weight; the existing
two-slot collapse turns bare `L^2` into the detected rank-one transfer. -/
theorem minimalGhost_false_of_spine_bareLefschetz
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge (V := V) (H := H) G)
    (M : MinimalPrimitiveGhost G)
    (hL : HasNativePointLifts
      (p := M.weight) (cl := H.cycleClass M.weight)
      (ambientTwoStepLefschetz
        (spineMinimalGhostLocalSeed G D M).sourceIndex M.sheet)) :
    False :=
  minimalGhost_false_of_localSeed_bareLefschetz
    G M (spineMinimalGhostLocalSeed G D M) hL

/-- **BARE-LEFSCHETZ SPINE FINALE.**

A conserved charge plus native point-lift naturality of the one bare two-slot
`L^2` motion selected by each hypothetical minimal ghost proves the complete
Stage-2G Hodge statement.

This bypasses the branch-packet realization law D entirely. -/
theorem bigradedBettiHodge_of_conservedCharge_and_bareLefschetz
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge (V := V) (H := H) G)
    (hL : ∀ M : MinimalPrimitiveGhost G,
      HasNativePointLifts
        (p := M.weight) (cl := H.cycleClass M.weight)
        (ambientTwoStepLefschetz
          (spineMinimalGhostLocalSeed G D M).sourceIndex M.sheet)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let M : MinimalPrimitiveGhost G :=
    minimalPrimitiveGhostOfFailure G hnot
  exact minimalGhost_false_of_spine_bareLefschetz
    G D M (hL M)

/-! ## Exact circularity audit of the ghost-indexed closure

The preceding implication is a useful reduction, but its ghost-indexed
hypothesis must not be mistaken for an independent geometric axiom.  Under
Hodge there are no minimal primitive ghosts at all, because every such object
stores a basis separator.  Hence the hypothesis is vacuous in the Hodge world.
Combined with the extinction theorem above, it is exactly equivalent to the
Hodge conclusion.
-/

/-- Hodge makes the type of minimal primitive ghosts empty. -/
theorem isEmpty_minimalPrimitiveGhost_of_hodge
    (G : GeometricCycleClassSpine V H)
    (hHodge : BigradedBettiHodgeStatement V H) :
    IsEmpty (MinimalPrimitiveGhost G) := by
  refine ⟨?_⟩
  intro M
  have hnone :=
    (bigradedBettiHodgeStatement_iff_no_basis_separator V H).mp
      hHodge M.weight M.sheet
  exact isEmpty_iff.mp hnone M.separator

/-- The exact ghost-indexed bare-L² closure consumed by the spine finale. -/
def MinimalGhostBareL2Closure
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge (V := V) (H := H) G) : Prop :=
  ∀ M : MinimalPrimitiveGhost G,
    HasNativePointLifts
      (p := M.weight) (cl := H.cycleClass M.weight)
      (ambientTwoStepLefschetz
        (spineMinimalGhostLocalSeed G D M).sourceIndex M.sheet)

/-- **CIRCULARITY RECEIPT.**
With the conserved spine source fixed, ghost-indexed bare-L² closure is
equivalent to the complete Stage-2G Hodge statement.  It is therefore a
conclusion-normal-form reduction target, not a foundational construction law. -/
theorem minimalGhostBareL2Closure_iff_hodge
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge (V := V) (H := H) G) :
    MinimalGhostBareL2Closure G D ↔
      BigradedBettiHodgeStatement V H := by
  constructor
  · intro hL
    exact bigradedBettiHodge_of_conservedCharge_and_bareLefschetz
      G D hL
  · intro hHodge M
    exact (isEmpty_iff.mp
      (isEmpty_minimalPrimitiveGhost_of_hodge G hHodge) M).elim

/-- Uniform operator form: it is enough to know that every ordered two-sheet
bare `L^2` ambient operator has native point lifts.  The minimal-ghost theorem
then selects only the one pair it actually needs. -/
theorem bigradedBettiHodge_of_conservedCharge_and_uniformBareLefschetz
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge (V := V) (H := H) G)
    (hL : ∀ (p : Nat)
      (i j : ClassicalHodgeBasisIndex V H p),
      HasNativePointLifts
        (p := p) (cl := H.cycleClass p)
        (ambientTwoStepLefschetz i j)) :
    BigradedBettiHodgeStatement V H :=
  bigradedBettiHodge_of_conservedCharge_and_bareLefschetz
    G D (fun M => hL M.weight
      (spineMinimalGhostLocalSeed G D M).sourceIndex M.sheet)

/-- Native mass manufactures the conserved charge, so the entire spine side
can be discharged from the already-isolated three native-mass laws. -/
noncomputable def massSpineLocalSeed
    (G : GeometricCycleClassSpine V H)
    (N : NativeMassCycleClassBridge V H)
    (M : MinimalPrimitiveGhost G) :
    MinimalGhostLocalSeed G M :=
  spineMinimalGhostLocalSeed G (N.toConservedCharge G) M

/-- **NATIVE-MASS + BARE-L² FINALE.**

This is the smallest current non-branch-packet route in the repository:
native-mass conservation supplies a nonzero algebraic source in every possible
minimal bad weight, and one bare local `L^2` native motion kills the detected
sheet. -/
theorem bigradedBettiHodge_of_nativeMassBridge_and_bareLefschetz
    (G : GeometricCycleClassSpine V H)
    (N : NativeMassCycleClassBridge V H)
    (hL : ∀ M : MinimalPrimitiveGhost G,
      HasNativePointLifts
        (p := M.weight) (cl := H.cycleClass M.weight)
        (ambientTwoStepLefschetz
          (massSpineLocalSeed G N M).sourceIndex M.sheet)) :
    BigradedBettiHodgeStatement V H := by
  exact bigradedBettiHodge_of_conservedCharge_and_bareLefschetz
    G (N.toConservedCharge G) hL

/-- Uniform version of the native-mass finale. -/
theorem bigradedBettiHodge_of_nativeMassBridge_and_uniformBareLefschetz
    (G : GeometricCycleClassSpine V H)
    (N : NativeMassCycleClassBridge V H)
    (hL : ∀ (p : Nat)
      (i j : ClassicalHodgeBasisIndex V H p),
      HasNativePointLifts
        (p := p) (cl := H.cycleClass p)
        (ambientTwoStepLefschetz i j)) :
    BigradedBettiHodgeStatement V H :=
  bigradedBettiHodge_of_conservedCharge_and_uniformBareLefschetz
    G (N.toConservedCharge G) hL

#check isEmpty_minimalPrimitiveGhost_of_hodge
#check MinimalGhostBareL2Closure
#check minimalGhostBareL2Closure_iff_hodge

#print axioms isEmpty_minimalPrimitiveGhost_of_hodge
#print axioms minimalGhostBareL2Closure_iff_hodge

#check spineMinimalGhostLocalSeed
#check spineMinimalGhostLocalSeed_source_ne_zero
#check minimalGhost_false_of_spine_bareLefschetz
#check bigradedBettiHodge_of_conservedCharge_and_bareLefschetz
#check bigradedBettiHodge_of_conservedCharge_and_uniformBareLefschetz
#check massSpineLocalSeed
#check bigradedBettiHodge_of_nativeMassBridge_and_bareLefschetz
#check bigradedBettiHodge_of_nativeMassBridge_and_uniformBareLefschetz

#print axioms spineMinimalGhostLocalSeed
#print axioms minimalGhost_false_of_spine_bareLefschetz
#print axioms bigradedBettiHodge_of_conservedCharge_and_bareLefschetz
#print axioms bigradedBettiHodge_of_conservedCharge_and_uniformBareLefschetz
#print axioms massSpineLocalSeed
#print axioms bigradedBettiHodge_of_nativeMassBridge_and_bareLefschetz
#print axioms bigradedBettiHodge_of_nativeMassBridge_and_uniformBareLefschetz

end GSTClassicalHodgeBareLefschetzSpineFinale
