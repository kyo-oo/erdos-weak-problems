import GSTClassicalHodgeOmniverseLefschetzRayCompiler
import GSTClassicalHodgePrimitivePushforwardNaturality
import GSTClassicalHodgeProjectiveSelfCorrespondences
import GSTClassicalHodgeBasisCycleBridge

/-!
# GST CLASSICAL HODGE — PROJECTIVE APEX SPOKES

The omniverse ray compiler shows that the exact fixed-weight Hodge landing does
not need a projective code observable, an all-state matrix-unit realization, or
materialization of every downstream graph edge.

This file pushes that reduction into genuine projective geometry.

Fix one synchronized nonzero algebraic Hodge apex `S`.  For a target basis
sheet `j`, a projective apex spoke consists of ONE actual endomorphism of the
complex projective scheme together with the ordinary cycle-class pushforward
naturality square.  The only Hodge-specific equation is evaluated at the one
apex state:

  f_*^H (S.hodge)
    = localized-L^2_(S.sourceIndex -> j) (S.hodge).

No condition is imposed on the action of `f` on any other Hodge state.
Naturality turns the genuine native pushforward into a cycle-class operator
pair.  The two-slot GST identity rewrites the right-hand side as the universal
nonzero scalar times the selected live source coefficient times the target
basis vector.  Dividing the actual pushed-forward native apex cycle by that
scalar therefore constructs the target basis cycle.

Thus this route replaces the historical `ProjectiveTwoGenerator` burden
(two projective maps, including a code observable, both correct on the whole
Hodge fiber) by one source-specific projective map per spoke.

The graph of every such C-scheme endomorphism is independently a genuine closed
subscheme of `X x_C X`; no finiteness of that graph is required for the native
pushforward argument used here.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeOmniverseProjectiveApexSpokes

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgePrimitiveArsenalRationalization
open GSTClassicalHodgeTwoSlotLefschetzCollapse
open GSTClassicalHodgeOmniverseTwoSlotLefschetzBranch
open GSTClassicalHodgeOmniverseLefschetzRayCompiler
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeAnalytificationFunctoriality
open GSTClassicalHodgeProjectivePointTransport
open GSTClassicalHodgePrimitivePushforwardNaturality
open GSTClassicalHodgeProjectiveSelfCorrespondences

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The universal nonzero normalization carried by every apex spoke. -/
noncomputable def apexSpokeScalar
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) : ℚ :=
  twoSlotScalar * hodgeCoordinate S.sourceIndex S.hodge

/-- The apex normalization is nonzero because the selected source coordinate is
live and the universal two-slot Lefschetz coefficient is nonzero. -/
theorem apexSpokeScalar_ne_zero
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) :
    apexSpokeScalar S ≠ 0 := by
  apply mul_ne_zero twoSlotScalar_ne_zero
  simpa [hodgeCoordinate] using S.sourceCoefficient_ne_zero

/-- **ONE GENUINE PROJECTIVE APEX SPOKE.**

`map` is an actual endomorphism over `Spec C`.
`naturality` is the ordinary geometric pushforward/cycle-class square.
`source_action` asks for the localized two-slot `L^2` equation only at the
single synchronized apex state. -/
structure ProjectiveApexL2Spoke
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p) where
  map : ComplexSchemeEndomorphism V
  naturality : GeometricPushforwardNaturality V H p map.hom
  source_action :
    naturality.cohomologyPushforward S.hodge.1 =
      (liftFiniteHodgeOperator (pairBasisIndex S.sourceIndex j)
        (diagonalLefschetzQ 2 2) S.hodge).1

namespace ProjectiveApexL2Spoke

variable
  {S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)}
  {j : ClassicalHodgeBasisIndex V H p}

/-- The graph carried by a projective apex spoke is a genuine closed algebraic
self-correspondence carrier in the projective self-product. -/
theorem graph_isClosed
    (R : ProjectiveApexL2Spoke S j) :
    IsClosedImmersion (graph V R.map) := by
  infer_instance

/-- Ordinary pushforward naturality packages the projective map into a genuine
cycle/cohomology operator pair. -/
noncomputable def operatorPair
    (R : ProjectiveApexL2Spoke S j) :=
  R.naturality.operatorPair

/-- **PROJECTIVE SPOKE ACTION = SCALED TARGET BASIS.**
The actual geometric cohomology pushforward sends the one apex state to the
nonzero universal scalar times the requested basis sheet. -/
theorem operatorPair_on_apex
    (R : ProjectiveApexL2Spoke S j) :
    R.operatorPair.cohomologyOperator S.hodge.1 =
      apexSpokeScalar S • (classicalHodgeBasis V H p j).1 := by
  change R.naturality.cohomologyPushforward S.hodge.1 = _
  rw [R.source_action]
  have hL := LinearMap.congr_fun
    (localized_L2_eq_scaled_matrixUnit
      (V := V) (H := H) (p := p) S.sourceIndex j)
    S.hodge
  have hLval := congrArg Subtype.val hL
  rw [hLval]
  simp [apexSpokeScalar, hodgeMatrixUnit_apply, smul_smul, mul_assoc]

/-- Execute the actual native projective pushforward on the apex cycle and
normalize by the nonzero source/spoke scalar. -/
noncomputable def targetCycle
    (R : ProjectiveApexL2Spoke S j) : codimensionCycles V.X p :=
  (apexSpokeScalar S)⁻¹ • R.operatorPair.cycleOperator S.cycle

/-- **ONE PROJECTIVE SPOKE -> EXACT TARGET BASIS CYCLE.** -/
theorem targetCycle_spec
    (R : ProjectiveApexL2Spoke S j) :
    H.cycleClass p R.targetCycle =
      (classicalHodgeBasis V H p j).1 := by
  have hnat := R.operatorPair.cycleClass_cycleOperator S.cycle
  rw [S.class_eq, R.operatorPair_on_apex] at hnat
  unfold targetCycle
  rw [LinearMap.map_smul, hnat]
  simp [apexSpokeScalar_ne_zero, smul_smul]

end ProjectiveApexL2Spoke

/-- A family of genuine projective apex spokes supplies an explicit basis-cycle
bridge for the whole Hodge fiber. -/
noncomputable def projectiveApexBasisBridge
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      ProjectiveApexL2Spoke S j) :
    HodgeConjecture.HodgeBasisCycleBridge V H p where
  basisCycle j := (R j).targetCycle
  basisCycle_spec j := (R j).targetCycle_spec

/-- **PROJECTIVE APEX-FAN FIXED-WEIGHT LANDING.**
One synchronized algebraic apex plus one source-specific projective `L^2` spoke
to each target basis direction forces the entire rational Hodge weight into the
genuine cycle-class range.  No code primitive, no global Hodge action equation,
and no all-edge materialization is required. -/
theorem hodge_weight_of_projectiveApexL2Spokes
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      ProjectiveApexL2Spoke S j) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  intro alpha halpha
  exact HodgeConjecture.hodge_class_has_cycle_of_basis_bridge
    V H (projectiveApexBasisBridge S R) alpha halpha

#check apexSpokeScalar
#check apexSpokeScalar_ne_zero
#check ProjectiveApexL2Spoke
#check ProjectiveApexL2Spoke.graph_isClosed
#check ProjectiveApexL2Spoke.operatorPair
#check ProjectiveApexL2Spoke.operatorPair_on_apex
#check ProjectiveApexL2Spoke.targetCycle
#check ProjectiveApexL2Spoke.targetCycle_spec
#check projectiveApexBasisBridge
#check hodge_weight_of_projectiveApexL2Spokes

#print axioms ProjectiveApexL2Spoke.graph_isClosed
#print axioms ProjectiveApexL2Spoke.operatorPair_on_apex
#print axioms ProjectiveApexL2Spoke.targetCycle_spec
#print axioms hodge_weight_of_projectiveApexL2Spokes

end GSTClassicalHodgeOmniverseProjectiveApexSpokes
