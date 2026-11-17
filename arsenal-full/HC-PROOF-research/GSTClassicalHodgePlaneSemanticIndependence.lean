import GSTClassicalHodgePlaneCompletenessUnboundedCrown
import GSTClassicalHodgeStage2GSemanticRigidity
import GSTClassicalHodgeLocalizedL2NativeCircularity
import GSTClassicalHodgeFullCorrespondenceGSTPlaneCompletion
import GSTClassicalHodgeOmniversalNativeOrbitSeparation
import GSTClassicalHodgeMinimalNativeGeometricCore
import GSTClassicalHodgeNativeExecutablePlane

/-!
# GST CLASSICAL HODGE — PLANE / GEOMETRIC SEMANTIC INDEPENDENCE

The intrinsic GST plane theorem is intentionally independent of the cycle-class
map.  That independence should be proved sharply, not merely stated.

Keep one Hodge bigrading and analytification fixed, and replace only the
Stage-2G cycle-class map by zero.  The resulting world has exactly the same
Hodge fibers and therefore exactly the same fixed-source GST plane calculus:
all sectors, all targets, normalized local `L^2`, exact finite collapse, and
the full unbounded higher-causal tower survive unchanged.

But any nonzero Hodge class makes the Hodge landing false in that same world.
Therefore no amount of intrinsic GST plane completeness alone can imply the
geometric Hodge statement for the unconstrained Stage-2G record.  Any
unconditional geometric proof must genuinely constrain/construct the
cycle-class semantics somewhere.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgePlaneSemanticIndependence

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgePlaneCompletenessUnboundedCrown
open GSTClassicalHodgeStage2GSemanticRigidity
open GSTClassicalHodgeOmniverseTwoSlotLefschetzBranch
open GSTClassicalHodgePrimitiveArsenalRationalization
open GSTClassicalHodgePiUnboundedOmniverseCrown
open GSTGraphV2OmniversalCore

variable {V : SmoothProjectiveComplexScheme}

/-- Transport a genuine Hodge-fiber state into the zero-cycle-class semantic
copy.  Analytification and Hodge bigrading are unchanged definitionally. -/
noncomputable def zeroCycleClassHodgeState
    (H : HodgeBigradedBettiData V)
    {p : Nat}
    (alpha : ClassicalHodgeFiber V H p) :
    ClassicalHodgeFiber V (zeroCycleClassData H) p :=
  ⟨alpha.1, alpha.2⟩

@[simp]
theorem zeroCycleClassHodgeState_val
    (H : HodgeBigradedBettiData V)
    {p : Nat}
    (alpha : ClassicalHodgeFiber V H p) :
    (zeroCycleClassHodgeState H alpha).1 = alpha.1 :=
  rfl

/-- Nonzeroness of a Hodge state is unchanged when only the cycle-class map is
erased. -/
theorem zeroCycleClassHodgeState_ne_zero
    (H : HodgeBigradedBettiData V)
    {p : Nat}
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    zeroCycleClassHodgeState H alpha ≠ 0 := by
  intro hzero
  apply halpha
  apply Subtype.ext
  exact congrArg Subtype.val hzero

/-- **ZERO-CYCLE WORLD STILL HAS FULL GST PLANE COMPLETENESS.**
All intrinsic omniverse data survive because the plane theorem depends on the
Hodge fiber and GST operators, not on cycle-class semantics. -/
theorem zeroCycleClass_full_GST_plane
    (H : HodgeBigradedBettiData V)
    {p : Nat}
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :=
  gst_plane_completeness_unbounded_via_universal_L2
    (V := V) (H := zeroCycleClassData H) (p := p)
    (zeroCycleClassHodgeState H alpha)
    (zeroCycleClassHodgeState_ne_zero H alpha halpha)

/-- **SHARP SEMANTIC INDEPENDENCE COUNTERMODEL.**
A nonzero rational Hodge state gives a single Stage-2G world in which the full
unbounded GST plane theorem is true while the geometric Hodge conclusion is
false. -/
theorem zeroCycleClass_plane_complete_and_hodge_false
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    (Nonempty
      { i : HodgeSupportIndex (zeroCycleClassHodgeState H alpha) //
        hodgeCoordinate i.1 (zeroCycleClassHodgeState H alpha) ≠ 0 })
    ∧ ¬ BigradedBettiHodgeStatement V (zeroCycleClassData H) := by
  constructor
  · obtain ⟨i, hi, _hevent, _hreach, _htower, _hL2, _hcollapse⟩ :=
      zeroCycleClass_full_GST_plane H alpha halpha
    exact ⟨⟨i, hi⟩⟩
  · exact not_bigradedBettiHodge_zeroCycleClass
      H p alpha.1 alpha.2 (by
        intro hzero
        apply halpha
        apply Subtype.ext
        exact hzero)

/-- **FULL PLANE / NATIVE-COMPLETION SEPARATION.**

The zero-cycle-class copy still has the complete intrinsic GST plane but fails
the exact native-plane completion predicate.  Because native completion was
proved equivalent to Stage-2G Hodge, this is the definitive obstruction: no
future strengthening of the intrinsic plane alone can manufacture the missing
native semantics. -/
theorem zeroCycleClass_plane_complete_and_nativeCompletion_false
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    (Nonempty
      { i : HodgeSupportIndex (zeroCycleClassHodgeState H alpha) //
        hodgeCoordinate i.1 (zeroCycleClassHodgeState H alpha) ≠ 0 })
      ∧
    ¬ GSTClassicalHodgeLocalizedL2NativeCircularity.NativePlaneCompletion
        V (zeroCycleClassData H) := by
  constructor
  · exact (zeroCycleClass_plane_complete_and_hodge_false H p alpha halpha).1
  · intro hcomplete
    have hHodge :
        BigradedBettiHodgeStatement V (zeroCycleClassData H) := by
      exact
        (GSTClassicalHodgeLocalizedL2NativeCircularity.nativePlaneCompletion_iff_bigradedBettiHodge
          (GSTClassicalHodgeGeometricCycleClassSpine.zeroCycleClassSpine H)).1
          hcomplete
    exact
      (not_bigradedBettiHodge_zeroCycleClass
        H p alpha.1 alpha.2 (by
          intro hzero
          apply halpha
          apply Subtype.ext
          exact hzero)) hHodge

/-- Consequently there is no universal implication from bare intrinsic plane
completeness to exact native-plane completion over the unconstrained Stage-2G
semantic record. -/
theorem no_bareStage2G_plane_to_nativeCompletion_implication
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    ¬ (∀ H' : HodgeBigradedBettiData V,
      (∀ q : Nat, ∀ a : ClassicalHodgeFiber V H' q,
        a ≠ 0 →
        Nonempty { i : HodgeSupportIndex a // hodgeCoordinate i.1 a ≠ 0 }) →
      GSTClassicalHodgeLocalizedL2NativeCircularity.NativePlaneCompletion
        V H') := by
  intro h
  let H0 := zeroCycleClassData H
  have hplane :
      ∀ q : Nat, ∀ a : ClassicalHodgeFiber V H0 q,
        a ≠ 0 →
        Nonempty { i : HodgeSupportIndex a // hodgeCoordinate i.1 a ≠ 0 } := by
    intro q a ha
    obtain ⟨i, hi, _hevent, _hreach, _htower, _hL2, _hcollapse⟩ :=
      gst_plane_completeness_unbounded_via_universal_L2
        (V := V) (H := H0) (p := q) a ha
    exact ⟨⟨i, hi⟩⟩
  have hcomplete := h H0 hplane
  exact
    (zeroCycleClass_plane_complete_and_nativeCompletion_false
      H p alpha halpha).2 hcomplete

/-- No universally quantified implication from intrinsic unbounded GST plane
completeness to Stage-2G Hodge can exist over the current unconstrained semantic
record.  The zero-cycle-class copy is the explicit witness. -/
theorem no_bareStage2G_plane_to_hodge_implication
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    ¬ (∀ H' : HodgeBigradedBettiData V,
      (∀ q : Nat, ∀ a : ClassicalHodgeFiber V H' q,
        a ≠ 0 →
        Nonempty { i : HodgeSupportIndex a // hodgeCoordinate i.1 a ≠ 0 }) →
      BigradedBettiHodgeStatement V H') := by
  intro h
  let H0 := zeroCycleClassData H
  have hplane :
      ∀ q : Nat, ∀ a : ClassicalHodgeFiber V H0 q,
        a ≠ 0 →
        Nonempty { i : HodgeSupportIndex a // hodgeCoordinate i.1 a ≠ 0 } := by
    intro q a ha
    obtain ⟨i, hi, _hevent, _hreach, _htower, _hL2, _hcollapse⟩ :=
      gst_plane_completeness_unbounded_via_universal_L2
        (V := V) (H := H0) (p := q) a ha
    exact ⟨⟨i, hi⟩⟩
  have hHodge := h H0 hplane
  exact (not_bigradedBettiHodge_zeroCycleClass
    H p alpha.1 alpha.2 (by
      intro hzero
      apply halpha
      apply Subtype.ext
      exact hzero)) hHodge

/-- **INTRINSIC / EXECUTABLE-PLANE SEPARATION.**
The zero-cycle semantic copy still satisfies the complete intrinsic GST plane,
but the executable full-correspondence plane is impossible as soon as the
Hodge fiber contains a nonzero state.  Hence the latter is genuine geometric
content and cannot be silently identified with the intrinsic plane theorem. -/
theorem zeroCycleClass_intrinsicPlane_but_not_fullCorrespondencePlane
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    (Nonempty
      { i : HodgeSupportIndex (zeroCycleClassHodgeState H alpha) //
        hodgeCoordinate i.1 (zeroCycleClassHodgeState H alpha) ≠ 0 })
      ∧
    ¬ GSTClassicalHodgeFullCorrespondenceGSTPlaneCompletion
        .FullCorrespondenceGSTPlaneCompleteness
          (GSTClassicalHodgeGeometricCycleClassSpine.zeroCycleClassSpine H) := by
  constructor
  · exact (zeroCycleClass_plane_complete_and_hodge_false H p alpha halpha).1
  · intro hplane
    have hHodge :
        BigradedBettiHodgeStatement V (zeroCycleClassData H) :=
      GSTClassicalHodgeFullCorrespondenceGSTPlaneCompletion
        .hodge_of_fullCorrespondenceGSTPlane
          (GSTClassicalHodgeGeometricCycleClassSpine.zeroCycleClassSpine H)
          hplane
    exact
      (not_bigradedBettiHodge_zeroCycleClass
        H p alpha.1 alpha.2 (by
          intro hzero
          apply halpha
          apply Subtype.ext
          exact hzero)) hHodge

/-- There is therefore no uniform theorem over the current Stage-2G semantic
record that upgrades intrinsic GST plane support to executable
full-correspondence plane completeness.  Such an upgrade must use genuinely
stronger geometric semantics than the bare record exposes. -/
theorem no_bareStage2G_intrinsic_to_fullCorrespondencePlane
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    ¬ (∀ H' : HodgeBigradedBettiData V,
      (∀ q : Nat, ∀ a : ClassicalHodgeFiber V H' q,
        a ≠ 0 →
        Nonempty { i : HodgeSupportIndex a //
          hodgeCoordinate i.1 a ≠ 0 }) →
      GSTClassicalHodgeFullCorrespondenceGSTPlaneCompletion
        .FullCorrespondenceGSTPlaneCompleteness
          (GSTClassicalHodgeGeometricCycleClassSpine.zeroCycleClassSpine H')) := by
  intro h
  let H0 := zeroCycleClassData H
  have hsupport :
      ∀ q : Nat, ∀ a : ClassicalHodgeFiber V H0 q,
        a ≠ 0 →
        Nonempty { i : HodgeSupportIndex a //
          hodgeCoordinate i.1 a ≠ 0 } := by
    intro q a ha
    obtain ⟨i, hi, _hevent, _hreach, _htower, _hL2, _hcollapse⟩ :=
      gst_plane_completeness_unbounded_via_universal_L2
        (V := V) (H := H0) (p := q) a ha
    exact ⟨⟨i, hi⟩⟩
  have hfull := h H0 hsupport
  exact
    (zeroCycleClass_intrinsicPlane_but_not_fullCorrespondencePlane
      H p alpha halpha).2 hfull

/-- **INTRINSIC PLANE / NO-GHOST-TOTALITY SEPARATION.**
Even the complete intrinsic unbounded GST plane does not force the old
native-orbit pairing-totality law.  On the zero-cycle semantic copy, pairing
totality would imply executable orbit cyclicity and therefore Hodge, contradicting
the explicit nonzero Hodge state. -/
theorem zeroCycleClass_intrinsicPlane_but_not_nativeOrbitPairingTotal
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    (Nonempty
      { i : HodgeSupportIndex (zeroCycleClassHodgeState H alpha) //
        hodgeCoordinate i.1 (zeroCycleClassHodgeState H alpha) ≠ 0 })
      ∧
    ¬ GSTClassicalHodgeOmniversalSeparatorGhostCrown
        .OmniversalNativeOrbitPairingTotal
          (GSTClassicalHodgeGeometricCycleClassSpine.zeroCycleClassSpine H) := by
  constructor
  · exact (zeroCycleClass_plane_complete_and_hodge_false H p alpha halpha).1
  · intro htotal
    have hHodge :
        BigradedBettiHodgeStatement V (zeroCycleClassData H) :=
      GSTClassicalHodgeOmniversalSeparatorGhostCrown
        .hodge_of_nativeOrbitPairingTotal
          (GSTClassicalHodgeGeometricCycleClassSpine.zeroCycleClassSpine H)
          htotal
    exact
      (not_bigradedBettiHodge_zeroCycleClass
        H p alpha.1 alpha.2 (by
          intro hzero
          apply halpha
          apply Subtype.ext
          exact hzero)) hHodge

/-- Likewise the executable geometric-program plane of the no-ghost route is
not a consequence of intrinsic plane completeness over the bare semantic
record. -/
theorem zeroCycleClass_intrinsicPlane_but_not_geometricProgramPlane
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    (Nonempty
      { i : HodgeSupportIndex (zeroCycleClassHodgeState H alpha) //
        hodgeCoordinate i.1 (zeroCycleClassHodgeState H alpha) ≠ 0 })
      ∧
    ¬ GSTClassicalHodgeOmniversalNativeOrbitSeparation
        .GeometricGSTPlaneCompleteness
          (GSTClassicalHodgeGeometricCycleClassSpine.zeroCycleClassSpine H) := by
  constructor
  · exact (zeroCycleClass_plane_complete_and_hodge_false H p alpha halpha).1
  · intro hplane
    have hHodge :
        BigradedBettiHodgeStatement V (zeroCycleClassData H) :=
      GSTClassicalHodgeOmniversalNativeOrbitSeparation
        .hodge_of_geometricGSTPlaneCompleteness
          (GSTClassicalHodgeGeometricCycleClassSpine.zeroCycleClassSpine H)
          hplane
    exact
      (not_bigradedBettiHodge_zeroCycleClass
        H p alpha.1 alpha.2 (by
          intro hzero
          apply halpha
          apply Subtype.ext
          exact hzero)) hHodge

/-- The zero-cycle semantic copy already satisfies the entire reduced native
background core.  Point classes are zero and hence Hodge; principal-cut kernel
stability is automatic because every target cycle class is zero.  Thus these
background laws do not contain the Hodge conclusion. -/
noncomputable def zeroCycleClassMinimalNativeCore
    (H : HodgeBigradedBettiData V) :
    GSTClassicalHodgeMinimalNativeGeometricCore.MinimalNativeGeometricCore
      (V := V) (H := zeroCycleClassData H) where
  pointClass_is_hodge := by
    intro p x
    change (0 :
      GSTGeometricRealizationStage2F.RationalSingularCohomology
        H.analytification (2 * p)) ∈
      rationalHodgeSubspace (H.hodgeBigrading p)
    exact Submodule.zero_mem _
  principalCut_kernelStable := by
    intro p Z hZ
    change (0 :
      GSTGeometricRealizationStage2F.RationalSingularCohomology
        H.analytification (2 * (p + 1))) = 0
    rfl

/-- A nonzero Hodge state therefore gives a model satisfying the reduced native
geometry core and the full intrinsic GST plane while the native executable
plane is false.  The executable plane, not the reduced background semantics,
is the conclusion-strength step. -/
theorem zeroCycleClass_reducedCore_intrinsicPlane_but_not_nativeExecutablePlane
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    Nonempty
      (GSTClassicalHodgeMinimalNativeGeometricCore.MinimalNativeGeometricCore
        (V := V) (H := zeroCycleClassData H))
    ∧
    (Nonempty
      { i : HodgeSupportIndex (zeroCycleClassHodgeState H alpha) //
        hodgeCoordinate i.1 (zeroCycleClassHodgeState H alpha) ≠ 0 })
    ∧
    ¬ GSTClassicalHodgeNativeExecutablePlane
        .NativeExecutableGSTPlaneCompleteness
          (V := V) (H := zeroCycleClassData H) := by
  refine ⟨⟨zeroCycleClassMinimalNativeCore H⟩,
    (zeroCycleClass_plane_complete_and_hodge_false H p alpha halpha).1, ?_⟩
  intro hplane
  have hHodge :
      BigradedBettiHodgeStatement V (zeroCycleClassData H) :=
    GSTClassicalHodgeNativeExecutablePlane
      .hodge_of_nativeExecutableGSTPlane hplane
  exact
    (not_bigradedBettiHodge_zeroCycleClass
      H p alpha.1 alpha.2 (by
        intro hzero
        apply halpha
        apply Subtype.ext
        exact hzero)) hHodge

/-- The reduced minimal native core by itself cannot uniformly manufacture the
native executable plane over Stage-2G data. -/
theorem no_reducedCore_to_nativeExecutablePlane_over_bareStage2G
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    ¬ (∀ H' : HodgeBigradedBettiData V,
      GSTClassicalHodgeMinimalNativeGeometricCore.MinimalNativeGeometricCore
        (V := V) (H := H') →
      GSTClassicalHodgeNativeExecutablePlane
        .NativeExecutableGSTPlaneCompleteness (V := V) (H := H')) := by
  intro h
  let H0 := zeroCycleClassData H
  let C :=
    zeroCycleClassMinimalNativeCore H
  have hplane := h H0 C
  exact
    (zeroCycleClass_reducedCore_intrinsicPlane_but_not_nativeExecutablePlane
      H p alpha halpha).2.2 hplane


#check zeroCycleClassHodgeState
#check zeroCycleClassHodgeState_ne_zero
#check zeroCycleClass_full_GST_plane
#check zeroCycleClass_plane_complete_and_hodge_false
#check zeroCycleClass_plane_complete_and_nativeCompletion_false
#check no_bareStage2G_plane_to_nativeCompletion_implication
#check no_bareStage2G_plane_to_hodge_implication
#check zeroCycleClass_intrinsicPlane_but_not_fullCorrespondencePlane
#check no_bareStage2G_intrinsic_to_fullCorrespondencePlane
#check zeroCycleClassMinimalNativeCore
#check zeroCycleClass_reducedCore_intrinsicPlane_but_not_nativeExecutablePlane
#check no_reducedCore_to_nativeExecutablePlane_over_bareStage2G
#check zeroCycleClass_intrinsicPlane_but_not_nativeOrbitPairingTotal
#check zeroCycleClass_intrinsicPlane_but_not_geometricProgramPlane

#print axioms zeroCycleClassHodgeState_ne_zero
#print axioms zeroCycleClass_full_GST_plane
#print axioms zeroCycleClass_plane_complete_and_hodge_false
#print axioms zeroCycleClass_plane_complete_and_nativeCompletion_false
#print axioms no_bareStage2G_plane_to_nativeCompletion_implication
#print axioms no_bareStage2G_plane_to_hodge_implication
#print axioms zeroCycleClass_intrinsicPlane_but_not_fullCorrespondencePlane
#print axioms no_bareStage2G_intrinsic_to_fullCorrespondencePlane
#print axioms zeroCycleClass_reducedCore_intrinsicPlane_but_not_nativeExecutablePlane
#print axioms no_reducedCore_to_nativeExecutablePlane_over_bareStage2G
#print axioms zeroCycleClass_intrinsicPlane_but_not_nativeOrbitPairingTotal
#print axioms zeroCycleClass_intrinsicPlane_but_not_geometricProgramPlane

end GSTClassicalHodgePlaneSemanticIndependence
