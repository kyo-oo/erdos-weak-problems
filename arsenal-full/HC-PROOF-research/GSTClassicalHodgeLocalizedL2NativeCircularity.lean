import GSTClassicalHodgePlaneCompletenessLefschetzCrown
import GSTClassicalHodgeNativeGeneratorNaturality
import GSTClassicalHodgeVerticalRayMassFactorization

/-!
# GST CLASSICAL HODGE — LOCALIZED L² NATIVE-CLOSURE CIRCULARITY

The intrinsic GST calculation proves that bare localized two-slot `L^2` is a
nonzero universal scalar times the matrix unit.  Therefore a geometric
externalization theorem for every source-to-target localized `L^2` chart must
be audited carefully: once one algebraic live source is available, native
stability of those target-specific `L^2` operators already gives every Hodge
basis cycle.

Conversely, if the Hodge conclusion for the weight is already true, every such
localized `L^2` operator automatically has native point lifts because it
preserves the Hodge fiber.

Hence, with one nonzero algebraic source, the all-target localized-`L^2`
native-lift family is exactly equivalent to the Hodge conclusion.  It cannot
be used as the final unproved "geometric axiom".  A genuine proof must descend
below this family and construct the native action from geometry that does not
already encode all target sheets.
-/

set_option maxHeartbeats 160000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeLocalizedL2NativeCircularity

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgePrimitiveArsenalRationalization
open GSTClassicalHodgeTwoSlotLefschetzCollapse
open GSTClassicalHodgeOmniverseTwoSlotLefschetzBranch
open GSTClassicalHodgeNativeGeneratorNaturality
open GSTClassicalHodgePlaneCompletenessTheorem
open GSTClassicalHodgePlaneCompletenessLefschetzCrown
open GSTClassicalHodgeSynchronizedDefectOrbit

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Ambient extension of the one localized bare `L^2` operator attached to the
ordered pair `(i,j)`. -/
noncomputable def ambientLocalizedL2
    (i j : ClassicalHodgeBasisIndex V H p) :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p) :=
  GSTClassicalHodgeUniversalTwoSlotNativeClosure.extendHodgeEndomorphism
    (V := V) (H := H)
    (liftFiniteHodgeOperator (pairBasisIndex i j) (diagonalLefschetzQ 2 2))

/-- On the genuine Hodge fiber the ambient extension is exactly localized
`L^2`. -/
theorem ambientLocalizedL2_on_hodge
    (i j : ClassicalHodgeBasisIndex V H p)
    (alpha : ClassicalHodgeFiber V H p) :
    ambientLocalizedL2 i j alpha.1 =
      (liftFiniteHodgeOperator (pairBasisIndex i j)
        (diagonalLefschetzQ 2 2) alpha).1 := by
  exact GSTClassicalHodgeUniversalTwoSlotNativeClosure.extendHodgeEndomorphism_on_hodge
    (V := V) (H := H)
    (liftFiniteHodgeOperator (pairBasisIndex i j) (diagonalLefschetzQ 2 2)) alpha

/-- Hodge for the whole weight automatically gives native point lifts for one
localized `L^2` chart. -/
theorem localizedL2_nativePointLifts_of_hodge_weight
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (hHodge :
      rationalHodgeSubspace (H.hodgeBigrading p) ≤
        LinearMap.range (H.cycleClass p))
    (i j : ClassicalHodgeBasisIndex V H p) :
    HasNativePointLifts
      (p := p) (cl := H.cycleClass p) (ambientLocalizedL2 i j) := by
  intro x
  let a : ClassicalHodgeFiber V H p :=
    ⟨H.cycleClass p (codimensionPointCycle V.X p x),
      G.pointClass_is_hodge p x⟩
  have hEq :
      ambientLocalizedL2 i j a.1 =
        (liftFiniteHodgeOperator (pairBasisIndex i j)
          (diagonalLefschetzQ 2 2) a).1 :=
    ambientLocalizedL2_on_hodge i j a
  have hmem :
      ambientLocalizedL2 i j a.1 ∈
        rationalHodgeSubspace (H.hodgeBigrading p) := by
    rw [hEq]
    exact (liftFiniteHodgeOperator (pairBasisIndex i j)
      (diagonalLefschetzQ 2 2) a).2
  exact hHodge hmem

/-- A native point-lift law for one localized `L^2` chart makes that operator
preserve the genuine algebraic cycle-class range. -/
theorem localizedL2_rangeStable_of_nativePointLifts
    (i j : ClassicalHodgeBasisIndex V H p)
    (hL : HasNativePointLifts
      (p := p) (cl := H.cycleClass p) (ambientLocalizedL2 i j)) :
    ∀ x,
      x ∈ LinearMap.range (H.cycleClass p) →
      ambientLocalizedL2 i j x ∈ LinearMap.range (H.cycleClass p) := by
  rw [← GSTClassicalHodgeAtomicSpan.smoothProjective_cycleClass_range_eq_atomic_span
    V H p]
  exact (smoothProjective_atomicStable_iff_nativePointLifts
    (V := V) (H := H) (p := p) (ambientLocalizedL2 i j)).2 hL

/-- One fixed nonzero algebraic source plus native localized-`L^2` lifts from
its live coordinate to every target basis direction forces the complete Hodge
weight. -/
theorem hodge_weight_of_fixedSource_localizedL2_native
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (L : ∀ j : ClassicalHodgeBasisIndex V H p,
      HasNativePointLifts
        (p := p) (cl := H.cycleClass p)
        (ambientLocalizedL2 S.sourceIndex j)) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  have hsource : S.hodge.1 ∈ LinearMap.range (H.cycleClass p) :=
    ⟨S.cycle, S.class_eq⟩
  have hbasis : ∀ j : ClassicalHodgeBasisIndex V H p,
      (classicalHodgeBasis V H p j).1 ∈
        LinearMap.range (H.cycleClass p) := by
    intro j
    have hstable := localizedL2_rangeStable_of_nativePointLifts
      S.sourceIndex j (L j) S.hodge.1 hsource
    have hEq :
        ambientLocalizedL2 S.sourceIndex j S.hodge.1 =
          twoSlotScalar •
            (hodgeMatrixUnit S.sourceIndex j S.hodge).1 := by
      rw [ambientLocalizedL2_on_hodge]
      have h := LinearMap.congr_fun
        (localized_L2_eq_scaled_matrixUnit
          (V := V) (H := H) (p := p) S.sourceIndex j) S.hodge
      exact congrArg Subtype.val h
    rw [hEq, hodgeMatrixUnit_apply] at hstable
    let c : ℚ := twoSlotScalar * hodgeCoordinate S.sourceIndex S.hodge
    have hc : c ≠ 0 := mul_ne_zero twoSlotScalar_ne_zero
      (by simpa [hodgeCoordinate] using S.sourceCoefficient_ne_zero)
    have hscaled :
        c • (classicalHodgeBasis V H p j).1 ∈
          LinearMap.range (H.cycleClass p) := by
      simpa [c, smul_smul, mul_assoc] using hstable
    have hinv := (LinearMap.range (H.cycleClass p)).smul_mem c⁻¹ hscaled
    simpa [c, hc, smul_smul] using hinv
  intro alpha halpha
  let a : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  rw [show a =
      ∑ j ∈ ((classicalHodgeBasis V H p).repr a).support,
        ((classicalHodgeBasis V H p).repr a j) •
          classicalHodgeBasis V H p j by
    exact (classicalHodgeBasis V H p).sum_repr a]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
  apply Submodule.sum_mem
  intro j hj
  exact (LinearMap.range (H.cycleClass p)).smul_mem
    ((classicalHodgeBasis V H p).repr a j) (hbasis j)

/-- **EXACT LOCALIZED-L² FRONTIER.**
With one synchronized nonzero algebraic source fixed, the all-target family of
native localized-`L^2` point lifts is equivalent to the complete fixed-weight
Hodge conclusion. -/
theorem allTarget_localizedL2_native_iff_hodge_weight
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) :
    (∀ j : ClassicalHodgeBasisIndex V H p,
      HasNativePointLifts
        (p := p) (cl := H.cycleClass p)
        (ambientLocalizedL2 S.sourceIndex j)) ↔
      rationalHodgeSubspace (H.hodgeBigrading p) ≤
        LinearMap.range (H.cycleClass p) := by
  constructor
  · exact hodge_weight_of_fixedSource_localizedL2_native S
  · intro hHodge j
    exact localizedL2_nativePointLifts_of_hodge_weight
      G hHodge S.sourceIndex j

/-! ## Global native-plane completion: exact closure, no hidden premise -/

/-- A weight is genuinely dead when its rational Hodge sector contains only
zero.  This is stated elementwise so the completion theorem does not require
any auxiliary nontriviality instance or basis choice. -/
def HodgeWeightTrivial
    (H : HodgeBigradedBettiData V)
    (p : Nat) : Prop :=
  ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
    alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
      alpha = 0

/-- **EXACT NATIVE PLANE COMPLETION AT ONE WEIGHT.**

There are exactly two legitimate terminal cases.

* The rational Hodge sector is zero, so there is nothing to algebraize.
* Otherwise one synchronized nonzero native seed exists and every GST
  localized-L² target firing from its canonical live coordinate has a genuine
  native point lift.

No ghost package, plane-completeness hypothesis, target-cycle family, or
surjectivity premise occurs in this definition. -/
def NativePlaneCompletionAt
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) : Prop :=
  HodgeWeightTrivial H p ∨
    ∃ S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p),
      ∀ j : ClassicalHodgeBasisIndex V H p,
        HasNativePointLifts
          (p := p) (cl := H.cycleClass p)
          (ambientLocalizedL2 S.sourceIndex j)

/-- **FIXED-WEIGHT COMPLETION EXACTNESS.**

The terminal native-plane completion predicate is not a new assumption.  It is
exactly equivalent to the fixed-weight Hodge conclusion.

The forward direction uses the already-proved localized-L² saturation theorem.
For the reverse direction, a nontrivial Hodge sector plus Hodge surjectivity
itself supplies a synchronized nonzero native seed; localized-L² native lifts
then follow theoremically.  Hence there is no third hidden completion law below
this equivalence. -/
theorem nativePlaneCompletionAt_iff_hodge_weight
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H) :
    NativePlaneCompletionAt V H p ↔
      rationalHodgeSubspace (H.hodgeBigrading p) ≤
        LinearMap.range (H.cycleClass p) := by
  constructor
  · rintro (hzero | ⟨S, hL⟩)
    · intro alpha halpha
      have hz : alpha = 0 := hzero alpha halpha
      rw [hz]
      exact (LinearMap.range (H.cycleClass p)).zero_mem
    · exact
        (allTarget_localizedL2_native_iff_hodge_weight G S).1 hL
  · intro hHodge
    by_cases hzero : HodgeWeightTrivial H p
    · exact Or.inl hzero
    · have hex :
          ∃ alpha : RationalSingularCohomology H.analytification (2 * p),
            alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) ∧
              alpha ≠ 0 := by
        by_contra hno
        apply hzero
        intro alpha halpha
        by_contra hne
        exact hno ⟨alpha, halpha, hne⟩
      obtain ⟨alpha, halpha, halpha0⟩ := hex
      obtain ⟨Z, hZ⟩ := hHodge halpha
      let a : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
      have ha : a ≠ 0 := by
        intro ha0
        apply halpha0
        have hv :=
          congrArg (fun z : ClassicalHodgeFiber V H p => z.1) ha0
        simpa [a] using hv
      let S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p) := {
        cycle := Z
        hodge := a
        hodge_ne_zero := ha
        class_eq := by
          simpa [a] using hZ
      }
      refine Or.inr ⟨S, ?_⟩
      intro j
      exact localizedL2_nativePointLifts_of_hodge_weight
        G hHodge S.sourceIndex j

/-- Pi-wide terminal native-plane completion. -/
def NativePlaneCompletion
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) : Prop :=
  ∀ p : Nat, NativePlaneCompletionAt V H p

/-- **GLOBAL COMPLETION THEOREM.**

For the geometric cycle-class spine, the complete pi-wide native GST-plane
closure is equivalent to the exact Stage-2G Hodge statement.  Thus any future
"plane completion", "native L² closure", or all-target realization premise
strong enough to supply this predicate is conclusion-strength, not a lower
axiom. -/
theorem nativePlaneCompletion_iff_bigradedBettiHodge
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H) :
    NativePlaneCompletion V H ↔
      BigradedBettiHodgeStatement V H := by
  constructor
  · intro h p
    exact
      (nativePlaneCompletionAt_iff_hodge_weight
        (V := V) (H := H) (p := p) G).1 (h p)
  · intro h p
    exact
      (nativePlaneCompletionAt_iff_hodge_weight
        (V := V) (H := H) (p := p) G).2 (h p)

#check ambientLocalizedL2
#check ambientLocalizedL2_on_hodge
#check localizedL2_nativePointLifts_of_hodge_weight
#check localizedL2_rangeStable_of_nativePointLifts
#check hodge_weight_of_fixedSource_localizedL2_native
#check allTarget_localizedL2_native_iff_hodge_weight
#check HodgeWeightTrivial
#check NativePlaneCompletionAt
#check nativePlaneCompletionAt_iff_hodge_weight
#check NativePlaneCompletion
#check nativePlaneCompletion_iff_bigradedBettiHodge

#print axioms ambientLocalizedL2_on_hodge
#print axioms localizedL2_nativePointLifts_of_hodge_weight
#print axioms hodge_weight_of_fixedSource_localizedL2_native
#print axioms allTarget_localizedL2_native_iff_hodge_weight
#print axioms nativePlaneCompletionAt_iff_hodge_weight
#print axioms nativePlaneCompletion_iff_bigradedBettiHodge

end GSTClassicalHodgeLocalizedL2NativeCircularity
