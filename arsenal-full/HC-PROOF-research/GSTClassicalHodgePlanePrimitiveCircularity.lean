import GSTClassicalHodgePlaneCompletenessTheorem
import GSTClassicalHodgeTwoGeneratorPointKernelSaturation
import GSTClassicalHodgeLimitlessSpinePropagation

/-!
# GST CLASSICAL HODGE — PRIMITIVE PLANE CIRCULARITY FIREWALL

The intrinsic GST plane is already complete by theorem.  A tempting next move
would be to declare native point-lift realizations of the two-slot GST
primitives as the missing "geometric plane axiom".  This file proves that such
a move is not logically innocent.

Once the genuine cycle-class spine is present, the fixed-weight Hodge
conclusion itself manufactures native point lifts for BOTH universal two-slot
primitives.  Indeed a genuine codimension-p point already has Hodge type; each
ambient two-slot primitive restricts to an endomorphism of the true Hodge
fiber; therefore Hodge surjectivity supplies a native cycle for its image.

Conversely, the existing two-generator saturation theorem says that a nonzero
algebraic seed plus these primitive point lifts proves the whole Hodge weight.
Hence, in every weight where the existing GST spine supplies the nonzero
algebraic seed, the all-pairs primitive-native package is EQUIVALENT to the
Hodge conclusion for that weight.

So these primitive realization packages may be useful as intermediate
certificates after an independent geometric construction, but they cannot be
silently promoted to axioms in an unconditional proof.  This closes the next
circularity loophole below common-class planes and strict correspondences.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePlanePrimitiveCircularity

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeUniversalTwoSlotNativeClosure
open GSTClassicalHodgeTwoGeneratorNativeArsenal
open GSTClassicalHodgeTwoGeneratorPointKernelSaturation
open GSTClassicalHodgeNativeGeneratorNaturality
open GSTClassicalHodgePrimitiveArsenalRationalization
open GSTClassicalHodgeLimitlessSpinePropagation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- **HODGE WEIGHT -> TWO-GENERATOR NATIVE REALIZATION.**

This is the converse direction that must be visible in any circularity audit.
If the entire rational Hodge weight is already in the genuine cycle-class
range, then the native point-lift fields of `TwoGeneratorNative` are theorems,
not extra information. -/
theorem twoGeneratorNative_of_hodge_weight
    (G : GeometricCycleClassSpine V H)
    (hHodge :
      rationalHodgeSubspace (H.hodgeBigrading p) ≤
        LinearMap.range (H.cycleClass p))
    (i j : ClassicalHodgeBasisIndex V H p) :
    TwoGeneratorNative (V := V) (H := H) i j := by
  refine {
    code := ?_
    lefschetz := ?_
  }
  · intro x
    let a : ClassicalHodgeFiber V H p :=
      ⟨H.cycleClass p (codimensionPointCycle V.X p x),
        G.pointClass_is_hodge p x⟩
    have heq :
        ambientTwoSlotCode i j a.1 =
          (twoSlotCodeHodge i j a).1 := by
      simpa [ambientTwoSlotCode] using
        (extendHodgeEndomorphism_on_hodge
          (V := V) (H := H) (twoSlotCodeHodge i j) a)
    have hout :
        ambientTwoSlotCode i j
            (H.cycleClass p (codimensionPointCycle V.X p x)) ∈
          rationalHodgeSubspace (H.hodgeBigrading p) := by
      change ambientTwoSlotCode i j a.1 ∈
        rationalHodgeSubspace (H.hodgeBigrading p)
      rw [heq]
      exact (twoSlotCodeHodge i j a).2
    exact hHodge hout
  · intro x
    let a : ClassicalHodgeFiber V H p :=
      ⟨H.cycleClass p (codimensionPointCycle V.X p x),
        G.pointClass_is_hodge p x⟩
    let T : Module.End ℚ (ClassicalHodgeFiber V H p) :=
      twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2)
    have heq :
        ambientTwoStepLefschetz i j a.1 = (T a).1 := by
      simpa [ambientTwoStepLefschetz, T] using
        (extendHodgeEndomorphism_on_hodge
          (V := V) (H := H) T a)
    have hout :
        ambientTwoStepLefschetz i j
            (H.cycleClass p (codimensionPointCycle V.X p x)) ∈
          rationalHodgeSubspace (H.hodgeBigrading p) := by
      change ambientTwoStepLefschetz i j a.1 ∈
        rationalHodgeSubspace (H.hodgeBigrading p)
      rw [heq]
      exact (T a).2
    exact hHodge hout

/-- All ordered two-slot charts acquire their native primitive realizations as
a theorem once the fixed-weight Hodge conclusion is known. -/
theorem allTwoGeneratorNative_of_hodge_weight
    (G : GeometricCycleClassSpine V H)
    (hHodge :
      rationalHodgeSubspace (H.hodgeBigrading p) ≤
        LinearMap.range (H.cycleClass p)) :
    ∀ i j : ClassicalHodgeBasisIndex V H p,
      TwoGeneratorNative (V := V) (H := H) i j := by
  intro i j
  exact twoGeneratorNative_of_hodge_weight G hHodge i j

/-- **EXACT FIXED-WEIGHT STATUS WITH ONE ALGEBRAIC SEED.**

When a nonzero algebraic Hodge seed already exists, the family of native
realizations of the two universal GST primitives is equivalent to Hodge for
that weight.  Therefore this family cannot be treated as a lower axiom. -/
theorem allTwoGeneratorNative_iff_hodge_weight_of_seed
    (G : GeometricCycleClassSpine V H)
    (hseed : AlgebraicHodgeSubspace V H p ≠ ⊥) :
    (∀ i j : ClassicalHodgeBasisIndex V H p,
      TwoGeneratorNative (V := V) (H := H) i j) ↔
      rationalHodgeSubspace (H.hodgeBigrading p) ≤
        LinearMap.range (H.cycleClass p) := by
  constructor
  · intro R
    exact hodge_weight_of_twoGeneratorNative hseed R
  · intro hHodge i j
    exact twoGeneratorNative_of_hodge_weight G hHodge i j

/-- The repository's conserved GST spine already supplies the nonzero algebraic
seed.  Under that internal source theorem, all-pairs two-generator native
realization and the fixed-weight Hodge conclusion are exactly equivalent. -/
theorem allTwoGeneratorNative_iff_hodge_weight_of_conservedSpine
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G) :
    (∀ i j : ClassicalHodgeBasisIndex V H p,
      TwoGeneratorNative (V := V) (H := H) i j) ↔
      rationalHodgeSubspace (H.hodgeBigrading p) ≤
        LinearMap.range (H.cycleClass p) := by
  exact allTwoGeneratorNative_iff_hodge_weight_of_seed G
    (D.algebraicHodgeSubspace_ne_bot p)

/-- Choice-free native lift data can be converted into the explicit chosen
point-transition object used by the point-kernel saturation theorem. -/
noncomputable def nativePointTransitionOfLifts
    {T : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p)}
    (hT : HasNativePointLifts
      (p := p) (cl := H.cycleClass p) T) :
    NativePointTransition (p := p) (cl := H.cycleClass p) T where
  imageCycle x := Classical.choose (hT x)
  imageCycle_spec x := Classical.choose_spec (hT x)

/-- Hodge therefore manufactures the explicit point-transition package for the
two primitive GST operators as well. -/
noncomputable def twoPrimitivePointTransitionsOfHodgeWeight
    (G : GeometricCycleClassSpine V H)
    (hHodge :
      rationalHodgeSubspace (H.hodgeBigrading p) ≤
        LinearMap.range (H.cycleClass p))
    (i j : ClassicalHodgeBasisIndex V H p) :
    TwoPrimitivePointTransitions (V := V) (H := H) i j := by
  let R := twoGeneratorNative_of_hodge_weight G hHodge i j
  exact {
    code := nativePointTransitionOfLifts R.code
    lefschetz := nativePointTransitionOfLifts R.lefschetz
  }

/-- **EXPLICIT POINT-KERNEL PACKAGE EXACT STATUS.**

With one nonzero algebraic seed, even the fully chosen pair of point-transition
kernels for every ordered chart is equivalent, up to `Nonempty`, to the Hodge
conclusion for the weight.  This prevents replacing a circular plane axiom by
an equally circular chosen-transition axiom. -/
theorem allTwoPrimitivePointTransitions_iff_hodge_weight_of_seed
    (G : GeometricCycleClassSpine V H)
    (hseed : AlgebraicHodgeSubspace V H p ≠ ⊥) :
    (∀ i j : ClassicalHodgeBasisIndex V H p,
      Nonempty (TwoPrimitivePointTransitions (V := V) (H := H) i j)) ↔
      rationalHodgeSubspace (H.hodgeBigrading p) ≤
        LinearMap.range (H.cycleClass p) := by
  constructor
  · intro K
    apply hodge_weight_of_two_primitive_point_transitions hseed
    intro i j
    exact Classical.choice (K i j)
  · intro hHodge i j
    exact ⟨twoPrimitivePointTransitionsOfHodgeWeight G hHodge i j⟩

/-- Conserved-spine specialization of the explicit point-kernel equivalence. -/
theorem allTwoPrimitivePointTransitions_iff_hodge_weight_of_conservedSpine
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G) :
    (∀ i j : ClassicalHodgeBasisIndex V H p,
      Nonempty (TwoPrimitivePointTransitions (V := V) (H := H) i j)) ↔
      rationalHodgeSubspace (H.hodgeBigrading p) ≤
        LinearMap.range (H.cycleClass p) := by
  exact allTwoPrimitivePointTransitions_iff_hodge_weight_of_seed G
    (D.algebraicHodgeSubspace_ne_bot p)

#check twoGeneratorNative_of_hodge_weight
#check allTwoGeneratorNative_of_hodge_weight
#check allTwoGeneratorNative_iff_hodge_weight_of_seed
#check allTwoGeneratorNative_iff_hodge_weight_of_conservedSpine
#check nativePointTransitionOfLifts
#check twoPrimitivePointTransitionsOfHodgeWeight
#check allTwoPrimitivePointTransitions_iff_hodge_weight_of_seed
#check allTwoPrimitivePointTransitions_iff_hodge_weight_of_conservedSpine

#print axioms twoGeneratorNative_of_hodge_weight
#print axioms allTwoGeneratorNative_iff_hodge_weight_of_seed
#print axioms allTwoGeneratorNative_iff_hodge_weight_of_conservedSpine
#print axioms allTwoPrimitivePointTransitions_iff_hodge_weight_of_seed
#print axioms allTwoPrimitivePointTransitions_iff_hodge_weight_of_conservedSpine

end GSTClassicalHodgePlanePrimitiveCircularity
