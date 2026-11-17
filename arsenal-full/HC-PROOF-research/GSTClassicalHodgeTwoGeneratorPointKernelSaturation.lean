import GSTClassicalHodgeTwoGeneratorNativeArsenal
import GSTClassicalHodgeAlgebraicArsenalSaturation
import GSTClassicalHodgeNativeGeneratorNaturality
import GSTClassicalHodgeGeneratorwiseAtomicStability

/-!
# GST CLASSICAL HODGE — TWO PRIMITIVE POINT KERNELS SATURATE ONE HODGE WEIGHT

The geometry-first route can be weakened to the exact generator-level data
actually consumed by algebraic saturation.

For an ordered pair of genuine Hodge sheets `(i,j)`, consider the two ambient
operators already fixed by the GST two-slot construction:

* the code observable `D = diag(0,1)`;
* the two-step finite-world Lefschetz operator `L²`.

Their ambient extensions are defined independently of algebraicity and have the
correct Hodge-fiber restrictions by construction.  Therefore we do NOT need a
native operator whose independently reconstructed ambient extension agrees on
all Hodge vectors.  It is enough to prove generatorwise native lifts for these
two fixed ambient maps.

The existing native-generator theorem turns those lifts into atomic stability.
Operator closure then gives atomic stability of the normalized word

    D ∘ L² ∘ (I-D),

and the finite GST computation identifies that word on the genuine Hodge fiber
with the rank-free matrix unit `E_{i,j}`.  Thus every algebraic Hodge seed has
its complete one-step matrix-unit orbit algebraic.  One nonzero seed therefore
saturates the entire weight.

Finally, chosen `NativePointTransition`s package the remaining geometry as two
explicit pointwise cycle equations.  This is strictly weaker than the earlier
`GeometryFirstTwoGenerator`: no independently reconstructed ambient operator is
required to agree on non-algebraic Hodge vectors.
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeExplicitArsenalGeneration
open GSTClassicalHodgeUniversalTwoSlotNativeClosure
open GSTClassicalHodgeTwoGeneratorNativeArsenal
open GSTClassicalHodgeNativeGeneratorNaturality
open GSTClassicalHodgeAlgebraicArsenalSaturation
open GSTClassicalHodgeGeneratorwiseAtomicStability

namespace GSTClassicalHodgeTwoGeneratorPointKernelSaturation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

abbrev HFiber (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) (p : Nat) :=
  ClassicalHodgeFiber V H p

/-- The exact normalized two-generator ambient word. -/
noncomputable def twoGeneratorAmbientWord
    (i j : ClassicalHodgeBasisIndex V H p) :
    Module.End ℚ
      (GSTGeometricRealizationStage2F.RationalSingularCohomology
        H.analytification (2 * p)) :=
  (forwardScalar sourceSlot targetSlot : ℚ)⁻¹ •
    ((ambientTwoSlotCode i j).comp
      ((ambientTwoStepLefschetz i j).comp
        (LinearMap.id - ambientTwoSlotCode i j)))

/-- **THE TWO-GENERATOR WORD IS THE HODGE MATRIX UNIT.**
This is a pure GST/Hodge calculation; no algebraicity or native-cycle witness
is used. -/
theorem twoGeneratorAmbientWord_on_hodge
    (i j : ClassicalHodgeBasisIndex V H p)
    (hij : i ≠ j)
    (alpha : HFiber V H p) :
    twoGeneratorAmbientWord i j alpha.1 =
      (hodgeMatrixUnit i j alpha).1 := by
  let src : HFiber V H p :=
    ((LinearMap.id - twoSlotCodeHodge i j :
      ClassicalHodgeFiber V H p →ₗ[ℚ] ClassicalHodgeFiber V H p) alpha)
  let mid : HFiber V H p :=
    twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2) src
  have hcode0 := extendHodgeEndomorphism_on_hodge
    (V := V) (H := H) (twoSlotCodeHodge i j) alpha
  have hsrc :
      ((LinearMap.id - ambientTwoSlotCode i j :
        GSTGeometricRealizationStage2F.RationalSingularCohomology
          H.analytification (2 * p) →ₗ[ℚ]
        GSTGeometricRealizationStage2F.RationalSingularCohomology
          H.analytification (2 * p)) alpha.1) = src.1 := by
    simp only [LinearMap.sub_apply, LinearMap.id_apply, ambientTwoSlotCode]
    rw [hcode0]
    rfl
  have hL := extendHodgeEndomorphism_on_hodge
    (V := V) (H := H)
    (twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2)) src
  have htgt := extendHodgeEndomorphism_on_hodge
    (V := V) (H := H) (twoSlotCodeHodge i j) mid
  unfold twoGeneratorAmbientWord
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [hsrc]
  rw [show (ambientTwoStepLefschetz i j) src.1 = mid.1 from hL]
  rw [show (ambientTwoSlotCode i j) mid.1 = (twoSlotCodeHodge i j mid).1
    from htgt]
  have h01 : hodgeCoordinate i (classicalHodgeBasis V H p j) = 0 :=
    hodgeCoordinate_basis_other i j hij
  have h10 : hodgeCoordinate j (classicalHodgeBasis V H p i) = 0 :=
    hodgeCoordinate_basis_other j i (Ne.symm hij)
  have hrw : ∀ w : RationalPureWindow 2,
      finiteHodgeRead (pairBasisIndex i j)
        (finiteHodgeWrite (pairBasisIndex i j) w) = w := by
    intro w
    funext r
    fin_cases r
    · simp [finiteHodgeRead, finiteHodgeWrite, sourceSlot, targetSlot,
        pairBasisIndex, h01]
    · simp [finiteHodgeRead, finiteHodgeWrite, sourceSlot, targetSlot,
        pairBasisIndex, h10]
  have hLval : (GSTTruncatedWorldCohomologyRing.worldAct 2 2
      ((GSTTruncatedWorldCohomologyRing.L 2 2) ^ 2)
      (GSTWorldPoincareDuality.worldBasis
        (GSTGlobalPureHodgeCosmology.pureDiagonalState (0 : Fin 2)))
      (GSTGlobalPureHodgeCosmology.pureDiagonalState (1 : Fin 2))) =
      (2 : ℤ) :=
    gst_forward_scalar_receipt (N := 2) (p := sourceSlot) (q := targetSlot)
      (by decide)
  have hfs : (forwardScalar (N := 2) (0 : Fin 2) (1 : Fin 2) : ℚ) = 2 := by
    exact_mod_cast
      (show forwardScalar (N := 2) (0 : Fin 2) (1 : Fin 2) = 2 from by decide)
  simp [src, mid, twoSlotCodeHodge, twoSlotHodgeOperator,
    liftFiniteHodgeOperator, finiteHodgeRead, finiteHodgeWrite,
    pureMatrixUnit, rationalPureBasis, diagonalLefschetzQ, sheetProjectorQ,
    twoSlotCode, hodgeMatrixUnit_apply, sourceSlot, targetSlot, hrw,
    pairBasisIndex, h01, h10, hodgeCoordinate_basis_self, hLval,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply]
  rw [hfs]
  norm_num
  rw [one_div, smul_smul, ← mul_assoc,
    inv_mul_cancel₀ (by norm_num : (2:ℚ) ≠ 0), one_mul]

/-- Native two-generator point lifts force the corresponding matrix-unit image
of every already-algebraic Hodge vector to remain algebraic.
The diagonal case is the code observable itself; the off-diagonal case is
the two-generator ambient word. -/
theorem twoGeneratorNative_matrixUnit_mem_algebraic
    {i j : ClassicalHodgeBasisIndex V H p}
    (R : TwoGeneratorNative (V := V) (H := H) i j)
    (alpha : HFiber V H p)
    (halpha : alpha ∈ AlgebraicHodgeSubspace V H p) :
    hodgeMatrixUnit i j alpha ∈ AlgebraicHodgeSubspace V H p := by
  by_cases hij : i = j
  · subst j
    have hstable : AtomicSpanStable (p := p) (cl := H.cycleClass p)
        (ambientTwoSlotCode i i) := by
      rw [smoothProjective_atomicStable_iff_nativePointLifts]
      exact R.code
    have himage := hstable alpha.1 halpha
    rw [show (ambientTwoSlotCode i i) alpha.1 =
        (twoSlotCodeHodge i i alpha).1 from
      extendHodgeEndomorphism_on_hodge (V := V) (H := H)
        (twoSlotCodeHodge i i) alpha] at himage
    have hdiag : (twoSlotCodeHodge i i alpha).1 =
        (hodgeMatrixUnit i i alpha).1 := by
      simp [twoSlotCodeHodge, twoSlotHodgeOperator,
        liftFiniteHodgeOperator, finiteHodgeRead, finiteHodgeWrite,
        pureMatrixUnit, rationalPureBasis, twoSlotCode, sourceSlot,
        targetSlot, pairBasisIndex, hodgeMatrixUnit_apply,
        hodgeCoordinate_basis_self]
    rw [hdiag] at himage
    exact himage
  · have hstable : AtomicSpanStable (p := p) (cl := H.cycleClass p)
        (twoGeneratorAmbientWord i j) := by
      rw [smoothProjective_atomicStable_iff_nativePointLifts]
      simpa [twoGeneratorAmbientWord] using R.normalizedWord_nativePointLifts
    have himage := hstable alpha.1 halpha
    rw [twoGeneratorAmbientWord_on_hodge i j hij alpha] at himage
    exact himage

/-- A family of two-generator native point-lift packages makes the actual
algebraic Hodge subspace invariant under every rank-free matrix unit. -/
theorem rankFreeArsenalInvariant_of_twoGeneratorNative
    (R : ∀ i j : ClassicalHodgeBasisIndex V H p,
      TwoGeneratorNative (V := V) (H := H) i j) :
    RankFreeArsenalInvariant (AlgebraicHodgeSubspace V H p) := by
  intro i j alpha halpha
  exact twoGeneratorNative_matrixUnit_mem_algebraic (R i j) alpha halpha

/-- One nonzero algebraic seed plus the two primitive native point-lift laws
saturates the whole genuine Hodge fiber. -/
theorem algebraicHodgeSubspace_eq_top_of_twoGeneratorNative
    (hseed : AlgebraicHodgeSubspace V H p ≠ ⊥)
    (R : ∀ i j : ClassicalHodgeBasisIndex V H p,
      TwoGeneratorNative (V := V) (H := H) i j) :
    AlgebraicHodgeSubspace V H p = ⊤ := by
  exact rankFreeArsenalInvariant_eq_top
    (AlgebraicHodgeSubspace V H p)
    (rankFreeArsenalInvariant_of_twoGeneratorNative R)
    hseed

/-- The same hypotheses give the exact weight-p Hodge landing. -/
theorem hodge_weight_of_twoGeneratorNative
    (hseed : AlgebraicHodgeSubspace V H p ≠ ⊥)
    (R : ∀ i j : ClassicalHodgeBasisIndex V H p,
      TwoGeneratorNative (V := V) (H := H) i j) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  have htop := algebraicHodgeSubspace_eq_top_of_twoGeneratorNative hseed R
  intro alpha halpha
  let a : HFiber V H p := ⟨alpha, halpha⟩
  have ha : a ∈ AlgebraicHodgeSubspace V H p := by
    rw [htop]
    trivial
  rw [GSTClassicalHodgeAtomicSpan.smoothProjective_cycleClass_range_eq_atomic_span V H p]
  exact ha

/-- Generator-level data for the two fixed ambient GST primitives. -/
structure TwoPrimitivePointTransitions
    (i j : ClassicalHodgeBasisIndex V H p) where
  code : NativePointTransition
    (p := p) (cl := H.cycleClass p) (ambientTwoSlotCode i j)
  lefschetz : NativePointTransition
    (p := p) (cl := H.cycleClass p) (ambientTwoStepLefschetz i j)

namespace TwoPrimitivePointTransitions

/-- Pointwise native transitions immediately supply the older existential
`TwoGeneratorNative` package. -/
def toTwoGeneratorNative
    {i j : ClassicalHodgeBasisIndex V H p}
    (K : TwoPrimitivePointTransitions (V := V) (H := H) i j) :
    TwoGeneratorNative (V := V) (H := H) i j where
  code := K.code.hasNativePointLifts
  lefschetz := K.lefschetz.hasNativePointLifts

end TwoPrimitivePointTransitions

/-- **POINT-KERNEL SATURATION CROWN.**
The complete fixed-weight Hodge target follows from one nonzero algebraic seed
and, for every ordered pair of Hodge sheets, two concrete pointwise native
transition constructions: the GST code observable and the GST two-step
Lefschetz observable. -/
theorem hodge_weight_of_two_primitive_point_transitions
    (hseed : AlgebraicHodgeSubspace V H p ≠ ⊥)
    (K : ∀ i j : ClassicalHodgeBasisIndex V H p,
      TwoPrimitivePointTransitions (V := V) (H := H) i j) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  exact hodge_weight_of_twoGeneratorNative hseed
    (fun i j => (K i j).toTwoGeneratorNative)

#check twoGeneratorAmbientWord
#check twoGeneratorAmbientWord_on_hodge
#check twoGeneratorNative_matrixUnit_mem_algebraic
#check rankFreeArsenalInvariant_of_twoGeneratorNative
#check algebraicHodgeSubspace_eq_top_of_twoGeneratorNative
#check hodge_weight_of_twoGeneratorNative
#check TwoPrimitivePointTransitions
#check hodge_weight_of_two_primitive_point_transitions

#print axioms twoGeneratorAmbientWord_on_hodge
#print axioms twoGeneratorNative_matrixUnit_mem_algebraic
#print axioms hodge_weight_of_twoGeneratorNative
#print axioms hodge_weight_of_two_primitive_point_transitions

end GSTClassicalHodgeTwoGeneratorPointKernelSaturation
